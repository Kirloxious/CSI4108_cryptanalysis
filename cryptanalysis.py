import random
import numpy as np

seed = 16
np.random.seed(seed)

#Split 16-bit data block into 4x4 sub-blocks to have a 4x4 S-box with 4 bit input and 4 bit output
def gen_s_box():
    sbox = [11, 12, 3, 13, 2, 7, 6, 8, 0, 10, 4, 1, 5, 15, 14, 9]
    return sbox

#5 16-bit round keys
def gen_round_keys():
    np.random.seed(100)
    keys = np.random.randint((2**16) - 1 , size=5, dtype=np.uint16)
    return keys

#10_000 16-bit plaintext strings
def gen_plaintext():
    strings = np.random.randint((2**16) - 1 , size=10_000, dtype=np.uint16)
    return strings

#Split a 16-bit int into 4 4-bit blocks
def bit_split(x):
    # force x to be 16 bits
    x = x & 0xffff

    return [(x >> (12 - 4 * i)) & 0xf for i in range(4)]

def bit_combine(blocks):
    n = 0 & 0xffff
    for b in blocks:
        n = ((n << 4) | b) & 0xffff
    return n

# Define a bit permutation function
def permute_bits(x):
    perm = [0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15] 
    # Permute bits according to the pattern
    permuted = 0
    for i in range(16):
        if (x >> i) & 1:
            permuted |= (1 << perm[i])

    return permuted & 0xffff

def apply_s_box(s_box, blocks):
    for i in range(0, 4):
        blocks[i] = s_box[blocks[i]]
    return blocks
        

#Encrypt plaintext with simple Feistel structuture with 5 round keys
def encrypt(text, keys, s_box):
    blocks = bit_split(text)
    for r in range(0, len(keys)-2):

        blocks = apply_s_box(s_box, blocks)

        text = bit_combine(blocks)

        #apply bit permutation
        text = permute_bits(text)
        b = bit_split(text)

        #XOR with round key
        text = text ^ keys[r]

        #split for next round
        blocks = bit_split(text)

    # Final round with no bit permutation
    blocks = apply_s_box(s_box, blocks)
    text = bit_combine(blocks)
    text = text ^ keys[-1]
    
    return text

def save_cipher(cipher):
    file = open("cipher.txt", "w")
    for c in cipher:
        file.write(f"{c} ")

    file.close()


class Diff_Analysis:

    def __init__(self) -> None:
        self.ddt = None
        self.best_pairs = None
        self.best_characteristic = None
        self.best_probability = None
        self.input_diff = None
        self.expected_output_diff = None
        self.chosen_ciphertext_pairs = None
        self.s_box = None
        self.inv_sbox = None


    # Generate the difference distribution table for a given S-box
    def difference_distribution_table(self, s_box):
        self.s_box = s_box
        ddt = np.zeros((16, 16), dtype=int)
        for x in range(16):
            for delta_x in range(16):
                x_prime = x ^ delta_x
                delta_y = s_box[x] ^ s_box[x_prime]
                ddt[delta_x][delta_y] += 1
        self.ddt = ddt
        return ddt

    def difference_pairs(self):
        best_pairs = []
        for delta_in in range(1, 16):
            # Find the output difference with the highest probability for this input difference
            max_freq = np.max(self.ddt[delta_in])
            output_diff = np.argmax(self.ddt[delta_in])
            best_pairs.append((delta_in, output_diff, max_freq))
        best_pairs.sort(key=lambda x: x[0])
        self.best_pairs = best_pairs
        return best_pairs

    # Compute the best differential probability for each possible first round input difference
    def compute_best_differential_probability(self, rounds=3):
        s_box_traces = []
        for pair in self.best_pairs:
            for i in range(1, 4):
                probability = 1
                s_box_trace = []
                # change which first input difference U1 to start with (ie: S11, S12, S13, S14)
                p = pair[0] << (4 * i)
                for r in range(1, rounds+1):
                    bits = bit_split(p)
                    for j in range(4):
                        if bits[j] != 0:
                            # The highest probable output bit of s_box according to difference distribution table
                            output_pair = self.best_pairs[bits[j]-1]
                            bits[j] = output_pair[1]

                            # Add probability of this output bit to total probability
                            probability *= (output_pair[2] / 16)
                            s_box_trace.append((r, j+1, output_pair))
                    p = bit_combine(bits)
                    p = permute_bits(p)

                s_box_traces.append((s_box_trace, probability, p))

        s_box_traces.sort(key=lambda x: x[1], reverse=True)
        self.best_characteristic = s_box_traces[0]
        self.best_probability = self.best_characteristic[1]
        self.input_diff =  self.best_characteristic[0][0][2][0] << (4 * (4 - self.best_characteristic[0][0][1]))
        self.expected_output_diff =  self.best_characteristic[len(self.best_characteristic)-1]
        return s_box_traces
    
    def choose_random_plaintext():
        return random.randint(0, 0xffff)

    def generate_chosen_ciphertext_pairs(self, s_box, keys, plaintexts):
        pairs = [] 
        for i in range(len(plaintexts)):
            #XOR with input_difference to get chosen plaintext
            pt1 = plaintexts[i] 
            pt2 = pt1 ^ self.input_diff
            ct1 = encrypt(pt1, keys, s_box)
            ct2 = encrypt(pt2, keys, s_box)
            pairs.append((ct1, ct2))
        return pairs

    def partial_decrypt(inv_sbox, ciphertext, partial_subkey):
        cipher_bits = bit_split(ciphertext)
        key_bits = bit_split(partial_subkey)
        result_bits = [0, 0, 0, 0]
        #XOR ciphertext with key, then apply inverse sbox
        for i in range(4):
            result_bits[i] = inv_sbox[cipher_bits[i] ^ key_bits[i]] 
        return bit_combine(result_bits)

    # Define a function to extract 8 arbitrary bits of the 16-bit round key
    def differential_attack(self, ciphertext_pairs):
        self.inv_sbox = [self.s_box.index(i) if i in self.s_box else i for i in range(len(self.s_box))]

        #generate all possible subkeys for [K5,5 .. K5,8 ; K5,13 .. K5,16]
        possible_subkeys = []
        for i in range(16):
            for j in range(16):
                key = bit_combine([0, i, 0, j])
                possible_subkeys.append(key)

        subkey_counts = dict()

        for ct1, ct2 in ciphertext_pairs:
                #ciphertext difference
                ct_diff = ct1 ^ ct2

                #filter out wrong pairs where zeros do not appear in blocks 1 and 3
                #since the input difference only influences blocks 2 and 4
                if(ct_diff & 0xf0f0) != 0:
                    continue

                for partial_subkey in possible_subkeys:
                    #Partial decrypt with all possible subkeys
                    dec1 = Diff_Analysis.partial_decrypt(self.inv_sbox, ct1, partial_subkey)
                    dec2 = Diff_Analysis.partial_decrypt(self.inv_sbox, ct2, partial_subkey)
                    
                    key_block = bit_split(partial_subkey)
                    key_str = f"{key_block[1]:1x} {key_block[3]:1x}"

                    #XOR partial decrypted to find expected output difference
                    if(dec1 ^ dec2) == self.expected_output_diff:
                        if key_str not in subkey_counts:
                            subkey_counts[key_str] = 1
                        else:
                            subkey_counts[key_str] += 1
            
        best_subkey = max(subkey_counts, key=subkey_counts.get)
        subkey_counts = {key: value / len(ciphertext_pairs) for key, value in subkey_counts.items()}
        return best_subkey, subkey_counts
    
def print_formatted_hex(message, n):
    blocks = bit_split(n)
    print(f"{message}: {blocks[0]:1x} {blocks[1]:1x} {blocks[2]:1x} {blocks[3]:1x}")

def print_formatted_binary(message, n):
    blocks = bit_split(n)
    print(f"{message}: {blocks[0]:04b} {blocks[1]:04b} {blocks[2]:04b} {blocks[3]:04b}")

def print_subkey_table(subkey_table):
    print("[K5..K8, K13..K16]   Prob")
    for key, prob in sorted(subkey_table.items(), key=lambda item: item[1], reverse=True):
        print(f"      [{key}]         {prob}")
    pass

#Shared for Person 1 & 2
sbox = gen_s_box()
diff_analysis = Diff_Analysis()
diff_analysis.difference_distribution_table(sbox)
diff_analysis.difference_pairs()
diff_analysis.compute_best_differential_probability()

#Hidden from Person 2
round_keys = gen_round_keys()
plaintexts = gen_plaintext()

#Encryption of plaintexts with half as being encrypted as chosen plaintexts
ciphertext_pairs = diff_analysis.generate_chosen_ciphertext_pairs(sbox, round_keys, plaintexts)

print(f"S-box: {sbox}")
print_formatted_binary("5th Round key", round_keys[4])

print(f"Difference distribution table: \n{diff_analysis.ddt}\n")

print("S-box Trail:")
for trace in diff_analysis.best_characteristic[0]:
    print(f"S-box{trace[0]}{trace[1]}: Input = {trace[2][0]}, Output = {trace[2][1]}, Probability = {trace[2][2]}/16")
print_formatted_binary("Plaintext with highest probability of encryption (Input difference)", diff_analysis.input_diff)
print_formatted_binary("Expected output difference", diff_analysis.expected_output_diff)

print(f"Probability of plaintext encrypted: {diff_analysis.best_probability*100}%") 



#Person 2 Analysis

best_subkey, subkey_counts = diff_analysis.differential_attack(ciphertext_pairs)

print("Recovered partial subkey: ", best_subkey)
print_subkey_table(subkey_counts)

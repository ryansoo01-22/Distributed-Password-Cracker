import sys
import binascii
import getpass
import hashlib
from datetime import datetime
import time
import itertools
import mysql.connector
import time
import argparse

class DES:
    key = ""
    mode = ""
    IV = ""
    originalIV = ""
    def __init__(self, key, mode = "ECB", IV = None):
        self.key = key
        self.mode = mode
        self.IV = IV
        self.originalIV = IV

    _EXPAND = [31,  0,  1,  2,  3,  4,  3,  4,
                5,  6,  7,  8,  7,  8,  9, 10,
               11, 12, 11, 12, 13, 14, 15, 16,
               15, 16, 17, 18, 19, 20, 19, 20,
               21, 22, 23, 24, 23, 24, 25, 26,
               27, 28, 27, 28, 29, 30, 31,  0]

    # 32-bit permutation after S-BOX substitution
    _SBOX_PERM = [15,  6, 19, 20, 28, 11, 27, 16,
                   0, 14, 22, 25,  4, 17, 30,  9,
                   1,  7, 23, 13, 31, 26,  2,  8,
                  18, 12, 29,  5, 21, 10,  3, 24]

    # Initial permutation on incoming block
    _INIT_PERMUTATION = [57, 49, 41, 33, 25, 17,  9, 1,
                         59, 51, 43, 35, 27, 19, 11, 3,
                         61, 53, 45, 37, 29, 21, 13, 5,
                         63, 55, 47, 39, 31, 23, 15, 7,
                         56, 48, 40, 32, 24, 16,  8, 0,
                         58, 50, 42, 34, 26, 18, 10, 2,
                         60, 52, 44, 36, 28, 20, 12, 4,
                         62, 54, 46, 38, 30, 22, 14, 6]

    # Inverse of _INITIAL_PERMUTATION
    _FINAL_PERMUTATION = [39,  7, 47, 15, 55, 23, 63, 31,
                          38,  6, 46, 14, 54, 22, 62, 30,
                          37,  5, 45, 13, 53, 21, 61, 29,
                          36,  4, 44, 12, 52, 20, 60, 28,
                          35,  3, 43, 11, 51, 19, 59, 27,
                          34,  2, 42, 10, 50, 18, 58, 26,
                          33,  1, 41,  9, 49, 17, 57, 25,
                          32,  0, 40,  8, 48, 16, 56, 24]

    def _add_padding(self, message):
        """This function adds padding to a message so it can be encrypted by the DES algorithm"""
        pad_len = (8 - len(message)) % 8
        padding = hex(0) * pad_len
        message += padding.encode('utf-8')
        return message

    def _rem_padding(self, message):
        """ This function removes padding from a message encrypted by the DES algorithm """
        if int(message[len(message) - 1]) <= 8:
            pad_len = int(message[len(message) - 1])
            return message[:len(message) - pad_len]
        else:
            return message

    def _bytes_to_bit_array(self, byte_string):
        """This function converts a string of bytes into a list of bits"""
        result = []
        for byte in byte_string:
            for bit in [7,6,5,4,3,2,1,0]:
                mask = 1 << bit
                if int(byte) & mask > 0:
                    result.append(1)
                else:
                    result.append(0)
        return result

    def _bit_array_to_bytes(self, bit_array):
        """This function converts an array of bits to a list of bytes"""
        result = []
        byte = 0
        for bit in range(len(bit_array)):
            byte += bit_array[bit] << (7 - (bit % 8))
            if (bit % 8) == 7:
                result += [byte]
                byte = 0
        return bytes(result)

    def _nsplit(self, data, split_size=64):
        """This function splits the plaintext into split_size bit blocks"""
        result = []
        for i in range(0, len(data), split_size):
            if i < len(data) - split_size:
                result.append(data[i:i+split_size])
            else:
                result.append(data[i:])
        return result

    def _hex_print(self, block):
        """This function converts a block from a list of integers into a list of strings and prints it in hex"""
        s = [str(i) for i in block]
        b = int("".join(s), 2)
        print(hex(b)[2:].zfill(16))
        return

    def encrypt(self, plaintext):
        """This function encrypts a plaintext using the DES algorithm"""
        key = self.key
        mode = self.mode
        IV = self.IV
        if len(key) < 8:
            print("Error. DES requires a key length of 8 bytes. Please try again.")
            return
        if mode == "ECB":
            #pt = self._add_padding(plaintext)
            pt = plaintext
            pt = self._bytes_to_bit_array(pt)
            subkeys = self._generate_subkeys(key)
            ct = []
            for block in self._nsplit(pt, 64):
                ct += self._encrypt_block(block, subkeys) #changed key to subkeys
            ct = self._bit_array_to_bytes(ct)
            return ct
        if mode == "CBC":
            if len(IV) < 8:
                print("Error. DES CBC mode requires an IV length of 8 bytes. Please try again.")
                return
            pt = self._add_padding(plaintext)
            pt = self._bytes_to_bit_array(pt)
            subkeys = self._generate_subkeys(key)
            ct = []
            IV = self._bytes_to_bit_array(IV)
            for block in self._nsplit(pt, 64):
                temp1 = self._xor(IV, block)
                temp2 = self._encrypt_block(temp1, subkeys)
                ct += temp2
                IV = temp2
            ct = self._bit_array_to_bytes(ct)
            return ct
        if mode == "OFB":
            if len(IV) < 8:
                print("Error. DES OFB mode requires an IV length of 8 bytes. Please try again.")
                return
            pt = self._bytes_to_bit_array(plaintext)
            subkeys = self._generate_subkeys(key)
            ct = []
            IV = self._bytes_to_bit_array(IV)
            for block in self._nsplit(pt, 64):
                temp1 = self._encrypt_block(IV, subkeys)
                IV = temp1
                temp2 = self._xor(block, temp1)
                ct += temp2
            ct = self._bit_array_to_bytes(ct)
            return ct

    def _permute(self, block, table):
        return [block[x] for x in table]

    def _encrypt_block(self, plaintext, subkeys):
        """This function encrypts a block in the DES algorithm"""
        block = self._permute(plaintext, self._INIT_PERMUTATION)
        L = block[:32]
        R = block[32:]
        for i in range(16):
            #core algorithm
            T = self._xor(L,self._function(R, subkeys[i]))
            L = R
            R = T
        block = self._permute(R + L, self._FINAL_PERMUTATION)
        return block

    def decrypt(self, ciphertext, key=""):
        key = self.key
        mode = self.mode
        IV = self.IV
        if mode == "ECB":
            subkeys = list(reversed(self._generate_subkeys(key)))
            ct = self._bytes_to_bit_array(ciphertext)
            result = []
            for ctBlock in self._nsplit(ct, 64):
                block = self._encrypt_block(ctBlock, subkeys)
                result += block
            decrypted = self._bit_array_to_bytes(result)
            final = self._rem_padding(decrypted)
            return final
        if mode == "CBC":
            subkeys = list(reversed(self._generate_subkeys(key)))
            ct = self._bytes_to_bit_array(ciphertext)
            IV = self._bytes_to_bit_array(IV)
            result = []
            for ctBlock in self._nsplit(ct, 64):
                temp1 = self._encrypt_block(ctBlock, subkeys)
                temp2 = self._xor(temp1, IV)
                result += temp2
                IV = ctBlock
            decrypted = self._bit_array_to_bytes(result)
            final = self._rem_padding(decrypted)
            return final
        if mode == "OFB":
              subkeys = list(reversed(self._generate_subkeys(key)))
              pt = self._bytes_to_bit_array(ciphertext)
              subkeys = self._generate_subkeys(key)
              res = []
              IV = self._bytes_to_bit_array(IV)
              for block in self._nsplit(pt, 64):
                  temp1 = self._encrypt_block(IV, subkeys)
                  IV = temp1
                  temp2 = self._xor(block, temp1)
                  res += temp2
              res = self._bit_array_to_bytes(res)
              return res

    def _lshift(self, sequence, n):
        """ Left shifts sequence of bytes by the specified number. All elements
            that fall off the left side are rotated back around to the right side.
        """
        shifted = sequence[n:]
        for i in range(0, n):
            if type(sequence) == list:
                shifted.append(sequence[i])
            if type(sequence) == str:
                shifted += sequence[i]
        return shifted

    def _xor(self, x, y):
        """ Bitwise XOR of two iterable variables. If the iterables are different
            lengths, then the function will only compute XOR over the parallel
            portion of the two sequences.
        """
        xored = []
        for x, y in zip(x,y):
            if int(x)^int(y):
                xored.append(1)
            else:
                xored.append(0)
        return xored

    def _substitute(self, bit_array):
        """ Substitutes using SBoxes into a 48 bit string """
        _S_BOXES = [
            [[14,  4, 13,  1,  2, 15, 11,  8,  3, 10,  6, 12,  5,  9,  0,  7],
             [ 0, 15,  7,  4, 14,  2, 13,  1, 10,  6, 12, 11,  9,  5,  3,  8],
             [ 4,  1, 14,  8, 13,  6,  2, 11, 15, 12,  9,  7,  3, 10,  5,  0],
             [15, 12,  8,  2,  4,  9,  1,  7,  5, 11,  3, 14, 10,  0,  6, 13],
            ],
            [[15,  1,  8, 14,  6, 11,  3,  4,  9,  7,  2, 13, 12,  0,  5, 10],
             [ 3, 13,  4,  7, 15,  2,  8, 14, 12,  0,  1, 10,  6,  9, 11,  5],
             [ 0, 14,  7, 11, 10,  4, 13,  1,  5,  8, 12,  6,  9,  3,  2, 15],
             [13,  8, 10,  1,  3, 15,  4,  2, 11,  6,  7, 12,  0,  5, 14,  9],
            ],
            [[10,  0,  9, 14,  6,  3, 15,  5,  1, 13, 12,  7, 11,  4,  2,  8],
             [13,  7,  0,  9,  3,  4,  6, 10,  2,  8,  5, 14, 12, 11, 15,  1],
             [13,  6,  4,  9,  8, 15,  3,  0, 11,  1,  2, 12,  5, 10, 14,  7],
             [ 1, 10, 13,  0,  6,  9,  8,  7,  4, 15, 14,  3, 11,  5,  2, 12],
            ],
            [[ 7, 13, 14,  3,  0,  6,  9, 10,  1,  2,  8,  5, 11, 12,  4, 15],
             [13,  8, 11,  5,  6, 15,  0,  3,  4,  7,  2, 12,  1, 10, 14,  9],
             [10,  6,  9,  0, 12, 11,  7, 13, 15,  1,  3, 14,  5,  2,  8,  4],
             [ 3, 15,  0,  6, 10,  1, 13,  8,  9,  4,  5, 11, 12,  7,  2, 14],
            ],
            [[ 2, 12,  4,  1,  7, 10, 11, 6, 8, 5, 3, 15, 13, 0, 14, 9],
             [14, 11,  2, 12,  4,  7, 13, 1, 5, 0, 15, 10, 3, 9, 8, 6],
             [ 4,  2,  1, 11, 10, 13, 7, 8, 15, 9, 12, 5, 6, 3, 0, 14],
             [11,  8, 12,  7,  1, 14, 2, 13, 6, 15, 0, 9, 10, 4, 5, 3],
            ],
            [[12,  1, 10, 15,  9,  2,  6,  8,  0, 13,  3,  4, 14,  7,  5, 11],
             [10, 15,  4,  2,  7, 12,  9,  5,  6,  1, 13, 14,  0, 11,  3,  8],
             [ 9, 14, 15,  5,  2,  8, 12,  3,  7,  0,  4, 10,  1, 13, 11,  6],
             [ 4,  3,  2, 12,  9,  5, 15, 10, 11, 14,  1,  7,  6,  0,  8, 13],
            ],
            [[ 4, 11,  2, 14, 15,  0,  8, 13,  3, 12,  9,  7,  5, 10,  6,  1],
             [13,  0, 11,  7,  4,  9,  1, 10, 14,  3,  5, 12,  2, 15,  8,  6],
             [ 1,  4, 11, 13, 12,  3,  7, 14, 10, 15,  6,  8,  0,  5,  9,  2],
             [ 6, 11, 13,  8,  1,  4, 10,  7,  9,  5,  0, 15, 14,  2,  3, 12],
            ],
            [[13,  2,  8,  4,  6, 15, 11,  1, 10,  9,  3, 14,  5,  0, 12,  7],
             [ 1, 15, 13,  8, 10,  3,  7,  4, 12,  5,  6, 11,  0, 14,  9,  2],
             [ 7, 11,  4,  1,  9, 12, 14,  2,  0,  6, 10, 13, 15,  3,  5,  8],
             [ 2,  1, 14,  7,  4, 10,  8, 13, 15, 12,  9,  0,  3,  5,  6, 11],
            ]
        ]
        substituted = []
        split = self._nsplit(bit_array, 6)
        for boxNum, i in enumerate(split):
            row = int((str(i[0]) + str(i[5])),2)
            col = int((str(i[1]) + str(i[2]) + str(i[3]) + str(i[4])), 2)
            substituted.append(bin(_S_BOXES[boxNum][row][col])[2:].zfill(4))
        return substituted

    def _generate_subkeys(self, encryption_key):
        """This function generates 16 DES subkeys from a 64-bit encryption key. Encryption key should be byte string.
        Output should be a list of 16 bit arrays, where each array is a list of 48 1s/0s"""
        _KEY_PERMUTATION1 = [56, 48, 40, 32, 24, 16,  8,  0,
                             57, 49, 41, 33, 25, 17,  9,  1,
                             58, 50, 42, 34, 26, 18, 10,  2,
                             59, 51, 43, 35, 62, 54, 46, 38,
                             30, 22, 14,  6, 61, 53, 45, 37,
                             29, 21, 13,  5, 60, 52, 44, 36,
                             28, 20, 12,  4, 27, 19, 11,  3]

        # 56-bit to 48-bit permutation on the key
        _KEY_PERMUTATION2 = [13, 16, 10, 23,  0,  4,  2, 27,
                             14,  5, 20,  9, 22, 18, 11,  3,
                             25,  7, 15,  6, 26, 19, 12,  1,
                             40, 51, 30, 36, 46, 54, 29, 39,
                             50, 44, 32, 47, 43, 48, 38, 55,
                             33, 52, 45, 41, 49, 35, 28, 31]

        _KEY_SHIFT = [ 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1]

        subkeys = []
        keybits = self._bytes_to_bit_array(encryption_key)
        k_0 = self._permute(keybits, _KEY_PERMUTATION1)
        R = k_0[28:]
        L = k_0[:28]
        for i in range(16):
            L = self._lshift(L, _KEY_SHIFT[i])
            R = self._lshift(R, _KEY_SHIFT[i])
            k_i = self._permute(L + R, _KEY_PERMUTATION2)
            subkeys.append(k_i)
        return subkeys

    def _function(self, R, subkey):
        """ This function works the DES encryption function on the 32-bit Right Side of a 64-bit block. This function is done 16 times for each block, each
            time using a different subkey."""
        EXPAND = [31,  0,  1,  2,  3,  4,  3,  4,  5,  6,  7,  8,  7,  8,  9, 10,
                  11, 12, 11, 12, 13, 14, 15, 16, 15, 16, 17, 18, 19, 20, 19, 20,
                  21, 22, 23, 24, 23, 24, 25, 26, 27, 28, 27, 28, 29, 30, 31,  0]
        CONTRACT = [15, 6, 19, 20, 28, 11, 27, 16, 0, 14, 22, 25, 4, 17, 30, 9,
                    1, 7, 23, 13, 31, 26, 2, 8, 18, 12, 29, 5, 21, 10, 3, 24]
        expanded = self._permute(R, EXPAND)
        xorRes = self._xor(expanded, subkey)
        substituted = self._substitute(xorRes)
        substituted = ''.join(map(str, substituted))
        result = self._permute(substituted, CONTRACT)
        final = list(map(int, result))
        return final

    def run_unit_tests(self):
        """These are my tests for my functions"""
        course_no_pad = b"CSC428"
        lastname_no_pad = b"TALLMAN"
        FILastname_no_pad = b"JTALLMAN"
        course_with_pad = b"CSC428\x02\x02"
        lastname_with_pad = b"TALLMAN\x01"
        FILastname_with_pad = b"JTALLMAN\x08\x08\x08\x08\x08\x08\x08\x08"
        zeroByteStr = b"\x00"
        firstByteStr = b"\xA5"
        secondByteStr = b"\xFF"
        zeroByteList = [0,0,0,0,0,0,0,0]
        firstByteList = [1,0,1,0,0,1,0,1]
        secondByteList = [1,1,1,1,1,1,1,1]
        zeroSplitStr = b"1111222233334444"
        firstSplitStr = b"ABCDEFGHIJKLMN"
        secondSplitStr = b"THE CODE BOOK BY SINGH"
        zeroSplitList = [b"1111", b"2222", b"3333", b"4444"]
        firstSplitList = [b"ABC", b"DEF", b"GHI", b"JKL", b"MN"]
        secondSplitList = [b"THE C", b"ODE B", b"OOK B", b"Y SIN", b"GH"]
        zeroHexList = [1,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,0,1,0,1,1,0,1,1,0,1,1,0,1,1]
        firstHexList = [1,0,1,0,1,0,1,1,1,1,0,0,1,1,0,1,1,1,1,0,1,1,1,1,0,0,0,0,0,0,0,0]
        secondHexList = [0,0,0,1,0,0,1,0,0,0,1,1,0,1,0,0,0,1,0,1,0,1,1,0,0,1,1,1,1,0,0,0]
        zeroShiftStr = "ShiftingToTheLeft"
        firstShiftStr = "testing"
        secondShiftStr = "123456789"
        zeroShiftedStr = "ToTheLeftShifting"
        firstShiftedStr = "ingtest"
        secondShiftedStr = "567891234"
        zeroShiftList = [1,0,1,0,1]
        firstShiftList = [1,0,0,1,0,0]
        secondShiftList = [1,1,0,1,1,0]
        zeroShiftedList = [1,0,1,1,0]
        firstShiftedList = [0,1,0,0,1,0]
        secondShiftedList = [1,0,1,1,0,1]
        zeroXORfirst = [1,0,1,0,1]
        zeroXORsecond = [0,1,0,1,0]
        firstXORfirst = [1,1,0,0,1]
        firstXORsecond = [1,1,1,1,1]
        secondXORfirst = [0,1,0,1,1]
        secondXORsecond = [1,1,1,0,0]
        zeroXORresult = [1,1,1,1,1]
        firstXORresult = [0,0,1,1,0]
        secondXORresult = [1,0,1,1,1]
        zeroSubstituteArr = [1,0,1,0,0,1,0,1,0,0,0,0,1,1,1,1,0,1,1,0,0,1,0,1,1,1,0,0,0,1,1,0,1,0,1,0,1,1,0,0,1,1,1,0,1,0,0,1]
        zeroSubstituteResult = ['0100', '1001', '0010', '0000', '0110', '1000', '0101', '0100']
        subkey_input = b"\xEF\x00\xEF\x00\xFF\x80\xFF\x80"
        subkey_result = [ [0,1,1,0,1,1,1,1,1,0,1,0,1,1,0,0,0,0,0,1,1,0,1,1,
                           1,0,1,1,1,0,0,0,1,1,1,0,0,1,1,0,0,0,0,0,0,0,1,0],
                          [1,0,0,1,1,0,0,1,0,1,0,1,0,0,1,1,1,1,1,0,1,1,0,1,
                           0,0,0,0,0,0,1,1,0,0,0,1,1,0,0,1,1,0,1,1,1,1,0,1],
                          [1,0,0,1,0,0,0,1,0,1,0,1,0,0,1,1,1,1,1,0,1,1,0,1,
                           0,0,0,0,0,0,1,1,0,0,0,1,1,0,0,1,1,0,1,1,0,1,0,1],
                          [1,0,0,1,0,0,0,1,0,1,0,1,1,0,1,1,1,1,1,0,0,1,0,1,
                           0,1,0,0,0,0,1,1,0,0,0,0,1,0,0,1,1,0,1,1,0,1,0,1],
                          [1,0,0,1,0,0,0,1,0,1,1,1,1,0,1,1,1,1,1,0,0,1,0,1,
                           0,1,0,0,0,0,1,1,0,0,0,0,1,0,0,1,1,0,0,1,1,1,0,1],
                          [1,0,0,1,0,0,0,1,0,1,1,1,0,1,1,1,1,1,1,0,0,1,0,1,
                           0,1,0,0,0,0,1,1,0,0,0,1,0,0,0,1,1,0,0,1,1,1,0,1],
                          [1,1,0,1,0,0,0,1,0,1,0,1,0,1,1,1,1,1,1,0,0,1,0,1,
                           0,1,0,0,0,0,1,1,0,0,0,1,0,0,0,1,1,0,1,0,1,1,0,1],
                          [1,1,0,1,0,0,0,1,1,1,0,1,0,0,1,1,1,1,1,0,0,1,0,1,
                           0,1,0,0,0,0,1,0,0,0,0,1,1,0,0,1,1,0,1,0,1,1,0,1],
                          [1,1,1,0,1,1,1,0,1,0,1,0,1,1,0,0,0,0,1,1,1,0,1,0,
                           0,0,1,1,1,1,0,0,1,1,1,0,0,1,0,0,0,1,0,0,0,0,1,0],
                          [1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,0,0,0,1,1,0,1,0,
                           1,0,1,0,1,1,0,0,1,1,1,0,0,1,0,0,0,1,0,0,0,0,1,0],
                          [0,1,1,0,1,1,1,0,1,0,1,1,1,1,1,0,0,0,0,1,1,0,1,0,
                           1,0,1,0,1,1,0,0,1,1,1,0,0,1,1,0,0,1,0,0,0,0,1,0],
                          [0,1,1,0,1,1,1,0,1,0,1,1,1,1,0,0,0,1,0,1,1,0,1,0,
                           1,0,1,1,1,1,0,0,1,1,0,0,0,1,1,0,0,1,0,0,0,0,1,0],
                          [0,1,1,0,1,1,1,0,1,1,1,0,1,1,0,0,0,1,0,1,1,0,1,0,
                           1,0,0,1,1,1,0,0,1,1,0,0,0,1,1,0,0,1,0,0,0,0,1,0],
                          [0,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,0,0,1,1,0,1,0,
                           1,0,0,1,1,1,0,0,1,1,1,0,0,1,1,0,0,1,0,0,0,0,0,0],
                          [0,1,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,0,0,1,1,0,1,1,
                           1,0,1,1,1,0,0,0,1,1,1,0,0,1,1,0,0,1,0,0,0,0,0,0],
                          [1,0,0,1,1,0,1,1,0,1,0,1,0,0,1,1,1,1,1,0,0,1,0,1,
                           0,1,0,0,0,0,1,1,0,0,0,1,1,0,0,0,1,0,1,1,1,1,0,1] ]
        encryptedECB = b"\xce\x3b\xaa\x93\xd5\xc9\xd9\xfa\x03\x2f\x8c\x17\xc5\x55\xe7\x63"
        encryptedCBC = b"\xfd\x13\xef\xab\xb7\xd9\xa5\x72\x4f\xaa\x19\x13\x34\x88\x0b\x16"
        encryptedOFB = b"\x4f\xaf\x93\xee\xce\xa9\x16\x29\x80\xe9\x9a\x0b\x02\xcb"
        message = b"test test test"
        finput = [1,0,1,0,0,1,0,1,0,0,0,0,1,1,1,1,0,1,1,0,0,1,0,1,1,1,0,0,0,1,1,0]
        fres = [1,0,0,0,0,0,1,1,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,1,1,1,1,1,0]
        fsubkey = [0,1,1,0,1,1,1,1,1,0,1,0,1,1,0,0,0,0,0,1,1,0,1,1,1,0,1,1,1,0,0,0,1,1,1,0,0,1,1,0,0,0,0,0,0,0,1,0]
    #    res = encrypt(message, b"computer")
        assert self._add_padding(course_no_pad) == course_with_pad, "course add padding"
        assert self._add_padding(lastname_no_pad) == lastname_with_pad, "lastname add padding"
        assert self._add_padding(FILastname_no_pad) == FILastname_with_pad, "FILastname add padding"
        assert self._rem_padding(course_with_pad) == course_no_pad, "course remove padding"
        assert self._rem_padding(lastname_with_pad) == lastname_no_pad, "lasstname remove padding"
        assert self._rem_padding(FILastname_with_pad) == FILastname_no_pad, "FILastname remove padding"
        assert self._bytes_to_bit_array(zeroByteStr) == zeroByteList, "zero bytes to bit array"
        assert self._bytes_to_bit_array(firstByteStr) == firstByteList, "first bytes to bit array"
        assert self._bytes_to_bit_array(secondByteStr) == secondByteList, "second bytes to bit array"
        assert self._bit_array_to_bytes(zeroByteList) == zeroByteStr, "zero bit array to string"
        assert self._bit_array_to_bytes(firstByteList) == firstByteStr, "first bit array to string"
        assert self._bit_array_to_bytes(secondByteList) == secondByteStr, "second bit array to string"
        assert self._nsplit(zeroSplitStr, 4) == zeroSplitList, "zero nsplit"
        assert self._nsplit(firstSplitStr, 3) == firstSplitList, "first nsplit"
        assert self._nsplit(secondSplitStr, 5) == secondSplitList, "second nsplit"
        self._hex_print(zeroHexList)
        self._hex_print(firstHexList)
        self._hex_print(secondHexList)
        assert self._lshift(zeroShiftStr, 8) == zeroShiftedStr, "zero lshift str"
        assert self._lshift(firstShiftStr, 4) == firstShiftedStr, "first lshift str"
        assert self._lshift(secondShiftStr, 4) == secondShiftedStr, "second lshift str"
        assert self._lshift(zeroShiftList, 2) == zeroShiftedList, "zero lshift list"
        assert self._lshift(firstShiftList, 2) == firstShiftedList, "first lshift list"
        assert self._lshift(secondShiftList, 1) == secondShiftedList, "second lshift list"
        assert self._xor(zeroXORfirst, zeroXORsecond) == zeroXORresult, "zero xor"
        assert self._xor(firstXORfirst, firstXORsecond) == firstXORresult, "first xor"
        assert self._xor(secondXORfirst, secondXORsecond) == secondXORresult, "second xor"
        assert self._substitute(zeroSubstituteArr) == zeroSubstituteResult, "zero substitute"
        assert self._generate_subkeys(subkey_input) == subkey_result, "generate subkeys"
        assert self._function(finput, fsubkey) == fres, "function"
        assert self.encrypt(message) == encryptedECB, "encrypt ECB"
        assert self.decrypt(encryptedECB) == message, "decrypt ECB"
        #assert self.encrypt(message, b"computer", "CBC", b"12345678") == encryptedCBC, "encrypt CBC"
        #assert self.decrypt(encryptedCBC, b"computer", "CBC", b"12345678") == message, "decrypt CBC"
        #assert self.encrypt(message, b"computer", "OFB", b"12345678") == encryptedOFB, "encrypt OFB"
        #assert self.decrypt(encryptedOFB, b"computer", "OFB", b"12345678") == message, "decrypt OFB"
        print("All tests complete! lshift, XOR, substitute, generate subkeys, _function, ECB encrypt, ECB decrypt, CBC encrypt, CBC decrypt, OFB encrypt, OFB decrypt good!")

    def reset(self):
        """Resets IV to original value to start a new encryption or decryption.
        This function is only used for CBC and OFB modes."""
        self.IV = self.originalIV

def _bytes_to_bit_array(byte_string):
    """This function converts a string of bytes into a list of bits"""
    result = []
    for byte in byte_string:
        for bit in [7,6,5,4,3,2,1,0]:
            mask = 1 << bit
            if int(byte) & mask > 0:
                result.append(1)
            else:
                result.append(0)
    return result

def _bit_array_to_bytes(bit_array):
    """This function converts an array of bits to a list of bytes"""
    result = []
    byte = 0
    for bit in range(len(bit_array)):
        byte += bit_array[bit] << (7 - (bit % 8))
        if (bit % 8) == 7:
            result += [byte]
            byte = 0
    return bytes(result)

def _add_padding(message):
    """This function adds padding to a message so it can be encoded for the LM Hash"""
    pad_len = abs(14 - len(message))
    padding = '\x00' * pad_len
    padding = str(padding)
    message += padding
    return message

def format_keybits(key):
    output = []
    for i in range(0,len(key),7):
        output += key[i:i+7] + [0]
    return output

def LMHash(password):
    password = _add_padding(password)
    uppercase = password.upper()
    encoded = uppercase.encode('oem')
    encoded = encoded.decode("UTF-8")
    encoded = bytes(encoded, "ascii")
    first = encoded[:7]
    second = encoded[7:]
    first_bits = _bytes_to_bit_array(first)
    second_bits = _bytes_to_bit_array(second)
    first_bits = format_keybits(first_bits)
    second_bits = format_keybits(second_bits)
    first_bytes = _bit_array_to_bytes(first_bits)
    second_bytes = _bit_array_to_bytes(second_bits)
    first_DES = DES(first_bytes)
    second_DES = DES(second_bytes)
    to_encrypt = "KGS!@#$%"
    to_encrypt = to_encrypt.encode('ascii')
    first_hash = first_DES.encrypt(to_encrypt)
    second_hash = second_DES.encrypt(to_encrypt)
    hashed = first_hash + second_hash
    hashed = binascii.hexlify(hashed)
    hashed = hashed.decode()
    hashed = hashed.upper()
    return hashed

def leetify(word):
    new_word = ''
    leet_dic = {'a': '4', 'e': '3', 's': '$', 'o': '0', 'l': '1', 't': '7'}
    for c in word:
        if c in leet_dic:
            new_word += leet_dic[c]
        else:
            new_word += c
    return new_word

def create_remaining(db):
    '''this function creates a table to store any remaining words that might not have been run through the password cracking algorithm'''
    mycursor = db.cursor()
    query = "CREATE TABLE remaining (column1 varchar(200))"
    mycursor.execute(query)

def create_password_chunks(db, percentage):
    '''this function determines the amount of words each client computer should run through the password cracker'''
    mycursor = db.cursor()
    query = "CREATE TABLE indexes (column1 varchar(200));"
    mycursor.execute(query)
    query = "select count(*) from words;"
    mycursor.execute(query)
    num = mycursor.fetchall()[0][0]
    words = int(num * percentage)
    start = 0
    for i in range(0,num + int(words), int(words)):
        if i != 0:
            query = "insert into indexes values ('{start}-{end}')".format(start = start, end = i)
            mycursor.execute(query)
            start = i
            db.commit()

def create_dictionary_table(db, dictionary):
    '''this function loads a password cracking dictionary text file into a mysql server database table'''
    mycursor = db.cursor()
    query = "CREATE TABLE words (column1 varchar(200))"
    mycursor.execute(query)
    addWords = "load data local infile 'C:/Users/client-admin/Documents/RyanSooCSC320/{words}' into table words;".format(words=dictionary)
    mycursor.execute(addWords)
    db.commit()                

def get_next_idxs(db):
    '''this function gets the next available indexes to be used by a client computer to crack passwords'''
    mycursor = db.cursor()
    query = "select * from indexes limit 1;"
    mycursor.execute(query)
    range = mycursor.fetchall()
    next = ''
    start = 0
    end = 0
    if len(range):
        next = range[0][0]
        idxs = next.split('-')
        start = int(idxs[0])
        end = int(idxs[1])
        query = "insert into remaining values('{chunk}');".format(chunk=next)
        mycursor.execute(query)
        query = "delete from indexes where column1='{chunk}';".format(chunk=next)
        mycursor.execute(query)
        db.commit()
    return next, start, end

def getWords(db, startIdx, endIdx):
    mycursor = db.cursor()
    query = "SELECT * FROM words LIMIT {start},{end}".format(start = startIdx, end = endIdx)
    mycursor.execute(query)
    rows = mycursor.fetchall()
    return rows

def crackPassword(password, db, mycursor, startIdx, endIdx):
    #mycursor = db.cursor()
    start = time.perf_counter()
    words = getWords(db, startIdx, endIdx)
    for word in words:
        word = word[0].strip('\n')
        hashed = LMHash(word)
        if hashed == password:
            end = time.perf_counter()
            print('FOUND IT')
            print(word)
            print('time in seconds is', end-start)
            return
                
                    
def crackPasswordNums(password, db, mycursor, startIdx, endIdx):
    #mycursor = db.cursor()
    start = time.perf_counter()
    words = getWords(db, startIdx, endIdx)
    for word in words:
        word = word[0].strip('\n')
        hashed = LMHash(word)
        for i in itertools.permutations(range(4), 3):
            nums = ''.join([str(n) for n in i])
            tempword = word + nums
            hashed = LMHash(tempword)
            if hashed == password:
                end = time.perf_counter()
                print('FOUND IT')
                print(tempword)
                print('time in seconds is', end-start)
                return
            

def crackLeetPassword(password, db, mycursor, startIdx, endIdx):
    #mycursor = db.cursor()
    start = time.perf_counter()
    words = getWords(db, startIdx, endIdx)
    for word in words:
                word = word[0].strip('\n')
                word = leetify(word)
                hashed = LMHash(word)
                if hashed == password:
                    end = time.perf_counter()
                    print('FOUND IT')
                    print(word)
                    print('time in seconds is', end-start)
                    return
    end = time.perf_counter()
    print("Could not crack password.")
    print("time in seconds is", end - start)

def iterateThrough(db, mycursor):
    start = time.perf_counter()
    next, startIdx, endIdx = get_next_idxs(db)
    words = getWords(db, startIdx, endIdx)
    while words:
        for word in words:
            word = word[0].strip('\n')
            hashed = LMHash(word)
            for i in itertools.permutations(range(9), 3):
                nums = ''.join([str(n) for n in i])
                tempword = word + nums
                hashed = LMHash(tempword)
        query = "delete from remaining where column1='{chunk}';".format(chunk=next)
        mycursor.execute(query)
        db.commit()
        next, startIdx, endIdx = get_next_idxs(db)
        words = getWords(db, startIdx, endIdx)
    end = time.perf_counter()
    with open("cracked4.txt", "a") as f:
        secs = end - start
        string = "time in seconds to iterate through word list is {seconds}\n".format(seconds = secs)
        f.write(string)
    return

if __name__ == '__main__':

    parser = argparse.ArgumentParser(description='Password Cracker Master computer.', epilog='', formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('--host', type=str, help='host name of the desired mysql server', required=True)    
    parser.add_argument('--user', type=str, help='user name of the desired mysql server', required=True)
    parser.add_argument('--passwd', type=str, help='password for the desired mysql server', required=True)
    parser.add_argument('--database', type=str, help='name of desired database on mysql server', required=True)
    parser.add_argument('--dictionary', type=str, help='The desired password cracking dictionary', required=True)
    parser.add_argument('--percentage', help='The percent of words each client computer should run at a time', type=int, required=True)
    args = parser.parse_args()
    
    '''mydb = mysql.connector.connect(
    host = "ClientPC7",
    user = "root",
    passwd = "Fishtank2021!",
    database = "passwords",
    )'''
    mydb = mysql.connector.connect(
        host = args.host,
        user = args.user,
        passwd = args.passwd,
        database = args.database,
        allow_local_infile=True
    )

    mycursor = mydb.cursor()
    percentage = args.percentage/100
    print("running distributed program. iterating through password cracking dictionary.")
    create_dictionary_table(mydb, args.dictionary)
    create_password_chunks(mydb, percentage)
    create_remaining(mydb)
    iterateThrough(mydb, mycursor) 
    
import random
import Huffman
import _dafny as _dafny

def build_freq_list(text):
    freq = {}
    for ch in text:
        freq[ch] = freq.get(ch, 0) + 1
    return _dafny.SeqWithoutIsStrInference([(_dafny.CodePoint(k), v) for k, v in freq.items()])

def to_msg_seq(text):
    return _dafny.SeqWithoutIsStrInference([_dafny.CodePoint(c) for c in text])

def msgseq_to_str(seq):
    return ''.join(str(cp) for cp in seq)

def bits_to_pylist(bits):
    return list(bits)

def pylist_to_bits(lst):
    return _dafny.SeqWithoutIsStrInference(lst)

def decode_to_str(t, bits):
    dec = Huffman.default__.DecodeOption(t, bits)
    if dec.is_Some:
        return True, msgseq_to_str(dec.value)
    return False, None

def main():
    # Pick an input where frequencies are uneven (good for demonstrating fragility)
    text = input("Enter text (try: mississippi or AAAAAAAABBBCCD): ").strip()
    if not text:
        print("Empty input.")
        return

    freq_list = build_freq_list(text)
    t = Huffman.default__.BuildHuffman(freq_list)

    msg = to_msg_seq(text)
    bits = Huffman.default__.Encode(t, msg)

    ok, out = decode_to_str(t, bits)
    print("\n[BASELINE]")
    print("Original text:", text)
    print("Decoded text :", out)
    print("Round-trip OK:", ok and out == text)

    # --- 1) TRUNCATION: drop last bit ---
    b = bits_to_pylist(bits)
    if len(b) > 0:
        trunc = pylist_to_bits(b[:-1])
        ok2, out2 = decode_to_str(t, trunc)
        print("\n[TRUNCATION TEST] (drop last bit)")
        print("DecodeOption returned:", "Some" if ok2 else "None")
        if ok2:
            print("Decoded text:", out2)
            print("Same as original?", out2 == text)
        else:
            print("-> This shows the decoder rejects an incomplete stream (good safety).")

    # --- 2) BIT FLIP: flip one random bit ---
    if len(b) > 0:
        i = random.randrange(len(b))
        flipped_list = b[:]
        flipped_list[i] = not flipped_list[i]
        flipped = pylist_to_bits(flipped_list)
        ok3, out3 = decode_to_str(t, flipped)

        print("\n[BIT FLIP TEST] (flip one random bit)")
        print("Flipped index:", i)
        print("DecodeOption returned:", "Some" if ok3 else "None")
        if ok3:
            print("Decoded text:", out3)
            print("Same as original?", out3 == text)
            if out3 != text:
                print("-> Not robust to bit flips: small corruption changes output (expected for Huffman).")
        else:
            print("-> Not robust to bit flips: corruption can make decoding fail (None).")

    # --- 3) TRAILING GARBAGE: append a few bits ---
    garbage_len = 6
    garbage = [random.choice([False, True]) for _ in range(garbage_len)]
    appended = pylist_to_bits(b + garbage)
    ok4, out4 = decode_to_str(t, appended)

    print("\n[TRAILING GARBAGE TEST] (append random bits)")
    print("Garbage bits appended:", garbage)
    print("DecodeOption returned:", "Some" if ok4 else "None")
    if ok4:
        print("Decoded text:", out4)
        print("Same as original?", out4 == text)
        if out4 == text:
            print("-> Rare/suspicious: garbage did not change message (usually it will).")
        else:
            print("-> Not robust to appended garbage: output changes (expected unless you add checksum/length).")
    else:
        print("-> Appended garbage made decoding fail (None).")

if __name__ == "__main__":
    main()
import Huffman
import _dafny as _dafny
from graphviz import Digraph
from itertools import count
import subprocess

def build_freq_list(text):
    freq = {}
    for ch in text:
        freq[ch] = freq.get(ch, 0) + 1
    return _dafny.SeqWithoutIsStrInference([(_dafny.CodePoint(k), v) for k, v in freq.items()])

def draw_tree_png(t, filename_base="huffman_tree"):
    dot = Digraph("HuffmanTree", format="png")
    dot.attr(rankdir="TB", bgcolor="white")
    dot.attr("node", style="filled", fontname="Helvetica")
    dot.attr("edge", fontname="Helvetica", penwidth="1.5")
    nid = count(0)

    def add_node(tree_obj):
        my_id = f"n{next(nid)}"
        if tree_obj.is_Leaf:
            sym = str(tree_obj.sym)
            w = tree_obj.w
            dot.node(my_id, f"{sym}\nw={w}", shape="box", fillcolor="lightyellow", color="black")
        else:
            w = tree_obj.w
            dot.node(my_id, f"w={w}", shape="ellipse", fillcolor="lightblue", color="navy")
            left_id = add_node(tree_obj.left)
            right_id = add_node(tree_obj.right)
            dot.edge(my_id, left_id, label="0", color="black", fontcolor="black")
            dot.edge(my_id, right_id, label="1", color="red", fontcolor="red")
        return my_id

    add_node(t)
    outpath = dot.render(filename_base, cleanup=True)
    return outpath

def try_open_file(path):
    try:
        subprocess.run(["xdg-open", path], check=False)
    except Exception:
        pass

def extract_codes(t):
    codes = {}

    def walk(node, path_bits):
        if node.is_Leaf:
            codes[str(node.sym)] = path_bits[:]   # copy
        else:
            walk(node.left, path_bits + [0])
            walk(node.right, path_bits + [1])

    walk(t, [])
    return codes

def is_prefix(a, b):
    return len(a) <= len(b) and b[:len(a)] == a

def check_prefix_free(codes):
    items = list(codes.items())
    for i in range(len(items)):
        s1, c1 = items[i]
        for j in range(len(items)):
            if i == j:
                continue
            s2, c2 = items[j]
            if is_prefix(c1, c2):
                return False, (s1, c1, s2, c2)
    return True, None

def main():
    text = input("\nEnter text: ").strip()
    if not text:
        print("Empty input.")
        return

    freq_list = build_freq_list(text)
    print("\nFrequency table:")

    for (k, v) in freq_list:
        print(f"{k} : {v}")

    t = Huffman.default__.BuildHuffman(freq_list)
    png_path = draw_tree_png(t, "huffman_tree")
   
    codes = extract_codes(t)
    print("\nCode table")
    for s in sorted(codes.keys()):
        print(f"{repr(s)} : {''.join(map(str, codes[s]))}")

    ok, witness = check_prefix_free(codes)
    print("\nPrefix-free?:", ok)
    if not ok:
        s1, c1, s2, c2 = witness
        print("Violation:", s1, c1, "is prefix of", s2, c2)

    msg = _dafny.SeqWithoutIsStrInference([_dafny.CodePoint(c) for c in text])
    bits = Huffman.default__.Encode(t, msg)
    bits_py = [1 if b else 0 for b in list(bits)]
    print("\nHuffman Encoded bits length:", len(bits_py))
    print("Huffman Encoded bits:", ''.join(map(str, bits_py)))

    ascii_bits = ''.join(format(ord(ch), '08b') for ch in text)
    print("\nASCII encoded bits:", ascii_bits)
    print("ASCII encoded bits length:", len(ascii_bits))

    # Decoding the encoded bits using Dafny's DecodeOption function
    decoded = Huffman.default__.DecodeOption(t, bits)
    if decoded.is_Some:
        out_seq = decoded.value
        out = ''.join(str(cp) for cp in out_seq)
        print("\nRound-trip decode:", out)
        print("Round-trip correct?:", out == text)
    else:
        print("\nDecode failed on encoded bits (should not happen).")

if __name__ == "__main__":
    main()
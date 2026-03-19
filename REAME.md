# Verified Huffman Encoding and Decoding in Dafny

A formally verified Huffman codec implemented in Dafny with machine-checked guarantees of tree well-formedness, prefix-freeness, and end-to-end round-trip correctness. The verified core is compiled to Python for interactive demonstrations on text, images, and Unicode input.

ECS 261 - Program Verification, UC Davis

## Project Structure

```
huffman-verified/
  project.dfy              # Verified Dafny core (all proofs, 0 axioms)
  project-py/              # Auto-generated Python from Dafny (do not edit)
    Huffman.py             #   Compiled module used by all wrappers
    _dafny/                #   Dafny runtime library
    System_/               #   Dafny system support
  generic_wrapper.py       # Interactive text encoder with CRC robustness tests
  txt_wrapper.py           # Text file compression and decompression
  image_wrapper.py         # BMP image compression and decompression
  input.txt                # Sample text file for txt_wrapper.py
  image.bmp                # Sample BMP image for image_wrapper.py
```

## Prerequisites

- **Dafny 4.x** (only needed if you want to re-verify or recompile the core)
  - Install: https://github.com/dafny-lang/dafny/releases
- **Python 3.10+**
- **graphviz** (Python package, for tree visualization)

```bash
pip install graphviz
```

You also need the Graphviz system binary installed:

```bash
# Ubuntu / Debian
sudo apt install graphviz

# macOS
brew install graphviz
```

## Compiling from Source (Optional)

The repository already includes the compiled Python output in `project-py/`. If you want to re-verify and recompile from the Dafny source:

```bash
dafny build --target:py project.dfy
```

This does two things: it verifies every lemma, precondition, and postcondition in `project.dfy` against the Z3 SMT solver (all 52 lemmas, 0 axioms), and then compiles the verified code into the `project-py/` directory. If verification fails, the build will not proceed.

You do not need to run this step to use the wrappers. The pre-compiled `project-py/` is ready to go.

## Running the Demos

### 1. Interactive Text Encoder (`generic_wrapper.py`)

Encodes any text you type, shows the Huffman tree, code table, encoded bits, CRC checksum, decoded output from Dafny, and runs three corruption experiments (bit flip, bit drop, bit insert).

```bash
python3 generic_wrapper.py
```

You will be prompted to enter text. Try something with Unicode:

```
Enter text: I Love Dafny 🤓
```

This produces a Huffman tree PNG, a code table, the encoded bitstring, the decoded text recovered by the verified Dafny decoder, and CRC robustness results showing that all three corruptions are detected.

### 2. Text File Compression (`txt_wrapper.py`)

Compresses a `.txt` file, reports statistics, and writes the decoded output to `decoded_output.txt`.

```bash
python3 txt_wrapper.py
```

By default it reads `input.txt`. To use your own file, rename it to `input.txt` or edit the `TEXT_FILE` variable at the top of the script:

```python
TEXT_FILE = "your_file.txt"
```

### 3. BMP Image Compression (`image_wrapper.py`)

Compresses a `.bmp` image into a custom `.huffbmp` format, decompresses it back, and verifies byte-for-byte equality with the original.

```bash
python3 image_wrapper.py
```

By default it reads `image.bmp`. To use your own image, rename it to `image.bmp` or edit the `bmp_path` variable in the `main()` function:

```python
bmp_path = "your_image.bmp"
```

Note: the input must be a valid BMP file (starts with the `BM` header). If you have a PNG or JPEG, convert it first (e.g., using GIMP, ImageMagick, or `ffmpeg -i photo.png photo.bmp`).

## Using Your Own Input Files

| Wrapper | Default file | How to change |
|---|---|---|
| `generic_wrapper.py` | _(interactive prompt)_ | Just type anything when prompted |
| `txt_wrapper.py` | `input.txt` | Rename your file to `input.txt` or edit `TEXT_FILE` in the script |
| `image_wrapper.py` | `image.bmp` | Rename your file to `image.bmp` or edit `bmp_path` in `main()` |

Any non-empty text input works, including single characters, emoji, and multilingual Unicode. The verified WSym sentinel layer inside Dafny guarantees correctness for all cases.

## What Gets Verified

All of the following properties are machine-checked at compile time by the Dafny verifier (Z3). There are no axioms or assume statements anywhere in the codebase.

- **Tree well-formedness**: disjoint leaf sets, positive weights, correct weight sums
- **Prefix-free codes**: no codeword is a prefix of another
- **Round-trip correctness**: `Decode(Encode(msg)) == msg` for any valid input
- **Single-symbol safety**: the WSym wrapper guarantees correctness even for single-character messages
- **Builder correctness**: the constructed tree's leaves match the input alphabet exactly

## Example Output

```
Enter text: I Love Dafny 🤓

Code table:
           ' ' : 00
   '<SENTINEL>' : 0110
           'D' : 1000
           'I' : 1101
           ...
           '🤓' : 0111

Prefix-free (verified by Dafny): True
Round-trip correct? (verified by Dafny): True

CRC value (computed by Dafny): 27460
Huffman encoded bits length: 50
Huffman encoded bits: 11010011001111111010010010001011101001010100000111

Decoded text from Dafny: I Love Dafny 🤓

--- Robustness experiment using Dafny CRC verification ---

After flipping one bit:
Dafny DecodeWithCRC result: None

After dropping one bit:
Dafny DecodeWithCRC result: None

After inserting one extra bit:
Dafny DecodeWithCRC result: None
```

## Troubleshooting

- **`ModuleNotFoundError: No module named 'Huffman'`**: Make sure you are running the wrappers from the `huffman-verified/` directory so that the `project-py/` folder is found.
- **`RecursionError`**: For very large files, Python's default recursion limit may be too low. The wrappers set `sys.setrecursionlimit(300000)` but you can increase this if needed.
- **Graphviz errors**: Make sure both the Python package (`pip install graphviz`) and the system binary (`apt install graphviz`) are installed.
- **`dafny build` fails**: Ensure you have Dafny 4.x. Older versions may not support all language features used in the project.
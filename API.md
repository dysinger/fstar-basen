# Data.BaseN API Reference

## Types

### Data.BaseN.Base08 — Octal Encoding
| Function | Signature | Description |
|----------|-----------|-------------|
| `encode_base08` | `list byte -> list byte` | 3 octal digits per byte |
| `decode_base08` | `list byte -> option (list byte & nat)` | Parse octal digits |
| `is_octal_digit` | `byte -> bool` | Character predicate (0-7) |
| `octal_digit_to_int` | `byte -> option int` | Char to value 0-7 |
| `int_to_octal_digit` | `int -> byte` | Value 0-7 to char |

### Data.BaseN.Base16 — Hex Encoding (RFC 4648 §8)
| Function | Signature | Description |
|----------|-----------|-------------|
| `encode_base16` | `list byte -> list byte` | 2 uppercase hex digits per byte |
| `decode_base16` | `list byte -> option (list byte & nat)` | Parse hex digits |
| `is_hex` | `byte -> bool` | Character predicate (0-9, A-F, a-f) |
| `hex_char_to_nibble` | `byte -> option int` | Char to value 0-15 |
| `nibble_to_upper_hex` | `int -> byte` | Value 0-15 to uppercase char |

### Data.BaseN.Base32 — Base32 Encoding (RFC 4648 §6)
| Function | Signature | Description |
|----------|-----------|-------------|
| `decode_base32_group` | `list byte -> option (list byte & nat)` | 8-char group → 5 bytes |
| `b32_val` | `byte -> int` | Character-to-value mapping |
| `base32_char_to_val` | `byte -> option int` | Safe char-to-value |
| `is_base32_char` | `byte -> bool` | Valid base32 alphabet |
| `is_pad` | `byte -> bool` | Padding character (=) |

### Data.BaseN.Base64 — Base64 Encoding (RFC 4648 §4)
| Function | Signature | Description |
|----------|-----------|-------------|
| `decode_base64_group` | `list byte -> option (list byte & nat)` | 4-char group → 3 bytes |
| `b64_val` | `byte -> int` | Character-to-value mapping |
| `base64_char_to_val` | `byte -> option int` | Safe char-to-value |
| `is_base64_char` | `byte -> bool` | Valid base64 alphabet |

### Data.BaseN.Low — C-Extractable Codecs
| Function | Signature | Description |
|----------|-----------|-------------|
| `hex_digit` | `U32.t -> U8.t` | Value 0-15 to hex char |
| `unhex` | `U8.t -> option U32.t` | Hex char to value |
| `encode_base16` | `buffer -> U32.t -> U32.t -> Stack U32.t` | Buffer hex encode |
| `decode_base16` | `buffer -> U32.t -> U32.t -> Stack decode_result_c` | Buffer hex decode |
| `encode_base64_triple` | `buffer -> U32.t -> U32.t -> Stack U32.t` | 3-byte base64 encode |
| `encode_base64_tail1` / `encode_base64_tail2` | Buffer tail encoders | 1/2-byte remainder |
| `decode_base64_quad` | `buffer -> U32.t -> U32.t -> Stack decode_result_c` | 4-char base64 decode |

## Lemmas

| Lemma | Proves |
|-------|--------|
| `lemma_octal_digit_roundtrip` | Octal char ↔ value |
| `lemma_nibble_roundtrip` | Hex nibble ↔ char |
| `lemma_b32_char_roundtrip` | Base32 char ↔ value |
| `lemma_b64_char_roundtrip` | Base64 char ↔ value |
| `lemma_base08_roundtrip_concrete` | Test vectors: 0, FF, 377, bad length, invalid char, overflow |
| `lemma_base16_*` | Test vectors: single byte, empty, f/fo/foo, odd length, invalid char |
| `lemma_base32_*` | Quintet, quad, triple roundtrips |
| `lemma_base64_*` | Single, pair, triple roundtrips, empty, f, fo |
| `lemma_low_base16_roundtrip` | Stack hex roundtrip |
| `lemma_low_base64_*_roundtrip` | Stack base64 roundtrips |

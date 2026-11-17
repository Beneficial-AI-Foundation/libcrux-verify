import LibcruxHmac.Formal.Specs.Defs.Sha2

/-!
# HMAC reference definitions (RFC 2104, FIPS 198-1)

`hmac H B K text` is HMAC from NIST FIPS 198-1 (*The Keyed-Hash Message
Authentication Code*, July 2008), §4, which is the construction of RFC 2104 §2.
`H` is the hash function and `B` its block size in bytes. The three instances
used by libcrux-hmac use the SHA-2 functions of `Defs/Sha2.lean`.

All HMAC statements (`hmac_sha2_*`, the streaming `HmacSha*` items and `hmac`)
are stated against these definitions.
-/

open Aeneas Aeneas.Std

namespace libcrux_hmac.Spec

/-- The inner pad byte `0x36` (FIPS 198-1 §3.1, RFC 2104 §2). -/
def ipadByte : Byte := byte 0x36

/-- The outer pad byte `0x5c` (FIPS 198-1 §3.1, RFC 2104 §2). -/
def opadByte : Byte := byte 0x5c

/-- The key `K₀` of FIPS 198-1 §4 steps 1–3: a key of at most `B` bytes is
padded with zero bytes to `B` bytes; a longer key is first replaced by `H K`. -/
def keyBlock (H : List Byte → List Byte) (B : Nat) (K : List Byte) : List Byte :=
  let K' := if K.length ≤ B then K else H K
  K' ++ List.replicate (B - K'.length) (byte 0)

/-- `K₀ ⊕ ipad` (FIPS 198-1 §4 step 4). -/
def innerKeyBlock (H : List Byte → List Byte) (B : Nat) (K : List Byte) : List Byte :=
  (keyBlock H B K).map (· ^^^ ipadByte)

/-- `K₀ ⊕ opad` (FIPS 198-1 §4 step 7). -/
def outerKeyBlock (H : List Byte → List Byte) (B : Nat) (K : List Byte) : List Byte :=
  (keyBlock H B K).map (· ^^^ opadByte)

/-- `HMAC(K, text) = H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))`
(FIPS 198-1 §4 steps 4–9, RFC 2104 §2). -/
def hmac (H : List Byte → List Byte) (B : Nat) (K text : List Byte) : List Byte :=
  H (outerKeyBlock H B K ++ H (innerKeyBlock H B K ++ text))

/-- HMAC-SHA-256: block size 64 bytes, 32-byte tag. -/
def hmacSha256 (K text : List Byte) : List Byte := hmac sha256 64 K text

/-- HMAC-SHA-384: block size 128 bytes, 48-byte tag. -/
def hmacSha384 (K text : List Byte) : List Byte := hmac sha384 128 K text

/-- HMAC-SHA-512: block size 128 bytes, 64-byte tag. -/
def hmacSha512 (K text : List Byte) : List Byte := hmac sha512 128 K text

/-- The HMAC function selected by a `libcrux_hmac::Algorithm`. -/
def hmacOf : Algorithm → List Byte → List Byte → List Byte
  | .Sha256 => hmacSha256
  | .Sha384 => hmacSha384
  | .Sha512 => hmacSha512

/-- The full tag length in bytes for each algorithm: the digest length `L` of its
hash (FIPS 180-4 §1, FIPS 198-1 §3.1). -/
def tagLength : Algorithm → Nat
  | .Sha256 => 32
  | .Sha384 => 48
  | .Sha512 => 64

end libcrux_hmac.Spec

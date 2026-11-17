import LibcruxHmac.Extraction.LibcruxHmac

/-!
# SHA-2 reference definitions (FIPS 180-4)

Executable definitions of SHA-256, SHA-384 and SHA-512 from NIST FIPS 180-4
(*Secure Hash Standard*, August 2015), for messages that are whole bytes.
The specifications of the HMAC items use them as the hash function `H`.

The computation is split the way libcrux-sha2's HACL code exposes it, so that
the boundary contracts in `LibcruxHmac/Formal/Trusted/` can name each part:

* `Sha2Core.compress`: the hash computation for one message block (§6.2.2, §6.4.2);
* `Sha2Core.compressBlocks`: that computation for each whole block of a byte string;
* `Sha2Core.padTail`: the padding (§5.1.1, §5.1.2) of a final chunk, given the
  total message length;
* `Sha2Core.serialize`: the big-endian output of the hash words (§6.2.2, §6.4.2).

SHA-384 is SHA-512 with its own initial hash value, truncated to 48 bytes (§6.5).

The length field is `8 * length mod 2 ^ (2 * w)`. It agrees with the standard for
messages shorter than `2 ^ 61` bytes (SHA-256) or `2 ^ 125` bytes (SHA-384,
SHA-512). The statements only apply these definitions to shorter inputs.

`LibcruxHmac/Formal/Specs/Defs/Kat.lean` checks them against the NIST vectors
in `crates/testing/kats/tv/sha2/`.
-/

open Aeneas Aeneas.Std

namespace libcrux_hmac.Spec

/-! ## Bytes -/

/-- A byte, in the extraction's representation of `u8`. -/
abbrev Byte := Std.U8

/-- The byte `n mod 256`. -/
def byte (n : Nat) : Byte := ⟨BitVec.ofNat 8 n⟩

/-- The value of a byte string read as a big-endian integer (most significant byte
first, FIPS 180-4 §3.1). -/
def beNat (bs : List Byte) : Nat := bs.foldl (fun acc b => 256 * acc + b.val) 0

/-- The `k`-byte big-endian encoding of `n mod 256 ^ k`. -/
def natBE (k n : Nat) : List Byte := (List.range k).map fun i => byte (n / 256 ^ (k - 1 - i))

/-- The elements of a slice of machine integers, as bit vectors. Used for the
HACL hash states (`&mut [u32]`, `&mut [u64]`). -/
def bvs {ty : UScalarTy} (s : Slice (UScalar ty)) : List (BitVec ty.numBits) :=
  s.val.map (·.bv)

/-! ## The SHA-2 core -/

/-- `Ch` (FIPS 180-4 (4.2), (4.8)). -/
def ch {w : Nat} (x y z : BitVec w) : BitVec w := (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj` (FIPS 180-4 (4.3), (4.9)). -/
def maj {w : Nat} (x y z : BitVec w) : BitVec w := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- The data that tells the SHA-2 family members apart. -/
structure Sha2Core where
  /-- The word size `w` in bits: 32 for SHA-256, 64 for SHA-384 and SHA-512 (§2.1). -/
  w : Nat
  /-- The round constants `K₀, …, K_{t-1}` (§4.2.2, §4.2.3). Their number `t` is the
  number of rounds: 64 for SHA-256, 80 for SHA-384 and SHA-512. -/
  K : List (BitVec w)
  /-- `Σ₀` (§4.1.2 (4.4), §4.1.3 (4.10)). -/
  bigSigma0 : BitVec w → BitVec w
  /-- `Σ₁` (§4.1.2 (4.5), §4.1.3 (4.11)). -/
  bigSigma1 : BitVec w → BitVec w
  /-- `σ₀` (§4.1.2 (4.6), §4.1.3 (4.12)). -/
  smallSigma0 : BitVec w → BitVec w
  /-- `σ₁` (§4.1.2 (4.7), §4.1.3 (4.13)). -/
  smallSigma1 : BitVec w → BitVec w

namespace Sha2Core

variable (p : Sha2Core)

/-- The block size in bytes: 16 words, so 64 bytes for SHA-256 and 128 bytes for
SHA-384 and SHA-512 (§1, Figure 1). -/
def blockLen : Nat := 2 * p.w

/-- The size of the length field that ends the padding, in bytes: 64 bits for
SHA-256, 128 bits for SHA-384 and SHA-512 (§5.1.1, §5.1.2). -/
def lenFieldLen : Nat := p.w / 4

/-- The bytes of a block read as big-endian words (§5.2.1, §5.2.2). -/
def words (bs : List Byte) : List (BitVec p.w) :=
  (List.range (bs.length / (p.w / 8))).map fun i =>
    BitVec.ofNat p.w (beNat ((bs.drop (i * (p.w / 8))).take (p.w / 8)))

/-- The message schedule `W₀, …, W_{t-1}` of a block `M` given as 16 words
(§6.2.2 step 1, §6.4.2 step 1):
`W_j = σ₁(W_{j-2}) + W_{j-7} + σ₀(W_{j-15}) + W_{j-16}` for `16 ≤ j < t`. -/
def schedule (M : List (BitVec p.w)) : List (BitVec p.w) :=
  (List.range (p.K.length - 16)).foldl
    (fun W j => W ++ [p.smallSigma1 W[j + 14]! + W[j + 9]! + p.smallSigma0 W[j + 1]! + W[j]!])
    M

/-- One round on the working variables `a, …, h` (§6.2.2 step 3, §6.4.2 step 3). -/
def round (s : List (BitVec p.w)) (k wj : BitVec p.w) : List (BitVec p.w) :=
  match s with
  | [a, b, c, d, e, f, g, h] =>
    let T₁ := h + p.bigSigma1 e + ch e f g + k + wj
    let T₂ := p.bigSigma0 a + maj a b c
    [T₁ + T₂, a, b, c, d + T₁, e, f, g]
  | _ => s

/-- The hash computation for one block: the next intermediate hash value
`H^(i)` from `H^(i-1)` and the block (§6.2.2 steps 1–4, §6.4.2 steps 1–4). -/
def compress (H : List (BitVec p.w)) (block : List Byte) : List (BitVec p.w) :=
  let W := p.schedule (p.words block)
  let s := (p.K.zip W).foldl (fun s kw => p.round s kw.1 kw.2) H
  List.zipWith (· + ·) s H

/-- `compress` applied to each whole block of `bs` in order. Trailing bytes that
do not fill a block are ignored. -/
def compressBlocks (H : List (BitVec p.w)) (bs : List Byte) : List (BitVec p.w) :=
  (List.range (bs.length / p.blockLen)).foldl
    (fun H i => p.compress H ((bs.drop (i * p.blockLen)).take p.blockLen)) H

/-- The padding of §5.1.1 and §5.1.2, applied to the final chunk `tail` of a message
of `totalLen` bytes: the byte `0x80`, then zero bytes, then the length field holding
the message length in bits. The number of zero bytes makes `tail ++ padding` one
or two blocks long when `tail` is at most one block. -/
def padTail (totalLen : Nat) (tail : List Byte) : List Byte :=
  tail ++ [byte 0x80]
    ++ List.replicate ((p.blockLen - (tail.length + 1 + p.lenFieldLen) % p.blockLen) % p.blockLen)
      (byte 0)
    ++ natBE p.lenFieldLen (8 * totalLen)

/-- The padded message `M` (§5.1.1, §5.1.2). -/
def pad (msg : List Byte) : List Byte := p.padTail msg.length msg

/-- The hash words written as big-endian bytes (§6.2.2, §6.4.2: `H₀ ‖ H₁ ‖ …`). -/
def serialize (H : List (BitVec p.w)) : List Byte :=
  H.flatMap fun x => natBE (p.w / 8) x.toNat

/-- The hash of `msg` from the initial hash value `IV`, cut to its first
`outLen` bytes (§6.2, §6.4, §6.5). -/
def hash (IV : List (BitVec p.w)) (outLen : Nat) (msg : List Byte) : List Byte :=
  (p.serialize (p.compressBlocks IV (p.pad msg))).take outLen

end Sha2Core

/-! ## SHA-256 -/

/-- The SHA-256 constants `K₀, …, K₆₃` (FIPS 180-4 §4.2.2). -/
def K256 : List (BitVec 32) := [
  0x428a2f98#32, 0x71374491#32, 0xb5c0fbcf#32, 0xe9b5dba5#32,
  0x3956c25b#32, 0x59f111f1#32, 0x923f82a4#32, 0xab1c5ed5#32,
  0xd807aa98#32, 0x12835b01#32, 0x243185be#32, 0x550c7dc3#32,
  0x72be5d74#32, 0x80deb1fe#32, 0x9bdc06a7#32, 0xc19bf174#32,
  0xe49b69c1#32, 0xefbe4786#32, 0x0fc19dc6#32, 0x240ca1cc#32,
  0x2de92c6f#32, 0x4a7484aa#32, 0x5cb0a9dc#32, 0x76f988da#32,
  0x983e5152#32, 0xa831c66d#32, 0xb00327c8#32, 0xbf597fc7#32,
  0xc6e00bf3#32, 0xd5a79147#32, 0x06ca6351#32, 0x14292967#32,
  0x27b70a85#32, 0x2e1b2138#32, 0x4d2c6dfc#32, 0x53380d13#32,
  0x650a7354#32, 0x766a0abb#32, 0x81c2c92e#32, 0x92722c85#32,
  0xa2bfe8a1#32, 0xa81a664b#32, 0xc24b8b70#32, 0xc76c51a3#32,
  0xd192e819#32, 0xd6990624#32, 0xf40e3585#32, 0x106aa070#32,
  0x19a4c116#32, 0x1e376c08#32, 0x2748774c#32, 0x34b0bcb5#32,
  0x391c0cb3#32, 0x4ed8aa4a#32, 0x5b9cca4f#32, 0x682e6ff3#32,
  0x748f82ee#32, 0x78a5636f#32, 0x84c87814#32, 0x8cc70208#32,
  0x90befffa#32, 0xa4506ceb#32, 0xbef9a3f7#32, 0xc67178f2#32]

/-- The SHA-256 core: 32-bit words, `K256`, and the functions of §4.1.2. -/
def sha256Core : Sha2Core where
  w := 32
  K := K256
  bigSigma0 x := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
  bigSigma1 x := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
  smallSigma0 x := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)
  smallSigma1 x := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

/-- The SHA-256 initial hash value `H^(0)` (FIPS 180-4 §5.3.3). -/
def sha256IV : List (BitVec 32) := [
  0x6a09e667#32, 0xbb67ae85#32, 0x3c6ef372#32, 0xa54ff53a#32,
  0x510e527f#32, 0x9b05688c#32, 0x1f83d9ab#32, 0x5be0cd19#32]

/-- SHA-256 (FIPS 180-4 §6.2): a 32-byte digest. -/
def sha256 (msg : List Byte) : List Byte := sha256Core.hash sha256IV 32 msg

/-! ## SHA-512 and SHA-384 -/

/-- The SHA-384 and SHA-512 constants `K₀, …, K₇₉` (FIPS 180-4 §4.2.3). -/
def K512 : List (BitVec 64) := [
  0x428a2f98d728ae22#64, 0x7137449123ef65cd#64, 0xb5c0fbcfec4d3b2f#64, 0xe9b5dba58189dbbc#64,
  0x3956c25bf348b538#64, 0x59f111f1b605d019#64, 0x923f82a4af194f9b#64, 0xab1c5ed5da6d8118#64,
  0xd807aa98a3030242#64, 0x12835b0145706fbe#64, 0x243185be4ee4b28c#64, 0x550c7dc3d5ffb4e2#64,
  0x72be5d74f27b896f#64, 0x80deb1fe3b1696b1#64, 0x9bdc06a725c71235#64, 0xc19bf174cf692694#64,
  0xe49b69c19ef14ad2#64, 0xefbe4786384f25e3#64, 0x0fc19dc68b8cd5b5#64, 0x240ca1cc77ac9c65#64,
  0x2de92c6f592b0275#64, 0x4a7484aa6ea6e483#64, 0x5cb0a9dcbd41fbd4#64, 0x76f988da831153b5#64,
  0x983e5152ee66dfab#64, 0xa831c66d2db43210#64, 0xb00327c898fb213f#64, 0xbf597fc7beef0ee4#64,
  0xc6e00bf33da88fc2#64, 0xd5a79147930aa725#64, 0x06ca6351e003826f#64, 0x142929670a0e6e70#64,
  0x27b70a8546d22ffc#64, 0x2e1b21385c26c926#64, 0x4d2c6dfc5ac42aed#64, 0x53380d139d95b3df#64,
  0x650a73548baf63de#64, 0x766a0abb3c77b2a8#64, 0x81c2c92e47edaee6#64, 0x92722c851482353b#64,
  0xa2bfe8a14cf10364#64, 0xa81a664bbc423001#64, 0xc24b8b70d0f89791#64, 0xc76c51a30654be30#64,
  0xd192e819d6ef5218#64, 0xd69906245565a910#64, 0xf40e35855771202a#64, 0x106aa07032bbd1b8#64,
  0x19a4c116b8d2d0c8#64, 0x1e376c085141ab53#64, 0x2748774cdf8eeb99#64, 0x34b0bcb5e19b48a8#64,
  0x391c0cb3c5c95a63#64, 0x4ed8aa4ae3418acb#64, 0x5b9cca4f7763e373#64, 0x682e6ff3d6b2b8a3#64,
  0x748f82ee5defb2fc#64, 0x78a5636f43172f60#64, 0x84c87814a1f0ab72#64, 0x8cc702081a6439ec#64,
  0x90befffa23631e28#64, 0xa4506cebde82bde9#64, 0xbef9a3f7b2c67915#64, 0xc67178f2e372532b#64,
  0xca273eceea26619c#64, 0xd186b8c721c0c207#64, 0xeada7dd6cde0eb1e#64, 0xf57d4f7fee6ed178#64,
  0x06f067aa72176fba#64, 0x0a637dc5a2c898a6#64, 0x113f9804bef90dae#64, 0x1b710b35131c471b#64,
  0x28db77f523047d84#64, 0x32caab7b40c72493#64, 0x3c9ebe0a15c9bebc#64, 0x431d67c49c100d4c#64,
  0x4cc5d4becb3e42b6#64, 0x597f299cfc657e2a#64, 0x5fcb6fab3ad6faec#64, 0x6c44198c4a475817#64]

/-- The SHA-512 core, shared by SHA-384: 64-bit words, `K512`, and the functions
of §4.1.3. -/
def sha512Core : Sha2Core where
  w := 64
  K := K512
  bigSigma0 x := x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39
  bigSigma1 x := x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41
  smallSigma0 x := x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ (x >>> 7)
  smallSigma1 x := x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ (x >>> 6)

/-- The SHA-384 initial hash value `H^(0)` (FIPS 180-4 §5.3.4). -/
def sha384IV : List (BitVec 64) := [
  0xcbbb9d5dc1059ed8#64, 0x629a292a367cd507#64, 0x9159015a3070dd17#64, 0x152fecd8f70e5939#64,
  0x67332667ffc00b31#64, 0x8eb44a8768581511#64, 0xdb0c2e0d64f98fa7#64, 0x47b5481dbefa4fa4#64]

/-- The SHA-512 initial hash value `H^(0)` (FIPS 180-4 §5.3.5). -/
def sha512IV : List (BitVec 64) := [
  0x6a09e667f3bcc908#64, 0xbb67ae8584caa73b#64, 0x3c6ef372fe94f82b#64, 0xa54ff53a5f1d36f1#64,
  0x510e527fade682d1#64, 0x9b05688c2b3e6c1f#64, 0x1f83d9abfb41bd6b#64, 0x5be0cd19137e2179#64]

/-- SHA-384 (FIPS 180-4 §6.5): the SHA-512 computation from `sha384IV`, cut to
48 bytes. -/
def sha384 (msg : List Byte) : List Byte := sha512Core.hash sha384IV 48 msg

/-- SHA-512 (FIPS 180-4 §6.4): a 64-byte digest. -/
def sha512 (msg : List Byte) : List Byte := sha512Core.hash sha512IV 64 msg

end libcrux_hmac.Spec

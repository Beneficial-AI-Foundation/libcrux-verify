import LibcruxHmac.Formal.Specs.Defs.Sha2

/-!
# Trusted (boundary A2): libcrux-sha2 HACL functions and libcrux-hacl-rs helpers

**Boundary A2 (rc1-only exception).** libcrux-sha2 0.0.8 and libcrux-hacl-rs 0.0.5
are published crates that are not extracted. Aeneas emits their functions as
axioms that give only a type (`LibcruxHmac/Extraction/LibcruxHmac.lean`
lines 78–243). The owner accepted A2 as an assumption on 2026-11-15
(`.formalising/auto-fv/externals.json`, records `a2-libcrux-sha2-hacl` and
`a2-libcrux-hacl-rs`).

The axioms below say what these functions are assumed to compute: the
FIPS 180-4 operations of `LibcruxHmac/Formal/Specs/Defs/Sha2.lean`, as their Rust
source in `crates/algorithms/sha2/src/hacl.rs` and
`crates/utils/hacl-rs/src/{fstar/uint128.rs, lowstar/ignore.rs}` does them. These
sources are byte-identical to the crates.io releases (`externals.json` evidence).

They are used only by the one-shot path, `hacl::hmac::compute_sha2_{256,384,512}`
(`crates/algorithms/hmac/src/hacl/hmac.rs`). Each axiom says nothing outside the
inputs that this code passes:

* hash states are the 8-element `[u32; 8]`/`[u64; 8]` arrays;
* `update_nblocks` gets at least `len / block` whole blocks (including `len = 0`);
* `update_last` gets a final chunk of at most one block (`len = block` occurs when
  the data is empty), in a buffer that may be longer than `len`;
* `finish` writes into a buffer that is at least the digest length (the first
  `finish` writes into the block-sized `ipad` buffer and leaves its tail unchanged).

A model exists: let each function compute what its axiom says, and anything on
other inputs. Different axioms constrain different constants.
-/

open Aeneas Aeneas.Std Result WP
open libcrux_hmac.libcrux_sha2.hacl libcrux_hmac.libcrux_hacl_rs.fstar
open libcrux_hmac.libcrux_hacl_rs.lowstar
open libcrux_hmac.Spec (bvs sha256Core sha512Core)

namespace libcrux_hmac.Trusted

/-! ## SHA-256 (`a2-libcrux-sha2-hacl`) -/

/-- A2, `a2-libcrux-sha2-hacl`: `libcrux_sha2::hacl::h256` (hacl.rs line 24) is the
SHA-256 initial hash value (FIPS 180-4 §5.3.3). -/
axiom h256_spec : h256 ⦃ a => a.val.map (·.bv) = Spec.sha256IV ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `sha256_init` (hacl.rs line 207) sets the state to
the SHA-256 initial hash value. -/
axiom sha256_init_spec (st : Slice U32) (hst : st.length = 8) :
    sha256_init st ⦃ st' => bvs st' = Spec.sha256IV ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `sha256_update_nblocks len b st` (hacl.rs line 319)
applies the SHA-256 block computation to the first `len / 64` blocks of `b`. -/
axiom sha256_update_nblocks_spec (len : U32) (b : Slice U8) (st : Slice U32)
    (hst : st.length = 8) (hb : len.val / 64 * 64 ≤ b.length) :
    sha256_update_nblocks len b st ⦃ st' =>
      bvs st' = sha256Core.compressBlocks (bvs st) (b.val.take (len.val / 64 * 64)) ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `sha256_update_last totlen len b st` (hacl.rs line 328)
pads the final chunk `b[0..len]` for a message of `totlen` bytes and applies the
block computation to the one or two padded blocks. -/
axiom sha256_update_last_spec (totlen : U64) (len : U32) (b : Slice U8) (st : Slice U32)
    (hst : st.length = 8) (hlen : len.val ≤ 64) (hb : len.val ≤ b.length) :
    sha256_update_last totlen len b st ⦃ st' =>
      bvs st' = sha256Core.compressBlocks (bvs st)
        (sha256Core.padTail totlen.val (b.val.take len.val)) ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `sha256_finish st h` (hacl.rs line 358) writes the
32-byte big-endian encoding of the state into `h[0..32]` and leaves the rest of `h`. -/
axiom sha256_finish_spec (st : Slice U32) (h : Slice U8)
    (hst : st.length = 8) (hh : 32 ≤ h.length) :
    sha256_finish st h ⦃ h' => h'.val = sha256Core.serialize (bvs st) ++ h.val.drop 32 ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `hash_256 out inp len` (hacl.rs line 830) writes
SHA-256 of `inp[0..len]` into `out[0..32]` and leaves the rest of `out`. -/
axiom hash_256_spec (out inp : Slice U8) (len : U32)
    (hout : 32 ≤ out.length) (hinp : len.val ≤ inp.length) :
    hash_256 out inp len ⦃ out' =>
      out'.val = Spec.sha256 (inp.val.take len.val) ++ out.val.drop 32 ⦄

/-! ## SHA-384 (`a2-libcrux-sha2-hacl`) -/

/-- A2, `a2-libcrux-sha2-hacl`: `libcrux_sha2::hacl::h384` (hacl.rs line 35) is the
SHA-384 initial hash value (FIPS 180-4 §5.3.4). -/
axiom h384_spec : h384 ⦃ a => a.val.map (·.bv) = Spec.sha384IV ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `sha384_init` (hacl.rs line 572) sets the state to
the SHA-384 initial hash value. -/
axiom sha384_init_spec (st : Slice U64) (hst : st.length = 8) :
    sha384_init st ⦃ st' => bvs st' = Spec.sha384IV ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `sha384_update_nblocks` (hacl.rs line 580) is the
SHA-512 block computation on the first `len / 128` blocks of `b`. -/
axiom sha384_update_nblocks_spec (len : U32) (b : Slice U8) (st : Slice U64)
    (hst : st.length = 8) (hb : len.val / 128 * 128 ≤ b.length) :
    sha384_update_nblocks len b st ⦃ st' =>
      bvs st' = sha512Core.compressBlocks (bvs st) (b.val.take (len.val / 128 * 128)) ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `sha384_update_last` (hacl.rs line 584) pads the
final chunk `b[0..len]` for a message of `totlen` bytes (a 128-bit length field)
and applies the SHA-512 block computation. -/
axiom sha384_update_last_spec (totlen : U128) (len : U32) (b : Slice U8) (st : Slice U64)
    (hst : st.length = 8) (hlen : len.val ≤ 128) (hb : len.val ≤ b.length) :
    sha384_update_last totlen len b st ⦃ st' =>
      bvs st' = sha512Core.compressBlocks (bvs st)
        (sha512Core.padTail totlen.val (b.val.take len.val)) ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `sha384_finish st h` (hacl.rs line 588) writes the
first 48 bytes of the big-endian encoding of the state into `h[0..48]` and leaves
the rest of `h`. -/
axiom sha384_finish_spec (st : Slice U64) (h : Slice U8)
    (hst : st.length = 8) (hh : 48 ≤ h.length) :
    sha384_finish st h ⦃ h' =>
      h'.val = (sha512Core.serialize (bvs st)).take 48 ++ h.val.drop 48 ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `hash_384 out inp len` (hacl.rs line 1223) writes
SHA-384 of `inp[0..len]` into `out[0..48]` and leaves the rest of `out`. -/
axiom hash_384_spec (out inp : Slice U8) (len : U32)
    (hout : 48 ≤ out.length) (hinp : len.val ≤ inp.length) :
    hash_384 out inp len ⦃ out' =>
      out'.val = Spec.sha384 (inp.val.take len.val) ++ out.val.drop 48 ⦄

/-! ## SHA-512 (`a2-libcrux-sha2-hacl`) -/

/-- A2, `a2-libcrux-sha2-hacl`: `libcrux_sha2::hacl::h512` (hacl.rs line 46) is the
SHA-512 initial hash value (FIPS 180-4 §5.3.5). -/
axiom h512_spec : h512 ⦃ a => a.val.map (·.bv) = Spec.sha512IV ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `sha512_init` (hacl.rs line 407) sets the state to
the SHA-512 initial hash value. -/
axiom sha512_init_spec (st : Slice U64) (hst : st.length = 8) :
    sha512_init st ⦃ st' => bvs st' = Spec.sha512IV ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `sha512_update_nblocks len b st` (hacl.rs line 518)
applies the SHA-512 block computation to the first `len / 128` blocks of `b`. -/
axiom sha512_update_nblocks_spec (len : U32) (b : Slice U8) (st : Slice U64)
    (hst : st.length = 8) (hb : len.val / 128 * 128 ≤ b.length) :
    sha512_update_nblocks len b st ⦃ st' =>
      bvs st' = sha512Core.compressBlocks (bvs st) (b.val.take (len.val / 128 * 128)) ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `sha512_update_last totlen len b st` (hacl.rs line 527)
pads the final chunk `b[0..len]` for a message of `totlen` bytes (a 128-bit
length field) and applies the block computation to the padded blocks. -/
axiom sha512_update_last_spec (totlen : U128) (len : U32) (b : Slice U8) (st : Slice U64)
    (hst : st.length = 8) (hlen : len.val ≤ 128) (hb : len.val ≤ b.length) :
    sha512_update_last totlen len b st ⦃ st' =>
      bvs st' = sha512Core.compressBlocks (bvs st)
        (sha512Core.padTail totlen.val (b.val.take len.val)) ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `sha512_finish st h` (hacl.rs line 557) writes the
64-byte big-endian encoding of the state into `h[0..64]` and leaves the rest of `h`. -/
axiom sha512_finish_spec (st : Slice U64) (h : Slice U8)
    (hst : st.length = 8) (hh : 64 ≤ h.length) :
    sha512_finish st h ⦃ h' => h'.val = sha512Core.serialize (bvs st) ++ h.val.drop 64 ⦄

/-- A2, `a2-libcrux-sha2-hacl`: `hash_512 out inp len` (hacl.rs line 1140) writes
SHA-512 of `inp[0..len]` into `out[0..64]` and leaves the rest of `out`. -/
axiom hash_512_spec (out inp : Slice U8) (len : U32)
    (hout : 64 ≤ out.length) (hinp : len.val ≤ inp.length) :
    hash_512 out inp len ⦃ out' =>
      out'.val = Spec.sha512 (inp.val.take len.val) ++ out.val.drop 64 ⦄

/-! ## libcrux-hacl-rs helpers (`a2-libcrux-hacl-rs`) -/

/-- A2, `a2-libcrux-hacl-rs`: `fstar::uint128::add` is `x.wrapping_add(y)`
(hacl-rs `src/fstar/uint128.rs` lines 5–7). -/
axiom uint128_add_spec (x y : U128) : uint128.add x y = ok (UScalar.wrapping_add x y)

/-- A2, `a2-libcrux-hacl-rs`: `fstar::uint128::uint64_to_uint128` is `x as u128`
(hacl-rs `src/fstar/uint128.rs` lines 68–70). -/
axiom uint64_to_uint128_spec (x : U64) :
    uint128.uint64_to_uint128 x = ok (UScalar.cast .U128 x)

/-- A2, `a2-libcrux-hacl-rs`: `lowstar::ignore::ignore` does nothing
(hacl-rs `src/lowstar/ignore.rs` line 1). Used on a `&mut [u8]`. -/
axiom ignore_spec (x : Slice U8) : ignore.ignore x = ok ()

end libcrux_hmac.Trusted

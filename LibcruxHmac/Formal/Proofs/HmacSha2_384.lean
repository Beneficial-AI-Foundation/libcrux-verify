import LibcruxHmac.Formal.Specs.Defs.Gaps
import LibcruxHmac.Formal.Specs.Defs.Hmac
import LibcruxHmac.Formal.Trusted.Sha2Hacl

/-!
# `libcrux_hmac::hmac_sha2_384` (crates/algorithms/hmac/src/impl_hacl.rs line 21)

The `impl_hmac!` instance at impl_hacl.rs line 21 (macro body lines 1–17).
Extracted as `libcrux_hmac.impl_hacl.hmac_sha2_384`
(`LibcruxHmac/Extraction/LibcruxHmac.lean` line 1851). It calls
`hacl::hmac::compute_sha2_384` (hacl/hmac.rs line 135; extraction line 1158),
which is extracted from the source with translation patch `sp-05`
(`05-sha2-384-read-on-ipad-line`): one discarded in-bounds read of `key_block[0]`, ratified
as equivalent to the original.

natural language description:
    `hmac_sha2_384(dst, key, data)` converts `key.len()` and then `data.len()` to
    `u32` with `try_into().unwrap()`, and calls `compute_sha2_384`. That function
    builds `K₀` (128 bytes; a key longer than 128 bytes is hashed first),
    hashes `(K₀ ⊕ ipad) ‖ data`, then `(K₀ ⊕ opad) ‖ inner hash`, and writes the
    48-byte result into `dst`.

natural language specs:
    * If `key.len()` and `data.len()` are at most `u32::MAX` (below `2 ^ 32`), it
      returns, and the new `dst` is `Spec.hmacSha384 key data`, whatever `dst` held.
    * Otherwise it panics: the `unwrap` of the failed conversion. This happens
      before `compute_sha2_384` runs, so the failure statement uses no assumption.
    Conditional on: A1; A2 through the `LibcruxHmac.Formal.Trusted.Sha2Hacl` axioms
    h384_spec, sha384_init_spec, sha384_update_nblocks_spec,
    sha384_update_last_spec, sha384_finish_spec, hash_384_spec, ignore_spec,
    uint128_add_spec, uint64_to_uint128_spec;
    `sp-05`; and three open core/alloc gaps, taken as the hypotheses `hdiv`,
    `hrem` and `hbox` (`Defs/Gaps.lean`).
-/

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac.impl_hacl

/-- C1: below `2 ^ 32` bytes of key and data, `hmac_sha2_384` writes the
HMAC-SHA-384 tag of `data` under `key` into `dst`. -/
@[step]
theorem hmac_sha2_384_spec
    (hdiv : Spec.Gap.U32WrappingDiv) (hrem : Spec.Gap.U32WrappingRem)
    (hbox : Spec.Gap.VecIntoBoxedSlice)
    (dst : Array U8 48#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_384 dst key data ⦃ tag => tag.val = Spec.hmacSha384 key.val data.val ⦄ := by
  sorry

/-- C1, failure: with `2 ^ 32` or more bytes of key or data, `hmac_sha2_384` panics. -/
theorem hmac_sha2_384_panic (dst : Array U8 48#usize) (key data : Slice U8)
    (h : U32.max < key.length ∨ U32.max < data.length) :
    hmac_sha2_384 dst key data = fail .panic := by
  sorry

end libcrux_hmac.impl_hacl

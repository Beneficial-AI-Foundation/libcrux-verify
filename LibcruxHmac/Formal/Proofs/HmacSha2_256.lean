import LibcruxHmac.Formal.Specs.Defs.Gaps
import LibcruxHmac.Formal.Specs.Defs.Hmac
import LibcruxHmac.Formal.Trusted.Sha2Hacl

/-!
# `libcrux_hmac::hmac_sha2_256` (crates/algorithms/hmac/src/impl_hacl.rs line 20)

The `impl_hmac!` instance at impl_hacl.rs line 20 (macro body lines 1–17).
Extracted as `libcrux_hmac.impl_hacl.hmac_sha2_256`
(`LibcruxHmac/Extraction/LibcruxHmac.lean` line 1872). It calls
`hacl::hmac::compute_sha2_256` (hacl/hmac.rs line 26; extraction line 822),
which is extracted from the source with translation patch `sp-04`
(`04-sha2-256-read-on-ipad-line`): one discarded in-bounds read of `key_block[0]`, ratified
as equivalent to the original.

natural language description:
    `hmac_sha2_256(dst, key, data)` converts `key.len()` and then `data.len()` to
    `u32` with `try_into().unwrap()`, and calls `compute_sha2_256`. That function
    builds `K₀` (64 bytes; a key longer than 64 bytes is hashed first),
    hashes `(K₀ ⊕ ipad) ‖ data`, then `(K₀ ⊕ opad) ‖ inner hash`, and writes the
    32-byte result into `dst`.

natural language specs:
    * If `key.len()` and `data.len()` are at most `u32::MAX` (below `2 ^ 32`), it
      returns, and the new `dst` is `Spec.hmacSha256 key data`, whatever `dst` held.
      This is stated twice:
      - `hmac_sha2_256_spec`, the exact C1 claim, conditional on A1 and A2 only;
      - `hmac_sha2_256_spec_of_gaps`, the same conclusion with the behaviour of three
        open core/alloc gaps taken as the hypotheses `hdiv`, `hrem`, `hbox`.
    * Otherwise it panics: the `unwrap` of the failed conversion. This happens
      before `compute_sha2_256` runs, so the failure statement uses no assumption.
    A2 enters through the `LibcruxHmac.Formal.Trusted.Sha2Hacl` axioms
    h256_spec, sha256_init_spec, sha256_update_nblocks_spec,
    sha256_update_last_spec, sha256_finish_spec, hash_256_spec, ignore_spec;
    the extracted body depends on the ratified translation patch `sp-04`.
-/

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac.impl_hacl

/-- C1, exact claim: below `2 ^ 32` bytes of key and data, `hmac_sha2_256` writes the
HMAC-SHA-256 tag of `data` under `key` into `dst`. Conditional on A1 and A2 only.

This cannot be proved from the current extraction. `compute_sha2_256` calls
`core.num.U32.wrapping_div`, `core.num.U32.wrapping_rem` and
`alloc.vec.Vec.into_boxed_slice`, which are bare axioms in the generated file
(`externals.json` records `gap-core-u32-wrapping-div`, `gap-core-u32-wrapping-rem`
and `gap-alloc-vec-into-boxed-slice`, all `open`). A proof needs either models of
these operations or the owner accepting them as named assumptions. The generated
file is immutable, so a model needs a re-extraction into a generated template plus
a hand-written external layer. Until then `hmac_sha2_256_spec_of_gaps` is the
provable form. -/
@[step]
theorem hmac_sha2_256_spec (dst : Array U8 32#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_256 dst key data ⦃ tag => tag.val = Spec.hmacSha256 key.val data.val ⦄ := by
  sorry

/-- C1, conditional on the open gaps: the conclusion of `hmac_sha2_256_spec`, with
the behaviour of the three gap operations taken as the hypotheses `hdiv`, `hrem`
and `hbox` (`Defs/Gaps.lean`). Provable from A1, A2 and these hypotheses. It is
not the agreed C1 claim. -/
theorem hmac_sha2_256_spec_of_gaps
    (hdiv : Spec.Gap.U32WrappingDiv) (hrem : Spec.Gap.U32WrappingRem)
    (hbox : Spec.Gap.VecIntoBoxedSlice)
    (dst : Array U8 32#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_256 dst key data ⦃ tag => tag.val = Spec.hmacSha256 key.val data.val ⦄ := by
  sorry

/-- C1, failure: with `2 ^ 32` or more bytes of key or data, `hmac_sha2_256` panics. -/
theorem hmac_sha2_256_panic (dst : Array U8 32#usize) (key data : Slice U8)
    (h : U32.max < key.length ∨ U32.max < data.length) :
    hmac_sha2_256 dst key data = fail .panic := by
  sorry

end libcrux_hmac.impl_hacl

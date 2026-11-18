import LibcruxHmac.Formal.Specs.Defs.Gaps
import LibcruxHmac.Formal.Specs.Defs.Hmac
import LibcruxHmac.Formal.Trusted.Sha2Hacl
import LibcruxHmac.Formal.Trusted.CoreAllocGaps
import LibcruxHmac.Formal.Proofs.Lemmas.ComputeSha2_512

/-!
# `libcrux_hmac::hmac_sha2_512` (crates/algorithms/hmac/src/impl_hacl.rs line 22)

The `impl_hmac!` instance at impl_hacl.rs line 22 (macro body lines 1–17).
Extracted as `libcrux_hmac.impl_hacl.hmac_sha2_512`
(`LibcruxHmac/Extraction/LibcruxHmac.lean` line 1830). It calls
`hacl::hmac::compute_sha2_512` (hacl/hmac.rs line 260; extraction line 1503),
which is extracted from the source with translation patch `sp-06`
(`06-sha2-512-read-on-ipad-line`): one discarded in-bounds read of `key_block[0]`, ratified
as equivalent to the original.

natural language description:
    `hmac_sha2_512(dst, key, data)` converts `key.len()` and then `data.len()` to
    `u32` with `try_into().unwrap()`, and calls `compute_sha2_512`. That function
    builds `K₀` (128 bytes; a key longer than 128 bytes is hashed first),
    hashes `(K₀ ⊕ ipad) ‖ data`, then `(K₀ ⊕ opad) ‖ inner hash`, and writes the
    64-byte result into `dst`.

natural language specs:
    * If `key.len()` and `data.len()` are at most `u32::MAX` (below `2 ^ 32`), it
      returns, and the new `dst` is `Spec.hmacSha512 key data`, whatever `dst` held.
      This is stated twice:
      - `hmac_sha2_512_spec`, the exact C1 claim, conditional on A1, A2 and the three
        accepted core/alloc gap assumptions (`Trusted/CoreAllocGaps.lean`);
      - `hmac_sha2_512_spec_of_gaps`, the same conclusion with the behaviour of these
        three gaps taken as the hypotheses `hdiv`, `hrem`, `hbox`.
    * Otherwise it panics: the `unwrap` of the failed conversion. This happens
      before `compute_sha2_512` runs, so the failure statement uses no assumption.
    A2 enters through the `LibcruxHmac.Formal.Trusted.Sha2Hacl` axioms
    h512_spec, sha512_init_spec, sha512_update_nblocks_spec,
    sha512_update_last_spec, sha512_finish_spec, hash_512_spec, ignore_spec,
    uint128_add_spec, uint64_to_uint128_spec;
    the extracted body depends on the ratified translation patch `sp-06`.
-/

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac.impl_hacl

/-- C1, conditional on the gap behaviours: the conclusion of `hmac_sha2_512_spec`,
with the behaviour of the three gap operations taken as the hypotheses `hdiv`,
`hrem` and `hbox` (`Defs/Gaps.lean`). Provable from A1, A2 and these hypotheses.
`hmac_sha2_512_spec` below is this theorem with the hypotheses discharged by the
accepted gap axioms. -/
theorem hmac_sha2_512_spec_of_gaps
    (hdiv : Spec.Gap.U32WrappingDiv) (hrem : Spec.Gap.U32WrappingRem)
    (hbox : Spec.Gap.VecIntoBoxedSlice)
    (dst : Array U8 64#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_512 dst key data ⦃ tag => tag.val = Spec.hmacSha512 key.val data.val ⦄ := by
  have hk : key.val.length ≤ U32.max := hkey
  have hd : data.val.length ≤ U32.max := hdata
  simp [hmac_sha2_512, core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from,
    core.num.tryFromUScalar, core.result.Result.unwrap, Slice.len, lift, hk, hd]
  simp only [Array.to_slice_mut]
  refine spec_bind (hacl.hmac.compute_sha2_512_spec_of_gaps hdiv hrem hbox _ key data _ _
    ?_ ?_ ?_) ?_
  · simp [Array.to_slice]
  · simp [Usize.ofNatCore]
    scalar_tac
  · simp [Usize.ofNatCore]
    scalar_tac
  · intro y hy
    rw [spec_ok]
    have hlen : y.val.length = (64#usize).val := by
      rw [hy]
      exact Spec.sha512_length _
    rw [Array.from_slice_val _ _ hlen, hy]

/-- C1, exact claim: below `2 ^ 32` bytes of key and data, `hmac_sha2_512` writes the
HMAC-SHA-512 tag of `data` under `key` into `dst`. Conditional on A1, A2 and the
three accepted gap assumptions.

`compute_sha2_512` calls `core.num.U32.wrapping_div`, `core.num.U32.wrapping_rem`
and `alloc.vec.Vec.into_boxed_slice`, which are bare axioms in the generated file.
By the owner's ruling of 2026-11-18 they are accepted as named assumptions: the
axioms `Trusted.u32_wrapping_div_spec`, `Trusted.u32_wrapping_rem_spec` and
`Trusted.vec_into_boxed_slice_spec` of `Trusted/CoreAllocGaps.lean`
(`externals.json` records `gap-core-u32-wrapping-div`, `gap-core-u32-wrapping-rem`
and `gap-alloc-vec-into-boxed-slice`). The proof is `hmac_sha2_512_spec_of_gaps`
applied to these three axioms. -/
@[step]
theorem hmac_sha2_512_spec (dst : Array U8 64#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_512 dst key data ⦃ tag => tag.val = Spec.hmacSha512 key.val data.val ⦄ :=
  hmac_sha2_512_spec_of_gaps Trusted.u32_wrapping_div_spec Trusted.u32_wrapping_rem_spec
    Trusted.vec_into_boxed_slice_spec dst key data hkey hdata

/-- C1, failure: with `2 ^ 32` or more bytes of key or data, `hmac_sha2_512` panics. -/
theorem hmac_sha2_512_panic (dst : Array U8 64#usize) (key data : Slice U8)
    (h : U32.max < key.length ∨ U32.max < data.length) :
    hmac_sha2_512 dst key data = fail .panic := by
  simp only [Slice.length] at h
  by_cases hkey : key.val.length ≤ U32.max
  · have hdata : ¬ data.val.length ≤ U32.max := by omega
    simp [hmac_sha2_512, core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from,
      core.num.tryFromUScalar, core.result.Result.unwrap, Slice.len, lift, hkey, hdata]
    rfl
  · simp [hmac_sha2_512, core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from,
      core.num.tryFromUScalar, core.result.Result.unwrap, Slice.len, lift, hkey]
    rfl

end libcrux_hmac.impl_hacl

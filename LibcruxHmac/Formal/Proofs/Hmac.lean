import LibcruxHmac.Formal.Proofs.HmacSha2_256
import LibcruxHmac.Formal.Proofs.HmacSha2_384
import LibcruxHmac.Formal.Proofs.HmacSha2_512
import LibcruxHmac.Formal.Proofs.Lemmas.HmacTail

/-!
# `libcrux_hmac::hmac` (crates/algorithms/hmac/src/hmac.rs lines 72–89)

Extracted as `libcrux_hmac.hmac` (`LibcruxHmac/Extraction/LibcruxHmac.lean`
lines 1890–1923). Translation patch `sp-08` (`08-hmac-inline-wrap-bufalloc-line-neutral`)
inlines the private helper `wrap_bufalloc` (hmac.rs lines 91–96) at its three
call sites before extraction. The reviewed equivalence maps
`wrap_bufalloc::<32, _>`, `::<48, _>` and `::<64, _>` to the `Sha256`, `Sha384`
and `Sha512` arms (hmac.rs lines 83, 84, 85). So this statement also covers
`wrap_bufalloc` at those three instances; there is no statement for the generic
helper.

natural language description:
    `hmac(alg, key, data, tag_length)` computes the full HMAC tag of `data` under
    `key` with the hash selected by `alg`: it calls `hmac_sha2_256`,
    `hmac_sha2_384` or `hmac_sha2_512` on a zeroed buffer of the native tag length
    and copies the buffer into a `Vec`. It then truncates the `Vec` to
    `tag_length`, which is the native length when `None` is given.

natural language specs:
    * If `key.len()` and `data.len()` are at most `u32::MAX` (below `2 ^ 32`), it
      returns the first `min(t, n)` bytes of `Spec.hmacOf alg key data`, where `n`
      is the native tag length and `t` is `tag_length` (or `n` for `None`).
      `Vec::truncate` does nothing when `t ≥ n`, so the result is never longer than
      `n`. (The Rust doc comment "Returns a vector of length `tag_length`" is
      wrong in that case.)
      This is stated twice:
      - `hmac_spec`, the exact C4 claim, conditional on C1 (`hmac_sha2_*_spec`),
        hence on A1 and A2, only;
      - `hmac_spec_of_gaps`, the same conclusion with the behaviour of four open
        core/alloc gaps taken as the hypotheses `hdiv`, `hrem`, `hbox` (inherited
        from C1) and `htrunc` (`Vec::truncate`).
    * Otherwise it panics: the `unwrap` in `hmac_sha2_*` fails before any hashing.
    The extracted body depends on the ratified translation patches `sp-08` (here)
    and `sp-04`/`sp-05`/`sp-06` (through `hmac_sha2_*`).
-/

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac

/-- C4, exact claim: below `2 ^ 32` bytes of key and data, `hmac` returns the HMAC
tag of `alg`, cut to `tag_length` bytes when that is shorter. Conditional on C1,
hence on A1 and A2, only.

This cannot be proved from the current extraction. `hmac` calls
`alloc.vec.Vec.truncate`, and through `hmac_sha2_*` also `core.num.U32.wrapping_div`,
`core.num.U32.wrapping_rem` and `alloc.vec.Vec.into_boxed_slice`. These are bare
axioms in the generated file (`externals.json` records `gap-alloc-vec-truncate`,
`gap-core-u32-wrapping-div`, `gap-core-u32-wrapping-rem` and
`gap-alloc-vec-into-boxed-slice`, all `open`). A proof needs either models of these
operations or the owner accepting them as named assumptions. The generated file is
immutable, so a model needs a re-extraction into a generated template plus a
hand-written external layer. Until then `hmac_spec_of_gaps` is the provable form. -/
@[step]
theorem hmac_spec (alg : Algorithm) (key data : Slice U8) (tag_length : Option Usize)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac alg key data tag_length ⦃ v =>
      v.val = (Spec.hmacOf alg key.val data.val).take
        ((tag_length.map (·.val)).getD (Spec.tagLength alg)) ⦄ := by
  sorry

/-- C4, conditional on the open gaps: the conclusion of `hmac_spec`, with the
behaviour of the four gap operations taken as the hypotheses `hdiv`, `hrem`,
`hbox` and `htrunc` (`Defs/Gaps.lean`). Provable from A1, A2 and these hypotheses,
through `hmac_sha2_*_spec_of_gaps`. It is not the agreed C4 claim. -/
theorem hmac_spec_of_gaps
    (hdiv : Spec.Gap.U32WrappingDiv) (hrem : Spec.Gap.U32WrappingRem)
    (hbox : Spec.Gap.VecIntoBoxedSlice) (htrunc : Spec.Gap.VecTruncate)
    (alg : Algorithm) (key data : Slice U8) (tag_length : Option Usize)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac alg key data tag_length ⦃ v =>
      v.val = (Spec.hmacOf alg key.val data.val).take
        ((tag_length.map (·.val)).getD (Spec.tagLength alg)) ⦄ := by
  unfold hmac
  cases alg <;> cases tag_length <;> simp only [tag_size, bind_ok] <;>
    first
    | refine spec_mono (hmac_tail htrunc _ _ _
        (impl_hacl.hmac_sha2_256_spec_of_gaps hdiv hrem hbox _ key data hkey hdata)) ?_
    | refine spec_mono (hmac_tail htrunc _ _ _
        (impl_hacl.hmac_sha2_384_spec_of_gaps hdiv hrem hbox _ key data hkey hdata)) ?_
    | refine spec_mono (hmac_tail htrunc _ _ _
        (impl_hacl.hmac_sha2_512_spec_of_gaps hdiv hrem hbox _ key data hkey hdata)) ?_
  all_goals (intro v hv; simp [hv, Spec.hmacOf, Spec.tagLength])

/-- C4, failure: with `2 ^ 32` or more bytes of key or data, `hmac` panics. -/
theorem hmac_panic (alg : Algorithm) (key data : Slice U8) (tag_length : Option Usize)
    (h : U32.max < key.length ∨ U32.max < data.length) :
    hmac alg key data tag_length = fail .panic := by
  unfold hmac
  cases alg <;> cases tag_length <;>
    simp [tag_size, impl_hacl.hmac_sha2_256_panic _ _ _ h, impl_hacl.hmac_sha2_384_panic _ _ _ h,
      impl_hacl.hmac_sha2_512_panic _ _ _ h]

end libcrux_hmac

import LibcruxHmac.Formal.Specs.Defs.Sha2

/-!
# Behaviour of the open core/alloc gaps, as named hypotheses

At the Aeneas pin `nightly-2026.11.09-5a392f4`, the Lean backend has no model of
four `core`/`alloc` functions that the extraction uses, so Aeneas emits them as
bare axioms (`LibcruxHmac/Extraction/LibcruxHmac.lean` lines 52, 59, 66, 74).
Their records in `.formalising/auto-fv/externals.json` are `open`: they are to be
modelled, and are not accepted assumptions.

So this file does **not** assume anything about them. Each definition below is
a `Prop` that states the Rust behaviour of one gap, restricted to the
instantiation the extraction uses. Only the conditional statements
`hmac_sha2_*_spec_of_gaps` and `hmac_spec_of_gaps` take these `Prop`s, as explicit
hypotheses. The exact claims `hmac_sha2_*_spec` and `hmac_spec` take none; they
can be proved once the gaps are modelled or accepted by the owner.

The two Debug-formatting gaps (`gap-core-tryfromint-error-debug-fmt` and
`a2-libcrux-traits-updateerror-debug-fmt`) need no hypothesis: they are only
instance arguments of `unwrap`/`expect`, whose Aeneas models never call them.
-/

open Aeneas Aeneas.Std Result WP
open libcrux_hmac.core.num.U32 (wrapping_div wrapping_rem)
open libcrux_hmac.alloc.vec.Vec (into_boxed_slice truncate)

namespace libcrux_hmac.Spec.Gap

/-- `gap-core-u32-wrapping-div`: for `u32`, `a.wrapping_div(b)` is `a / b` when
`b ≠ 0` (Rust `core::num`, uint_macros.rs line 2782). Used by
`hacl::hmac::compute_sha2_{256,384,512}`. -/
def U32WrappingDiv : Prop :=
  ∀ a b : U32, b.val ≠ 0 → wrapping_div a b ⦃ r => r.val = a.val / b.val ⦄

/-- `gap-core-u32-wrapping-rem`: for `u32`, `a.wrapping_rem(b)` is `a % b` when
`b ≠ 0` (Rust `core::num`, uint_macros.rs line 2835). Used by
`hacl::hmac::compute_sha2_{256,384,512}`. -/
def U32WrappingRem : Prop :=
  ∀ a b : U32, b.val ≠ 0 → wrapping_rem a b ⦃ r => r.val = a.val % b.val ⦄

/-- `gap-alloc-vec-into-boxed-slice`: `Vec::<u8>::into_boxed_slice` returns the
elements of the vector, in order (Rust `alloc`, vec/mod.rs line 1731). Used by
`hacl::hmac::compute_sha2_{256,384,512}`. -/
def VecIntoBoxedSlice : Prop :=
  ∀ v : alloc.vec.Vec U8, into_boxed_slice alloc.alloc.Global v = ok v.slice

/-- `gap-alloc-vec-truncate`: `Vec::<u8>::truncate(len)` keeps the first `len`
elements, and changes nothing when `len` is at least the length (Rust `alloc`,
vec/mod.rs line 1816). Used by `libcrux_hmac::hmac`. -/
def VecTruncate : Prop :=
  ∀ (v : alloc.vec.Vec U8) (n : Usize),
    truncate alloc.alloc.Global v n ⦃ v' => v'.val = v.val.take n.val ⦄

end libcrux_hmac.Spec.Gap

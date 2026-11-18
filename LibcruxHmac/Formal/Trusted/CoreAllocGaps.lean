import LibcruxHmac.Formal.Specs.Defs.Gaps

/-!
# Trusted (accepted assumptions): four `core`/`alloc` functions without a model

At the Aeneas pin `nightly-2026.11.09-5a392f4`, the Lean backend has no model of
`core::num::{u32}::wrapping_div`, `core::num::{u32}::wrapping_rem`,
`alloc::vec::Vec::into_boxed_slice` and `alloc::vec::Vec::truncate`. Aeneas emits
them as bare axioms that give only a type (`LibcruxHmac/Extraction/LibcruxHmac.lean`
lines 52, 59, 66, 74).

**Owner ruling of 2026-11-18.** The owner accepted these four functions as named
assumptions. Their records in `.formalising/auto-fv/externals.json`
(`gap-core-u32-wrapping-div`, `gap-core-u32-wrapping-rem`,
`gap-alloc-vec-into-boxed-slice`, `gap-alloc-vec-truncate`) are
`assumption-accepted`. The four axioms below are these assumptions. Each asserts
exactly one `Prop` of `LibcruxHmac/Formal/Specs/Defs/Gaps.lean`, which is the Rust
behaviour of that function for the instantiation the extraction uses, and nothing
more. The Rust sources are those of toolchain `nightly-2026-09-17` (rustc
`923c95cdf`).

They are used by `hacl::hmac::compute_sha2_{256,384,512}` (the first three) and by
`libcrux_hmac::hmac` (`truncate`). The exact claims `hmac_sha2_*_spec` and
`hmac_spec` are proved from the conditional forms `hmac_sha2_*_spec_of_gaps` and
`hmac_spec_of_gaps` and these axioms.

Follow-up: modelling these functions (or adding them upstream to Aeneas) would let
each axiom be proved, and then removed. The record
`gap-core-tryfromint-error-debug-fmt` stays open; nothing here relies on it (that
`fmt` is only an instance argument of `unwrap`, never called).
-/

namespace libcrux_hmac.Trusted

/-- Accepted assumption, `gap-core-u32-wrapping-div` (owner ruling 2026-11-18): for
`u32`, `a.wrapping_div(b)` is `a / b` when `b ≠ 0`. Rust source:
`core::num::{u32}::wrapping_div`, library/core/src/num/uint_macros.rs line 2782
(Rust nightly-2026-09-17, rustc 923c95cdf). Extraction axiom:
`LibcruxHmac/Extraction/LibcruxHmac.lean` line 52. Used by
`hacl::hmac::compute_sha2_{256,384,512}`. -/
axiom u32_wrapping_div_spec : Spec.Gap.U32WrappingDiv

/-- Accepted assumption, `gap-core-u32-wrapping-rem` (owner ruling 2026-11-18): for
`u32`, `a.wrapping_rem(b)` is `a % b` when `b ≠ 0`. Rust source:
`core::num::{u32}::wrapping_rem`, library/core/src/num/uint_macros.rs line 2835
(Rust nightly-2026-09-17, rustc 923c95cdf). Extraction axiom:
`LibcruxHmac/Extraction/LibcruxHmac.lean` line 59. Used by
`hacl::hmac::compute_sha2_{256,384,512}`. -/
axiom u32_wrapping_rem_spec : Spec.Gap.U32WrappingRem

/-- Accepted assumption, `gap-alloc-vec-into-boxed-slice` (owner ruling 2026-11-18):
`Vec::<u8>::into_boxed_slice` returns the elements of the vector, in order. Rust
source: `alloc::vec::Vec::into_boxed_slice`, library/alloc/src/vec/mod.rs line 1731
(Rust nightly-2026-09-17, rustc 923c95cdf). Extraction axiom:
`LibcruxHmac/Extraction/LibcruxHmac.lean` line 66. Used by
`hacl::hmac::compute_sha2_{256,384,512}`. -/
axiom vec_into_boxed_slice_spec : Spec.Gap.VecIntoBoxedSlice

/-- Accepted assumption, `gap-alloc-vec-truncate` (owner ruling 2026-11-18):
`Vec::<u8>::truncate(len)` keeps the first `len` elements, and changes nothing when
`len` is at least the length. Rust source: `alloc::vec::Vec::truncate`,
library/alloc/src/vec/mod.rs line 1816 (Rust nightly-2026-09-17, rustc 923c95cdf).
Extraction axiom: `LibcruxHmac/Extraction/LibcruxHmac.lean` line 74. Used by
`libcrux_hmac::hmac`. -/
axiom vec_truncate_spec : Spec.Gap.VecTruncate

end libcrux_hmac.Trusted

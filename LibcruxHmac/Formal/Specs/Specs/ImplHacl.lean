import LibcruxHmac.Formal.Proofs.HmacSha2_256
import LibcruxHmac.Formal.Proofs.HmacSha2_384
import LibcruxHmac.Formal.Proofs.HmacSha2_512

/-!
# Specifications for `crates/algorithms/hmac/src/impl_hacl.rs`

Public items of `impl_hacl.rs` (claim C1) and their statements. Each statement
is declared once, in `LibcruxHmac/Formal/Proofs/`. It is restated here with
`recall`, which fails to build if the declared statement differs.

* `libcrux_hmac::hmac_sha2_256` (C1): `hmac_sha2_256_spec`,
  `hmac_sha2_256_spec_of_gaps`, `hmac_sha2_256_panic` (`Proofs/HmacSha2_256.lean`);
* `libcrux_hmac::hmac_sha2_384` (C1): `hmac_sha2_384_spec`,
  `hmac_sha2_384_spec_of_gaps`, `hmac_sha2_384_panic` (`Proofs/HmacSha2_384.lean`);
* `libcrux_hmac::hmac_sha2_512` (C1): `hmac_sha2_512_spec`,
  `hmac_sha2_512_spec_of_gaps`, `hmac_sha2_512_panic` (`Proofs/HmacSha2_512.lean`).

Two forms of the success statement:
* `hmac_sha2_*_spec` is the exact C1 claim, conditional on A1 and A2 only. It
  cannot be proved from the current extraction: `compute_sha2_*` calls three
  operations that are bare axioms in the generated file (`externals.json` records
  `gap-core-u32-wrapping-div`, `gap-core-u32-wrapping-rem`,
  `gap-alloc-vec-into-boxed-slice`, all `open`). A proof needs models of them (a
  re-extraction into a generated template plus a hand-written external layer) or
  the owner accepting them as named assumptions.
* `hmac_sha2_*_spec_of_gaps` has the same conclusion, with the behaviour of these
  operations as the explicit hypotheses `hdiv`, `hrem`, `hbox` (`Defs/Gaps.lean`).
  It is provable from A1, A2 and these hypotheses. It is not the agreed claim.

Not stated: `hacl::hmac::compute_sha2_{256,384,512}`. Under the default features
(no `expose-hacl`) they are `pub(crate)`, so they are proof helpers, not public
API.

Each `#print axioms` below is followed by its guard list. The guard is
**pending**: until the proof PR, the output also contains `sorryAx`. After the
proof PR it must show exactly the listed axioms.
-/

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac.impl_hacl

/-! ## `libcrux_hmac::hmac_sha2_256` (C1) -/

recall hmac_sha2_256_spec (dst : Array U8 32#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_256 dst key data ⦃ tag => tag.val = Spec.hmacSha256 key.val data.val ⦄

#print axioms hmac_sha2_256_spec
/- Axiom guard (pending; exact claim, blocked on the open gaps):
   * Lean: `propext`, `Classical.choice`, `Quot.sound`.
   * Extraction axioms reached through `hmac_sha2_256` (boundary A2, types only):
     `libcrux_sha2.hacl.{h256, hash_256, sha256_init, sha256_update_nblocks,
     sha256_update_last, sha256_finish}`, `libcrux_hacl_rs.lowstar.ignore.ignore`.
   * Trusted axioms the proof rests on (A2, `Trusted/Sha2Hacl.lean`):
     `Trusted.h256_spec`, `Trusted.sha256_init_spec`, `Trusted.sha256_update_nblocks_spec`,
     `Trusted.sha256_update_last_spec`, `Trusted.sha256_finish_spec`,
     `Trusted.hash_256_spec`, `Trusted.ignore_spec`.
   * Translation patch (A1, ratified): `sp-04`.
   * Gap operations: today `core.num.U32.wrapping_div`, `core.num.U32.wrapping_rem`
     and `alloc.vec.Vec.into_boxed_slice` are bare extraction axioms reached
     through `hmac_sha2_256`. A proof needs them modelled (they then leave this list,
     replaced by the model's own dependencies) or accepted by the owner as named
     assumptions (they then stay, recorded as accepted).
   * `core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt` (extraction axiom,
     only an instance argument of `unwrap`, never called). -/

recall hmac_sha2_256_spec_of_gaps
    (hdiv : Spec.Gap.U32WrappingDiv) (hrem : Spec.Gap.U32WrappingRem)
    (hbox : Spec.Gap.VecIntoBoxedSlice)
    (dst : Array U8 32#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_256 dst key data ⦃ tag => tag.val = Spec.hmacSha256 key.val data.val ⦄

/-- info: 'libcrux_hmac.impl_hacl.hmac_sha2_256_spec_of_gaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.h256_spec,
 Trusted.hash_256_spec,
 Trusted.ignore_spec,
 Trusted.sha256_finish_spec,
 Trusted.sha256_init_spec,
 Trusted.sha256_update_last_spec,
 Trusted.sha256_update_nblocks_spec,
 libcrux_sha2.hacl.h256,
 libcrux_sha2.hacl.hash_256,
 libcrux_sha2.hacl.sha256_finish,
 libcrux_sha2.hacl.sha256_init,
 libcrux_sha2.hacl.sha256_update_last,
 libcrux_sha2.hacl.sha256_update_nblocks,
 alloc.vec.Vec.into_boxed_slice,
 core.num.U32.wrapping_div,
 core.num.U32.wrapping_rem,
 libcrux_hacl_rs.lowstar.ignore.ignore,
 core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in #print axioms hmac_sha2_256_spec_of_gaps
/- Axiom guard (pending; conditional form):
   * Lean: `propext`, `Classical.choice`, `Quot.sound`.
   * Extraction axioms reached through `hmac_sha2_256` (boundary A2, types only):
     `libcrux_sha2.hacl.{h256, hash_256, sha256_init, sha256_update_nblocks,
     sha256_update_last, sha256_finish}`, `libcrux_hacl_rs.lowstar.ignore.ignore`.
   * Trusted axioms the proof rests on (A2, `Trusted/Sha2Hacl.lean`):
     `Trusted.h256_spec`, `Trusted.sha256_init_spec`, `Trusted.sha256_update_nblocks_spec`,
     `Trusted.sha256_update_last_spec`, `Trusted.sha256_finish_spec`,
     `Trusted.hash_256_spec`, `Trusted.ignore_spec`.
   * Translation patch (A1, ratified): `sp-04`.
   * Extraction axioms of the open gaps, reached through `hmac_sha2_256`:
     `core.num.U32.wrapping_div`, `core.num.U32.wrapping_rem`,
     `alloc.vec.Vec.into_boxed_slice` (their behaviour is assumed only through
     the hypotheses `hdiv`, `hrem`, `hbox`), and
     `core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt` (never called). -/

recall hmac_sha2_256_panic (dst : Array U8 32#usize) (key data : Slice U8)
    (h : U32.max < key.length ∨ U32.max < data.length) :
    hmac_sha2_256 dst key data = fail .panic

/-- info: 'libcrux_hmac.impl_hacl.hmac_sha2_256_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 libcrux_sha2.hacl.h256,
 libcrux_sha2.hacl.hash_256,
 libcrux_sha2.hacl.sha256_finish,
 libcrux_sha2.hacl.sha256_init,
 libcrux_sha2.hacl.sha256_update_last,
 libcrux_sha2.hacl.sha256_update_nblocks,
 alloc.vec.Vec.into_boxed_slice,
 core.num.U32.wrapping_div,
 core.num.U32.wrapping_rem,
 libcrux_hacl_rs.lowstar.ignore.ignore,
 core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in #print axioms hmac_sha2_256_panic
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`, and the
   extraction axioms reached through `hmac_sha2_256` (as for `hmac_sha2_256_spec`).
   No Trusted axiom and no gap hypothesis. -/

/-! ## `libcrux_hmac::hmac_sha2_384` (C1) -/

recall hmac_sha2_384_spec (dst : Array U8 48#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_384 dst key data ⦃ tag => tag.val = Spec.hmacSha384 key.val data.val ⦄

#print axioms hmac_sha2_384_spec
/- Axiom guard (pending; exact claim, blocked on the open gaps):
   * Lean: `propext`, `Classical.choice`, `Quot.sound`.
   * Extraction axioms reached through `hmac_sha2_384` (boundary A2, types only):
     `libcrux_sha2.hacl.{h384, hash_384, sha384_init, sha384_update_nblocks,
     sha384_update_last, sha384_finish}`, `libcrux_hacl_rs.lowstar.ignore.ignore`,
     `libcrux_hacl_rs.fstar.uint128.{add, uint64_to_uint128}`.
   * Trusted axioms the proof rests on (A2, `Trusted/Sha2Hacl.lean`):
     `Trusted.h384_spec`, `Trusted.sha384_init_spec`, `Trusted.sha384_update_nblocks_spec`,
     `Trusted.sha384_update_last_spec`, `Trusted.sha384_finish_spec`,
     `Trusted.hash_384_spec`, `Trusted.ignore_spec`,
     `Trusted.uint128_add_spec`, `Trusted.uint64_to_uint128_spec`.
   * Translation patch (A1, ratified): `sp-05`.
   * Gap operations: today `core.num.U32.wrapping_div`, `core.num.U32.wrapping_rem`
     and `alloc.vec.Vec.into_boxed_slice` are bare extraction axioms reached
     through `hmac_sha2_384`. A proof needs them modelled (they then leave this list,
     replaced by the model's own dependencies) or accepted by the owner as named
     assumptions (they then stay, recorded as accepted).
   * `core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt` (extraction axiom,
     only an instance argument of `unwrap`, never called). -/

recall hmac_sha2_384_spec_of_gaps
    (hdiv : Spec.Gap.U32WrappingDiv) (hrem : Spec.Gap.U32WrappingRem)
    (hbox : Spec.Gap.VecIntoBoxedSlice)
    (dst : Array U8 48#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_384 dst key data ⦃ tag => tag.val = Spec.hmacSha384 key.val data.val ⦄

/-- info: 'libcrux_hmac.impl_hacl.hmac_sha2_384_spec_of_gaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.h384_spec,
 Trusted.hash_384_spec,
 Trusted.ignore_spec,
 Trusted.sha384_finish_spec,
 Trusted.sha384_init_spec,
 Trusted.sha384_update_last_spec,
 Trusted.sha384_update_nblocks_spec,
 Trusted.uint128_add_spec,
 Trusted.uint64_to_uint128_spec,
 libcrux_sha2.hacl.h384,
 libcrux_sha2.hacl.hash_384,
 libcrux_sha2.hacl.sha384_finish,
 libcrux_sha2.hacl.sha384_init,
 libcrux_sha2.hacl.sha384_update_last,
 libcrux_sha2.hacl.sha384_update_nblocks,
 alloc.vec.Vec.into_boxed_slice,
 core.num.U32.wrapping_div,
 core.num.U32.wrapping_rem,
 libcrux_hacl_rs.fstar.uint128.add,
 libcrux_hacl_rs.fstar.uint128.uint64_to_uint128,
 libcrux_hacl_rs.lowstar.ignore.ignore,
 core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in #print axioms hmac_sha2_384_spec_of_gaps
/- Axiom guard (pending; conditional form):
   * Lean: `propext`, `Classical.choice`, `Quot.sound`.
   * Extraction axioms reached through `hmac_sha2_384` (boundary A2, types only):
     `libcrux_sha2.hacl.{h384, hash_384, sha384_init, sha384_update_nblocks,
     sha384_update_last, sha384_finish}`, `libcrux_hacl_rs.lowstar.ignore.ignore`,
     `libcrux_hacl_rs.fstar.uint128.{add, uint64_to_uint128}`.
   * Trusted axioms the proof rests on (A2, `Trusted/Sha2Hacl.lean`):
     `Trusted.h384_spec`, `Trusted.sha384_init_spec`, `Trusted.sha384_update_nblocks_spec`,
     `Trusted.sha384_update_last_spec`, `Trusted.sha384_finish_spec`,
     `Trusted.hash_384_spec`, `Trusted.ignore_spec`,
     `Trusted.uint128_add_spec`, `Trusted.uint64_to_uint128_spec`.
   * Translation patch (A1, ratified): `sp-05`.
   * Extraction axioms of the open gaps, reached through `hmac_sha2_384`:
     `core.num.U32.wrapping_div`, `core.num.U32.wrapping_rem`,
     `alloc.vec.Vec.into_boxed_slice` (their behaviour is assumed only through
     the hypotheses `hdiv`, `hrem`, `hbox`), and
     `core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt` (never called). -/

recall hmac_sha2_384_panic (dst : Array U8 48#usize) (key data : Slice U8)
    (h : U32.max < key.length ∨ U32.max < data.length) :
    hmac_sha2_384 dst key data = fail .panic

/-- info: 'libcrux_hmac.impl_hacl.hmac_sha2_384_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 libcrux_sha2.hacl.h384,
 libcrux_sha2.hacl.hash_384,
 libcrux_sha2.hacl.sha384_finish,
 libcrux_sha2.hacl.sha384_init,
 libcrux_sha2.hacl.sha384_update_last,
 libcrux_sha2.hacl.sha384_update_nblocks,
 alloc.vec.Vec.into_boxed_slice,
 core.num.U32.wrapping_div,
 core.num.U32.wrapping_rem,
 libcrux_hacl_rs.fstar.uint128.add,
 libcrux_hacl_rs.fstar.uint128.uint64_to_uint128,
 libcrux_hacl_rs.lowstar.ignore.ignore,
 core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in #print axioms hmac_sha2_384_panic
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`, and the
   extraction axioms reached through `hmac_sha2_384` (as for `hmac_sha2_384_spec`).
   No Trusted axiom and no gap hypothesis. -/

/-! ## `libcrux_hmac::hmac_sha2_512` (C1) -/

recall hmac_sha2_512_spec (dst : Array U8 64#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_512 dst key data ⦃ tag => tag.val = Spec.hmacSha512 key.val data.val ⦄

#print axioms hmac_sha2_512_spec
/- Axiom guard (pending; exact claim, blocked on the open gaps):
   * Lean: `propext`, `Classical.choice`, `Quot.sound`.
   * Extraction axioms reached through `hmac_sha2_512` (boundary A2, types only):
     `libcrux_sha2.hacl.{h512, hash_512, sha512_init, sha512_update_nblocks,
     sha512_update_last, sha512_finish}`, `libcrux_hacl_rs.lowstar.ignore.ignore`,
     `libcrux_hacl_rs.fstar.uint128.{add, uint64_to_uint128}`.
   * Trusted axioms the proof rests on (A2, `Trusted/Sha2Hacl.lean`):
     `Trusted.h512_spec`, `Trusted.sha512_init_spec`, `Trusted.sha512_update_nblocks_spec`,
     `Trusted.sha512_update_last_spec`, `Trusted.sha512_finish_spec`,
     `Trusted.hash_512_spec`, `Trusted.ignore_spec`,
     `Trusted.uint128_add_spec`, `Trusted.uint64_to_uint128_spec`.
   * Translation patch (A1, ratified): `sp-06`.
   * Gap operations: today `core.num.U32.wrapping_div`, `core.num.U32.wrapping_rem`
     and `alloc.vec.Vec.into_boxed_slice` are bare extraction axioms reached
     through `hmac_sha2_512`. A proof needs them modelled (they then leave this list,
     replaced by the model's own dependencies) or accepted by the owner as named
     assumptions (they then stay, recorded as accepted).
   * `core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt` (extraction axiom,
     only an instance argument of `unwrap`, never called). -/

recall hmac_sha2_512_spec_of_gaps
    (hdiv : Spec.Gap.U32WrappingDiv) (hrem : Spec.Gap.U32WrappingRem)
    (hbox : Spec.Gap.VecIntoBoxedSlice)
    (dst : Array U8 64#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_512 dst key data ⦃ tag => tag.val = Spec.hmacSha512 key.val data.val ⦄

/-- info: 'libcrux_hmac.impl_hacl.hmac_sha2_512_spec_of_gaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.h512_spec,
 Trusted.hash_512_spec,
 Trusted.ignore_spec,
 Trusted.sha512_finish_spec,
 Trusted.sha512_init_spec,
 Trusted.sha512_update_last_spec,
 Trusted.sha512_update_nblocks_spec,
 Trusted.uint128_add_spec,
 Trusted.uint64_to_uint128_spec,
 libcrux_sha2.hacl.h512,
 libcrux_sha2.hacl.hash_512,
 libcrux_sha2.hacl.sha512_finish,
 libcrux_sha2.hacl.sha512_init,
 libcrux_sha2.hacl.sha512_update_last,
 libcrux_sha2.hacl.sha512_update_nblocks,
 alloc.vec.Vec.into_boxed_slice,
 core.num.U32.wrapping_div,
 core.num.U32.wrapping_rem,
 libcrux_hacl_rs.fstar.uint128.add,
 libcrux_hacl_rs.fstar.uint128.uint64_to_uint128,
 libcrux_hacl_rs.lowstar.ignore.ignore,
 core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in #print axioms hmac_sha2_512_spec_of_gaps
/- Axiom guard (pending; conditional form):
   * Lean: `propext`, `Classical.choice`, `Quot.sound`.
   * Extraction axioms reached through `hmac_sha2_512` (boundary A2, types only):
     `libcrux_sha2.hacl.{h512, hash_512, sha512_init, sha512_update_nblocks,
     sha512_update_last, sha512_finish}`, `libcrux_hacl_rs.lowstar.ignore.ignore`,
     `libcrux_hacl_rs.fstar.uint128.{add, uint64_to_uint128}`.
   * Trusted axioms the proof rests on (A2, `Trusted/Sha2Hacl.lean`):
     `Trusted.h512_spec`, `Trusted.sha512_init_spec`, `Trusted.sha512_update_nblocks_spec`,
     `Trusted.sha512_update_last_spec`, `Trusted.sha512_finish_spec`,
     `Trusted.hash_512_spec`, `Trusted.ignore_spec`,
     `Trusted.uint128_add_spec`, `Trusted.uint64_to_uint128_spec`.
   * Translation patch (A1, ratified): `sp-06`.
   * Extraction axioms of the open gaps, reached through `hmac_sha2_512`:
     `core.num.U32.wrapping_div`, `core.num.U32.wrapping_rem`,
     `alloc.vec.Vec.into_boxed_slice` (their behaviour is assumed only through
     the hypotheses `hdiv`, `hrem`, `hbox`), and
     `core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt` (never called). -/

recall hmac_sha2_512_panic (dst : Array U8 64#usize) (key data : Slice U8)
    (h : U32.max < key.length ∨ U32.max < data.length) :
    hmac_sha2_512 dst key data = fail .panic

/-- info: 'libcrux_hmac.impl_hacl.hmac_sha2_512_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 libcrux_sha2.hacl.h512,
 libcrux_sha2.hacl.hash_512,
 libcrux_sha2.hacl.sha512_finish,
 libcrux_sha2.hacl.sha512_init,
 libcrux_sha2.hacl.sha512_update_last,
 libcrux_sha2.hacl.sha512_update_nblocks,
 alloc.vec.Vec.into_boxed_slice,
 core.num.U32.wrapping_div,
 core.num.U32.wrapping_rem,
 libcrux_hacl_rs.fstar.uint128.add,
 libcrux_hacl_rs.fstar.uint128.uint64_to_uint128,
 libcrux_hacl_rs.lowstar.ignore.ignore,
 core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in #print axioms hmac_sha2_512_panic
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`, and the
   extraction axioms reached through `hmac_sha2_512` (as for `hmac_sha2_512_spec`).
   No Trusted axiom and no gap hypothesis. -/

end libcrux_hmac.impl_hacl

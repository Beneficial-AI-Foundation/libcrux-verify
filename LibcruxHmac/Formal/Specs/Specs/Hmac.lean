import LibcruxHmac.Formal.Proofs.TagSize
import LibcruxHmac.Formal.Proofs.Hmac

/-!
# Specifications for `crates/algorithms/hmac/src/hmac.rs`

Public items of `hmac.rs` and their statements. Each statement is declared once,
in `LibcruxHmac/Formal/Proofs/`. It is restated here with `recall`, which fails to
build if the declared statement differs.

* `libcrux_hmac::tag_size`: `tag_size_spec` (`Proofs/TagSize.lean`);
* `libcrux_hmac::hmac` (C4): `hmac_spec`, `hmac_spec_of_gaps`, `hmac_panic`
  (`Proofs/Hmac.lean`).

Two forms of the `hmac` success statement:
* `hmac_spec` is the exact C4 claim, conditional on C1, hence on A1, A2 and the
  accepted core/alloc gap assumptions. `hmac` reaches four operations that are bare
  axioms in the generated file (`externals.json` records `gap-alloc-vec-truncate`,
  `gap-core-u32-wrapping-div`, `gap-core-u32-wrapping-rem`,
  `gap-alloc-vec-into-boxed-slice`). By the owner's ruling of 2026-11-18 they are
  accepted as named assumptions, the axioms `Trusted.vec_truncate_spec`,
  `Trusted.u32_wrapping_div_spec`, `Trusted.u32_wrapping_rem_spec` and
  `Trusted.vec_into_boxed_slice_spec` (`Trusted/CoreAllocGaps.lean`). The proof
  applies `hmac_spec_of_gaps` to these axioms.
* `hmac_spec_of_gaps` has the same conclusion, with the behaviour of these
  operations as the explicit hypotheses `hdiv`, `hrem`, `hbox`, `htrunc`
  (`Defs/Gaps.lean`). It is provable from A1, A2 and these hypotheses.

Definitions, not separate statements: `Algorithm`, `Error`, the trait `HmacState`.

Not stated:
* the derived `Clone`, `Copy`, `Debug` and `PartialEq` impls of `Algorithm` and
  `Error`;
* the private helper `wrap_bufalloc`: translation patch `sp-08` inlines it, and
  `hmac_spec` and `hmac_spec_of_gaps` cover its three instances (hmac.rs
  lines 83–85).

Each `#print axioms` below is checked by `#guard_msgs` against the exact list of
axioms that Lean prints. All statements are proved, so no list contains `sorryAx`.
The comment after each guard explains where its entries come from.
-/

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac

/-! ## `libcrux_hmac::tag_size` -/

recall tag_size_spec (alg : Algorithm) :
    tag_size alg ⦃ n => n.val = Spec.tagLength alg ⦄

/-- info: 'libcrux_hmac.tag_size_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tag_size_spec
/- Axiom guard:`propext`, `Classical.choice`, `Quot.sound`.
   No Trusted axiom, no extraction axiom. -/

/-! ## `libcrux_hmac::hmac` (C4) -/

recall hmac_spec (alg : Algorithm) (key data : Slice U8) (tag_length : Option Usize)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac alg key data tag_length ⦃ v =>
      v.val = (Spec.hmacOf alg key.val data.val).take
        ((tag_length.map (·.val)).getD (Spec.tagLength alg)) ⦄

/-- info: 'libcrux_hmac.hmac_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.h256_spec,
 Trusted.h384_spec,
 Trusted.h512_spec,
 Trusted.hash_256_spec,
 Trusted.hash_384_spec,
 Trusted.hash_512_spec,
 Trusted.ignore_spec,
 Trusted.sha256_finish_spec,
 Trusted.sha256_init_spec,
 Trusted.sha256_update_last_spec,
 Trusted.sha256_update_nblocks_spec,
 Trusted.sha384_finish_spec,
 Trusted.sha384_init_spec,
 Trusted.sha384_update_last_spec,
 Trusted.sha384_update_nblocks_spec,
 Trusted.sha512_finish_spec,
 Trusted.sha512_init_spec,
 Trusted.sha512_update_last_spec,
 Trusted.sha512_update_nblocks_spec,
 Trusted.u32_wrapping_div_spec,
 Trusted.u32_wrapping_rem_spec,
 Trusted.uint128_add_spec,
 Trusted.uint64_to_uint128_spec,
 Trusted.vec_into_boxed_slice_spec,
 Trusted.vec_truncate_spec,
 libcrux_sha2.hacl.h256,
 libcrux_sha2.hacl.h384,
 libcrux_sha2.hacl.h512,
 libcrux_sha2.hacl.hash_256,
 libcrux_sha2.hacl.hash_384,
 libcrux_sha2.hacl.hash_512,
 libcrux_sha2.hacl.sha256_finish,
 libcrux_sha2.hacl.sha256_init,
 libcrux_sha2.hacl.sha256_update_last,
 libcrux_sha2.hacl.sha256_update_nblocks,
 libcrux_sha2.hacl.sha384_finish,
 libcrux_sha2.hacl.sha384_init,
 libcrux_sha2.hacl.sha384_update_last,
 libcrux_sha2.hacl.sha384_update_nblocks,
 libcrux_sha2.hacl.sha512_finish,
 libcrux_sha2.hacl.sha512_init,
 libcrux_sha2.hacl.sha512_update_last,
 libcrux_sha2.hacl.sha512_update_nblocks,
 alloc.vec.Vec.into_boxed_slice,
 alloc.vec.Vec.truncate,
 core.num.U32.wrapping_div,
 core.num.U32.wrapping_rem,
 libcrux_hacl_rs.fstar.uint128.add,
 libcrux_hacl_rs.fstar.uint128.uint64_to_uint128,
 libcrux_hacl_rs.lowstar.ignore.ignore,
 core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in #print axioms hmac_spec
/- Axiom guard (exact claim; no `sorryAx`):
   * Lean: `propext`, `Classical.choice`, `Quot.sound`.
   * Extraction axioms reached through `hmac` (boundary A2, types only):
     `libcrux_sha2.hacl.{h256, h384, h512, hash_256, hash_384, hash_512,
     sha{256,384,512}_{init, update_nblocks, update_last, finish}}` and
     `libcrux_hacl_rs.{fstar.uint128.add, fstar.uint128.uint64_to_uint128,
     lowstar.ignore.ignore}`.
   * Trusted axioms the proof rests on (A2, `Trusted/Sha2Hacl.lean`), through C1:
     as for `hmac_spec_of_gaps` below.
   * Trusted axioms for the accepted core/alloc gaps (owner ruling 2026-11-18,
     `Trusted/CoreAllocGaps.lean`): `Trusted.u32_wrapping_div_spec`,
     `Trusted.u32_wrapping_rem_spec`, `Trusted.vec_into_boxed_slice_spec` (through
     C1) and `Trusted.vec_truncate_spec`. The bare extraction axioms
     `alloc.vec.Vec.truncate`, `alloc.vec.Vec.into_boxed_slice`,
     `core.num.U32.wrapping_div` and `core.num.U32.wrapping_rem` stay in the list:
     they are the constants these four axioms speak about.
   * `core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt` (extraction axiom,
     never called).
   * Translation patches (A1, ratified): `sp-04`, `sp-05`, `sp-06`, `sp-08`. -/

recall hmac_spec_of_gaps
    (hdiv : Spec.Gap.U32WrappingDiv) (hrem : Spec.Gap.U32WrappingRem)
    (hbox : Spec.Gap.VecIntoBoxedSlice) (htrunc : Spec.Gap.VecTruncate)
    (alg : Algorithm) (key data : Slice U8) (tag_length : Option Usize)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac alg key data tag_length ⦃ v =>
      v.val = (Spec.hmacOf alg key.val data.val).take
        ((tag_length.map (·.val)).getD (Spec.tagLength alg)) ⦄

/-- info: 'libcrux_hmac.hmac_spec_of_gaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.h256_spec,
 Trusted.h384_spec,
 Trusted.h512_spec,
 Trusted.hash_256_spec,
 Trusted.hash_384_spec,
 Trusted.hash_512_spec,
 Trusted.ignore_spec,
 Trusted.sha256_finish_spec,
 Trusted.sha256_init_spec,
 Trusted.sha256_update_last_spec,
 Trusted.sha256_update_nblocks_spec,
 Trusted.sha384_finish_spec,
 Trusted.sha384_init_spec,
 Trusted.sha384_update_last_spec,
 Trusted.sha384_update_nblocks_spec,
 Trusted.sha512_finish_spec,
 Trusted.sha512_init_spec,
 Trusted.sha512_update_last_spec,
 Trusted.sha512_update_nblocks_spec,
 Trusted.uint128_add_spec,
 Trusted.uint64_to_uint128_spec,
 libcrux_sha2.hacl.h256,
 libcrux_sha2.hacl.h384,
 libcrux_sha2.hacl.h512,
 libcrux_sha2.hacl.hash_256,
 libcrux_sha2.hacl.hash_384,
 libcrux_sha2.hacl.hash_512,
 libcrux_sha2.hacl.sha256_finish,
 libcrux_sha2.hacl.sha256_init,
 libcrux_sha2.hacl.sha256_update_last,
 libcrux_sha2.hacl.sha256_update_nblocks,
 libcrux_sha2.hacl.sha384_finish,
 libcrux_sha2.hacl.sha384_init,
 libcrux_sha2.hacl.sha384_update_last,
 libcrux_sha2.hacl.sha384_update_nblocks,
 libcrux_sha2.hacl.sha512_finish,
 libcrux_sha2.hacl.sha512_init,
 libcrux_sha2.hacl.sha512_update_last,
 libcrux_sha2.hacl.sha512_update_nblocks,
 alloc.vec.Vec.into_boxed_slice,
 alloc.vec.Vec.truncate,
 core.num.U32.wrapping_div,
 core.num.U32.wrapping_rem,
 libcrux_hacl_rs.fstar.uint128.add,
 libcrux_hacl_rs.fstar.uint128.uint64_to_uint128,
 libcrux_hacl_rs.lowstar.ignore.ignore,
 core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in #print axioms hmac_spec_of_gaps
/- Axiom guard (conditional form):
   * Lean: `propext`, `Classical.choice`, `Quot.sound`.
   * Extraction axioms reached through `hmac` (boundary A2, types only):
     `libcrux_sha2.hacl.{h256, h384, h512, hash_256, hash_384, hash_512,
     sha{256,384,512}_{init, update_nblocks, update_last, finish}}` and
     `libcrux_hacl_rs.{fstar.uint128.add, fstar.uint128.uint64_to_uint128,
     lowstar.ignore.ignore}`.
   * Extraction axioms of open gaps, reached through `hmac`:
     `alloc.vec.Vec.into_boxed_slice`, `alloc.vec.Vec.truncate`,
     `core.num.U32.wrapping_div`, `core.num.U32.wrapping_rem` (each assumed only
     through the hypotheses `hbox`, `htrunc`, `hdiv`, `hrem`), and
     `core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt` (never called).
   * Trusted axioms the proof rests on (A2, `Trusted/Sha2Hacl.lean`), through C1:
     `Trusted.{h256, h384, h512}_spec`, `Trusted.sha{256,384,512}_init_spec`,
     `Trusted.sha{256,384,512}_update_nblocks_spec`,
     `Trusted.sha{256,384,512}_update_last_spec`, `Trusted.sha{256,384,512}_finish_spec`,
     `Trusted.hash_{256,384,512}_spec`, `Trusted.uint128_add_spec`,
     `Trusted.uint64_to_uint128_spec`, `Trusted.ignore_spec`.
   * Translation patches (A1, ratified): `sp-04`, `sp-05`, `sp-06`, `sp-08`. -/

recall hmac_panic (alg : Algorithm) (key data : Slice U8) (tag_length : Option Usize)
    (h : U32.max < key.length ∨ U32.max < data.length) :
    hmac alg key data tag_length = fail .panic

/-- info: 'libcrux_hmac.hmac_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 libcrux_sha2.hacl.h256,
 libcrux_sha2.hacl.h384,
 libcrux_sha2.hacl.h512,
 libcrux_sha2.hacl.hash_256,
 libcrux_sha2.hacl.hash_384,
 libcrux_sha2.hacl.hash_512,
 libcrux_sha2.hacl.sha256_finish,
 libcrux_sha2.hacl.sha256_init,
 libcrux_sha2.hacl.sha256_update_last,
 libcrux_sha2.hacl.sha256_update_nblocks,
 libcrux_sha2.hacl.sha384_finish,
 libcrux_sha2.hacl.sha384_init,
 libcrux_sha2.hacl.sha384_update_last,
 libcrux_sha2.hacl.sha384_update_nblocks,
 libcrux_sha2.hacl.sha512_finish,
 libcrux_sha2.hacl.sha512_init,
 libcrux_sha2.hacl.sha512_update_last,
 libcrux_sha2.hacl.sha512_update_nblocks,
 alloc.vec.Vec.into_boxed_slice,
 alloc.vec.Vec.truncate,
 core.num.U32.wrapping_div,
 core.num.U32.wrapping_rem,
 libcrux_hacl_rs.fstar.uint128.add,
 libcrux_hacl_rs.fstar.uint128.uint64_to_uint128,
 libcrux_hacl_rs.lowstar.ignore.ignore,
 core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in #print axioms hmac_panic
/- Axiom guard:`propext`, `Classical.choice`, `Quot.sound`, and the
   extraction axioms reached through `hmac` (as for `hmac_spec`). No Trusted
   axiom and no gap hypothesis: the `unwrap` fails before any of them is called. -/

end libcrux_hmac

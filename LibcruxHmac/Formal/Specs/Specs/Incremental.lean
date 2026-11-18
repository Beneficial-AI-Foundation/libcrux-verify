import LibcruxHmac.Formal.Proofs.HmacStreamNew
import LibcruxHmac.Formal.Proofs.HmacStreamUpdate
import LibcruxHmac.Formal.Proofs.HmacStreamFinalize

/-!
# Specifications for `crates/algorithms/hmac/src/incremental.rs`

Public items of `incremental.rs` (claim C3) and their statements. Each statement
is declared once, in `LibcruxHmac/Formal/Proofs/`. It is restated here with
`recall`, which fails to build if the declared statement differs.

* `<HmacStream as HmacState>::new` (C3): `new_spec`; `new_sha{256,384,512}_spec`
  (`Proofs/HmacStreamNew.lean`);
* `<HmacStream as HmacState>::update` (C3): `update_spec`, `update_full`,
  `update_err`; `update_sha{256,384,512}_{spec,full,err}`
  (`Proofs/HmacStreamUpdate.lean`);
* `<HmacStream as HmacState>::finalize` (C3): `finalize_spec`;
  `finalize_sha{256,384,512}_spec` (`Proofs/HmacStreamFinalize.lean`).

The trait methods are generic in the digest. Each is stated once for any digest
that meets a `DigestContract` (`Defs/Stream.lean`). It is then instantiated at the
public aliases `HmacSha256`, `HmacSha384` and `HmacSha512`, with the instance
terms the extraction itself uses (`incremental.hmac_sha2_*_slices`), and with
the A2 contract axioms `Trusted.sha{256,384,512}Contract`
(`Trusted/Sha2Stream.lean`). The alias statements are proved from the generic
ones; this also shows that the generic hypotheses hold for the aliases.

Definitions, not separate statements: the struct `HmacStream` and the three
type aliases.

Not stated (agreed exclusion, boundary A3): `incremental::hmac_slices`, which
Aeneas extracts as an axiom (its `&[&[u8]]` argument is a nested borrow), and
the wrappers `hmac_sha2_{256,384,512}_slices`, which call it.

Total-length limit. The digest accepts at most `maxLen` bytes in total
(`2 ^ 61 - 1` for SHA-256, `2 ^ 64 - 1` for SHA-384/512, the `BLOCK`-byte inner
pad included). The three `update` statements cover every input: within the limit
the data is appended (`update_spec`); an input that would pass the limit is
dropped silently, and `update` still returns `Ok(())` with the state unchanged
(`update_full`, from the A2 law `DigestContract.update_full`); an input over
`u32::MAX` bytes is rejected with `Err` (`update_err`). `finalize` is stated
against the accepted transcript, the bytes actually absorbed. So C3 holds for
concatenations within the limit: the tag is `Spec.hmacSha* key (d₁ ‖ … ‖ dₙ)`,
the mathematical HMAC, which is the tag of the C1 function `hmac_sha2_*` when the
key and the concatenation are below `2 ^ 32` bytes. Past the limit, the tag is
the HMAC of the accepted transcript.

The two `example`s at the end check that the alias statements compose: `new`,
two `update`s and `finalize` give the HMAC of the concatenated data; and an
`update` past the limit is dropped, so `finalize` gives the HMAC of the accepted
transcript.

Each `#print axioms` below is checked by `#guard_msgs` against the exact list of
axioms that Lean prints. All statements are proved, so no list contains `sorryAx`.
The comment after each guard explains where its entries come from. No statement
here uses a translation patch or a core/alloc gap.
-/

open Aeneas Aeneas.Std Result WP
open libcrux_hmac.libcrux_traits.digest (InitializeDigestState)
open libcrux_hmac.libcrux_traits.digest.arrayref (DigestIncremental)
open libcrux_hmac.Spec (DigestContract StreamRep HmacSha256 HmacSha384 HmacSha512
  sha256Digest sha256Init sha384Digest sha384Init sha512Digest sha512Init
  sha256StreamMax sha512StreamMax)

namespace libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState

/-! ## `<HmacStream as HmacState>::new` (C3) -/

recall new_spec {D S : Type} {OUTLEN : Usize} (BLOCK : Usize)
    (inst : DigestIncremental D S OUTLEN) (init : InitializeDigestState S)
    {H : List U8 → List U8} {maxLen : Nat} (C : DigestContract inst init H maxLen)
    (hOB : OUTLEN.val ≤ BLOCK.val) (hB : BLOCK.val ≤ U32.max) (hmax : 2 ^ 33 ≤ maxLen)
    (key : Slice U8) :
    new BLOCK inst init key ⦃ r =>
      (key.length ≤ U32.max → ∃ st, r = .Ok st ∧ StreamRep C st key.val []) ∧
      (U32.max < key.length → r = .Err .InvalidInputLength) ⦄

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.new_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in
#print axioms new_spec
/- Axiom guard: `propext`, `Classical.choice`, `Quot.sound`, and
   `libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt` (an extraction
   axiom, A2; only an instance argument of `expect`, never called). -/

recall new_sha256_spec (key : Slice U8) :
    new 64#usize sha256Digest sha256Init key ⦃ r =>
      (key.length ≤ U32.max →
        ∃ st, r = .Ok st ∧ StreamRep Trusted.sha256Contract st key.val []) ∧
      (U32.max < key.length → r = .Err .InvalidInputLength) ⦄

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.new_sha256_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha256Contract,
 libcrux_sha2.impl_hacl.Sha256,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha25632.finish,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha256.reset,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha256.update,
 libcrux_sha2.impl_hacl.Sha256.Insts.Libcrux_traitsDigestInitializeDigestState.new,
 libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in
#print axioms new_sha256_spec
/- Axiom guard: `propext`, `Classical.choice`, `Quot.sound`;
   Trusted (A2): `Trusted.sha256Contract`; extraction axioms (A2, types only):
   `libcrux_sha2.impl_hacl.Sha256`, its `InitializeDigestState` `new`, the
   `Sha256Hash` digest-trait `update`, `reset` and `finish`, and
   `libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt`. -/

recall new_sha384_spec (key : Slice U8) :
    new 128#usize sha384Digest sha384Init key ⦃ r =>
      (key.length ≤ U32.max →
        ∃ st, r = .Ok st ∧ StreamRep Trusted.sha384Contract st key.val []) ∧
      (U32.max < key.length → r = .Err .InvalidInputLength) ⦄

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.new_sha384_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha384Contract,
 libcrux_sha2.impl_hacl.Sha384,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha38448.finish,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha384.reset,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha384.update,
 libcrux_sha2.impl_hacl.Sha384.Insts.Libcrux_traitsDigestInitializeDigestState.new,
 libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in
#print axioms new_sha384_spec
/- Axiom guard: `propext`, `Classical.choice`, `Quot.sound`;
   Trusted (A2): `Trusted.sha384Contract`; extraction axioms (A2, types only):
   `libcrux_sha2.impl_hacl.Sha384`, its `InitializeDigestState` `new`, the
   `Sha384Hash` digest-trait `update`, `reset` and `finish`, and
   `libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt`. -/

recall new_sha512_spec (key : Slice U8) :
    new 128#usize sha512Digest sha512Init key ⦃ r =>
      (key.length ≤ U32.max →
        ∃ st, r = .Ok st ∧ StreamRep Trusted.sha512Contract st key.val []) ∧
      (U32.max < key.length → r = .Err .InvalidInputLength) ⦄

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.new_sha512_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha512Contract,
 libcrux_sha2.impl_hacl.Sha512,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha51264.finish,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha512.reset,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha512.update,
 libcrux_sha2.impl_hacl.Sha512.Insts.Libcrux_traitsDigestInitializeDigestState.new,
 libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in
#print axioms new_sha512_spec
/- Axiom guard: `propext`, `Classical.choice`, `Quot.sound`;
   Trusted (A2): `Trusted.sha512Contract`; extraction axioms (A2, types only):
   `libcrux_sha2.impl_hacl.Sha512`, its `InitializeDigestState` `new`, the
   `Sha512Hash` digest-trait `update`, `reset` and `finish`, and
   `libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt`. -/

/-! ## `<HmacStream as HmacState>::update` (C3) -/

recall update_spec {D S : Type} {OUTLEN BLOCK : Usize}
    (inst : DigestIncremental D S OUTLEN) (init : InitializeDigestState S)
    {H : List U8 → List U8} {maxLen : Nat} (C : DigestContract inst init H maxLen)
    (st : incremental.HmacStream D S OUTLEN BLOCK) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep C st key msg) (hdata : data.length ≤ U32.max)
    (hlen : BLOCK.val + msg.length + data.length ≤ maxLen) :
    update inst init st data ⦃ r st' =>
      r = .Ok () ∧ StreamRep C st' key (msg ++ data.val) ⦄

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.update_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms update_spec
/- Axiom guard: `propext`, `Classical.choice`, `Quot.sound`. -/

recall update_err {D S : Type} {OUTLEN BLOCK : Usize}
    (inst : DigestIncremental D S OUTLEN) (init : InitializeDigestState S)
    {H : List U8 → List U8} {maxLen : Nat} (C : DigestContract inst init H maxLen)
    (st : incremental.HmacStream D S OUTLEN BLOCK) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep C st key msg) (hdata : U32.max < data.length) :
    update inst init st data = ok (.Err .InvalidInputLength, st)

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.update_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms update_err
/- Axiom guard: `propext`, `Classical.choice`, `Quot.sound`. -/

recall update_full {D S : Type} {OUTLEN BLOCK : Usize}
    (inst : DigestIncremental D S OUTLEN) (init : InitializeDigestState S)
    {H : List U8 → List U8} {maxLen : Nat} (C : DigestContract inst init H maxLen)
    (st : incremental.HmacStream D S OUTLEN BLOCK) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep C st key msg) (hdata : data.length ≤ U32.max)
    (hbound : BLOCK.val + msg.length ≤ maxLen)
    (hover : maxLen < BLOCK.val + msg.length + data.length) :
    update inst init st data = ok (.Ok (), st)

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.update_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms update_full
/- Axiom guard: `propext`, `Classical.choice`, `Quot.sound`. -/

recall update_sha256_spec (st : HmacSha256) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha256Contract st key msg) (hdata : data.length ≤ U32.max)
    (hlen : 64 + msg.length + data.length ≤ sha256StreamMax) :
    update sha256Digest sha256Init st data ⦃ r st' =>
      r = .Ok () ∧ StreamRep Trusted.sha256Contract st' key (msg ++ data.val) ⦄

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.update_sha256_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha256Contract,
 libcrux_sha2.impl_hacl.Sha256,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha25632.finish,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha256.reset,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha256.update,
 libcrux_sha2.impl_hacl.Sha256.Insts.Libcrux_traitsDigestInitializeDigestState.new] -/
#guard_msgs in
#print axioms update_sha256_spec
/- Axiom guard: `propext`, `Classical.choice`, `Quot.sound`;
   Trusted (A2): `Trusted.sha256Contract`; extraction axioms (A2, types only):
   `libcrux_sha2.impl_hacl.Sha256` and its digest-trait operations. -/

recall update_sha256_err (st : HmacSha256) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha256Contract st key msg) (hdata : U32.max < data.length) :
    update sha256Digest sha256Init st data = ok (.Err .InvalidInputLength, st)

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.update_sha256_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha256Contract,
 libcrux_sha2.impl_hacl.Sha256,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha25632.finish,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha256.reset,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha256.update,
 libcrux_sha2.impl_hacl.Sha256.Insts.Libcrux_traitsDigestInitializeDigestState.new] -/
#guard_msgs in
#print axioms update_sha256_err
/- Axiom guard: as for `update_sha256_spec`. -/

recall update_sha256_full (st : HmacSha256) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha256Contract st key msg) (hdata : data.length ≤ U32.max)
    (hbound : 64 + msg.length ≤ sha256StreamMax)
    (hover : sha256StreamMax < 64 + msg.length + data.length) :
    update sha256Digest sha256Init st data = ok (.Ok (), st)

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.update_sha256_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha256Contract,
 libcrux_sha2.impl_hacl.Sha256,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha25632.finish,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha256.reset,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha256.update,
 libcrux_sha2.impl_hacl.Sha256.Insts.Libcrux_traitsDigestInitializeDigestState.new] -/
#guard_msgs in
#print axioms update_sha256_full
/- Axiom guard: as for `update_sha256_spec`. -/

recall update_sha384_spec (st : HmacSha384) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha384Contract st key msg) (hdata : data.length ≤ U32.max)
    (hlen : 128 + msg.length + data.length ≤ sha512StreamMax) :
    update sha384Digest sha384Init st data ⦃ r st' =>
      r = .Ok () ∧ StreamRep Trusted.sha384Contract st' key (msg ++ data.val) ⦄

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.update_sha384_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha384Contract,
 libcrux_sha2.impl_hacl.Sha384,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha38448.finish,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha384.reset,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha384.update,
 libcrux_sha2.impl_hacl.Sha384.Insts.Libcrux_traitsDigestInitializeDigestState.new] -/
#guard_msgs in
#print axioms update_sha384_spec
/- Axiom guard: `propext`, `Classical.choice`, `Quot.sound`;
   Trusted (A2): `Trusted.sha384Contract`; extraction axioms (A2, types only):
   `libcrux_sha2.impl_hacl.Sha384` and its digest-trait operations. -/

recall update_sha384_err (st : HmacSha384) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha384Contract st key msg) (hdata : U32.max < data.length) :
    update sha384Digest sha384Init st data = ok (.Err .InvalidInputLength, st)

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.update_sha384_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha384Contract,
 libcrux_sha2.impl_hacl.Sha384,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha38448.finish,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha384.reset,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha384.update,
 libcrux_sha2.impl_hacl.Sha384.Insts.Libcrux_traitsDigestInitializeDigestState.new] -/
#guard_msgs in
#print axioms update_sha384_err
/- Axiom guard: as for `update_sha384_spec`. -/

recall update_sha384_full (st : HmacSha384) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha384Contract st key msg) (hdata : data.length ≤ U32.max)
    (hbound : 128 + msg.length ≤ sha512StreamMax)
    (hover : sha512StreamMax < 128 + msg.length + data.length) :
    update sha384Digest sha384Init st data = ok (.Ok (), st)

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.update_sha384_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha384Contract,
 libcrux_sha2.impl_hacl.Sha384,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha38448.finish,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha384.reset,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha384.update,
 libcrux_sha2.impl_hacl.Sha384.Insts.Libcrux_traitsDigestInitializeDigestState.new] -/
#guard_msgs in
#print axioms update_sha384_full
/- Axiom guard: as for `update_sha384_spec`. -/

recall update_sha512_spec (st : HmacSha512) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha512Contract st key msg) (hdata : data.length ≤ U32.max)
    (hlen : 128 + msg.length + data.length ≤ sha512StreamMax) :
    update sha512Digest sha512Init st data ⦃ r st' =>
      r = .Ok () ∧ StreamRep Trusted.sha512Contract st' key (msg ++ data.val) ⦄

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.update_sha512_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha512Contract,
 libcrux_sha2.impl_hacl.Sha512,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha51264.finish,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha512.reset,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha512.update,
 libcrux_sha2.impl_hacl.Sha512.Insts.Libcrux_traitsDigestInitializeDigestState.new] -/
#guard_msgs in
#print axioms update_sha512_spec
/- Axiom guard: `propext`, `Classical.choice`, `Quot.sound`;
   Trusted (A2): `Trusted.sha512Contract`; extraction axioms (A2, types only):
   `libcrux_sha2.impl_hacl.Sha512` and its digest-trait operations. -/

recall update_sha512_err (st : HmacSha512) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha512Contract st key msg) (hdata : U32.max < data.length) :
    update sha512Digest sha512Init st data = ok (.Err .InvalidInputLength, st)

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.update_sha512_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha512Contract,
 libcrux_sha2.impl_hacl.Sha512,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha51264.finish,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha512.reset,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha512.update,
 libcrux_sha2.impl_hacl.Sha512.Insts.Libcrux_traitsDigestInitializeDigestState.new] -/
#guard_msgs in
#print axioms update_sha512_err
/- Axiom guard: as for `update_sha512_spec`. -/

recall update_sha512_full (st : HmacSha512) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha512Contract st key msg) (hdata : data.length ≤ U32.max)
    (hbound : 128 + msg.length ≤ sha512StreamMax)
    (hover : sha512StreamMax < 128 + msg.length + data.length) :
    update sha512Digest sha512Init st data = ok (.Ok (), st)

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.update_sha512_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha512Contract,
 libcrux_sha2.impl_hacl.Sha512,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha51264.finish,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha512.reset,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha512.update,
 libcrux_sha2.impl_hacl.Sha512.Insts.Libcrux_traitsDigestInitializeDigestState.new] -/
#guard_msgs in
#print axioms update_sha512_full
/- Axiom guard: as for `update_sha512_spec`. -/

/-! ## `<HmacStream as HmacState>::finalize` (C3) -/

recall finalize_spec {D S : Type} {OUTLEN BLOCK : Usize}
    (inst : DigestIncremental D S OUTLEN) (init : InitializeDigestState S)
    {H : List U8 → List U8} {maxLen : Nat} (C : DigestContract inst init H maxLen)
    (hOB : OUTLEN.val ≤ BLOCK.val) (hB : BLOCK.val ≤ U32.max) (hmax : 2 ^ 33 ≤ maxLen)
    (st : incremental.HmacStream D S OUTLEN BLOCK) (key msg : List U8)
    (dst : Array U8 OUTLEN) (hrep : StreamRep C st key msg) :
    finalize inst init st dst ⦃ tag => tag.val = Spec.hmac H BLOCK.val key msg ⦄

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.finalize_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in
#print axioms finalize_spec
/- Axiom guard: `propext`, `Classical.choice`, `Quot.sound`, and
   `libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt` (never called). -/

recall finalize_sha256_spec (st : HmacSha256) (key msg : List U8) (dst : Array U8 32#usize)
    (hrep : StreamRep Trusted.sha256Contract st key msg) :
    finalize sha256Digest sha256Init st dst ⦃ tag => tag.val = Spec.hmacSha256 key msg ⦄

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.finalize_sha256_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha256Contract,
 libcrux_sha2.impl_hacl.Sha256,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha25632.finish,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha256.reset,
 libcrux_sha2.impl_digest_trait.Sha256Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha256.update,
 libcrux_sha2.impl_hacl.Sha256.Insts.Libcrux_traitsDigestInitializeDigestState.new,
 libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in
#print axioms finalize_sha256_spec
/- Axiom guard: as for `new_sha256_spec`. -/

recall finalize_sha384_spec (st : HmacSha384) (key msg : List U8) (dst : Array U8 48#usize)
    (hrep : StreamRep Trusted.sha384Contract st key msg) :
    finalize sha384Digest sha384Init st dst ⦃ tag => tag.val = Spec.hmacSha384 key msg ⦄

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.finalize_sha384_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha384Contract,
 libcrux_sha2.impl_hacl.Sha384,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha38448.finish,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha384.reset,
 libcrux_sha2.impl_digest_trait.Sha384Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha384.update,
 libcrux_sha2.impl_hacl.Sha384.Insts.Libcrux_traitsDigestInitializeDigestState.new,
 libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in
#print axioms finalize_sha384_spec
/- Axiom guard: as for `new_sha384_spec`. -/

recall finalize_sha512_spec (st : HmacSha512) (key msg : List U8) (dst : Array U8 64#usize)
    (hrep : StreamRep Trusted.sha512Contract st key msg) :
    finalize sha512Digest sha512Init st dst ⦃ tag => tag.val = Spec.hmacSha512 key msg ⦄

/-- info: 'libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.finalize_sha512_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Trusted.sha512Contract,
 libcrux_sha2.impl_hacl.Sha512,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha51264.finish,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha512.reset,
 libcrux_sha2.impl_digest_trait.Sha512Hash.Insts.Libcrux_traitsDigestDigestIncrementalBaseSha512.update,
 libcrux_sha2.impl_hacl.Sha512.Insts.Libcrux_traitsDigestInitializeDigestState.new,
 libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt] -/
#guard_msgs in
#print axioms finalize_sha512_spec
/- Axiom guard: as for `new_sha512_spec`. -/

/-! ## The statements compose into C3 -/

/-- At `HmacSha256`, within the total limit: `new`, then `update` with `d₁` and
`d₂`, then `finalize` writes HMAC-SHA-256 of `d₁ ‖ d₂`. With a key and data below
`2 ^ 32` bytes this is the tag of the C1 function `hmac_sha2_256`. -/
example (key d₁ d₂ : Slice U8) (dst : Array U8 32#usize)
    (hk : key.length ≤ U32.max) (h₁ : d₁.length ≤ U32.max) (h₂ : d₂.length ≤ U32.max)
    (hlen : 64 + d₁.length + d₂.length ≤ sha256StreamMax) :
    (do
      let r ← new 64#usize sha256Digest sha256Init key
      match r with
      | .Ok st =>
        let (_, st) ← update sha256Digest sha256Init st d₁
        let (_, st) ← update sha256Digest sha256Init st d₂
        finalize sha256Digest sha256Init st dst
      | .Err _ => fail .panic) ⦃ tag =>
        tag.val = Spec.hmacSha256 key.val (d₁.val ++ d₂.val) ⦄ := by
  step as ⟨r, hr, _hr⟩
  obtain ⟨st, rfl, hst⟩ := hr hk
  simp only
  step as ⟨r₁, st₁, _e₁, h₁'⟩
  step as ⟨r₂, st₂, _e₂, h₂'⟩
  step as ⟨tag, htag⟩
  simpa using htag

/-- At `HmacSha256`, past the total limit: from a state keyed with `key` after the
accepted data `msg`, an `update` whose data would pass the limit is dropped, and
`finalize` writes HMAC-SHA-256 of the accepted transcript `msg`. -/
example (st : HmacSha256) (key msg : List U8) (d : Slice U8) (dst : Array U8 32#usize)
    (hrep : StreamRep Trusted.sha256Contract st key msg) (hd : d.length ≤ U32.max)
    (hbound : 64 + msg.length ≤ sha256StreamMax)
    (hover : sha256StreamMax < 64 + msg.length + d.length) :
    (do
      let (_, st) ← update sha256Digest sha256Init st d
      finalize sha256Digest sha256Init st dst) ⦃ tag =>
        tag.val = Spec.hmacSha256 key msg ⦄ := by
  simp only [update_sha256_full st key msg d hrep hd hbound hover, bind_ok]
  exact finalize_sha256_spec st key msg dst hrep

end libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState

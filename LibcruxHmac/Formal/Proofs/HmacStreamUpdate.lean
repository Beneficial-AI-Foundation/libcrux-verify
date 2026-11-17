import LibcruxHmac.Formal.Trusted.Sha2Stream

/-!
# `<libcrux_hmac::incremental::HmacStream as HmacState>::update`
(crates/algorithms/hmac/src/incremental.rs lines 68–70)

Extracted as `libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.update`
(`LibcruxHmac/Extraction/LibcruxHmac.lean` lines 2017–2041), generic in the digest.
Stated once generically (`update_spec`, `update_err`), then at `HmacSha256`,
`HmacSha384` and `HmacSha512` with the A2 contract axioms; the alias
corollaries are proved from the generic statements.

natural language description:
    `update(data)` feeds `data` to the inner digest state and maps the digest's
    error to `Error::InvalidInputLength`.

natural language specs:
    Let `st` be keyed with `key` after the data `msg` (`StreamRep C st key msg`).
    * If `data.len() ≤ u32::MAX` and the inner digest stays within its total
      limit (`BLOCK + msg.len() + data.len() ≤ maxLen`; `BLOCK` bytes are the
      inner pad), `update` returns `Ok(())` and the new state is keyed with `key`
      after `msg ‖ data`.
    * If `data.len() > u32::MAX`, `update` returns `Err(InvalidInputLength)` and
      the state is unchanged.
    It does not panic in these cases. Not covered: an input within `u32::MAX`
    that passes the digest's total limit (`2 ^ 61 - 1` bytes for SHA-256,
    `2 ^ 64 - 1` for SHA-384/512). There libcrux-sha2 drops the input and still
    returns `Ok(())` (A2; `impl_hacl.rs` line 112 discards HACL's error code), so
    the later tag is not the HMAC of all the data.
    Conditional on: A1; for the aliases, A2 through the axioms
    `Trusted.sha256Contract`, `Trusted.sha384Contract`, `Trusted.sha512Contract`.
-/

open Aeneas Aeneas.Std Result WP
open libcrux_hmac.libcrux_traits.digest (InitializeDigestState)
open libcrux_hmac.libcrux_traits.digest.arrayref (DigestIncremental)
open libcrux_hmac.Spec (DigestContract StreamRep HmacSha256 HmacSha384 HmacSha512
  sha256Digest sha256Init sha384Digest sha384Init sha512Digest sha512Init
  sha256StreamMax sha512StreamMax)

namespace libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState

/-- C3, `update`, for any digest that meets its contract: within the limits,
`update` returns `Ok(())` and appends `data` to the absorbed data. -/
theorem update_spec {D S : Type} {OUTLEN BLOCK : Usize}
    (inst : DigestIncremental D S OUTLEN) (init : InitializeDigestState S)
    {H : List U8 → List U8} {maxLen : Nat} (C : DigestContract inst init H maxLen)
    (st : incremental.HmacStream D S OUTLEN BLOCK) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep C st key msg) (hdata : data.length ≤ U32.max)
    (hlen : BLOCK.val + msg.length + data.length ≤ maxLen) :
    update inst init st data ⦃ r st' =>
      r = .Ok () ∧ StreamRep C st' key (msg ++ data.val) ⦄ := by
  sorry

/-- C3, `update`, for any digest that meets its contract: with more than
`u32::MAX` bytes, `update` returns `Err(InvalidInputLength)` and leaves the
state unchanged. -/
theorem update_err {D S : Type} {OUTLEN BLOCK : Usize}
    (inst : DigestIncremental D S OUTLEN) (init : InitializeDigestState S)
    {H : List U8 → List U8} {maxLen : Nat} (C : DigestContract inst init H maxLen)
    (st : incremental.HmacStream D S OUTLEN BLOCK) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep C st key msg) (hdata : U32.max < data.length) :
    update inst init st data = ok (.Err .InvalidInputLength, st) := by
  sorry

/-- C3, `update` at `HmacSha256`. -/
@[step]
theorem update_sha256_spec (st : HmacSha256) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha256Contract st key msg) (hdata : data.length ≤ U32.max)
    (hlen : 64 + msg.length + data.length ≤ sha256StreamMax) :
    update sha256Digest sha256Init st data ⦃ r st' =>
      r = .Ok () ∧ StreamRep Trusted.sha256Contract st' key (msg ++ data.val) ⦄ :=
  update_spec sha256Digest sha256Init Trusted.sha256Contract st key msg data hrep hdata
    (by simpa using hlen)

/-- C3, `update` at `HmacSha256`, error case. -/
theorem update_sha256_err (st : HmacSha256) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha256Contract st key msg) (hdata : U32.max < data.length) :
    update sha256Digest sha256Init st data = ok (.Err .InvalidInputLength, st) :=
  update_err sha256Digest sha256Init Trusted.sha256Contract st key msg data hrep hdata

/-- C3, `update` at `HmacSha384`. -/
@[step]
theorem update_sha384_spec (st : HmacSha384) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha384Contract st key msg) (hdata : data.length ≤ U32.max)
    (hlen : 128 + msg.length + data.length ≤ sha512StreamMax) :
    update sha384Digest sha384Init st data ⦃ r st' =>
      r = .Ok () ∧ StreamRep Trusted.sha384Contract st' key (msg ++ data.val) ⦄ :=
  update_spec sha384Digest sha384Init Trusted.sha384Contract st key msg data hrep hdata
    (by simpa using hlen)

/-- C3, `update` at `HmacSha384`, error case. -/
theorem update_sha384_err (st : HmacSha384) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha384Contract st key msg) (hdata : U32.max < data.length) :
    update sha384Digest sha384Init st data = ok (.Err .InvalidInputLength, st) :=
  update_err sha384Digest sha384Init Trusted.sha384Contract st key msg data hrep hdata

/-- C3, `update` at `HmacSha512`. -/
@[step]
theorem update_sha512_spec (st : HmacSha512) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha512Contract st key msg) (hdata : data.length ≤ U32.max)
    (hlen : 128 + msg.length + data.length ≤ sha512StreamMax) :
    update sha512Digest sha512Init st data ⦃ r st' =>
      r = .Ok () ∧ StreamRep Trusted.sha512Contract st' key (msg ++ data.val) ⦄ :=
  update_spec sha512Digest sha512Init Trusted.sha512Contract st key msg data hrep hdata
    (by simpa using hlen)

/-- C3, `update` at `HmacSha512`, error case. -/
theorem update_sha512_err (st : HmacSha512) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha512Contract st key msg) (hdata : U32.max < data.length) :
    update sha512Digest sha512Init st data = ok (.Err .InvalidInputLength, st) :=
  update_err sha512Digest sha512Init Trusted.sha512Contract st key msg data hrep hdata

end libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState

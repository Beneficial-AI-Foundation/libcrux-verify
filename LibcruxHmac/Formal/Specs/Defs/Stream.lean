import LibcruxHmac.Formal.Specs.Defs.Hmac

/-!
# Streaming HMAC: digest contract, state invariant, and the three aliases

`incremental::HmacStream<OUTLEN, BLOCK, D>` (incremental.rs lines 10–18) holds
an incremental digest state `inner` of the digest `D` and the block `opad`. The
state type of libcrux-sha2 is opaque in the extraction (boundary A2): it is an
`axiom ... : Type`. Its operations are axioms too.

* `DigestContract` is what an incremental digest is assumed to do. It names a
  relation `Represents s m`, "the state `s` has absorbed exactly the bytes `m`",
  and gives one law for each operation the HMAC code calls. The laws restate
  the Rust source of libcrux-sha2 0.0.8 (`impl_digest_trait.rs` lines 43, 54–61,
  71–72; `hacl.rs` lines 667 and 974), restricted to what HMAC uses.
* `StreamRep` is the invariant of an `HmacStream` keyed with `key` that has
  absorbed `msg`.
* `HmacSha256`, `HmacSha384`, `HmacSha512` and their instance arguments are the
  Rust type aliases of incremental.rs lines 85–92. They are the instantiations
  the extraction itself uses in `incremental.hmac_sha2_*_slices`
  (`LibcruxHmac/Extraction/LibcruxHmac.lean` lines 2192–2224).

The contracts for the three SHA-2 states are the axioms of
`LibcruxHmac/Formal/Trusted/Sha2Stream.lean`.
-/

open Aeneas Aeneas.Std Result WP
open libcrux_hmac.libcrux_traits.digest

namespace libcrux_hmac.Spec

/-- The contract of an incremental digest `inst` whose fresh states come from
`init`, for the hash function `H`, valid while at most `maxLen` bytes in total
are absorbed.

`Represents s m` means: `s` is the state reached from a fresh state by updates
whose concatenated inputs are `m`. The laws are:

* `new`: `init.new` returns a state that has absorbed nothing;
* `update_ok`: an update with at most `u32::MAX` bytes, within the total limit,
  returns `Ok(())` and appends its input;
* `update_err`: an update with more than `u32::MAX` bytes returns
  `Err(InvalidPayloadLength)` and leaves the state unchanged
  (`impl_digest_trait.rs` lines 56–58);
* `finish`: the output is `H m`, whatever the destination array held. -/
structure DigestContract {D S : Type} {N : Usize}
    (inst : arrayref.DigestIncremental D S N) (init : InitializeDigestState S)
    (H : List Byte → List Byte) (maxLen : Nat) where
  /-- `s` has absorbed exactly the bytes `m`. -/
  Represents : S → List Byte → Prop
  new : init.new ⦃ s => Represents s [] ⦄
  update_ok : ∀ (s : S) (m : List Byte) (c : Slice Byte),
    Represents s m → c.length ≤ U32.max → m.length + c.length ≤ maxLen →
    inst.DigestIncrementalBaseInst.update s c ⦃ r s' =>
      r = .Ok () ∧ Represents s' (m ++ c.val) ⦄
  update_err : ∀ (s : S) (m : List Byte) (c : Slice Byte),
    Represents s m → U32.max < c.length →
    inst.DigestIncrementalBaseInst.update s c = ok (.Err .InvalidPayloadLength, s)
  finish : ∀ (s : S) (m : List Byte) (dst : Array Byte N),
    Represents s m → inst.finish s dst ⦃ d => d.val = H m ⦄

/-- The invariant of a streaming HMAC state `st` for the key `key` after the data
`msg`: `st.opad` is `K₀ ⊕ opad`, and `st.inner` has absorbed `(K₀ ⊕ ipad) ‖ msg`
(incremental.rs lines 16–17 and 35–62). -/
def StreamRep {D S : Type} {OUTLEN BLOCK : Usize}
    {inst : arrayref.DigestIncremental D S OUTLEN} {init : InitializeDigestState S}
    {H : List Byte → List Byte} {maxLen : Nat}
    (C : DigestContract inst init H maxLen)
    (st : incremental.HmacStream D S OUTLEN BLOCK) (key msg : List Byte) : Prop :=
  st.opad.val = outerKeyBlock H BLOCK.val key ∧
    C.Represents st.inner (innerKeyBlock H BLOCK.val key ++ msg)

/-! ## The total-length limits of the libcrux-sha2 streaming states -/

/-- The SHA-256 streaming state accepts at most `2 ^ 61 - 1` bytes in total
(`hacl.rs` line 667: `2305843009213693951u64`). Above it, HACL returns
`MaximumLengthExceeded`, and `impl_hacl.rs` line 112 discards that error code. -/
def sha256StreamMax : Nat := 2 ^ 61 - 1

/-- The SHA-384 and SHA-512 streaming states accept at most `2 ^ 64 - 1` bytes in
total (`hacl.rs` line 974: `18446744073709551615u64`). -/
def sha512StreamMax : Nat := 2 ^ 64 - 1

/-! ## The aliases `HmacSha256`, `HmacSha384`, `HmacSha512` -/

noncomputable section

open libcrux_sha2.impl_digest_trait libcrux_sha2.impl_hacl

/-- The `DigestIncremental<32>` instance of `libcrux_sha2::Sha256Hash`. -/
abbrev sha256Digest := Sha256Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha25632

/-- The `InitializeDigestState` instance of `libcrux_sha2::impl_hacl::Sha256`. -/
abbrev sha256Init := Sha256.Insts.Libcrux_traitsDigestInitializeDigestState

/-- `HmacSha256 = HmacStream<32, 64, Sha256Hash>` (incremental.rs line 86). -/
abbrev HmacSha256 := incremental.HmacStream Sha256Hash Sha256 32#usize 64#usize

/-- The `DigestIncremental<48>` instance of `libcrux_sha2::Sha384Hash`. -/
abbrev sha384Digest := Sha384Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha38448

/-- The `InitializeDigestState` instance of `libcrux_sha2::impl_hacl::Sha384`. -/
abbrev sha384Init := Sha384.Insts.Libcrux_traitsDigestInitializeDigestState

/-- `HmacSha384 = HmacStream<48, 128, Sha384Hash>` (incremental.rs line 89). -/
abbrev HmacSha384 := incremental.HmacStream Sha384Hash Sha384 48#usize 128#usize

/-- The `DigestIncremental<64>` instance of `libcrux_sha2::Sha512Hash`. -/
abbrev sha512Digest := Sha512Hash.Insts.Libcrux_traitsDigestArrayrefDigestIncrementalSha51264

/-- The `InitializeDigestState` instance of `libcrux_sha2::impl_hacl::Sha512`. -/
abbrev sha512Init := Sha512.Insts.Libcrux_traitsDigestInitializeDigestState

/-- `HmacSha512 = HmacStream<64, 128, Sha512Hash>` (incremental.rs line 92). -/
abbrev HmacSha512 := incremental.HmacStream Sha512Hash Sha512 64#usize 128#usize

end

end libcrux_hmac.Spec

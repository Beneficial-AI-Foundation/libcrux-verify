import LibcruxHmac.Formal.Proofs.Lemmas.Sha2Pure

/-!
# Pure facts for the HMAC proofs

Facts about the reference definitions (`Specs/Defs/Sha2.lean`, `Specs/Defs/Hmac.lean`) that
the proofs of `hacl::hmac::compute_sha2_{256,384,512}` use: the lengths of the digests,
the pad bytes as machine integers, and the split of a hash into the blocks that HACL
processes one call at a time.
-/

open Aeneas Aeneas.Std

namespace libcrux_hmac.Spec

theorem byte_zero : byte 0 = 0#u8 := by decide
theorem byte_ipad : byte 0x36 = 54#u8 := by decide
theorem byte_opad : byte 0x5c = 92#u8 := by decide

theorem u8_xor_comm (a b : U8) : a ^^^ b = b ^^^ a := by
  apply UScalar.eq_of_val_eq
  simp [Nat.xor_comm]

/-- XOR of a constant byte string with a key block, in the order the Rust code uses
(`ipad[i] ^= key_block[i]`), against the order of `innerKeyBlock` / `outerKeyBlock`. -/
theorem zipWith_xor_replicate (c : U8) (l : List U8) :
    List.zipWith (· ^^^ ·) (List.replicate l.length c) l = l.map (· ^^^ c) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.replicate_succ, ih, u8_xor_comm]

/-! ## Lengths of the digests -/

theorem Sha2Core.hash_length (p : Sha2Core) (IV : List (BitVec p.w)) (outLen : Nat)
    (m : List Byte) (h : outLen ≤ IV.length * (p.w / 8)) :
    (p.hash IV outLen m).length = outLen := by
  rw [Sha2Core.hash, List.length_take, Sha2Core.serialize_length, Sha2Core.compressBlocks_length]
  exact Nat.min_eq_left h

theorem sha256_length (m : List Byte) : (sha256 m).length = 32 :=
  Sha2Core.hash_length sha256Core sha256IV 32 m (by decide)

theorem sha384_length (m : List Byte) : (sha384 m).length = 48 :=
  Sha2Core.hash_length sha512Core sha384IV 48 m (by decide)

theorem sha512_length (m : List Byte) : (sha512 m).length = 64 :=
  Sha2Core.hash_length sha512Core sha512IV 64 m (by decide)

/-! ## Lengths of the HACL states -/

theorem bvs_length {ty : UScalarTy} (s : Slice (UScalar ty)) : (bvs s).length = s.length := by
  simp [bvs, Slice.length]

theorem len_of_iv {ty : UScalarTy} (s : Slice (UScalar ty)) (IV : List (BitVec ty.numBits))
    (h : bvs s = IV) : s.length = IV.length := by
  rw [← bvs_length, h]

theorem len_of_compress256 (s s' : Slice U32) (bs : List Byte)
    (h : bvs s' = sha256Core.compressBlocks (bvs s) bs) : s'.length = s.length := by
  have h1 : s'.length = (sha256Core.compressBlocks (bvs s) bs).length := by
    have := congrArg List.length h
    rwa [bvs_length] at this
  exact (h1.trans (Sha2Core.compressBlocks_length sha256Core (bvs s) bs)).trans (bvs_length s)

theorem len_of_compress512 (s s' : Slice U64) (bs : List Byte)
    (h : bvs s' = sha512Core.compressBlocks (bvs s) bs) : s'.length = s.length := by
  have h1 : s'.length = (sha512Core.compressBlocks (bvs s) bs).length := by
    have := congrArg List.length h
    rwa [bvs_length] at this
  exact (h1.trans (Sha2Core.compressBlocks_length sha512Core (bvs s) bs)).trans (bvs_length s)

theorem serialize256_length (st : Slice U32) (hst : st.length = 8) :
    (sha256Core.serialize (bvs st)).length = 32 := by
  have h := Sha2Core.serialize_length sha256Core (bvs st)
  have h2 : (bvs st).length = 8 := (bvs_length st).trans hst
  exact h.trans (by simp [h2, sha256Core])

theorem serialize512_length (st : Slice U64) (hst : st.length = 8) :
    (sha512Core.serialize (bvs st)).length = 64 := by
  have h := Sha2Core.serialize_length sha512Core (bvs st)
  have h2 : (bvs st).length = 8 := (bvs_length st).trans hst
  exact h.trans (by simp [h2, sha512Core])

/-! ## Splitting a hash into the calls HACL makes -/

namespace Sha2Core

variable (p : Sha2Core)

/-- A hash of `P ++ data` where `P` is a prefix of whole blocks: HACL first applies the
blocks of `P`, then the whole blocks `data[0..fl]`, then pads the tail `data[fl..]`
for a message of length `|P| + |data|`. -/
theorem compressBlocks_pad_split (hB : 0 < p.blockLen) (H : List (BitVec p.w))
    (P data : List Byte) (fl : Nat)
    (hP : p.blockLen ∣ P.length) (hfl : p.blockLen ∣ fl) (hle : fl ≤ data.length) :
    p.compressBlocks (p.compressBlocks (p.compressBlocks H P) (data.take fl))
        (p.padTail (P.length + data.length) (data.drop fl))
      = p.compressBlocks H (p.pad (P ++ data)) := by
  have htake : (data.take fl).length = fl := by simp; omega
  have hdiv : p.blockLen ∣ (data.take fl).length := by rw [htake]; exact hfl
  have h3 : p.padTail (P.length + data.length) (P ++ data)
      = P ++ p.padTail (P.length + data.length) data :=
    padTail_append p _ _ _ hP
  have h4 : p.padTail (P.length + data.length) data
      = data.take fl ++ p.padTail (P.length + data.length) (data.drop fl) := by
    have := padTail_append p (P.length + data.length) (data.take fl) (data.drop fl) hdiv
    rwa [List.take_append_drop] at this
  unfold pad
  rw [List.length_append, h3, h4, compressBlocks_append p hB H P _ hP,
    compressBlocks_append p hB _ _ _ hdiv]

end Sha2Core

end libcrux_hmac.Spec

import LibcruxHmac.Formal.Specs.Defs.Hmac

/-!
# Pure list lemmas for the SHA-2 reference definitions

Facts about `Sha2Core.compressBlocks`, `Sha2Core.padTail` and `Sha2Core.serialize`
(`Specs/Defs/Sha2.lean`), for any `p : Sha2Core`. The proofs of
`hacl::hmac::compute_sha2_{256,384,512}` use them to turn the calls that HACL makes
(one block at a time, then the padded tail) into the single hash of the spec.
-/

open Aeneas Aeneas.Std

namespace libcrux_hmac.Spec.Sha2Core

variable (p : Sha2Core)

/-! ## Lengths -/

theorem round_length (s : List (BitVec p.w)) (k wj : BitVec p.w) :
    (p.round s k wj).length = s.length := by
  unfold round
  split <;> simp_all

theorem foldl_round_length (l : List (BitVec p.w × BitVec p.w)) (s : List (BitVec p.w)) :
    (l.foldl (fun s kw => p.round s kw.1 kw.2) s).length = s.length := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => simp [List.foldl_cons, ih, round_length]

theorem compress_length (H : List (BitVec p.w)) (block : List Byte) :
    (p.compress H block).length = H.length := by
  unfold compress
  simp [foldl_round_length]

theorem compressBlocks_length (H : List (BitVec p.w)) (bs : List Byte) :
    (p.compressBlocks H bs).length = H.length := by
  unfold compressBlocks
  generalize List.range (bs.length / p.blockLen) = l
  induction l generalizing H with
  | nil => rfl
  | cons a l ih => simp [List.foldl_cons, ih, compress_length]

theorem natBE_length (k n : Nat) : (natBE k n).length = k := by
  simp [natBE]

theorem serialize_length (H : List (BitVec p.w)) :
    (p.serialize H).length = H.length * (p.w / 8) := by
  unfold serialize
  induction H with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, natBE_length, ih, List.length_cons]
    ring

/-! ## `compressBlocks` and `padTail` on a prefix of whole blocks -/

theorem compressBlocks_nil (H : List (BitVec p.w)) : p.compressBlocks H [] = H := by
  simp [compressBlocks]

private theorem foldl_range_congr {α : Type _} (F G : α → Nat → α) (n : Nat)
    (h : ∀ i < n, ∀ x, F x i = G x i) (x : α) :
    (List.range n).foldl F x = (List.range n).foldl G x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      ih (fun i hi => h i (by omega))]
    simp [h n (by omega)]

/-- `compressBlocks` can be split after a prefix of whole blocks. -/
theorem compressBlocks_append (hB : 0 < p.blockLen) (H : List (BitVec p.w))
    (a b : List Byte) (h : p.blockLen ∣ a.length) :
    p.compressBlocks H (a ++ b) = p.compressBlocks (p.compressBlocks H a) b := by
  obtain ⟨m, hm⟩ := h
  have hlen : (a ++ b).length / p.blockLen = m + b.length / p.blockLen := by
    rw [List.length_append, hm, Nat.mul_add_div hB]
  unfold compressBlocks
  rw [hlen, List.range_add, List.foldl_append, hm, Nat.mul_div_cancel_left _ hB, List.foldl_map]
  rw [foldl_range_congr
    (fun H i => p.compress H (((a ++ b).drop (i * p.blockLen)).take p.blockLen))
    (fun H i => p.compress H ((a.drop (i * p.blockLen)).take p.blockLen)) m ?_ H]
  · apply foldl_range_congr
    intro i _ x
    rw [List.drop_append, List.drop_eq_nil_of_le
      (show a.length ≤ (m + i) * p.blockLen by rw [hm]; nlinarith), List.nil_append]
    have hmi : (m + i) * p.blockLen = p.blockLen * m + i * p.blockLen := by ring
    rw [hm, hmi, Nat.add_sub_cancel_left]
  · intro i hi x
    have hle : (i + 1) * p.blockLen ≤ a.length := by
      rw [hm]; nlinarith [Nat.mul_le_mul_left p.blockLen hi]
    have hle' : i * p.blockLen ≤ a.length := by nlinarith
    show p.compress x (((a ++ b).drop (i * p.blockLen)).take p.blockLen)
      = p.compress x ((a.drop (i * p.blockLen)).take p.blockLen)
    have hsucc : (i + 1) * p.blockLen = i * p.blockLen + p.blockLen := by ring
    rw [List.drop_append_of_le_length hle', List.take_append_of_le_length]
    rw [List.length_drop]; omega

/-- The padding of a tail does not depend on a prefix of whole blocks. -/
theorem padTail_append (n : Nat) (a t : List Byte) (h : p.blockLen ∣ a.length) :
    p.padTail n (a ++ t) = a ++ p.padTail n t := by
  obtain ⟨k, hk⟩ := h
  unfold padTail
  have : (a ++ t).length + 1 + p.lenFieldLen
      = p.blockLen * k + (t.length + 1 + p.lenFieldLen) := by
    simp only [List.length_append, hk]; omega
  rw [this, Nat.mul_add_mod]
  simp [List.append_assoc]

end libcrux_hmac.Spec.Sha2Core

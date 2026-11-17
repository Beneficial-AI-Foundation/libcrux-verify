import LibcruxHmac.Formal.Proofs.Lemmas.HmacPure

/-!
# Values of wrapping operations without overflow

`compute_sha2_*` computes block counts and total lengths with `wrapping_*` operations.
For the lengths that occur, they do not wrap.
-/

open Aeneas Aeneas.Std

namespace libcrux_hmac.Lemmas

theorem wrapping_add_val {ty : UScalarTy} (a b : UScalar ty) (h : a.val + b.val < 2 ^ ty.numBits) :
    (UScalar.wrapping_add a b).val = a.val + b.val := by
  rw [UScalar.wrapping_add_val_eq, UScalar.size_def]
  exact Nat.mod_eq_of_lt h

theorem wrapping_mul_val {ty : UScalarTy} (a b : UScalar ty) (h : a.val * b.val < 2 ^ ty.numBits) :
    (UScalar.wrapping_mul a b).val = a.val * b.val := by
  rw [UScalar.wrapping_mul_val_eq, UScalar.size_def]
  exact Nat.mod_eq_of_lt h

theorem wrapping_sub_val {ty : UScalarTy} (a b : UScalar ty) (h : b.val ≤ a.val) :
    (UScalar.wrapping_sub a b).val = a.val - b.val := by
  have ha : a.val < 2 ^ ty.numBits := a.bv.isLt
  have hb : b.val < 2 ^ ty.numBits := b.bv.isLt
  show (a.bv - b.bv).toNat = a.val - b.val
  rw [BitVec.toNat_sub]
  show (2 ^ ty.numBits - b.val + a.val) % 2 ^ ty.numBits = a.val - b.val
  have : 2 ^ ty.numBits - b.val + a.val = (a.val - b.val) + 2 ^ ty.numBits := by omega
  rw [this, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem cast_u32_u64 (a : U32) : (UScalar.cast .U64 a).val = a.val := by scalar_tac

theorem cast_u32_u128 (a : U32) : (UScalar.cast .U128 a).val = a.val := by scalar_tac

theorem w32_sub (a b : U32) (h : b.val ≤ a.val) :
    (core.num.U32.wrapping_sub a b).val = a.val - b.val := wrapping_sub_val a b h

theorem w32_mul (a b : U32) (h : a.val * b.val < 4294967296) :
    (core.num.U32.wrapping_mul a b).val = a.val * b.val :=
  wrapping_mul_val a b (by simpa using h)

theorem w64_add (a b : U64) (h : a.val + b.val < 18446744073709551616) :
    (core.num.U64.wrapping_add a b).val = a.val + b.val :=
  wrapping_add_val a b (by simpa using h)

theorem w128_add (a b : U128) (h : a.val + b.val < 340282366920938463463374607431768211456) :
    (core.num.U128.wrapping_add a b).val = a.val + b.val :=
  wrapping_add_val a b (by simpa using h)

end libcrux_hmac.Lemmas

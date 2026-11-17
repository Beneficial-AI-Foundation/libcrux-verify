import LibcruxHmac.Extraction.LibcruxHmac

/-!
# Helper lemmas for `HmacStream::new` (streaming path, claim C3)

The loop of `new` (incremental.rs lines 51–54) XORs the key block with the inner
and outer pad bytes. `new_loop_spec` says it computes
`k_xor_ipad = K₀.map (· ^^^ 0x36)` and `k_xor_opad = K₀.map (· ^^^ 0x5c)`.
-/

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState

/-- The pad loop of `new`: both output blocks are the key block XOR the pad byte,
whatever they held before. -/
theorem new_loop_spec {BLOCK : Usize} (key_block ipad0 opad0 : Array U8 BLOCK) :
    new_loop { start := 0#usize, «end» := BLOCK } key_block ipad0 opad0 ⦃ r =>
      r.1.val = key_block.val.map (· ^^^ 54#u8) ∧
      r.2.val = key_block.val.map (· ^^^ 92#u8) ⦄ := by
  unfold new_loop
  apply loop.spec_decr_nat (fun p => BLOCK.val - p.1.start.val)
    (fun p => p.1.«end» = BLOCK ∧ p.1.start.val ≤ BLOCK.val ∧
      (∀ i, i < p.1.start.val → p.2.1.val[i]! = key_block.val[i]! ^^^ 54#u8) ∧
      (∀ i, i < p.1.start.val → p.2.2.val[i]! = key_block.val[i]! ^^^ 92#u8))
  · rintro ⟨iter, ipad, opad⟩ ⟨hend, hle, hi, ho⟩
    dsimp only at hend hle hi ho
    unfold new_loop.body
    step as ⟨o, iter1, hnext, hend1⟩
    split at hnext
    · rename_i hlt
      obtain ⟨rfl, hs⟩ := hnext
      step as ⟨x, hx⟩
      simp only [lift]
      step as ⟨a, ha⟩
      step as ⟨a1, ha1⟩
      subst ha ha1 hx
      have hlenI : iter.start.val < ipad.val.length := by have := ipad.property; scalar_tac
      have hlenO : iter.start.val < opad.val.length := by have := opad.property; scalar_tac
      refine ⟨by rw [hend1, hend], by scalar_tac, ?_, ?_, by scalar_tac⟩
      · intro i hi'
        by_cases h : i = iter.start.val
        · subst h; simp_lists
        · have hb1 : i < ipad.val.length := by have := ipad.property; scalar_tac
          have hb2 : i < key_block.val.length := by have := key_block.property; scalar_tac
          have h' := hi i (by omega)
          simp_lists
          simpa [List.getElem?_eq_getElem hb1, List.getElem?_eq_getElem hb2] using h'
      · intro i hi'
        by_cases h : i = iter.start.val
        · subst h; simp_lists
        · have hb1 : i < opad.val.length := by have := opad.property; scalar_tac
          have hb2 : i < key_block.val.length := by have := key_block.property; scalar_tac
          have h' := ho i (by omega)
          simp_lists
          simpa [List.getElem?_eq_getElem hb1, List.getElem?_eq_getElem hb2] using h'
    · rename_i hge
      obtain ⟨rfl, hs⟩ := hnext
      simp only [spec_ok]
      have hst : iter.start.val = BLOCK.val := by
        have : iter.end.val = BLOCK.val := by rw [hend]
        omega
      refine ⟨?_, ?_⟩ <;> apply List.ext_getElem <;> simp
      · intro i hi'
        have hb1 : i < ipad.val.length := by have := ipad.property; scalar_tac
        have hb2 : i < key_block.val.length := by have := key_block.property; scalar_tac
        simpa [List.getElem?_eq_getElem hb1, List.getElem?_eq_getElem hb2] using hi i (by omega)
      · intro i hi'
        have hb1 : i < opad.val.length := by have := opad.property; scalar_tac
        have hb2 : i < key_block.val.length := by have := key_block.property; scalar_tac
        simpa [List.getElem?_eq_getElem hb1, List.getElem?_eq_getElem hb2] using ho i (by omega)
  · refine ⟨rfl, by simp, ?_, ?_⟩ <;> intro i hi <;> simp at hi

import LibcruxHmac.Formal.Proofs.Lemmas.XorPre

/-!
# The xor loops of `hacl::hmac::compute_sha2_{256,384,512}`

Each function builds `ipad` and `opad` with a loop over `0..n`, `pad[i] ^= key_block[i]`
(`loop0` for `ipad`, `loop1` for `opad`). The six loops are extracted with the same body,
so their specs are one proof, instantiated six times.
-/

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac

theorem hacl.hmac.compute_sha2_256_loop0_spec (key_block ipad : Slice U8) (n : U32)
    (hn : n.val = ipad.length) (hk : ipad.length ≤ key_block.length) :
    hacl.hmac.compute_sha2_256_loop0 { start := 0#u32, «end» := n } key_block ipad
      ⦃ r => r.val = List.zipWith (· ^^^ ·) ipad.val key_block.val ⦄ := by
  unfold hacl.hmac.compute_sha2_256_loop0
  apply loop.spec_decr_nat
    (fun (p : core.ops.range.Range U32 × Slice U8) => n.val - p.1.start.val)
    (fun p => p.1.end = n ∧ p.1.start.val ≤ n.val ∧
       p.2.val = xorPre ipad.val key_block.val p.1.start.val)
  · rintro ⟨it, pad⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    unfold hacl.hmac.compute_sha2_256_loop0.body
    step as ⟨o, iter1, o_post, o_end⟩
    by_cases hlt : it.start.val < it.end.val
    · simp only [hlt, ite_true] at o_post
      obtain ⟨rfl, hs⟩ := o_post
      dsimp only
      have hpl : pad.length = ipad.length := by simp [Slice.length, h3]
      have hlt' : it.start.val < n.val := by rw [h1] at hlt; exact hlt
      have hst : it.start.val < ipad.length := by omega
      have hkb : it.start.val < key_block.length := by omega
      step*
      have hi1 : i1.val = it.start.val := by scalar_tac
      have hi2 : i2.val = it.start.val := by scalar_tac
      have hi3 : i3.val = it.start.val := by scalar_tac
      have hxi : xi = ipad.val[it.start.val]'hst :=
        xi_post.trans (xorPre_get' _ _ _ _ _ h3 hst hi1 (by show i1.val < pad.length; omega))
      have hyi : yi = key_block.val[it.start.val]'hkb := by
        rw [yi_post]; simp only [hi2]
      have h4 : i4 = ipad.val[it.start.val]'hst ^^^ key_block.val[it.start.val]'hkb := by
        rw [← hxi, ← hyi]; exact UScalar.eq_of_val_eq i4_post
      refine ⟨by rw [o_end, h1], by omega, ?_, by omega⟩
      rw [s_post, Slice.set_val_eq, h3, h4, hi3, hs]
      exact xorPre_set _ _ _ hst hkb
    · simp only [hlt, ite_false] at o_post
      obtain ⟨rfl, hs⟩ := o_post
      dsimp only
      simp only [spec_ok]
      have hst : it.start.val = ipad.length := by rw [h1] at hlt; omega
      rw [h3, hst]
      exact xorPre_end _ _ hk
  · simp [xorPre_zero]

theorem hacl.hmac.compute_sha2_256_loop1_spec (key_block ipad : Slice U8) (n : U32)
    (hn : n.val = ipad.length) (hk : ipad.length ≤ key_block.length) :
    hacl.hmac.compute_sha2_256_loop1 { start := 0#u32, «end» := n } key_block ipad
      ⦃ r => r.val = List.zipWith (· ^^^ ·) ipad.val key_block.val ⦄ := by
  unfold hacl.hmac.compute_sha2_256_loop1
  apply loop.spec_decr_nat
    (fun (p : core.ops.range.Range U32 × Slice U8) => n.val - p.1.start.val)
    (fun p => p.1.end = n ∧ p.1.start.val ≤ n.val ∧
       p.2.val = xorPre ipad.val key_block.val p.1.start.val)
  · rintro ⟨it, pad⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    unfold hacl.hmac.compute_sha2_256_loop1.body
    step as ⟨o, iter1, o_post, o_end⟩
    by_cases hlt : it.start.val < it.end.val
    · simp only [hlt, ite_true] at o_post
      obtain ⟨rfl, hs⟩ := o_post
      dsimp only
      have hpl : pad.length = ipad.length := by simp [Slice.length, h3]
      have hlt' : it.start.val < n.val := by rw [h1] at hlt; exact hlt
      have hst : it.start.val < ipad.length := by omega
      have hkb : it.start.val < key_block.length := by omega
      step*
      have hi1 : i1.val = it.start.val := by scalar_tac
      have hi2 : i2.val = it.start.val := by scalar_tac
      have hi3 : i3.val = it.start.val := by scalar_tac
      have hxi : xi = ipad.val[it.start.val]'hst :=
        xi_post.trans (xorPre_get' _ _ _ _ _ h3 hst hi1 (by show i1.val < pad.length; omega))
      have hyi : yi = key_block.val[it.start.val]'hkb := by
        rw [yi_post]; simp only [hi2]
      have h4 : i4 = ipad.val[it.start.val]'hst ^^^ key_block.val[it.start.val]'hkb := by
        rw [← hxi, ← hyi]; exact UScalar.eq_of_val_eq i4_post
      refine ⟨by rw [o_end, h1], by omega, ?_, by omega⟩
      rw [s_post, Slice.set_val_eq, h3, h4, hi3, hs]
      exact xorPre_set _ _ _ hst hkb
    · simp only [hlt, ite_false] at o_post
      obtain ⟨rfl, hs⟩ := o_post
      dsimp only
      simp only [spec_ok]
      have hst : it.start.val = ipad.length := by rw [h1] at hlt; omega
      rw [h3, hst]
      exact xorPre_end _ _ hk
  · simp [xorPre_zero]

theorem hacl.hmac.compute_sha2_384_loop0_spec (key_block ipad : Slice U8) (n : U32)
    (hn : n.val = ipad.length) (hk : ipad.length ≤ key_block.length) :
    hacl.hmac.compute_sha2_384_loop0 { start := 0#u32, «end» := n } key_block ipad
      ⦃ r => r.val = List.zipWith (· ^^^ ·) ipad.val key_block.val ⦄ := by
  unfold hacl.hmac.compute_sha2_384_loop0
  apply loop.spec_decr_nat
    (fun (p : core.ops.range.Range U32 × Slice U8) => n.val - p.1.start.val)
    (fun p => p.1.end = n ∧ p.1.start.val ≤ n.val ∧
       p.2.val = xorPre ipad.val key_block.val p.1.start.val)
  · rintro ⟨it, pad⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    unfold hacl.hmac.compute_sha2_384_loop0.body
    step as ⟨o, iter1, o_post, o_end⟩
    by_cases hlt : it.start.val < it.end.val
    · simp only [hlt, ite_true] at o_post
      obtain ⟨rfl, hs⟩ := o_post
      dsimp only
      have hpl : pad.length = ipad.length := by simp [Slice.length, h3]
      have hlt' : it.start.val < n.val := by rw [h1] at hlt; exact hlt
      have hst : it.start.val < ipad.length := by omega
      have hkb : it.start.val < key_block.length := by omega
      step*
      have hi1 : i1.val = it.start.val := by scalar_tac
      have hi2 : i2.val = it.start.val := by scalar_tac
      have hi3 : i3.val = it.start.val := by scalar_tac
      have hxi : xi = ipad.val[it.start.val]'hst :=
        xi_post.trans (xorPre_get' _ _ _ _ _ h3 hst hi1 (by show i1.val < pad.length; omega))
      have hyi : yi = key_block.val[it.start.val]'hkb := by
        rw [yi_post]; simp only [hi2]
      have h4 : i4 = ipad.val[it.start.val]'hst ^^^ key_block.val[it.start.val]'hkb := by
        rw [← hxi, ← hyi]; exact UScalar.eq_of_val_eq i4_post
      refine ⟨by rw [o_end, h1], by omega, ?_, by omega⟩
      rw [s_post, Slice.set_val_eq, h3, h4, hi3, hs]
      exact xorPre_set _ _ _ hst hkb
    · simp only [hlt, ite_false] at o_post
      obtain ⟨rfl, hs⟩ := o_post
      dsimp only
      simp only [spec_ok]
      have hst : it.start.val = ipad.length := by rw [h1] at hlt; omega
      rw [h3, hst]
      exact xorPre_end _ _ hk
  · simp [xorPre_zero]

theorem hacl.hmac.compute_sha2_384_loop1_spec (key_block ipad : Slice U8) (n : U32)
    (hn : n.val = ipad.length) (hk : ipad.length ≤ key_block.length) :
    hacl.hmac.compute_sha2_384_loop1 { start := 0#u32, «end» := n } key_block ipad
      ⦃ r => r.val = List.zipWith (· ^^^ ·) ipad.val key_block.val ⦄ := by
  unfold hacl.hmac.compute_sha2_384_loop1
  apply loop.spec_decr_nat
    (fun (p : core.ops.range.Range U32 × Slice U8) => n.val - p.1.start.val)
    (fun p => p.1.end = n ∧ p.1.start.val ≤ n.val ∧
       p.2.val = xorPre ipad.val key_block.val p.1.start.val)
  · rintro ⟨it, pad⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    unfold hacl.hmac.compute_sha2_384_loop1.body
    step as ⟨o, iter1, o_post, o_end⟩
    by_cases hlt : it.start.val < it.end.val
    · simp only [hlt, ite_true] at o_post
      obtain ⟨rfl, hs⟩ := o_post
      dsimp only
      have hpl : pad.length = ipad.length := by simp [Slice.length, h3]
      have hlt' : it.start.val < n.val := by rw [h1] at hlt; exact hlt
      have hst : it.start.val < ipad.length := by omega
      have hkb : it.start.val < key_block.length := by omega
      step*
      have hi1 : i1.val = it.start.val := by scalar_tac
      have hi2 : i2.val = it.start.val := by scalar_tac
      have hi3 : i3.val = it.start.val := by scalar_tac
      have hxi : xi = ipad.val[it.start.val]'hst :=
        xi_post.trans (xorPre_get' _ _ _ _ _ h3 hst hi1 (by show i1.val < pad.length; omega))
      have hyi : yi = key_block.val[it.start.val]'hkb := by
        rw [yi_post]; simp only [hi2]
      have h4 : i4 = ipad.val[it.start.val]'hst ^^^ key_block.val[it.start.val]'hkb := by
        rw [← hxi, ← hyi]; exact UScalar.eq_of_val_eq i4_post
      refine ⟨by rw [o_end, h1], by omega, ?_, by omega⟩
      rw [s_post, Slice.set_val_eq, h3, h4, hi3, hs]
      exact xorPre_set _ _ _ hst hkb
    · simp only [hlt, ite_false] at o_post
      obtain ⟨rfl, hs⟩ := o_post
      dsimp only
      simp only [spec_ok]
      have hst : it.start.val = ipad.length := by rw [h1] at hlt; omega
      rw [h3, hst]
      exact xorPre_end _ _ hk
  · simp [xorPre_zero]

theorem hacl.hmac.compute_sha2_512_loop0_spec (key_block ipad : Slice U8) (n : U32)
    (hn : n.val = ipad.length) (hk : ipad.length ≤ key_block.length) :
    hacl.hmac.compute_sha2_512_loop0 { start := 0#u32, «end» := n } key_block ipad
      ⦃ r => r.val = List.zipWith (· ^^^ ·) ipad.val key_block.val ⦄ := by
  unfold hacl.hmac.compute_sha2_512_loop0
  apply loop.spec_decr_nat
    (fun (p : core.ops.range.Range U32 × Slice U8) => n.val - p.1.start.val)
    (fun p => p.1.end = n ∧ p.1.start.val ≤ n.val ∧
       p.2.val = xorPre ipad.val key_block.val p.1.start.val)
  · rintro ⟨it, pad⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    unfold hacl.hmac.compute_sha2_512_loop0.body
    step as ⟨o, iter1, o_post, o_end⟩
    by_cases hlt : it.start.val < it.end.val
    · simp only [hlt, ite_true] at o_post
      obtain ⟨rfl, hs⟩ := o_post
      dsimp only
      have hpl : pad.length = ipad.length := by simp [Slice.length, h3]
      have hlt' : it.start.val < n.val := by rw [h1] at hlt; exact hlt
      have hst : it.start.val < ipad.length := by omega
      have hkb : it.start.val < key_block.length := by omega
      step*
      have hi1 : i1.val = it.start.val := by scalar_tac
      have hi2 : i2.val = it.start.val := by scalar_tac
      have hi3 : i3.val = it.start.val := by scalar_tac
      have hxi : xi = ipad.val[it.start.val]'hst :=
        xi_post.trans (xorPre_get' _ _ _ _ _ h3 hst hi1 (by show i1.val < pad.length; omega))
      have hyi : yi = key_block.val[it.start.val]'hkb := by
        rw [yi_post]; simp only [hi2]
      have h4 : i4 = ipad.val[it.start.val]'hst ^^^ key_block.val[it.start.val]'hkb := by
        rw [← hxi, ← hyi]; exact UScalar.eq_of_val_eq i4_post
      refine ⟨by rw [o_end, h1], by omega, ?_, by omega⟩
      rw [s_post, Slice.set_val_eq, h3, h4, hi3, hs]
      exact xorPre_set _ _ _ hst hkb
    · simp only [hlt, ite_false] at o_post
      obtain ⟨rfl, hs⟩ := o_post
      dsimp only
      simp only [spec_ok]
      have hst : it.start.val = ipad.length := by rw [h1] at hlt; omega
      rw [h3, hst]
      exact xorPre_end _ _ hk
  · simp [xorPre_zero]

theorem hacl.hmac.compute_sha2_512_loop1_spec (key_block ipad : Slice U8) (n : U32)
    (hn : n.val = ipad.length) (hk : ipad.length ≤ key_block.length) :
    hacl.hmac.compute_sha2_512_loop1 { start := 0#u32, «end» := n } key_block ipad
      ⦃ r => r.val = List.zipWith (· ^^^ ·) ipad.val key_block.val ⦄ := by
  unfold hacl.hmac.compute_sha2_512_loop1
  apply loop.spec_decr_nat
    (fun (p : core.ops.range.Range U32 × Slice U8) => n.val - p.1.start.val)
    (fun p => p.1.end = n ∧ p.1.start.val ≤ n.val ∧
       p.2.val = xorPre ipad.val key_block.val p.1.start.val)
  · rintro ⟨it, pad⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    unfold hacl.hmac.compute_sha2_512_loop1.body
    step as ⟨o, iter1, o_post, o_end⟩
    by_cases hlt : it.start.val < it.end.val
    · simp only [hlt, ite_true] at o_post
      obtain ⟨rfl, hs⟩ := o_post
      dsimp only
      have hpl : pad.length = ipad.length := by simp [Slice.length, h3]
      have hlt' : it.start.val < n.val := by rw [h1] at hlt; exact hlt
      have hst : it.start.val < ipad.length := by omega
      have hkb : it.start.val < key_block.length := by omega
      step*
      have hi1 : i1.val = it.start.val := by scalar_tac
      have hi2 : i2.val = it.start.val := by scalar_tac
      have hi3 : i3.val = it.start.val := by scalar_tac
      have hxi : xi = ipad.val[it.start.val]'hst :=
        xi_post.trans (xorPre_get' _ _ _ _ _ h3 hst hi1 (by show i1.val < pad.length; omega))
      have hyi : yi = key_block.val[it.start.val]'hkb := by
        rw [yi_post]; simp only [hi2]
      have h4 : i4 = ipad.val[it.start.val]'hst ^^^ key_block.val[it.start.val]'hkb := by
        rw [← hxi, ← hyi]; exact UScalar.eq_of_val_eq i4_post
      refine ⟨by rw [o_end, h1], by omega, ?_, by omega⟩
      rw [s_post, Slice.set_val_eq, h3, h4, hi3, hs]
      exact xorPre_set _ _ _ hst hkb
    · simp only [hlt, ite_false] at o_post
      obtain ⟨rfl, hs⟩ := o_post
      dsimp only
      simp only [spec_ok]
      have hst : it.start.val = ipad.length := by rw [h1] at hlt; omega
      rw [h3, hst]
      exact xorPre_end _ _ hk
  · simp [xorPre_zero]

end libcrux_hmac

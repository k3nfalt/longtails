import LongTails.Proofs.NcConcaveRhoLip

open scoped BigOperators

namespace LongTails.Proofs.NcConcavePhi

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds LongTails.Proofs.NcConcavePartTwo

variable {n : ℕ}

noncomputable def nz (z : Fin n → ℝ) : ℝ := Real.sqrt (1 + sq2 z)

noncomputable def phiN (z : Fin n → ℝ) (i : Fin n) : ℝ := z i / nz z

noncomputable def dphiN (z h : Fin n → ℝ) (i : Fin n) : ℝ :=
  h i / nz z - z i * (∑ j, z j * h j) / nz z ^ 3

lemma rho_eq_phiN (u : Fin (n + 1) → ℝ) : rho u = phiN (q u) := rfl

lemma drho_eq_dphiN (u v : Fin (n + 1) → ℝ) : drho u v = dphiN (q u) (dq u v) := rfl

lemma nz_pos (z : Fin n → ℝ) : 0 < nz z := Real.sqrt_pos.mpr (by linarith [sq2_nonneg z])

lemma nz_sq (z : Fin n → ℝ) : nz z ^ 2 = 1 + sq2 z := Real.sq_sqrt (by linarith [sq2_nonneg z])

lemma one_le_nz (z : Fin n → ℝ) : 1 ≤ nz z := by
  rw [nz, Real.le_sqrt (by norm_num) (by linarith [sq2_nonneg z])]
  linarith [sq2_nonneg z]

lemma sq2_phiN (z : Fin n → ℝ) : sq2 (phiN z) ≤ 1 := by
  have h : sq2 (phiN z) = sq2 z / nz z ^ 2 := by
    simp only [sq2, phiN, div_pow, ← Finset.sum_div]
  rw [h, nz_sq, div_le_one (by linarith [sq2_nonneg z])]
  linarith

lemma sq2_dphiN_le (z h : Fin n → ℝ) : sq2 (dphiN z h) ≤ sq2 h := by
  have hspos : 0 < nz z := nz_pos z
  have hs2 : nz z ^ 2 = 1 + sq2 z := nz_sq z
  have hQ : 0 ≤ sq2 z := sq2_nonneg _
  have hD : 0 ≤ sq2 h := sq2_nonneg _
  have hpt : ∀ i, dphiN z h i ^ 2 = h i ^ 2 / nz z ^ 2 -
      2 * (∑ j, z j * h j) / nz z ^ 4 * (z i * h i) +
      (∑ j, z j * h j) ^ 2 / nz z ^ 6 * z i ^ 2 := by
    intro i; simp only [dphiN]; field_simp; ring
  have hexp : sq2 (dphiN z h) = sq2 h / nz z ^ 2 +
      (∑ j, z j * h j) ^ 2 * (sq2 z - 2 * nz z ^ 2) / nz z ^ 6 := by
    unfold sq2
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      ← Finset.mul_sum]
    field_simp
    ring
  rw [hexp]
  have h1 : sq2 h / nz z ^ 2 ≤ sq2 h := div_le_self hD (by nlinarith [one_le_nz z])
  have h2 : (∑ j, z j * h j) ^ 2 * (sq2 z - 2 * nz z ^ 2) / nz z ^ 6 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by nlinarith))
      (by positivity)
  linarith

lemma sq2_sub_expand (z z' : Fin n → ℝ) :
    sq2 (fun i => z i - z' i) = sq2 z + sq2 z' - 2 * ∑ i, z i * z' i := by
  unfold sq2
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma nz_diff_sq (z z' : Fin n → ℝ) : (nz z - nz z') ^ 2 ≤ sq2 (fun i => z i - z' i) := by
  have hA := sq2_nonneg z
  have hB := sq2_nonneg z'
  set C := ∑ i, z i * z' i
  have hCS : C ^ 2 ≤ sq2 z * sq2 z' := inner_le_sq2 z z'
  have hD := sq2_nonneg (fun i => z i - z' i)
  rw [sq2_sub_expand] at hD ⊢
  have hn := nz_sq z
  have hn' := nz_sq z'
  have hp := (nz_pos z).le
  have hp' := (nz_pos z').le
  have hprod : 1 + C ≤ nz z * nz z' := by
    by_contra hc
    push Not at hc
    have h0 : 0 ≤ nz z * nz z' := mul_nonneg hp hp'
    have h1 : (nz z * nz z') ^ 2 < (1 + C) ^ 2 := by nlinarith
    have h2 : (nz z * nz z') ^ 2 = (1 + sq2 z) * (1 + sq2 z') := by rw [mul_pow, hn, hn']
    nlinarith
  nlinarith

lemma sq2_add_le (a b : Fin n → ℝ) : sq2 (fun i => a i + b i) ≤ 2 * sq2 a + 2 * sq2 b := by
  unfold sq2
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (a i - b i)]

lemma inv_nz_diff_sq (z z' : Fin n → ℝ) :
    (1 / nz z - 1 / nz z') ^ 2 ≤ sq2 (fun i => z i - z' i) / (nz z ^ 2 * nz z' ^ 2) := by
  have hp := nz_pos z
  have hp' := nz_pos z'
  have e : 1 / nz z - 1 / nz z' = (nz z' - nz z) / (nz z * nz z') := by field_simp
  rw [e, div_pow, mul_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have := nz_diff_sq z' z
  have h2 : sq2 (fun i => z' i - z i) = sq2 (fun i => z i - z' i) := by
    unfold sq2; exact Finset.sum_congr rfl fun i _ => by ring
  linarith

lemma inv_nz_diff_sq' (z z' : Fin n → ℝ) :
    (1 / nz z - 1 / nz z') ^ 2 ≤ sq2 (fun i => z i - z' i) := by
  have h := inv_nz_diff_sq z z'
  have h1 := one_le_nz z
  have h2 := one_le_nz z'
  have hD := sq2_nonneg (fun i => z i - z' i)
  have h3 : 1 ≤ nz z * nz z' := by nlinarith
  have : 1 ≤ nz z ^ 2 * nz z' ^ 2 := by rw [← mul_pow]; nlinarith
  exact h.trans (div_le_self hD this)

lemma phiN_lip (z z' : Fin n → ℝ) :
    sq2 (fun i => phiN z i - phiN z' i) ≤ 4 * sq2 (fun i => z i - z' i) := by
  have hp := nz_pos z
  have hp' := nz_pos z'
  have e : (fun i => phiN z i - phiN z' i) =
      fun i => (z i - z' i) / nz z + z' i * (1 / nz z - 1 / nz z') := by
    funext i; simp only [phiN]; field_simp; ring
  rw [e]
  refine (sq2_add_le _ _).trans ?_
  have h1 : sq2 (fun i => (z i - z' i) / nz z) ≤ sq2 (fun i => z i - z' i) := by
    have : sq2 (fun i => (z i - z' i) / nz z) = sq2 (fun i => z i - z' i) / nz z ^ 2 := by
      simp only [sq2, div_pow, ← Finset.sum_div]
    rw [this]
    exact div_le_self (sq2_nonneg _) (by nlinarith [one_le_nz z])
  have h2 : sq2 (fun i => z' i * (1 / nz z - 1 / nz z')) ≤ sq2 (fun i => z i - z' i) := by
    have : sq2 (fun i => z' i * (1 / nz z - 1 / nz z')) = sq2 z' * (1 / nz z - 1 / nz z') ^ 2 := by
      simp only [sq2, mul_pow, ← Finset.sum_mul]
    rw [this]
    have hi := inv_nz_diff_sq z z'
    have hz' : sq2 z' ≤ nz z' ^ 2 := by rw [nz_sq]; linarith
    have hD := sq2_nonneg (fun i => z i - z' i)
    calc sq2 z' * (1 / nz z - 1 / nz z') ^ 2 ≤
        nz z' ^ 2 * (sq2 (fun i => z i - z' i) / (nz z ^ 2 * nz z' ^ 2)) :=
          mul_le_mul hz' hi (sq_nonneg _) (by positivity)
      _ = sq2 (fun i => z i - z' i) / nz z ^ 2 := by field_simp
      _ ≤ _ := div_le_self hD (by nlinarith [one_le_nz z])
  linarith

lemma sq2_add4_le (a b c d : Fin n → ℝ) :
    sq2 (fun i => a i + b i + c i + d i) ≤ 4 * (sq2 a + sq2 b + sq2 c + sq2 d) := by
  unfold sq2
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  show (a i + b i + c i + d i) ^ 2 ≤ 4 * (a i ^ 2 + b i ^ 2 + c i ^ 2 + d i ^ 2)
  nlinarith [sq_nonneg (a i - b i), sq_nonneg (a i - c i), sq_nonneg (a i - d i),
    sq_nonneg (b i - c i), sq_nonneg (b i - d i), sq_nonneg (c i - d i)]

lemma sq2_smul (c : ℝ) (a : Fin n → ℝ) : sq2 (fun i => a i * c) = sq2 a * c ^ 2 := by
  simp only [sq2, mul_pow, ← Finset.sum_mul]

lemma dphiN_lip (z z' h : Fin n → ℝ) :
    sq2 (fun i => dphiN z h i - dphiN z' h i) ≤ 40 * sq2 (fun i => z i - z' i) * sq2 h := by
  have hp := nz_pos z
  have hp' := nz_pos z'
  set ψ := 1 / nz z
  set ψ' := 1 / nz z'
  set s := ∑ j, phiN z j * h j
  set s' := ∑ j, phiN z' j * h j
  have e : (fun i => dphiN z h i - dphiN z' h i) = fun i =>
      h i * (ψ - ψ') + (phiN z' i - phiN z i) * (s * ψ) + phiN z' i * ((s' - s) * ψ) +
        phiN z' i * (s' * (ψ' - ψ)) := by
    funext i
    have hs : s = (∑ j, z j * h j) / nz z := by
      simp only [s, phiN, div_mul_eq_mul_div, Finset.sum_div]
    have hs' : s' = (∑ j, z' j * h j) / nz z' := by
      simp only [s', phiN, div_mul_eq_mul_div, Finset.sum_div]
    simp only [dphiN, hs, hs', ψ, ψ', phiN]
    field_simp
    ring
  rw [e]
  refine (sq2_add4_le _ _ _ _).trans ?_
  have hΔ := sq2_nonneg (fun i => z i - z' i)
  have hH := sq2_nonneg h
  have hψ : ψ ≤ 1 := by
    simp only [ψ]; rw [div_le_one hp]; exact one_le_nz z
  have hψ0 : 0 ≤ ψ := by positivity
  have hdψ : (ψ - ψ') ^ 2 ≤ sq2 (fun i => z i - z' i) := inv_nz_diff_sq' z z'
  have hs2 : s ^ 2 ≤ sq2 h := by
    have := inner_le_sq2 (phiN z) h
    nlinarith [sq2_phiN z]
  have hs2' : s' ^ 2 ≤ sq2 h := by
    have := inner_le_sq2 (phiN z') h
    nlinarith [sq2_phiN z']
  have hdphi : sq2 (fun i => phiN z' i - phiN z i) ≤ 4 * sq2 (fun i => z i - z' i) := by
    have h1 := phiN_lip z' z
    have h2 : sq2 (fun i => z' i - z i) = sq2 (fun i => z i - z' i) := by
      unfold sq2; exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  have hds : (s' - s) ^ 2 ≤ 4 * sq2 (fun i => z i - z' i) * sq2 h := by
    have e2 : s' - s = ∑ j, (phiN z' j - phiN z j) * h j := by
      simp only [s, s', ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e2]
    have := inner_le_sq2 (fun j => phiN z' j - phiN z j) h
    nlinarith
  have t1 : sq2 (fun i => h i * (ψ - ψ')) ≤ sq2 h * sq2 (fun i => z i - z' i) := by
    rw [sq2_smul]; exact mul_le_mul_of_nonneg_left hdψ hH
  have t2 : sq2 (fun i => (phiN z' i - phiN z i) * (s * ψ)) ≤
      4 * sq2 (fun i => z i - z' i) * sq2 h := by
    rw [sq2_smul, mul_pow]
    have hψ2 : ψ ^ 2 ≤ 1 := by nlinarith
    have h3 : s ^ 2 * ψ ^ 2 ≤ sq2 h := by nlinarith [sq_nonneg s]
    calc _ ≤ 4 * sq2 (fun i => z i - z' i) * (s ^ 2 * ψ ^ 2) :=
          mul_le_mul_of_nonneg_right hdphi (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have t3 : sq2 (fun i => phiN z' i * ((s' - s) * ψ)) ≤ 4 * sq2 (fun i => z i - z' i) * sq2 h := by
    rw [sq2_smul, mul_pow]
    have hψ2 : ψ ^ 2 ≤ 1 := by nlinarith
    have h3 : (s' - s) ^ 2 * ψ ^ 2 ≤ 4 * sq2 (fun i => z i - z' i) * sq2 h := by
      nlinarith [sq_nonneg (s' - s)]
    calc _ ≤ 1 * ((s' - s) ^ 2 * ψ ^ 2) := mul_le_mul_of_nonneg_right (sq2_phiN z') (by positivity)
      _ ≤ _ := by linarith
  have t4 : sq2 (fun i => phiN z' i * (s' * (ψ' - ψ))) ≤ sq2 h * sq2 (fun i => z i - z' i) := by
    rw [sq2_smul, mul_pow]
    have hdψ' : (ψ' - ψ) ^ 2 ≤ sq2 (fun i => z i - z' i) := by
      have : (ψ' - ψ) ^ 2 = (ψ - ψ') ^ 2 := by ring
      linarith
    calc _ ≤ 1 * (s' ^ 2 * (ψ' - ψ) ^ 2) := mul_le_mul_of_nonneg_right (sq2_phiN z') (by positivity)
      _ ≤ sq2 h * sq2 (fun i => z i - z' i) := by
          rw [one_mul]; exact mul_le_mul hs2' hdψ' (sq_nonneg _) hH
  nlinarith

lemma phiN_line0 (z d : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t : ℝ => phiN (fun j => z j + t * d j) i) (dphiN z d i) 0 := by
  have e : (fun j => z j + 0 * d j) = z := by funext j; simp
  have hnum : HasDerivAt (fun t : ℝ => z i + t * d i) (d i) 0 := by
    have h := HasDerivAt.const_add (z i) (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ)) (d i))
    simpa using h
  have hsq : HasDerivAt (fun t : ℝ => sq2 (fun j => z j + t * d j)) (∑ j, 2 * z j * d j) 0 := by
    have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
      (fun j _ => HasDerivAt.pow (by
        have h := HasDerivAt.const_add (z j) (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ)) (d j))
        simpa using h : HasDerivAt (fun t : ℝ => z j + t * d j) (d j) 0) 2)
    unfold sq2
    convert h using 1
    apply Finset.sum_congr rfl; intro j _
    simp
  have h0 : 1 + sq2 (fun j => z j + (0 : ℝ) * d j) ≠ 0 := by
    rw [e]; linarith [sq2_nonneg z]
  have hn := HasDerivAt.sqrt (HasDerivAt.const_add 1 hsq) h0
  have hn0 : Real.sqrt (1 + sq2 (fun j => z j + (0 : ℝ) * d j)) ≠ 0 := by
    rw [e]; exact (nz_pos z).ne'
  have hq := HasDerivAt.div hnum hn hn0
  unfold phiN nz
  convert hq using 1
  rw [e]
  unfold dphiN nz
  have hp := nz_pos z
  unfold nz at hp
  have h2 : (∑ j, 2 * z j * d j) = 2 * ∑ j, z j * d j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [h2]
  simp only [zero_mul, add_zero]
  field_simp

lemma phiN_line (z d : Fin n → ℝ) (w : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ i, w i * phiN (fun j => z j + s * d j) i)
      (∑ i, w i * dphiN (fun j => z j + t * d j) d i) t := by
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
    (fun i _ => HasDerivAt.const_mul (w i) (phiN_line0 (fun j => z j + t * d j) d i))
  have h0 : HasDerivAt (fun y : ℝ => ∑ i ∈ (Finset.univ : Finset (Fin n)),
      w i * phiN (fun j => z j + t * d j + y * d j) i)
      (∑ i ∈ (Finset.univ : Finset (Fin n)), w i * dphiN (fun j => z j + t * d j) d i) (t - t) := by
    rw [sub_self]; exact h
  have hshift := HasDerivAt.comp_sub_const t t h0
  convert hshift using 1
  funext s
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2; funext j; ring

theorem phiN_model (z z' : Fin n → ℝ) :
    sq2 (fun i => phiN z' i - phiN z i - dphiN z (fun j => z' j - z j) i) ≤
      40 * sq2 (fun j => z' j - z j) ^ 2 := by
  set d : Fin n → ℝ := fun j => z' j - z j
  set E : Fin n → ℝ := fun i => phiN z' i - phiN z i - dphiN z d i
  set g : ℝ → ℝ := fun s => ∑ i, E i * phiN (fun j => z j + s * d j) i
  have hg : ∀ t, HasDerivAt g (∑ i, E i * dphiN (fun j => z j + t * d j) d i) t :=
    fun t => phiN_line z d E t
  obtain ⟨ξ, hξ01, hξ⟩ := exists_hasDerivAt_eq_slope g _ (by norm_num : (0 : ℝ) < 1)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have h0 : g 0 = ∑ i, E i * phiN z i := by
    simp only [g, zero_mul, add_zero]
  have h1 : g 1 = ∑ i, E i * phiN z' i := by
    simp only [g, one_mul, d]; congr 1; funext i; congr 2; funext j; ring
  rw [sub_zero, div_one, h1, h0] at hξ
  have key : sq2 E = ∑ i, E i * (dphiN (fun j => z j + ξ * d j) d i - dphiN z d i) := by
    have e1 : sq2 E = ∑ i, E i * (phiN z' i - phiN z i) - ∑ i, E i * dphiN z d i := by
      simp only [sq2, E, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, E i * (phiN z' i - phiN z i) = ∑ i, E i * phiN z' i - ∑ i, E i * phiN z i := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, ← hξ, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hlip := dphiN_lip (fun j => z j + ξ * d j) z d
  have hΔ : sq2 (fun i => z i + ξ * d i - z i) ≤ sq2 d := by
    have : sq2 (fun i => z i + ξ * d i - z i) = ξ ^ 2 * sq2 d := by
      simp only [sq2, add_sub_cancel_left, mul_pow, ← Finset.mul_sum]
    rw [this]
    have : ξ ^ 2 ≤ 1 := by nlinarith [hξ01.1, hξ01.2]
    nlinarith [sq2_nonneg d]
  have hcs := inner_le_sq2 E (fun i => dphiN (fun j => z j + ξ * d j) d i - dphiN z d i)
  rw [← key] at hcs
  have hD := sq2_nonneg d
  have hE := sq2_nonneg E
  have hb : sq2 (fun i => dphiN (fun j => z j + ξ * d j) d i - dphiN z d i) ≤ 40 * sq2 d * sq2 d :=
    hlip.trans (by nlinarith)
  have : sq2 E ^ 2 ≤ sq2 E * (40 * sq2 d ^ 2) := by
    calc sq2 E ^ 2 ≤ sq2 E * sq2 (fun i => dphiN (fun j => z j + ξ * d j) d i - dphiN z d i) := hcs
      _ ≤ sq2 E * (40 * sq2 d * sq2 d) := mul_le_mul_of_nonneg_left hb hE
      _ = _ := by ring
  rcases eq_or_lt_of_le hE with h | h
  · rw [← h]; positivity
  · nlinarith

end LongTails.Proofs.NcConcavePhi

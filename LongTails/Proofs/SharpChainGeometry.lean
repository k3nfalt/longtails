import LongTails.Proofs.MintyChainGeometry

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.SharpChainGeometry

open MintyChainGeometry

section Generic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma inner_add_sq_le (a b : F) (s : ℝ) :
    ⟪a, b⟫ + s ^ 2 ≤ Real.sqrt (‖a‖ ^ 2 + s ^ 2) * Real.sqrt (‖b‖ ^ 2 + s ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  have h1 : |⟪a, b⟫| ≤ ‖a‖ * ‖b‖ := abs_real_inner_le_norm a b
  have h2 : ⟪a, b⟫ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : ⟪a, b⟫ ≤ ‖a‖ * ‖b‖ := (le_abs_self _).trans h1
  have h4 : 0 ≤ (‖a‖ * s - ‖b‖ * s) ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg s, mul_nonneg (norm_nonneg a) (norm_nonneg b),
    mul_nonneg (mul_nonneg (norm_nonneg a) (norm_nonneg b)) (sq_nonneg s)]

lemma sqrt_norm_lower (a b : F) (s : ℝ) (h : 0 < Real.sqrt (‖a‖ ^ 2 + s ^ 2)) :
    Real.sqrt (‖a‖ ^ 2 + s ^ 2) + ⟪a, b - a⟫ / Real.sqrt (‖a‖ ^ 2 + s ^ 2) ≤
      Real.sqrt (‖b‖ ^ 2 + s ^ 2) := by
  have hm := inner_add_sq_le a b s
  have hsq : Real.sqrt (‖a‖ ^ 2 + s ^ 2) ^ 2 = ‖a‖ ^ 2 + s ^ 2 := Real.sq_sqrt (by positivity)
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [← sub_nonneg]
  have key : Real.sqrt (‖b‖ ^ 2 + s ^ 2) - (Real.sqrt (‖a‖ ^ 2 + s ^ 2) +
      (⟪a, b⟫ - ‖a‖ ^ 2) / Real.sqrt (‖a‖ ^ 2 + s ^ 2)) =
      (Real.sqrt (‖a‖ ^ 2 + s ^ 2) * Real.sqrt (‖b‖ ^ 2 + s ^ 2) - (⟪a, b⟫ + s ^ 2)) /
        Real.sqrt (‖a‖ ^ 2 + s ^ 2) := by
    field_simp
    rw [hsq]
    ring
  rw [key]
  exact div_nonneg (by linarith) h.le

lemma lipschitz_of_subgradient (g : F → ℝ) (G : F → F) (M : ℝ)
    (hsub : ∀ x y, g x + ⟪G x, y - x⟫ ≤ g y) (hG : ∀ x, ‖G x‖ ≤ M) (x y : F) :
    g y - g x ≤ M * ‖y - x‖ := by
  have h := hsub y x
  have hc : ⟪G y, x - y⟫ ≥ -(‖G y‖ * ‖x - y‖) := by
    have := abs_real_inner_le_norm (G y) (x - y)
    have := neg_abs_le ⟪G y, x - y⟫
    linarith
  have hn : ‖x - y‖ = ‖y - x‖ := norm_sub_rev x y
  have hm : ‖G y‖ * ‖x - y‖ ≤ M * ‖y - x‖ := by
    rw [hn]
    exact mul_le_mul_of_nonneg_right (hG y) (norm_nonneg _)
  linarith

end Generic

variable {d k : ℕ}

set_option hygiene false in
local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable def gap (μ0 D : ℝ) (m : ℕ) : ℝ := D * Real.sqrt ((1 - μ0 ^ 2) ^ m)

noncomputable def tgtN (μ0 D : ℝ) (k j : ℕ) : ℝ :=
  if j < k then -(μ0 * gap μ0 D j) else -gap μ0 D k

noncomputable def tgt (μ0 D : ℝ) (j : Fin (k + 1)) : ℝ := tgtN μ0 D k j.val

noncomputable def dev (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : E) (j : Fin (k + 1)) : ℝ :=
  u (π j) - tgt μ0 D j

def mask (m : ℕ) (c : Fin (k + 1) → ℝ) : Fin (k + 1) → ℝ := fun j => if j.val < m then c j else 0

def unit (m : Fin (k + 1)) : Fin (k + 1) → ℝ := fun j => if j = m then 1 else 0

noncomputable def offset (μ0 D : ℝ) (k m : ℕ) : ℝ := m * (μ0 * gap μ0 D k / (4 * (k + 1)))

noncomputable def chainRoot (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d) (m : Fin (k + 1)) (u : E) : ℝ :=
  Real.sqrt (‖lift π (mask m.val (dev μ0 D π u))‖ ^ 2 + gap μ0 D m.val ^ 2)

noncomputable def chainVal (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d) (m : Fin (k + 1)) (u : E) : ℝ :=
  μ0 * chainRoot μ0 D π m u + u (π m) - offset μ0 D k m.val

noncomputable def chainGrad (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d) (m : Fin (k + 1)) (u : E) : E :=
  (μ0 / chainRoot μ0 D π m u) • lift π (mask m.val (dev μ0 D π u)) + lift π (unit m)

noncomputable def radialVal (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : E) : ℝ :=
  μ0 / 2 * ‖lift π (dev μ0 D π u)‖

noncomputable def radialGrad (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : E) : E :=
  (μ0 / 2 / ‖lift π (dev μ0 D π u)‖) • lift π (dev μ0 D π u)

noncomputable def coneVal (D : ℝ) (u : E) : ℝ := 3 * ‖u‖ - 9 * D

noncomputable def coneGrad (u : E) : E := (3 / ‖u‖) • u

noncomputable def chainPiece (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d) (m : Fin (k + 1)) (u : E) :
    ℝ × E := (chainVal μ0 D π m u, chainGrad μ0 D π m u)

noncomputable def bestUpTo (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : E) : ℕ → ℝ × E
  | 0 => chainPiece μ0 D π ⟨0, Nat.succ_pos k⟩ u
  | t + 1 =>
    if h : t + 1 < k + 1 then
      (if (bestUpTo μ0 D π u t).1 < chainVal μ0 D π ⟨t + 1, h⟩ u then
        chainPiece μ0 D π ⟨t + 1, h⟩ u else bestUpTo μ0 D π u t)
    else bestUpTo μ0 D π u t

noncomputable def answer (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : E) : ℝ × E :=
  if max (bestUpTo μ0 D π u k).1 (radialVal μ0 D π u) ≤ coneVal D u then (coneVal D u, coneGrad u)
  else if radialVal μ0 D π u ≤ (bestUpTo μ0 D π u k).1 then bestUpTo μ0 D π u k
  else (radialVal μ0 D π u, radialGrad μ0 D π u)

noncomputable def partialAnswer (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d) (t : ℕ) (u : E) : ℝ × E :=
  if (bestUpTo μ0 D π u t).1 ≤ coneVal D u then (coneVal D u, coneGrad u)
  else bestUpTo μ0 D π u t

noncomputable def hardValue (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : E) : ℝ :=
  (answer μ0 D π u).1

section Basic

variable (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d)

lemma inner_lift_lift (a c : Fin (k + 1) → ℝ) : ⟪lift π a, lift π c⟫ = ∑ j, a j * c j := by
  rw [inner_lift]
  simp [lift_apply]

lemma inner_lift_unit (m : Fin (k + 1)) (w : E) : ⟪lift π (unit m), w⟫ = w (π m) := by
  rw [inner_lift]
  simp [unit]

lemma norm_lift_unit (m : Fin (k + 1)) : ‖lift π (unit m)‖ = 1 := by
  have h := norm_lift_sq π (unit m)
  have hs : ∑ j, unit m j ^ 2 = 1 := by simp [unit]
  rw [hs] at h
  have := norm_nonneg (lift π (unit m))
  nlinarith [sq_nonneg (‖lift π (unit m)‖ - 1)]

lemma inner_mask_eq (m : ℕ) (u y : E) :
    ⟪lift π (mask m (dev μ0 D π u)), y - u⟫ =
      ⟪lift π (mask m (dev μ0 D π u)),
        lift π (mask m (dev μ0 D π y)) - lift π (mask m (dev μ0 D π u))⟫ := by
  rw [lift_sub, inner_lift, inner_lift_lift]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mask, dev]
  split_ifs
  · simp only [PiLp.sub_apply]
    ring
  · simp

lemma inner_dev_eq (u y : E) :
    ⟪lift π (dev μ0 D π u), y - u⟫ =
      ⟪lift π (dev μ0 D π u), lift π (dev μ0 D π y) - lift π (dev μ0 D π u)⟫ := by
  rw [lift_sub, inner_lift, inner_lift_lift]
  apply Finset.sum_congr rfl
  intro j _
  simp only [dev, PiLp.sub_apply]
  ring

lemma gap_pos (hμ0 : μ0 ^ 2 < 1) (hD : 0 < D) (m : ℕ) : 0 < gap μ0 D m := by
  unfold gap
  have : 0 < (1 - μ0 ^ 2) ^ m := pow_pos (by linarith) m
  positivity

lemma gap_sq (hμ0 : μ0 ^ 2 < 1) (m : ℕ) : gap μ0 D m ^ 2 = D ^ 2 * (1 - μ0 ^ 2) ^ m := by
  unfold gap
  rw [mul_pow, Real.sq_sqrt (pow_nonneg (by linarith) m)]

lemma gap_succ_sq (hμ0 : μ0 ^ 2 < 1) (m : ℕ) :
    gap μ0 D (m + 1) ^ 2 = (1 - μ0 ^ 2) * gap μ0 D m ^ 2 := by
  rw [gap_sq μ0 D hμ0, gap_sq μ0 D hμ0, pow_succ]
  ring

lemma gap_anti (hμ0 : μ0 ^ 2 < 1) (hD : 0 < D) {m n : ℕ} (h : m ≤ n) :
    gap μ0 D n ≤ gap μ0 D m := by
  unfold gap
  apply mul_le_mul_of_nonneg_left _ hD.le
  apply Real.sqrt_le_sqrt
  apply pow_le_pow_of_le_one (by nlinarith [sq_nonneg μ0]) (by nlinarith [sq_nonneg μ0]) h

lemma chainRoot_pos (hμ0 : μ0 ^ 2 < 1) (hD : 0 < D) (m : Fin (k + 1)) (u : E) :
    0 < chainRoot μ0 D π m u := by
  unfold chainRoot
  apply Real.sqrt_pos.mpr
  have := gap_pos μ0 D hμ0 hD m.val
  positivity

lemma chain_subgradient (hμ : 0 ≤ μ0) (hμ0 : μ0 ^ 2 < 1) (hD : 0 < D) (m : Fin (k + 1)) (u y : E) :
    chainVal μ0 D π m u + ⟪chainGrad μ0 D π m u, y - u⟫ ≤ chainVal μ0 D π m y := by
  have hr := chainRoot_pos μ0 D π hμ0 hD m u
  have hl := sqrt_norm_lower (lift π (mask m.val (dev μ0 D π u)))
    (lift π (mask m.val (dev μ0 D π y))) (gap μ0 D m.val) hr
  unfold chainVal chainGrad
  rw [inner_add_left, inner_smul_left, inner_lift_unit, inner_mask_eq]
  simp only [conj_trivial, PiLp.sub_apply]
  unfold chainRoot at hr ⊢
  have e : μ0 / Real.sqrt (‖lift π (mask (↑m) (dev μ0 D π u))‖ ^ 2 + gap μ0 D ↑m ^ 2) *
      ⟪lift π (mask (↑m) (dev μ0 D π u)), lift π (mask (↑m) (dev μ0 D π y)) -
        lift π (mask (↑m) (dev μ0 D π u))⟫ =
      μ0 * (⟪lift π (mask (↑m) (dev μ0 D π u)), lift π (mask (↑m) (dev μ0 D π y)) -
        lift π (mask (↑m) (dev μ0 D π u))⟫ /
        Real.sqrt (‖lift π (mask (↑m) (dev μ0 D π u))‖ ^ 2 + gap μ0 D ↑m ^ 2)) := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hl hμ]

lemma chainGrad_norm (hμ : 0 ≤ μ0) (hμ0 : μ0 ^ 2 < 1) (hD : 0 < D) (m : Fin (k + 1)) (u : E) :
    ‖chainGrad μ0 D π m u‖ ≤ μ0 + 1 := by
  have hr := chainRoot_pos μ0 D π hμ0 hD m u
  unfold chainGrad
  refine (norm_add_le _ _).trans ?_
  rw [norm_lift_unit, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hμ hr.le)]
  have hle : ‖lift π (mask m.val (dev μ0 D π u))‖ ≤ chainRoot μ0 D π m u := by
    unfold chainRoot
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (gap μ0 D m.val)]
  have : μ0 / chainRoot μ0 D π m u * ‖lift π (mask m.val (dev μ0 D π u))‖ ≤ μ0 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hr]
    exact mul_le_mul_of_nonneg_left hle hμ
  linarith

lemma radial_subgradient (hμ : 0 ≤ μ0) (u y : E) :
    radialVal μ0 D π u + ⟪radialGrad μ0 D π u, y - u⟫ ≤ radialVal μ0 D π y := by
  unfold radialVal radialGrad
  by_cases h0 : ‖lift π (dev μ0 D π u)‖ = 0
  · rw [h0]
    simp only [mul_zero, div_zero, zero_smul, inner_zero_left, add_zero]
    positivity
  · have hp : 0 < ‖lift π (dev μ0 D π u)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hr : 0 < Real.sqrt (‖lift π (dev μ0 D π u)‖ ^ 2 + 0 ^ 2) := by
      rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hp.le]
      exact hp
    have hl := sqrt_norm_lower (lift π (dev μ0 D π u)) (lift π (dev μ0 D π y)) 0 hr
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      Real.sqrt_sq (norm_nonneg _)] at hl
    rw [inner_smul_left, inner_dev_eq]
    simp only [conj_trivial]
    have e : μ0 / 2 / ‖lift π (dev μ0 D π u)‖ *
        ⟪lift π (dev μ0 D π u), lift π (dev μ0 D π y) - lift π (dev μ0 D π u)⟫ =
        μ0 / 2 * (⟪lift π (dev μ0 D π u), lift π (dev μ0 D π y) - lift π (dev μ0 D π u)⟫ /
          ‖lift π (dev μ0 D π u)‖) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ μ0 / 2)]

lemma radialGrad_norm (hμ : 0 ≤ μ0) (u : E) : ‖radialGrad μ0 D π u‖ ≤ μ0 / 2 := by
  unfold radialGrad
  rw [norm_smul, Real.norm_eq_abs]
  by_cases h0 : ‖lift π (dev μ0 D π u)‖ = 0
  · rw [h0]
    simp
    positivity
  · have hp : 0 < ‖lift π (dev μ0 D π u)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    rw [abs_of_nonneg (by positivity), div_mul_cancel₀ _ hp.ne']

lemma cone_subgradient (u y : E) : coneVal D u + ⟪coneGrad u, y - u⟫ ≤ coneVal D y := by
  unfold coneVal coneGrad
  by_cases h0 : ‖u‖ = 0
  · rw [h0]
    simp only [div_zero, zero_smul, inner_zero_left, add_zero, mul_zero]
    have := norm_nonneg y
    linarith
  · have hp : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hr : 0 < Real.sqrt (‖u‖ ^ 2 + 0 ^ 2) := by
      rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hp.le]
      exact hp
    have hl := sqrt_norm_lower u y 0 hr
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      Real.sqrt_sq (norm_nonneg _)] at hl
    rw [inner_smul_left]
    simp only [conj_trivial]
    have e : 3 / ‖u‖ * ⟪u, y - u⟫ = 3 * (⟪u, y - u⟫ / ‖u‖) := by ring
    rw [e]
    nlinarith

lemma coneGrad_norm (u : E) : ‖coneGrad u‖ ≤ 3 := by
  unfold coneGrad
  rw [norm_smul, Real.norm_eq_abs]
  by_cases h0 : ‖u‖ = 0
  · rw [h0]
    simp
  · have hp : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    rw [abs_of_nonneg (by positivity), div_mul_cancel₀ _ hp.ne']

end Basic

end LongTails.Proofs.SharpChainGeometry

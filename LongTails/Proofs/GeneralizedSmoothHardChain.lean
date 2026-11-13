import LongTails.Proofs.GeneralizedSmoothHardTransfer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.GeneralizedSmoothHardChain

open GeneralizedSmoothHardDual GeneralizedSmoothHardDualSegments GeneralizedSmoothHardTransfer
open CompactConjugate

noncomputable def weight (m : ℕ) (L₁ ε : ℝ) (i : Fin m) : ℝ :=
  2 * ε * L₁ * Real.exp (((m : ℝ) - 1 - i.val) / Real.sqrt m)

noncomputable def peak (m : ℕ) (L₁ ε : ℝ) : ℝ :=
  2 * ε * L₁ * Real.exp (((m : ℝ) - 1) / Real.sqrt m)

lemma weight_pos (m : ℕ) (L₁ ε : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε) (i : Fin m) :
    0 < weight m L₁ ε i := by unfold weight; positivity

lemma peak_pos (m : ℕ) (L₁ ε : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε) :
    0 < peak m L₁ ε := by unfold peak; positivity

lemma weight_le_peak {m : ℕ} (_hm : 0 < m) (L₁ ε : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε)
    (i : Fin m) : weight m L₁ ε i ≤ peak m L₁ ε := by
  unfold weight peak
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  linarith [(Nat.cast_nonneg i.val : (0 : ℝ) ≤ i.val)]

lemma weight_lower {m : ℕ} (L₁ ε : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε)
    (i : Fin m) : 2 * ε * L₁ ≤ weight m L₁ ε i := by
  have hi : (i.val : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
  have he : 1 ≤ Real.exp (((m : ℝ) - 1 - i.val) / Real.sqrt m) :=
    Real.one_le_exp_iff.mpr (div_nonneg (by linarith) (Real.sqrt_nonneg _))
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * ε * L₁ by positivity)
  simpa only [mul_one, weight] using hh

lemma weight_ratio {m : ℕ} (L₁ ε : ℝ) (j l : Fin m) :
    weight m L₁ ε j = weight m L₁ ε l * Real.exp (((l.val : ℝ) - j.val) / Real.sqrt m) := by
  unfold weight
  rw [mul_assoc (2 * ε * L₁), ← Real.exp_add]
  congr 2
  ring

lemma weight_ratio_lower {m : ℕ} (hm : 0 < m) (L₁ ε : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε)
    (j l : Fin m) (hjl : j < l) :
    weight m L₁ ε l * (1 + 1 / Real.sqrt m) ≤ weight m L₁ ε j := by
  have hjl' : (j.val : ℝ) + 1 ≤ l.val := by exact_mod_cast hjl
  have hs : 0 < Real.sqrt m := by positivity
  have hr : 1 / Real.sqrt m ≤ ((l.val : ℝ) - j.val) / Real.sqrt m := by
    gcongr
    linarith
  have he := Real.add_one_le_exp (((l.val : ℝ) - j.val) / Real.sqrt m)
  rw [weight_ratio L₁ ε j l]
  apply mul_le_mul_of_nonneg_left _ (weight_pos m L₁ ε hL₁ hε l).le
  linarith

lemma ratio_margin (A B h L₁ : ℝ) (hB : 0 < B) (hh : 0 < h) (hh' : h ≤ 1)
    (hL₁ : 0 < L₁) (hAB : B * (1 + h) ≤ A) :
    h / (8 * L₁) * (A + B) < 2 * (A - B) / L₁ := by
  have hd : 0 < A - B := by nlinarith [mul_pos hB hh]
  have hbound : h * (A + B) ≤ 3 * (A - B) := by
    have hc := mul_nonneg (sub_nonneg.mpr hh') hd.le
    nlinarith only [hAB, hc]
  have hs : h * (A + B) < 16 * (A - B) := by linarith
  have ht := div_lt_div_of_pos_right hs (show 0 < 8 * L₁ by positivity)
  convert ht using 1 <;> field_simp
  ring

lemma weight_strict_order {m : ℕ} (hm : 0 < m) (L₁ ε : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε)
    (j l : Fin m) (hjl : j < l) : weight m L₁ ε l < weight m L₁ ε j := by
  have hh := weight_ratio_lower hm L₁ ε hL₁ hε j l hjl
  have hb := weight_pos m L₁ ε hL₁ hε l
  have hs : 0 < 1 / Real.sqrt m := by positivity
  nlinarith [mul_pos hb hs]

lemma weight_margin {m : ℕ} (hm : 0 < m) (L₁ ε : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε)
    (j l : Fin m) (hjl : j < l) :
    (1 / (8 * L₁ * Real.sqrt m)) * (weight m L₁ ε j + weight m L₁ ε l) <
      2 * (weight m L₁ ε j - weight m L₁ ε l) / L₁ := by
  have hs : 0 < Real.sqrt m := by positivity
  have hsone : 1 ≤ Real.sqrt m := by
    have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ m by exact_mod_cast hm)
    simpa using hh
  have hh := ratio_margin _ _ (1 / Real.sqrt m) L₁ (weight_pos m L₁ ε hL₁ hε l)
    (by positivity) ((div_le_one hs).mpr hsone) hL₁ (weight_ratio_lower hm L₁ ε hL₁ hε j l hjl)
  convert hh using 1
  ring

noncomputable def objective (m : ℕ) (L₀ L₁ ε : ℝ) (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  value (feasible (weight m L₁ ε)) (dual L₀ L₁)
    (y + shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε))

noncomputable def field (m : ℕ) (L₀ L₁ ε : ℝ) (y : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  maximizer (feasible (weight m L₁ ε)) (dual L₀ L₁)
    (y + shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε))

lemma field_tail_zero {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (j l : Fin m) (hjl : j < l)
    (y : EuclideanSpace ℝ (Fin m)) (hyj : -(1 / (8 * L₁ * Real.sqrt m)) ≤ y j)
    (hyl : y l ≤ 1 / (8 * L₁ * Real.sqrt m)) : field m L₀ L₁ ε y l = 0 := by
  have hG := weight_pos m L₁ ε hL₁ hε
  have hB := (peak_pos m L₁ ε hL₁ hε).le
  have hGB := weight_le_peak hm L₁ ε hL₁ hε
  have hK := feasible_compact (weight m L₁ ε) (peak m L₁ ε) hG hB hGB
  have hne : (feasible (weight m L₁ ε)).Nonempty := ⟨0, feasible_zero _⟩
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε)
  have hu := maximizer_spec hK hne hH (y + shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε))
  exact shifted_optimizer_tail_zero hm L₀ L₁ (peak m L₁ ε) _ hL₀ hL₁ (weight m L₁ ε)
    hG hB hGB j l hjl (weight_strict_order hm L₁ ε hL₁ hε j l hjl).le y _ hu.1 hu.2 hyj hyl
    (weight_margin hm L₁ ε hL₁ hε j l hjl)

lemma radial_upper (L₀ L₁ s B : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁)
    (hs : 0 ≤ s) (hsB : s ≤ B) :
    radial L₀ L₁ s ≤ s * (Real.log (1 + L₁ * B / L₀) / L₁) := by
  have hh := entropy_upper 4 1 (L₁ * s / L₀) (by norm_num) (by norm_num) (by positivity)
  norm_num only [entropy, div_one, div_self, one_mul] at hh
  have ht := mul_le_mul_of_nonneg_left hh (show 0 ≤ L₀ / L₁ ^ 2 by positivity)
  have hb : Real.log (1 + L₁ * s / L₀) ≤ Real.log (1 + L₁ * B / L₀) := by
    apply Real.log_le_log (by positivity)
    gcongr
  have he : L₀ / L₁ ^ 2 * (L₁ * s / L₀ * Real.log (1 + L₁ * s / L₀)) =
      s * (Real.log (1 + L₁ * s / L₀) / L₁) := by field_simp
  simp only [add_comm (L₁ * s / L₀) 1] at ht
  change radial L₀ L₁ s ≤ _ at ht
  rw [he] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb hL₁.le) hs)

noncomputable def vertex {m : ℕ} (G : Fin m → ℝ) (i : Fin m) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j => if j = i then G i else 0)

lemma vertex_feasible {m : ℕ} (G : Fin m → ℝ) (hG : ∀ i, 0 < G i) (i : Fin m) :
    vertex G i ∈ feasible G := by
  constructor
  · intro j
    change 0 ≤ if j = i then G i else 0
    split
    · exact (hG i).le
    · exact le_rfl
  · change (∑ j, (if j = i then G i else 0) / G j) ≤ 1
    have he (j : Fin m) : (if j = i then G i else 0) / G j = if j = i then 1 else 0 := by
      split_ifs with hj
      · subst j
        exact div_self (hG i).ne'
      · exact zero_div _
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, le_refl]

lemma vertex_sum {m : ℕ} (G : Fin m → ℝ) (i : Fin m) : ∑ j, vertex G i j = G i := by
  simp [vertex]

lemma vertex_inner {m : ℕ} (G : Fin m → ℝ) (i : Fin m) (y : EuclideanSpace ℝ (Fin m)) :
    ⟪y, vertex G i⟫ = G i * y i := by
  simp [PiLp.inner_apply, vertex]

lemma tailSum_lower {m : ℕ} (G : Fin m → ℝ) (hG : ∀ i, 0 ≤ G i) (i : Fin m) :
    G i ≤ tailSum G i := by
  have hh := Finset.single_le_sum (f := fun j => if i ≤ j then G j else 0)
    (s := Finset.univ) (fun j _ => by split; exact hG j; exact le_rfl) (Finset.mem_univ i)
  simpa [tailSum] using hh

lemma shifted_vertex_bound {m : ℕ} (hm : 0 < m) (L₀ L₁ B : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ) (hG : ∀ i, 0 < G i)
    (i : Fin m) (hiB : G i ≤ B) (y : EuclideanSpace ℝ (Fin m)) :
    G i * (y i + 2 / L₁) ≤
      ⟪y + shift L₀ L₁ B G, vertex G i⟫ - dual L₀ L₁ (vertex G i) := by
  let C := 4 / L₁ * Real.log (1 + 1 / (1 / Real.sqrt m))
  have hC : 0 ≤ C := by
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    have hh : 0 ≤ 1 / (1 / Real.sqrt m) := by positivity
    linarith
  have hv := vertex_feasible G hG i
  have hd := (dual_bound hm L₀ L₁ hL₀ hL₁ (vertex G i) hv.1).2
  rw [vertex_sum] at hd
  have hr := radial_upper L₀ L₁ (G i) B hL₀ hL₁ (hG i).le hiB
  have ht := mul_le_mul_of_nonneg_left (tailSum_lower G (fun j => (hG j).le) i) hC
  have he : G i * shiftCoordinate L₀ L₁ B G i =
      G i * (2 * (Real.log (1 + L₁ * B / L₀) / L₁) + 2 / L₁) + C * tailSum G i := by
    unfold shiftCoordinate C
    field_simp [(hG i).ne']
  rw [vertex_inner]
  change G i * (y i + 2 / L₁) ≤ G i * (y i + shiftCoordinate L₀ L₁ B G i) - _
  simp only [mul_add]
  rw [he]
  change dual L₀ L₁ (vertex G i) ≤ 2 * radial L₀ L₁ (G i) + G i * C at hd
  nlinarith only [hd, hr, ht]

lemma objective_vertex_bound {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε)
    (i : Fin m) (y : EuclideanSpace ℝ (Fin m)) :
    weight m L₁ ε i * (y i + 2 / L₁) ≤ objective m L₀ L₁ ε y := by
  have hG := weight_pos m L₁ ε hL₁ hε
  have hB := (peak_pos m L₁ ε hL₁ hε).le
  have hGB := weight_le_peak hm L₁ ε hL₁ hε
  have hK := feasible_compact (weight m L₁ ε) (peak m L₁ ε) hG hB hGB
  have hne : (feasible (weight m L₁ ε)).Nonempty := ⟨0, feasible_zero _⟩
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε)
  have hu := maximizer_spec hK hne hH (y + shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε))
  exact (shifted_vertex_bound hm L₀ L₁ _ hL₀ hL₁ _ hG i (hGB i) y).trans
    (hu.2 (vertex_feasible _ hG i))

lemma objective_gap {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε)
    (i : Fin m) (y : EuclideanSpace ℝ (Fin m))
    (hy : -(1 / (8 * L₁ * Real.sqrt m)) ≤ y i) :
    15 * ε / 4 ≤ objective m L₀ L₁ ε y := by
  have hs : 1 ≤ Real.sqrt m := by
    have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ m by exact_mod_cast hm)
    simpa using hh
  have ht : 1 / (8 * L₁ * Real.sqrt m) ≤ 1 / (8 * L₁) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hy' : 15 / (8 * L₁) ≤ y i + 2 / L₁ := by
    have he : 2 / L₁ - 1 / (8 * L₁) = 15 / (8 * L₁) := by ring
    linarith
  have hh := mul_le_mul (weight_lower L₁ ε hL₁ hε i) hy'
    (show 0 ≤ 15 / (8 * L₁) by positivity) (weight_pos m L₁ ε hL₁ hε i).le
  have he : 2 * ε * L₁ * (15 / (8 * L₁)) = 15 * ε / 4 := by field_simp; ring
  rw [he] at hh
  exact hh.trans (objective_vertex_bound hm L₀ L₁ ε hL₀ hL₁ hε i y)

lemma objective_hasGradientAt {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (y : EuclideanSpace ℝ (Fin m)) :
    HasGradientAt (objective m L₀ L₁ ε) (field m L₀ L₁ ε y) y := by
  have hh := conjugate_hasGradientAt hm L₀ L₁ (peak m L₁ ε) hL₀ hL₁
    (weight m L₁ ε) (weight_pos m L₁ ε hL₁ hε) (peak_pos m L₁ ε hL₁ hε).le
    (weight_le_peak hm L₁ ε hL₁ hε) (y + shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε))
  rw [hasGradientAt_iff_hasFDerivAt]
  have ht := hh.hasFDerivAt.comp y ((hasFDerivAt_id y).add_const
    (shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε)))
  convert ht using 1
  · rfl
  · simp only [ContinuousLinearMap.comp_id, field]

lemma field_pair {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (x y : EuclideanSpace ℝ (Fin m)) :
    ‖field m L₀ L₁ ε x - field m L₀ L₁ ε y‖ ≤
      (L₀ + L₁ * max ‖field m L₀ L₁ ε x‖ ‖field m L₀ L₁ ε y‖) * ‖x - y‖ := by
  have hh := conjugate_field_pair hm L₀ L₁ (peak m L₁ ε) hL₀ hL₁
    (weight m L₁ ε) (weight_pos m L₁ ε hL₁ hε) (peak_pos m L₁ ε hL₁ hε).le
    (weight_le_peak hm L₁ ε hL₁ hε)
    (x + shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε))
    (y + shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε))
  simpa only [field, add_sub_add_right_eq_sub] using hh

lemma field_norm_bound {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (y : EuclideanSpace ℝ (Fin m)) :
    ‖field m L₀ L₁ ε y‖ ≤ peak m L₁ ε := by
  have hG := weight_pos m L₁ ε hL₁ hε
  have hB := (peak_pos m L₁ ε hL₁ hε).le
  have hGB := weight_le_peak hm L₁ ε hL₁ hε
  have hK := feasible_compact (weight m L₁ ε) (peak m L₁ ε) hG hB hGB
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε)
  exact feasible_norm_bound _ _ hG hB hGB _
    (maximizer_spec hK ⟨0, feasible_zero _⟩ hH _).1

lemma objective_nonnegative {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (y : EuclideanSpace ℝ (Fin m)) :
    0 ≤ objective m L₀ L₁ ε y :=
  conjugate_nonnegative hm L₀ L₁ (peak m L₁ ε) hL₀ hL₁
    (weight m L₁ ε) (weight_pos m L₁ ε hL₁ hε) (peak_pos m L₁ ε hL₁ hε).le
    (weight_le_peak hm L₁ ε hL₁ hε) _

lemma objective_zero {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (y : EuclideanSpace ℝ (Fin m))
    (hy : ∀ i, y i + shiftCoordinate L₀ L₁ (peak m L₁ ε) (weight m L₁ ε) i ≤ 0) :
    objective m L₀ L₁ ε y = 0 :=
  conjugate_zero_of_nonpositive hm L₀ L₁ (peak m L₁ ε) hL₀ hL₁
    (weight m L₁ ε) (weight_pos m L₁ ε hL₁ hε) (peak_pos m L₁ ε hL₁ hε).le
    (weight_le_peak hm L₁ ε hL₁ hε) _ hy

lemma inner_prefix_eq {m : ℕ} (j : Fin m) (x y z : EuclideanSpace ℝ (Fin m))
    (hxy : ∀ i, i ≤ j → x i = y i) (hz : ∀ i, j < i → z i = 0) : ⟪x, z⟫ = ⟪y, z⟫ := by
  simp only [PiLp.inner_apply, Real.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ≤ j
  · rw [hxy i hi]
  · simp only [hz i (lt_of_not_ge hi), mul_zero]

lemma field_prefix_eq {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -(1 / (8 * L₁ * Real.sqrt m)) ≤ x j)
    (hxt : ∀ i, j < i → x i ≤ 1 / (8 * L₁ * Real.sqrt m))
    (hyt : ∀ i, j < i → y i ≤ 1 / (8 * L₁ * Real.sqrt m)) :
    field m L₀ L₁ ε x = field m L₀ L₁ ε y := by
  let σ := shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε)
  let u := field m L₀ L₁ ε x
  let v := field m L₀ L₁ ε y
  have hG := weight_pos m L₁ ε hL₁ hε
  have hB := (peak_pos m L₁ ε hL₁ hε).le
  have hGB := weight_le_peak hm L₁ ε hL₁ hε
  have hK := feasible_compact (weight m L₁ ε) (peak m L₁ ε) hG hB hGB
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε)
  have hu := maximizer_spec hK ⟨0, feasible_zero _⟩ hH (x + σ)
  have hv := maximizer_spec hK ⟨0, feasible_zero _⟩ hH (y + σ)
  have hu0 (i : Fin m) (hi : j < i) : u i = 0 :=
    field_tail_zero hm L₀ L₁ ε hL₀ hL₁ hε j i hi x hxj (hxt i hi)
  have hyj : -(1 / (8 * L₁ * Real.sqrt m)) ≤ y j := by rw [← hxy j le_rfl]; exact hxj
  have hv0 (i : Fin m) (hi : j < i) : v i = 0 :=
    field_tail_zero hm L₀ L₁ ε hL₀ hL₁ hε j i hi y hyj (hyt i hi)
  have hab (i : Fin m) (hi : i ≤ j) : (x + σ) i = (y + σ) i := by
    change x i + σ i = y i + σ i
    rw [hxy i hi]
  have heu := inner_prefix_eq j (x + σ) (y + σ) u hab hu0
  have hev := inner_prefix_eq j (x + σ) (y + σ) v hab hv0
  have hg := dual_optimizer_growth hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε)
    (x + σ) u v hu.1 hv.1 hu.2
  have hvu : ⟪y + σ, u⟫ - dual L₀ L₁ u ≤ ⟪y + σ, v⟫ - dual L₀ L₁ v := hv.2 hu.1
  rw [heu, hev] at hg
  have hn : ‖u - v‖ ^ 2 / (2 * (L₀ + L₁ * max ‖u‖ ‖v‖)) ≤ 0 := by linarith
  have hp : 0 < 2 * (L₀ + L₁ * max ‖u‖ ‖v‖) := by positivity
  have hs := (div_le_iff₀ hp).mp hn
  have he : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

lemma objective_remainder {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (x y : EuclideanSpace ℝ (Fin m)) :
    0 ≤ objective m L₀ L₁ ε y - objective m L₀ L₁ ε x - ⟪field m L₀ L₁ ε x, y - x⟫ ∧
    objective m L₀ L₁ ε y - objective m L₀ L₁ ε x - ⟪field m L₀ L₁ ε x, y - x⟫ ≤
      (L₀ + L₁ * peak m L₁ ε) * ‖y - x‖ ^ 2 := by
  let σ := shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε)
  have hG := weight_pos m L₁ ε hL₁ hε
  have hB := (peak_pos m L₁ ε hL₁ hε).le
  have hGB := weight_le_peak hm L₁ ε hL₁ hε
  have hK := feasible_compact (weight m L₁ ε) (peak m L₁ ε) hG hB hGB
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε)
  have hu := maximizer_spec hK ⟨0, feasible_zero _⟩ hH (x + σ)
  have hv := maximizer_spec hK ⟨0, feasible_zero _⟩ hH (y + σ)
  have hd : ‖field m L₀ L₁ ε y - field m L₀ L₁ ε x‖ ≤
      (L₀ + L₁ * peak m L₁ ε) * ‖(y + σ) - (x + σ)‖ := by
    rw [add_sub_add_right_eq_sub]
    apply (field_pair hm L₀ L₁ ε hL₀ hL₁ hε y x).trans
    gcongr
    exact max_le (field_norm_bound hm L₀ L₁ ε hL₀ hL₁ hε y)
      (field_norm_bound hm L₀ L₁ ε hL₀ hL₁ hε x)
  have hh := value_remainder_bound (dual L₀ L₁) (x + σ) (y + σ)
    (field m L₀ L₁ ε x) (field m L₀ L₁ ε y) (L₀ + L₁ * peak m L₁ ε)
    (hu.2 hv.1) (hv.2 hu.1) hd
  simpa only [add_sub_add_right_eq_sub, objective, value, field, σ] using hh

lemma objective_convex {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) :
    ConvexOn ℝ univ (objective m L₀ L₁ ε) := by
  let σ := shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε)
  have hG := weight_pos m L₁ ε hL₁ hε
  have hB := (peak_pos m L₁ ε hL₁ hε).le
  have hGB := weight_le_peak hm L₁ ε hL₁ hε
  have hK := feasible_compact (weight m L₁ ε) (peak m L₁ ε) hG hB hGB
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε)
  have hc := value_convex hK ⟨0, feasible_zero _⟩ hH
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hh := hc.2 (mem_univ (x + σ)) (mem_univ (y + σ)) ha hb hab
  have he : a • (x + σ) + b • (y + σ) = (a • x + b • y) + σ := by
    calc
      _ = (a • x + b • y) + (a + b) • σ := by simp only [smul_add, add_smul]; abel
      _ = _ := by rw [hab, one_smul]
  rw [he] at hh
  exact hh

lemma field_lipschitz {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) :
    LipschitzWith ⟨L₀ + L₁ * peak m L₁ ε, by have hp := peak_pos m L₁ ε hL₁ hε; positivity⟩
      (field m L₀ L₁ ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖field m L₀ L₁ ε x - field m L₀ L₁ ε y‖ ≤ (L₀ + L₁ * peak m L₁ ε) * ‖x - y‖
  apply (field_pair hm L₀ L₁ ε hL₀ hL₁ hε x y).trans
  gcongr
  exact max_le (field_norm_bound hm L₀ L₁ ε hL₀ hL₁ hε x)
    (field_norm_bound hm L₀ L₁ ε hL₀ hL₁ hε y)

lemma objective_prefix_eq {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -(1 / (8 * L₁ * Real.sqrt m)) ≤ x j)
    (hxt : ∀ i, j < i → x i ≤ 1 / (8 * L₁ * Real.sqrt m))
    (hyt : ∀ i, j < i → y i ≤ 1 / (8 * L₁ * Real.sqrt m)) :
    objective m L₀ L₁ ε x = objective m L₀ L₁ ε y := by
  let σ := shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε)
  have hg := field_prefix_eq hm L₀ L₁ ε hL₀ hL₁ hε j x y hxy hxj hxt hyt
  have hyj : -(1 / (8 * L₁ * Real.sqrt m)) ≤ y j := by rw [← hxy j le_rfl]; exact hxj
  have hz (i : Fin m) (hi : j < i) : field m L₀ L₁ ε y i = 0 :=
    field_tail_zero hm L₀ L₁ ε hL₀ hL₁ hε j i hi y hyj (hyt i hi)
  have he := inner_prefix_eq j (x + σ) (y + σ) (field m L₀ L₁ ε y)
    (fun i hi => by change x i + σ i = y i + σ i; rw [hxy i hi]) hz
  change ⟪x + σ, field m L₀ L₁ ε x⟫ - dual L₀ L₁ (field m L₀ L₁ ε x) =
    ⟪y + σ, field m L₀ L₁ ε y⟫ - dual L₀ L₁ (field m L₀ L₁ ε y)
  rw [hg, he]

end LongTails.Proofs.GeneralizedSmoothHardChain

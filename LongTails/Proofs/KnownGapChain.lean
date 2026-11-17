import LongTails.Proofs.KnownGapChainWeights

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.KnownGapChain

open GeneralizedSmoothHardDual GeneralizedSmoothHardDualSegments GeneralizedSmoothHardTransfer
open CompactConjugate GeneralizedSmoothHardChain KnownGapChainWeights

noncomputable def objective (m : ℕ) (L₀ L₁ ε h : ℝ) (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  value (feasible (weight m L₁ ε h)) (dual L₀ L₁)
    (y + shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h))

noncomputable def field (m : ℕ) (L₀ L₁ ε h : ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  maximizer (feasible (weight m L₁ ε h)) (dual L₀ L₁)
    (y + shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h))

section

variable {m : ℕ} (hm : 0 < m) (L₀ L₁ ε h : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε)
  (hh : 0 < h)

include hm hL₀ hL₁ hε hh

lemma field_tail_zero (j l : Fin m) (hjl : j < l)
    (y : EuclideanSpace ℝ (Fin m)) (hyj : -(margin L₁ h) ≤ y j)
    (hyl : y l ≤ margin L₁ h) : field m L₀ L₁ ε h y l = 0 := by
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hK := feasible_compact (weight m L₁ ε h) (peak m L₁ ε h) hG hB hGB
  have hne : (feasible (weight m L₁ ε h)).Nonempty := ⟨0, feasible_zero _⟩
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
  have hu := maximizer_spec hK hne hH (y + shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h))
  exact shifted_optimizer_tail_zero hm L₀ L₁ (peak m L₁ ε h) _ hL₀ hL₁ (weight m L₁ ε h)
    hG hB hGB j l hjl (weight_strict_order L₁ ε h hL₁ hε hh j l hjl).le y _ hu.1 hu.2 hyj hyl
    (weight_margin L₁ ε h hL₁ hε hh j l hjl)

lemma objective_vertex_bound (i : Fin m) (y : EuclideanSpace ℝ (Fin m)) :
    weight m L₁ ε h i * (y i + 2 / L₁) ≤ objective m L₀ L₁ ε h y := by
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hK := feasible_compact (weight m L₁ ε h) (peak m L₁ ε h) hG hB hGB
  have hne : (feasible (weight m L₁ ε h)).Nonempty := ⟨0, feasible_zero _⟩
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
  have hu := maximizer_spec hK hne hH (y + shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h))
  exact (shifted_vertex_bound hm L₀ L₁ _ hL₀ hL₁ _ hG i (hGB i) y).trans
    (hu.2 (vertex_feasible _ hG i))

lemma objective_gap (i : Fin m) (y : EuclideanSpace ℝ (Fin m))
    (hy : -(margin L₁ h) ≤ y i) : 15 * ε / 4 ≤ objective m L₀ L₁ ε h y := by
  have ht := margin_le L₁ h hL₁
  have hy' : 15 / (8 * L₁) ≤ y i + 2 / L₁ := by
    have he : 2 / L₁ - 1 / (8 * L₁) = 15 / (8 * L₁) := by ring
    linarith
  have hh' := mul_le_mul (weight_lower L₁ ε h hL₁ hε hh.le i) hy'
    (show 0 ≤ 15 / (8 * L₁) by positivity) (weight_pos m L₁ ε h hL₁ hε i).le
  have he : 2 * ε * L₁ * (15 / (8 * L₁)) = 15 * ε / 4 := by field_simp; ring
  rw [he] at hh'
  exact hh'.trans (objective_vertex_bound hm L₀ L₁ ε h hL₀ hL₁ hε hh i y)

lemma objective_hasGradientAt (y : EuclideanSpace ℝ (Fin m)) :
    HasGradientAt (objective m L₀ L₁ ε h) (field m L₀ L₁ ε h y) y := by
  have hh' := conjugate_hasGradientAt hm L₀ L₁ (peak m L₁ ε h) hL₀ hL₁
    (weight m L₁ ε h) (weight_pos m L₁ ε h hL₁ hε) (peak_pos m L₁ ε h hL₁ hε).le
    (weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le) (y + shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h))
  rw [hasGradientAt_iff_hasFDerivAt]
  have ht := hh'.hasFDerivAt.comp y ((hasFDerivAt_id y).add_const
    (shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h)))
  convert ht using 1
  · rfl
  · simp only [ContinuousLinearMap.comp_id, field]

lemma field_pair (x y : EuclideanSpace ℝ (Fin m)) :
    ‖field m L₀ L₁ ε h x - field m L₀ L₁ ε h y‖ ≤
      (L₀ + L₁ * max ‖field m L₀ L₁ ε h x‖ ‖field m L₀ L₁ ε h y‖) * ‖x - y‖ := by
  have hh' := conjugate_field_pair hm L₀ L₁ (peak m L₁ ε h) hL₀ hL₁
    (weight m L₁ ε h) (weight_pos m L₁ ε h hL₁ hε) (peak_pos m L₁ ε h hL₁ hε).le
    (weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le)
    (x + shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h))
    (y + shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h))
  simpa only [field, add_sub_add_right_eq_sub] using hh'

lemma field_norm_bound (y : EuclideanSpace ℝ (Fin m)) :
    ‖field m L₀ L₁ ε h y‖ ≤ peak m L₁ ε h := by
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hK := feasible_compact (weight m L₁ ε h) (peak m L₁ ε h) hG hB hGB
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
  exact feasible_norm_bound _ _ hG hB hGB _
    (maximizer_spec hK ⟨0, feasible_zero _⟩ hH _).1

lemma objective_nonnegative (y : EuclideanSpace ℝ (Fin m)) :
    0 ≤ objective m L₀ L₁ ε h y :=
  conjugate_nonnegative hm L₀ L₁ (peak m L₁ ε h) hL₀ hL₁
    (weight m L₁ ε h) (weight_pos m L₁ ε h hL₁ hε) (peak_pos m L₁ ε h hL₁ hε).le
    (weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le) _

lemma objective_zero (y : EuclideanSpace ℝ (Fin m))
    (hy : ∀ i, y i + shiftCoordinate L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h) i ≤ 0) :
    objective m L₀ L₁ ε h y = 0 :=
  conjugate_zero_of_nonpositive hm L₀ L₁ (peak m L₁ ε h) hL₀ hL₁
    (weight m L₁ ε h) (weight_pos m L₁ ε h hL₁ hε) (peak_pos m L₁ ε h hL₁ hε).le
    (weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le) _ hy

omit hm hL₀ in
lemma feasible_sum_le_peak (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ feasible (weight m L₁ ε h)) :
    ∑ i, z i ≤ peak m L₁ ε h := by
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  obtain ⟨hz0, hz1⟩ := hz
  have hterm (i : Fin m) : z i ≤ peak m L₁ ε h * (z i / weight m L₁ ε h i) := by
    rw [mul_div_assoc', le_div_iff₀ (hG i)]
    have := mul_le_mul_of_nonneg_left (hGB i) (hz0 i)
    linarith
  calc ∑ i, z i ≤ ∑ i, peak m L₁ ε h * (z i / weight m L₁ ε h i) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = peak m L₁ ε h * ∑ i, z i / weight m L₁ ε h i := by rw [Finset.mul_sum]
    _ ≤ peak m L₁ ε h * 1 := mul_le_mul_of_nonneg_left hz1 hB
    _ = peak m L₁ ε h := mul_one _

lemma objective_upper (y : EuclideanSpace ℝ (Fin m)) (M : ℝ) (hM : 0 ≤ M)
    (hy : ∀ i, y i + shiftCoordinate L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h) i ≤ M) :
    objective m L₀ L₁ ε h y ≤ peak m L₁ ε h * M := by
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hK := feasible_compact (weight m L₁ ε h) (peak m L₁ ε h) hG hB hGB
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
  set σ := shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h)
  have hu := maximizer_spec hK ⟨0, feasible_zero _⟩ hH (y + σ)
  set u := maximizer (feasible (weight m L₁ ε h)) (dual L₀ L₁) (y + σ)
  have hd := (dual_bound hm L₀ L₁ hL₀ hL₁ u hu.1.1).1
  have hinner : ⟪y + σ, u⟫ ≤ M * ∑ i, u i := by
    simp only [PiLp.inner_apply, Real.inner_apply, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hui := hu.1.1 i
    have hyi : (y + σ) i ≤ M := hy i
    change (y + σ) i * u i ≤ M * u i
    nlinarith
  have hsum := feasible_sum_le_peak L₁ ε h hL₁ hε hh u hu.1
  change ⟪y + σ, u⟫ - dual L₀ L₁ u ≤ peak m L₁ ε h * M
  nlinarith [mul_le_mul_of_nonneg_left hsum hM]

lemma field_prefix_eq (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -(margin L₁ h) ≤ x j)
    (hxt : ∀ i, j < i → x i ≤ margin L₁ h)
    (hyt : ∀ i, j < i → y i ≤ margin L₁ h) :
    field m L₀ L₁ ε h x = field m L₀ L₁ ε h y := by
  let σ := shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h)
  let u := field m L₀ L₁ ε h x
  let v := field m L₀ L₁ ε h y
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hK := feasible_compact (weight m L₁ ε h) (peak m L₁ ε h) hG hB hGB
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
  have hu := maximizer_spec hK ⟨0, feasible_zero _⟩ hH (x + σ)
  have hv := maximizer_spec hK ⟨0, feasible_zero _⟩ hH (y + σ)
  have hu0 (i : Fin m) (hi : j < i) : u i = 0 :=
    field_tail_zero hm L₀ L₁ ε h hL₀ hL₁ hε hh j i hi x hxj (hxt i hi)
  have hyj : -(margin L₁ h) ≤ y j := by rw [← hxy j le_rfl]; exact hxj
  have hv0 (i : Fin m) (hi : j < i) : v i = 0 :=
    field_tail_zero hm L₀ L₁ ε h hL₀ hL₁ hε hh j i hi y hyj (hyt i hi)
  have hab (i : Fin m) (hi : i ≤ j) : (x + σ) i = (y + σ) i := by
    change x i + σ i = y i + σ i
    rw [hxy i hi]
  have heu := inner_prefix_eq j (x + σ) (y + σ) u hab hu0
  have hev := inner_prefix_eq j (x + σ) (y + σ) v hab hv0
  have hg := dual_optimizer_growth hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
    (x + σ) u v hu.1 hv.1 hu.2
  have hvu : ⟪y + σ, u⟫ - dual L₀ L₁ u ≤ ⟪y + σ, v⟫ - dual L₀ L₁ v := hv.2 hu.1
  rw [heu, hev] at hg
  have hn : ‖u - v‖ ^ 2 / (2 * (L₀ + L₁ * max ‖u‖ ‖v‖)) ≤ 0 := by linarith
  have hp : 0 < 2 * (L₀ + L₁ * max ‖u‖ ‖v‖) := by positivity
  have hs := (div_le_iff₀ hp).mp hn
  have he : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

lemma objective_remainder (x y : EuclideanSpace ℝ (Fin m)) :
    0 ≤ objective m L₀ L₁ ε h y - objective m L₀ L₁ ε h x - ⟪field m L₀ L₁ ε h x, y - x⟫ ∧
    objective m L₀ L₁ ε h y - objective m L₀ L₁ ε h x - ⟪field m L₀ L₁ ε h x, y - x⟫ ≤
      (L₀ + L₁ * peak m L₁ ε h) * ‖y - x‖ ^ 2 := by
  let σ := shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h)
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hK := feasible_compact (weight m L₁ ε h) (peak m L₁ ε h) hG hB hGB
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
  have hu := maximizer_spec hK ⟨0, feasible_zero _⟩ hH (x + σ)
  have hv := maximizer_spec hK ⟨0, feasible_zero _⟩ hH (y + σ)
  have hd : ‖field m L₀ L₁ ε h y - field m L₀ L₁ ε h x‖ ≤
      (L₀ + L₁ * peak m L₁ ε h) * ‖(y + σ) - (x + σ)‖ := by
    rw [add_sub_add_right_eq_sub]
    apply (field_pair hm L₀ L₁ ε h hL₀ hL₁ hε hh y x).trans
    gcongr
    exact max_le (field_norm_bound hm L₀ L₁ ε h hL₀ hL₁ hε hh y)
      (field_norm_bound hm L₀ L₁ ε h hL₀ hL₁ hε hh x)
  have hh' := value_remainder_bound (dual L₀ L₁) (x + σ) (y + σ)
    (field m L₀ L₁ ε h x) (field m L₀ L₁ ε h y) (L₀ + L₁ * peak m L₁ ε h)
    (hu.2 hv.1) (hv.2 hu.1) hd
  simpa only [add_sub_add_right_eq_sub, objective, value, field, σ] using hh'

lemma objective_convex : ConvexOn ℝ univ (objective m L₀ L₁ ε h) := by
  let σ := shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h)
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hK := feasible_compact (weight m L₁ ε h) (peak m L₁ ε h) hG hB hGB
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
  have hc := value_convex hK ⟨0, feasible_zero _⟩ hH
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hh' := hc.2 (mem_univ (x + σ)) (mem_univ (y + σ)) ha hb hab
  have he : a • (x + σ) + b • (y + σ) = (a • x + b • y) + σ := by
    calc
      _ = (a • x + b • y) + (a + b) • σ := by simp only [smul_add, add_smul]; abel
      _ = _ := by rw [hab, one_smul]
  rw [he] at hh'
  exact hh'

lemma field_lipschitz :
    LipschitzWith ⟨L₀ + L₁ * peak m L₁ ε h,
      by have hp := peak_pos m L₁ ε h hL₁ hε; positivity⟩ (field m L₀ L₁ ε h) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖field m L₀ L₁ ε h x - field m L₀ L₁ ε h y‖ ≤ (L₀ + L₁ * peak m L₁ ε h) * ‖x - y‖
  apply (field_pair hm L₀ L₁ ε h hL₀ hL₁ hε hh x y).trans
  gcongr
  exact max_le (field_norm_bound hm L₀ L₁ ε h hL₀ hL₁ hε hh x)
    (field_norm_bound hm L₀ L₁ ε h hL₀ hL₁ hε hh y)

lemma objective_prefix_eq (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -(margin L₁ h) ≤ x j)
    (hxt : ∀ i, j < i → x i ≤ margin L₁ h)
    (hyt : ∀ i, j < i → y i ≤ margin L₁ h) :
    objective m L₀ L₁ ε h x = objective m L₀ L₁ ε h y := by
  let σ := shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h)
  have hg := field_prefix_eq hm L₀ L₁ ε h hL₀ hL₁ hε hh j x y hxy hxj hxt hyt
  have hyj : -(margin L₁ h) ≤ y j := by rw [← hxy j le_rfl]; exact hxj
  have hz (i : Fin m) (hi : j < i) : field m L₀ L₁ ε h y i = 0 :=
    field_tail_zero hm L₀ L₁ ε h hL₀ hL₁ hε hh j i hi y hyj (hyt i hi)
  have he := inner_prefix_eq j (x + σ) (y + σ) (field m L₀ L₁ ε h y)
    (fun i hi => by change x i + σ i = y i + σ i; rw [hxy i hi]) hz
  change ⟪x + σ, field m L₀ L₁ ε h x⟫ - dual L₀ L₁ (field m L₀ L₁ ε h x) =
    ⟪y + σ, field m L₀ L₁ ε h y⟫ - dual L₀ L₁ (field m L₀ L₁ ε h y)
  rw [hg, he]

end

end LongTails.Proofs.KnownGapChain

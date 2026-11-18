import LongTails.Proofs.TailEntropySegments

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.TailEntropyConjugate

open TailEntropyDual TailEntropySegments CompactConjugate
open GeneralizedSmoothHardDual (radial radial_derivative radial_nonneg feasible feasible_zero
  feasible_compact feasible_convex feasible_norm_bound)
open GeneralizedSmoothHardDualSegments (path)

section

variable {m : ℕ} (L₀ L₁ : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ)

include hL₀ hL₁

lemma dual_optimizer_growth (a u v : EuclideanSpace ℝ (Fin m)) (hu : u ∈ feasible G)
    (hv : v ∈ feasible G)
    (hopt : IsMaxOn (fun z => ⟪a, z⟫ - dual L₀ L₁ z) (feasible G) u) :
    ⟪a, v⟫ - dual L₀ L₁ v + ‖u - v‖ ^ 2 / (2 * (L₀ + L₁ * max ‖u‖ ‖v‖)) ≤
      ⟪a, u⟫ - dual L₀ L₁ u := by
  apply maximizer_growth_of_segment
  · intro t ht
    have hh := dual_segment_bound L₀ L₁ hL₀ hL₁ u v hu.1 hv.1 t ht
    change dual L₀ L₁ (path u v t) ≤ _
    rw [norm_sub_rev v] at hh
    convert hh using 1
    field_simp
  · intro t ht
    exact hopt ((feasible_convex G) hu hv (sub_nonneg.mpr ht.2) ht.1 (by ring))

lemma dual_optimizer_distance (a b u v : EuclideanSpace ℝ (Fin m)) (hu : u ∈ feasible G)
    (hv : v ∈ feasible G)
    (hoptu : IsMaxOn (fun z => ⟪a, z⟫ - dual L₀ L₁ z) (feasible G) u)
    (hoptv : IsMaxOn (fun z => ⟪b, z⟫ - dual L₀ L₁ z) (feasible G) v) :
    ‖u - v‖ ≤ (L₀ + L₁ * max ‖u‖ ‖v‖) * ‖a - b‖ := by
  have hu' := dual_optimizer_growth L₀ L₁ hL₀ hL₁ G a u v hu hv hoptu
  have hv' := dual_optimizer_growth L₀ L₁ hL₀ hL₁ G b v u hv hu hoptv
  rw [norm_sub_rev v, max_comm ‖v‖] at hv'
  exact maximizer_distance_bound (dual L₀ L₁) a b u v _ (by positivity) hu' hv'

variable (B : ℝ) (hG : ∀ i, 0 < G i) (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B)

include hG hB hGB

lemma conjugate_hasGradientAt (a : EuclideanSpace ℝ (Fin m)) :
    HasGradientAt (value (feasible G) (dual L₀ L₁))
      (maximizer (feasible G) (dual L₀ L₁) a) a := by
  have hK := feasible_compact G B hG hB hGB
  have hne : (feasible G).Nonempty := ⟨0, feasible_zero G⟩
  have hH := dual_continuousOn_feasible L₀ L₁ hL₀ hL₁ G
  apply value_hasGradientAt hK hne hH (L₀ + L₁ * B) (by positivity)
  intro x v hv
  have hu := maximizer_spec hK hne hH x
  have hg := dual_optimizer_growth L₀ L₁ hL₀ hL₁ G x _ v hu.1 hv hu.2
  apply le_trans _ hg
  gcongr
  apply max_le
  · exact feasible_norm_bound G B hG hB hGB _ hu.1
  · exact feasible_norm_bound G B hG hB hGB v hv

lemma conjugate_field_pair (a b : EuclideanSpace ℝ (Fin m)) :
    let g := maximizer (feasible G) (dual L₀ L₁)
    ‖g a - g b‖ ≤ (L₀ + L₁ * max ‖g a‖ ‖g b‖) * ‖a - b‖ := by
  have hK := feasible_compact G B hG hB hGB
  have hne : (feasible G).Nonempty := ⟨0, feasible_zero G⟩
  have hH := dual_continuousOn_feasible L₀ L₁ hL₀ hL₁ G
  have ha := maximizer_spec hK hne hH a
  have hb := maximizer_spec hK hne hH b
  exact dual_optimizer_distance L₀ L₁ hL₀ hL₁ G a b _ _ ha.1 hb.1 ha.2 hb.2

lemma conjugate_nonnegative (a : EuclideanSpace ℝ (Fin m)) :
    0 ≤ value (feasible G) (dual L₀ L₁) a := by
  have hh := (maximizer_spec (feasible_compact G B hG hB hGB) ⟨0, feasible_zero G⟩
    (dual_continuousOn_feasible L₀ L₁ hL₀ hL₁ G) a).2 (feasible_zero G)
  change ⟪a, (0 : EuclideanSpace ℝ (Fin m))⟫ - dual L₀ L₁ 0 ≤
    value (feasible G) (dual L₀ L₁) a at hh
  simpa only [inner_zero_right, dual_zero, sub_zero] using hh

lemma conjugate_zero_of_nonpositive (a : EuclideanSpace ℝ (Fin m)) (ha : ∀ i, a i ≤ 0) :
    value (feasible G) (dual L₀ L₁) a = 0 := by
  apply le_antisymm _ (conjugate_nonnegative L₀ L₁ hL₀ hL₁ G B hG hB hGB a)
  have hu := (maximizer_spec (feasible_compact G B hG hB hGB) ⟨0, feasible_zero G⟩
    (dual_continuousOn_feasible L₀ L₁ hL₀ hL₁ G) a).1
  have hn := dual_nonneg L₀ L₁ hL₀ hL₁ _ hu.1
  have hi : ⟪a, maximizer (feasible G) (dual L₀ L₁) a⟫ ≤ 0 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_nonpos
    intro i _
    simp only [Real.inner_apply]
    exact mul_nonpos_of_nonpos_of_nonneg (ha i) (hu.1 i)
  unfold value
  linarith

end

lemma radial_derivative_mono (L₀ L₁ a b : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (ha : 0 ≤ a)
    (hab : a ≤ b) : Real.log (1 + L₁ * a / L₀) / L₁ ≤ Real.log (1 + L₁ * b / L₀) / L₁ := by
  apply div_le_div_of_nonneg_right _ hL₁.le
  apply Real.log_le_log (by positivity)
  have : L₁ * a / L₀ ≤ L₁ * b / L₀ := by gcongr
  linarith

lemma radial_sub_le (L₀ L₁ a b B : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (ha : 0 ≤ a)
    (hab : a ≤ b) (hbB : b ≤ B) :
    radial L₀ L₁ b - radial L₀ L₁ a ≤ (b - a) * (Real.log (1 + L₁ * B / L₀) / L₁) := by
  rcases hab.eq_or_lt with he | hlt
  · subst he; simp
  have hcont : ContinuousOn (radial L₀ L₁) (Icc a b) := fun s hs =>
    (radial_derivative L₀ L₁ s hL₀ hL₁ (ha.trans hs.1)).continuousAt.continuousWithinAt
  have hdiff : ∀ s ∈ Ioo a b, HasDerivAt (radial L₀ L₁) (Real.log (1 + L₁ * s / L₀) / L₁) s :=
    fun s hs => radial_derivative L₀ L₁ s hL₀ hL₁ (ha.trans hs.1.le)
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (radial L₀ L₁)
    (fun s => Real.log (1 + L₁ * s / L₀) / L₁) hlt hcont hdiff
  have hmono := radial_derivative_mono L₀ L₁ c B hL₀ hL₁ (ha.trans hc.1.le)
    (hc.2.le.trans hbB)
  rw [eq_div_iff (by linarith : b - a ≠ 0)] at hceq
  nlinarith

lemma radial_le (L₀ L₁ b B : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hb : 0 ≤ b) (hbB : b ≤ B) :
    radial L₀ L₁ b ≤ b * (Real.log (1 + L₁ * B / L₀) / L₁) := by
  have h := radial_sub_le L₀ L₁ 0 b B hL₀ hL₁ le_rfl hb hbB
  simpa [radial] using h

end LongTails.Proofs.TailEntropyConjugate

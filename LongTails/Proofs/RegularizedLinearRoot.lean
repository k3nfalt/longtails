import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

open Topology

namespace OracleTemplate.RegularizedLinearRoot

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma affine_sphere (s v : E) {r : ℝ} (hv : v ≠ 0) (hr : ‖s‖ ≤ r) :
    ∃ t : ℝ, ‖s + t • v‖ = r := by
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hr
  let T := (r + ‖s‖) / ‖v‖
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hnorm : ‖T • v‖ = r + ‖s‖ := by
    rw [norm_smul, Real.norm_of_nonneg hT]
    dsimp [T]
    field_simp
  have hlarge : r ≤ ‖s + T • v‖ := by
    have hh := norm_sub_le (s + T • v) s
    rw [show s + T • v - s = T • v by abel, hnorm] at hh
    linarith
  have hc : Continuous (fun t : ℝ => ‖s + t • v‖) := by fun_prop
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc hT hc.continuousOn
    (show r ∈ Set.Icc ‖s + (0 : ℝ) • v‖ ‖s + T • v‖ from ⟨by simpa using hr, hlarge⟩)
  exact ⟨t, ht⟩

lemma singular_affine_sphere (A : E →L[ℝ] E) (s v : E) {r : ℝ}
    (hv : v ≠ 0) (hAv : A v = 0) (hr : ‖s‖ ≤ r) :
    ∃ w : E, A w = A s ∧ ‖w‖ = r := by
  obtain ⟨t, ht⟩ := affine_sphere s v hv hr
  exact ⟨s + t • v, by simp [hAv], ht⟩

lemma shifted_injective (J : E →L[ℝ] E) {α : ℝ} (hα : ‖J‖ < α) :
    Function.Injective (J + α • ContinuousLinearMap.id ℝ E) := by
  apply (J + α • ContinuousLinearMap.id ℝ E).toLinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have he : J v = -(α • v) := by
    apply eq_neg_of_add_eq_zero_left
    simpa using hv
  have hn := J.le_opNorm v
  rw [he, norm_neg, norm_smul, Real.norm_of_nonneg ((norm_nonneg J).trans hα.le)] at hn
  have hz : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  exact norm_eq_zero.mp hz

lemma large_feasible [FiniteDimensional ℝ E] (J : E →L[ℝ] E) (g : E)
    {k : ℝ} (hk : 0 < k) :
    ∃ α : ℝ, ∃ s : E, 0 < α ∧ J s + α • s = -g ∧ ‖s‖ ≤ α / k := by
  let α := ‖J‖ + k + ‖g‖ + 1
  have hα : ‖J‖ < α := by dsimp [α]; linarith [norm_nonneg g]
  have hi := shifted_injective J hα
  have hs : Function.Surjective (J + α • ContinuousLinearMap.id ℝ E) :=
    (LinearMap.injective_iff_surjective (f := (J + α • ContinuousLinearMap.id ℝ E).toLinearMap)).mp hi
  obtain ⟨s, hs⟩ := hs (-g)
  have he : J s + α • s = -g := by simpa using hs
  have he' : α • s = -g - J s := by rw [← he]; abel
  have hnorm := norm_sub_le (-g) (J s)
  rw [norm_neg, ← he', norm_smul, Real.norm_of_nonneg ((norm_nonneg J).trans hα.le)] at hnorm
  have hj := J.le_opNorm s
  have hbound : (k + ‖g‖ + 1) * ‖s‖ ≤ ‖g‖ := by dsimp [α] at hnorm; nlinarith
  have hs1 : ‖s‖ ≤ 1 := by nlinarith [norm_nonneg g, norm_nonneg s]
  refine ⟨α, s, (norm_nonneg J).trans_lt hα, he, hs1.trans ?_⟩
  rw [le_div_iff₀ hk]
  dsimp [α]
  nlinarith [norm_nonneg J, norm_nonneg g]

lemma minimal_feasible [FiniteDimensional ℝ E] (J : E →L[ℝ] E) (g : E)
    {k : ℝ} (hk : 0 < k) :
    ∃ α : ℝ, ∃ s : E, 0 ≤ α ∧ J s + α • s = -g ∧ ‖s‖ ≤ α / k ∧
      ∀ β : ℝ, ∀ t : E, 0 ≤ β → J t + β • t = -g → ‖t‖ ≤ β / k → α ≤ β := by
  obtain ⟨A, u, hA, hu, hnu⟩ := large_feasible J g hk
  let S : Set (ℝ × E) := {p | 0 ≤ p.1 ∧ p.1 ≤ A ∧
    J p.2 + p.1 • p.2 = -g ∧ ‖p.2‖ ≤ p.1 / k}
  have hSc : IsClosed S := by
    apply IsClosed.inter (isClosed_le continuous_const continuous_fst)
    apply IsClosed.inter (isClosed_le continuous_fst continuous_const)
    exact (isClosed_eq (show Continuous (fun p : ℝ × E => J p.2 + p.1 • p.2) by fun_prop)
      (show Continuous (fun _ : ℝ × E => -g) by fun_prop)).inter
      (isClosed_le (show Continuous (fun p : ℝ × E => ‖p.2‖) by fun_prop)
        (show Continuous (fun p : ℝ × E => p.1 / k) by fun_prop))
  have hSb : S ⊆ Set.Icc (0 : ℝ) A ×ˢ Metric.closedBall (0 : E) (A / k) := by
    rintro ⟨a, s⟩ ⟨h0, ha, _, hn⟩
    refine ⟨⟨h0, ha⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hn.trans (div_le_div_of_nonneg_right ha hk.le)
  have hcompact : IsCompact S :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : E) (A / k))).of_isClosed_subset hSc hSb
  have hSne : S.Nonempty := ⟨(A, u), hA.le, le_rfl, hu, hnu⟩
  obtain ⟨⟨α, s⟩, hmem, hmin⟩ := hcompact.exists_isMinOn hSne continuous_fst.continuousOn
  refine ⟨α, s, hmem.1, hmem.2.2.1, hmem.2.2.2, ?_⟩
  intro β t hβ ht hnt
  by_cases hβA : β ≤ A
  · exact hmin (show (β, t) ∈ S from ⟨hβ, hβA, ht, hnt⟩)
  · exact hmem.2.1.trans (le_of_not_ge hβA)

lemma smaller_feasible_of_unit [CompleteSpace E] (J : E →L[ℝ] E) (g s : E)
    {α k : ℝ} (hα : 0 < α) (hu : IsUnit (J + α • ContinuousLinearMap.id ℝ E))
    (he : J s + α • s = -g) (hn : ‖s‖ < α / k) :
    ∃ β : ℝ, ∃ t : E, 0 ≤ β ∧ β < α ∧ J t + β • t = -g ∧ ‖t‖ ≤ β / k := by
  let A : ℝ → E →L[ℝ] E := fun β => J + β • ContinuousLinearMap.id ℝ E
  let t : ℝ → E := fun β => Ring.inverse (A β) (-g)
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have huA : IsUnit (A α) := hu
  have hsolve : ∀ β, IsUnit (A β) → A β (t β) = -g := by
    intro β hβ
    have hh := congrArg (fun B : E →L[ℝ] E => B (-g)) (Ring.mul_inverse_cancel (A β) hβ)
    simpa [t, mul_apply_eq_comp] using hh
  have htα : t α = s := by
    apply (ContinuousLinearMap.isUnit_iff_bijective.mp huA).1
    rw [hsolve α huA]
    exact he.symm
  have htc : ContinuousAt t α := by
    rcases huA with ⟨u, hu⟩
    have hInv : ContinuousAt Ring.inverse (A α) := hu ▸ NormedRing.inverse_continuousAt u
    exact (hInv.comp hAc.continuousAt).clm_apply continuousAt_const
  have hnear : ∀ᶠ β in 𝓝 α, 0 < β ∧ IsUnit (A β) ∧ ‖t β‖ < β / k := by
    have hpos : ∀ᶠ β in 𝓝 α, 0 < β := eventually_gt_nhds hα
    have hunit : ∀ᶠ β in 𝓝 α, IsUnit (A β) :=
      hAc.continuousAt (Units.isOpen.mem_nhds huA)
    have hnorm : ∀ᶠ β in 𝓝 α, ‖t β‖ < β / k :=
      (htc.norm.eventually_lt (continuousAt_id.div_const k) (by simpa [htα] using hn))
    filter_upwards [hpos, hunit, hnorm] with β h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨l, u, hαlu, hlu⟩ := hnear.exists_Ioo_subset
  obtain ⟨β, hlβ, hβα⟩ := exists_between hαlu.1
  have hβ := hlu (show β ∈ Set.Ioo l u from ⟨hlβ, hβα.trans hαlu.2⟩)
  exact ⟨β, t β, hβ.1.le, hβα, hsolve β hβ.2.1, hβ.2.2.le⟩

lemma exists_root [FiniteDimensional ℝ E] (J : E →L[ℝ] E) (g : E)
    {k : ℝ} (hk : 0 < k) : ∃ s : E, g + J s + (k * ‖s‖) • s = 0 := by
  by_cases hg : g = 0
  · exact ⟨0, by simp [hg]⟩
  obtain ⟨α, s, hα0, he, hn, hmin⟩ := minimal_feasible J g hk
  have hα : 0 < α := by
    by_contra! hh
    have ha0 : α = 0 := le_antisymm hh hα0
    have hs0 : s = 0 := norm_eq_zero.mp (by simpa [ha0] using hn)
    simp only [ha0, hs0, map_zero, zero_smul, add_zero] at he
    exact hg (neg_eq_zero.mp he.symm)
  have hsphere : ∃ w : E, J w + α • w = -g ∧ ‖w‖ = α / k := by
    by_cases hEq : ‖s‖ = α / k
    · exact ⟨s, he, hEq⟩
    have hlt : ‖s‖ < α / k := lt_of_le_of_ne hn hEq
    let A := J + α • ContinuousLinearMap.id ℝ E
    by_cases hu : IsUnit A
    · obtain ⟨β, t, hβ, hβα, ht, hnt⟩ := smaller_feasible_of_unit J g s hα hu he hlt
      exact False.elim (not_le_of_gt hβα (hmin β t hβ ht hnt))
    · have hker : ∃ v : E, v ≠ 0 ∧ A v = 0 := by
        by_contra! hh
        have hi : Function.Injective A := by
          apply A.toLinearMap.ker_eq_bot.mp
          rw [LinearMap.ker_eq_bot']
          intro v hv
          by_contra hne
          exact hh v hne hv
        exact hu (ContinuousLinearMap.isUnit_iff_bijective.mpr
          ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩)
      obtain ⟨v, hv, hAv⟩ := hker
      obtain ⟨w, hw, hnw⟩ := singular_affine_sphere A s v hv hAv hn
      exact ⟨w, hw.trans he, hnw⟩
  obtain ⟨w, hw, hnw⟩ := hsphere
  refine ⟨w, ?_⟩
  have hcoef : k * ‖w‖ = α := by rw [hnw]; field_simp
  rw [hcoef, add_assoc, hw, add_neg_cancel]

end OracleTemplate.RegularizedLinearRoot

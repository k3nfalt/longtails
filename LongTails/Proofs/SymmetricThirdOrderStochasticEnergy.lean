import LongTails.Proofs.SymmetricThirdOrderGoodEvents
import LongTails.Proofs.SymmetricThirdOrderPhasePartition

namespace LongTails.Proofs.SymmetricThirdOrderStochasticEnergy

open LongTails.Algorithms.SymmetricThirdOrder
open LongTails.Proofs.SymmetricThirdOrderEnergy
open LongTails.Proofs.SymmetricThirdOrderPhasePartition
open LongTails.Proofs.CompositeCubicAcceleration
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def potential (f : E → ℝ) (xstar : E) (s : OuterState E) : ℝ :=
  s.weight * (f s.point - f xstar) + ‖s.momentum - xstar‖ ^ 2 / 2

noncomputable def activeDissipation (L δ X : ℝ) (s : OuterState E) (z : E) : ℝ :=
  if X ≤ s.weight then 0 else rawDissipation L δ s z

lemma potential_nonneg (f : E → ℝ) (xstar : E) (s : OuterState E)
    (hmin : ∀ x, f xstar ≤ f x) (hA : 0 ≤ s.weight) : 0 ≤ potential f xstar s := by
  exact add_nonneg (mul_nonneg hA (sub_nonneg.mpr (hmin _))) (by positivity)

lemma activeDissipation_nonneg {L δ X : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (s : OuterState E) (z : E) (hA : 0 ≤ s.weight) : 0 ≤ activeDissipation L δ X s z := by
  unfold activeDissipation
  split
  · rfl
  · unfold rawDissipation
    have hμ : 0 < δ * 4 ^ s.grid := by positivity
    have ha := (trialWeight_pos hμ hA).le
    positivity

lemma outer_energy_step [FiniteDimensional ℝ E] (f : E → ℝ) (C : Set E)
    (fallback xstar : E) {L δ X tolerance : ℝ} (M : ℕ)
    (hC : IsCompact C) (hconv : ConvexOn ℝ C f) (hstar : xstar ∈ C)
    (hL : 0 ≤ L) (hδ : 0 < δ) (s : OuterState E) (z v e : E)
    (hA : 0 ≤ s.weight) (hactive : s.weight < X) (hx : s.point ∈ C) (hz : z ∈ C)
    (hsub : ∀ w ∈ C, f z - f w ≤ ⟪v, z - w⟫)
    (hres : ‖v + (δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2) • (z - outerCenter δ s)‖ ≤
      (3 / 16 : ℝ) * (δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2) * ‖z - outerCenter δ s‖ + 35 * tolerance) :
    let μ := δ * 4 ^ s.grid
    let a := LongTails.Algorithms.CompositeCubicAcceleration.trialWeight μ s.weight
    let lam := δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2
    let β := min 1 (μ / lam)
    potential f xstar (outerAdvance C fallback L δ X M s z (v + e)) +
      (3 / 8 : ℝ) * activeDissipation L δ X s z ≤
      potential f xstar s + β * (s.weight + a) * (2450 * tolerance ^ 2) / (2 * lam) -
        (β * a) * ⟪e, s.momentum - (β * a) • v - xstar⟫ + (β * a) ^ 2 * ‖e‖ ^ 2 / 2 := by
  let μ := δ * 4 ^ s.grid
  let a := LongTails.Algorithms.CompositeCubicAcceleration.trialWeight μ s.weight
  let lam := δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2
  let β := min 1 (μ / lam)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hl : 0 < lam := by dsimp [lam]; positivity
  have ha : 0 < a := trialWeight_pos hμ hA
  have hb : 0 < β ∧ β ≤ 1 := ⟨(damping_properties hμ hl).1, (damping_properties hμ hl).2.1⟩
  have hleft : 0 ≤ (1 - β) * s.weight := mul_nonneg (sub_nonneg.mpr hb.2) hA
  have hright : 0 < β * (s.weight + a) := mul_pos hb.1 (add_pos_of_nonneg_of_pos hA ha)
  have hmix := (convex_mixture hconv hx hz hleft hright.le (add_pos_of_nonneg_of_pos hleft hright)).2
  have he : (1 - β) * s.weight + β * (s.weight + a) = s.weight + β * a := by ring
  rw [he] at hmix
  have hr := residual_square_bound (norm_nonneg _) hres
  have hr' : ‖v + lam • (z - outerCenter δ s)‖ ^ 2 ≤
      (1 / 2 : ℝ) ^ 2 * lam ^ 2 * ‖z - outerCenter δ s‖ ^ 2 + 2450 * tolerance ^ 2 := by
    norm_num only [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
    exact hr
  have hh := projected_noisy_potential hA ha.le hb.1.le rfl he.symm
    (center_identity s.toState hμ hA) hmix (hsub s.point hx) (hsub xstar hstar) hl
    (damped_step_bound hμ hl hA) hr'
    (SymmetricThirdOrderMinimizers.projectPoint_distance C fallback
      (s.momentum - (β * a) • (v + e)) xstar hC ⟨xstar, hstar⟩ hconv.1 hstar)
  change potential f xstar (outerAdvance C fallback L δ X M s z (v + e)) +
    (3 / 8 : ℝ) * activeDissipation L δ X s z ≤ _
  simp only [potential, outerAdvance, activeDissipation, ite_eq_right (not_le.mpr hactive)]
  convert hh using 1
  dsimp only [rawDissipation, μ, a, lam, β, outerCenter]
  ring

lemma normal_support [CompleteSpace E] {f : E → ℝ} (hf : Differentiable ℝ f)
    (hc : ConvexOn ℝ Set.univ f) {C : Set E} {z n : E}
    (hn : ∀ w ∈ C, ⟪n, w - z⟫ ≤ 0) (w : E) (hw : w ∈ C) :
    f z - f w ≤ ⟪gradient f z + n, z - w⟫ := by
  have hg := OracleTemplate.Gradient.convex_support hc (fun x => (hf x).hasGradientAt) z w
  have hnormal := hn w hw
  have he : z - w = -(w - z) := by abel
  rw [inner_add_left, he, inner_neg_right, inner_neg_right]
  linarith

open MeasureTheory

lemma outer_expected_step [FiniteDimensional ℝ E] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (e : Ω → E)
    (hei : Integrable e P) (hemean : (∫ ω, e ω ∂P) = 0)
    (he₂ : Integrable (fun ω => ‖e ω‖ ^ 2) P) {V : ℝ}
    (hvar : (∫ ω, ‖e ω‖ ^ 2 ∂P) ≤ V)
    (f : E → ℝ) (C : Set E) (fallback xstar : E) {L δ X tolerance : ℝ} (M : ℕ)
    (hC : IsCompact C) (hconv : ConvexOn ℝ C f) (hstar : xstar ∈ C)
    (hL : 0 ≤ L) (hδ : 0 < δ) (hX : 0 ≤ X) (hδX : 1 ≤ δ * X)
    (s : OuterState E) (z v : E) (hA : 0 ≤ s.weight) (hAb : s.weight ≤ 3 * X)
    (hx : s.point ∈ C) (hz : z ∈ C)
    (hsub : ∀ w ∈ C, f z - f w ≤ ⟪v, z - w⟫)
    (hres : ‖v + (δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2) • (z - outerCenter δ s)‖ ≤
      (3 / 16 : ℝ) * (δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2) * ‖z - outerCenter δ s‖ + 35 * tolerance)
    (hEi : Integrable (fun ω => potential f xstar (outerAdvance C fallback L δ X M s z (v + e ω))) P) :
    (∫ ω, potential f xstar (outerAdvance C fallback L δ X M s z (v + e ω)) +
      (3 / 8 : ℝ) * activeDissipation L δ X s z ∂P) ≤
      potential f xstar s + (3 * X) * (2450 * tolerance ^ 2 + V) / (2 * δ) := by
  have hV : 0 ≤ V := (integral_nonneg (fun _ => sq_nonneg _)).trans hvar
  by_cases hstop : X ≤ s.weight
  · simp only [outerAdvance, ite_eq_left hstop, activeDissipation, mul_zero, add_zero, integral_const,
      probReal_univ, one_smul]
    exact le_add_of_nonneg_right (by positivity)
  let μ := δ * 4 ^ s.grid
  let a := LongTails.Algorithms.CompositeCubicAcceleration.trialWeight μ s.weight
  let lam := δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2
  let β := min 1 (μ / lam)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hl : δ ≤ lam := by
    dsimp [lam]
    exact le_add_of_nonneg_right (by positivity)
  have hlpos : 0 < lam := hδ.trans_le hl
  have ha : 0 < a := trialWeight_pos hμ hA
  have hb : 0 < β ∧ β ≤ 1 := ⟨(damping_properties hμ hlpos).1, (damping_properties hμ hlpos).2.1⟩
  have hnew := SymmetricThirdOrderOuter.outerAdvance_weight_bound (L := L) C fallback M hδ hδX
    s z v hA hAb
  have hweight : s.weight + β * a ≤ 3 * X := by
    simpa only [outerAdvance, ite_eq_right hstop] using hnew
  have hcoeff : β * (s.weight + a) ≤ 3 * X :=
    (damped_weight_bound hA hb.2 rfl rfl).trans hweight
  apply expected_energy_increment P hei hemean he₂ hvar hδ hl
    (mul_nonneg hb.1.le (add_nonneg hA ha.le)) hcoeff (damped_step_bound hμ hlpos hA)
    (by positivity) (s.momentum - (β * a) • v - xstar) (hEi.add (integrable_const _))
  intro ω
  exact outer_energy_step f C fallback xstar M hC hconv hstar hL hδ s z v (e ω)
    hA (lt_of_not_ge hstop) hx hz hsub hres

lemma potential_integrable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : E → ℝ) (hf : Continuous f) (C : Set E) (hC : IsCompact C) (xstar : E)
    (hstar : xstar ∈ C) (hmin : ∀ x, f xstar ≤ f x)
    (S : Ω → OuterState E) (hS : SymmetricThirdOrderMeasurability.MeasurableState S)
    {B : ℝ} (hB : 0 ≤ B) (hA : ∀ ω, 0 ≤ (S ω).weight ∧ (S ω).weight ≤ B)
    (hx : ∀ ω, (S ω).point ∈ C) (hv : ∀ ω, (S ω).momentum ∈ C) :
    Integrable (fun ω => potential f xstar (S ω)) P := by
  obtain ⟨xf, hxf, hmax⟩ := hC.exists_isMaxOn ⟨xstar, hstar⟩ hf.continuousOn
  obtain ⟨xd, hxd, hdist⟩ := hC.exists_isMaxOn ⟨xstar, hstar⟩
    ((continuous_id.sub (continuous_const (y := xstar))).norm.continuousOn)
  have hm : Measurable (fun ω => potential f xstar (S ω)) :=
    (hS.weight.mul ((hf.measurable.comp hS.point).sub measurable_const)).add
      (((hS.momentum.sub measurable_const).norm.pow_const 2).div_const 2)
  apply (integrable_const (B * (f xf - f xstar) + ‖xd - xstar‖ ^ 2 / 2)).mono' hm.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (potential_nonneg f xstar (S ω) hmin (hA ω).1)]
  unfold potential
  apply add_le_add
  · exact mul_le_mul (hA ω).2 (sub_le_sub_right (hmax (hx ω)) _)
      (sub_nonneg.mpr (hmin _)) hB
  · have hd : ‖(S ω).momentum - xstar‖ ≤ ‖xd - xstar‖ := hdist (hv ω)
    gcongr

lemma sampled_potential_integrable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure (ℕ → Ω)) [IsFiniteMeasure P]
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (f : E → ℝ) (hf : Continuous f) (xstar : E) (hstar : xstar ∈ cfg.C)
    (hmin : ∀ x, f xstar ≤ f x) (hC : IsCompact cfg.C) (hconv : Convex ℝ cfg.C)
    (hx : cfg.x0 ∈ cfg.C) (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ)
    (hX : 0 ≤ cfg.threshold) (hδX : 1 ≤ cfg.δ * cfg.threshold) (t : ℕ) :
    Integrable (fun ξ => potential f xstar (sampledState cfg oracle ξ t)) P := by
  apply potential_integrable P f hf cfg.C hC xstar hstar hmin _
    (SymmetricThirdOrderHistory.measurable_sampledState cfg oracle ho hC ⟨cfg.x0, hx⟩ hconv hL hδ t)
    (show 0 ≤ 3 * cfg.threshold by positivity)
  · intro ξ
    exact ⟨SymmetricThirdOrderHistory.sampledState_weight_nonneg cfg oracle ξ hL hδ t,
      SymmetricThirdOrderHistory.sampledState_weight_bound cfg oracle ξ hL hδ hX hδX t⟩
  · intro ξ
    exact (SymmetricThirdOrderHistory.sampledState_feasible cfg oracle ξ hC hconv hx hL hδ t).1
  · intro ξ
    exact (SymmetricThirdOrderHistory.sampledState_feasible cfg oracle ξ hC hconv hx hL hδ t).2

lemma activeDissipation_bound {L δ X D Λ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (hX : 0 ≤ X)
    (hδX : 1 ≤ δ * X) (hΛ : 0 ≤ Λ) (s : OuterState E) (z : E)
    (hA : 0 ≤ s.weight) (hAb : s.weight ≤ 3 * X)
    (hd : ‖z - outerCenter δ s‖ ≤ D) (hlam : δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2 ≤ Λ) :
    activeDissipation L δ X s z ≤ 3 * X * Λ * D ^ 2 := by
  by_cases hstop : X ≤ s.weight
  · simp only [activeDissipation, ite_eq_left hstop]
    positivity
  let μ := δ * 4 ^ s.grid
  let a := LongTails.Algorithms.CompositeCubicAcceleration.trialWeight μ s.weight
  let lam := δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2
  let β := min 1 (μ / lam)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hl : 0 < lam := by dsimp [lam]; positivity
  have hb : β ≤ 1 := (damping_properties hμ hl).2.1
  have hn := SymmetricThirdOrderOuter.outerAdvance_weight_bound (L := L) Set.univ z 0 hδ hδX s z z hA hAb
  have hnew : s.weight + β * a ≤ 3 * X := by simpa only [outerAdvance, ite_eq_right hstop] using hn
  have hcoeff : β * (s.weight + a) ≤ 3 * X := (damped_weight_bound hA hb rfl rfl).trans hnew
  change (if X ≤ s.weight then 0 else β * (s.weight + a) * lam * ‖z - outerCenter δ s‖ ^ 2) ≤ _
  rw [ite_eq_right hstop]
  have hd0 : 0 ≤ D := (norm_nonneg _).trans hd
  gcongr

lemma measurable_activeDissipation [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type} [MeasurableSpace Ω] (L δ X : ℝ) (S : Ω → OuterState E) (z : Ω → E)
    (hS : SymmetricThirdOrderMeasurability.MeasurableState S) (hz : Measurable z) :
    Measurable (fun ω => activeDissipation L δ X (S ω) (z ω)) := by
  classical
  have hc := SymmetricThirdOrderMeasurability.measurable_outerCenter δ S hS
  have hA := hS.weight
  have hj := hS.grid
  have hr : Measurable (fun ω => rawDissipation L δ (S ω) (z ω)) := by
    dsimp only [rawDissipation]
    have hμ : Measurable (fun ω => δ * (4 : ℝ) ^ (S ω).grid) := by fun_prop
    have hl : Measurable (fun ω => δ + 8 * L * ‖z ω - outerCenter δ (S ω)‖ ^ 2) := by fun_prop
    have ha : Measurable (fun ω => LongTails.Algorithms.CompositeCubicAcceleration.trialWeight
        (δ * 4 ^ (S ω).grid) (S ω).weight) := by
      unfold LongTails.Algorithms.CompositeCubicAcceleration.trialWeight
      fun_prop
    exact ((measurable_const.min (hμ.div hl)).mul (hA.add ha)).mul hl |>.mul ((hz.sub hc).norm.pow_const 2)
  have hh : Measurable (fun ω => if X ≤ (S ω).weight then (0 : ℝ) else rawDissipation L δ (S ω) (z ω)) :=
    measurable_const.ite (measurableSet_le measurable_const hS.weight) hr
  exact hh

lemma sampled_dissipation_integrable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure (ℕ → Ω)) [IsFiniteMeasure P]
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hconv : Convex ℝ cfg.C) (hx : cfg.x0 ∈ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (hX : 0 ≤ cfg.threshold)
    (hδX : 1 ≤ cfg.δ * cfg.threshold) (t : ℕ) :
    Integrable (fun ξ => activeDissipation cfg.L cfg.δ cfg.threshold (sampledState cfg oracle ξ t)
      (sampledCleanup cfg oracle ξ t).1) P := by
  obtain ⟨w, hw, hmax⟩ := hC.exists_isMaxOn ⟨cfg.x0, hx⟩
    ((continuous_id.sub (continuous_const (y := cfg.x0))).norm.continuousOn)
  let D := 2 * ‖w - cfg.x0‖
  have hm := measurable_activeDissipation cfg.L cfg.δ cfg.threshold _ _
    (SymmetricThirdOrderHistory.measurable_sampledState cfg oracle ho hC ⟨cfg.x0, hx⟩ hconv hL hδ t)
    (SymmetricThirdOrderHistory.measurable_sampledCleanup cfg oracle ho hC ⟨cfg.x0, hx⟩ hconv hL hδ t).fst
  apply (integrable_const (3 * cfg.threshold * (cfg.δ + 8 * cfg.L * D ^ 2) * D ^ 2)).mono'
    hm.aestronglyMeasurable
  filter_upwards [] with ξ
  have hA := SymmetricThirdOrderHistory.sampledState_weight_nonneg cfg oracle ξ hL hδ t
  have hAb := SymmetricThirdOrderHistory.sampledState_weight_bound cfg oracle ξ hL hδ hX hδX t
  have hf := SymmetricThirdOrderHistory.sampledState_feasible cfg oracle ξ hC hconv hx hL hδ t
  have hc := SymmetricThirdOrderOuter.outerCenter_mem hconv hδ _ hA hf.1 hf.2
  have hz := SymmetricThirdOrderHistory.sampledCleanup_mem cfg oracle ξ hC ⟨cfg.x0, hx⟩ t
  have hd : ‖(sampledCleanup cfg oracle ξ t).1 - outerCenter cfg.δ (sampledState cfg oracle ξ t)‖ ≤ D := by
    calc
      _ = ‖((sampledCleanup cfg oracle ξ t).1 - cfg.x0) +
        (cfg.x0 - outerCenter cfg.δ (sampledState cfg oracle ξ t))‖ := by congr 1; abel
      _ ≤ ‖(sampledCleanup cfg oracle ξ t).1 - cfg.x0‖ +
        ‖cfg.x0 - outerCenter cfg.δ (sampledState cfg oracle ξ t)‖ := norm_add_le _ _
      _ ≤ ‖w - cfg.x0‖ + ‖w - cfg.x0‖ := add_le_add (hmax hz)
        (by rw [norm_sub_rev]; exact hmax hc)
      _ = D := by dsimp [D]; ring
  rw [Real.norm_eq_abs, abs_of_nonneg (activeDissipation_nonneg hL hδ _ _ hA)]
  apply activeDissipation_bound hL hδ hX hδX (by positivity) _ _ hA hAb hd
  have hD : 0 ≤ D := by dsimp [D]; positivity
  gcongr

open SymmetricThirdOrderGoodEvents

variable [CompleteSpace E]

noncomputable def accumulated {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (ξ : ℕ → Ω) (T : ℕ) : ℝ :=
  (3 / 8 : ℝ) * ∑ t ∈ Finset.range T, activeDissipation cfg.L cfg.δ cfg.threshold
    (sampledState cfg oracle ξ t) (sampledCleanup cfg oracle ξ t).1

noncomputable def killedEnergy {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (f : E → ℝ) (xstar : E) (T : ℕ) : (ℕ → Ω) → ℝ :=
  (survived cfg oracle (gradient f) (fderiv ℝ (gradient f)) T).indicator
    (fun ξ => potential f xstar (sampledState cfg oracle ξ T) + accumulated cfg oracle ξ T)

lemma accumulated_nonneg {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (ξ : ℕ → Ω) (T : ℕ) (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) :
    0 ≤ accumulated cfg oracle ξ T := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro t _
  exact activeDissipation_nonneg hL hδ _ _
    (SymmetricThirdOrderHistory.sampledState_weight_nonneg cfg oracle ξ hL hδ t)

lemma accumulated_succ {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (ξ : ℕ → Ω) (T : ℕ) :
    accumulated cfg oracle ξ (T + 1) = accumulated cfg oracle ξ T +
      (3 / 8 : ℝ) * activeDissipation cfg.L cfg.δ cfg.threshold
        (sampledState cfg oracle ξ T) (sampledCleanup cfg oracle ξ T).1 := by
  simp only [accumulated, Finset.sum_range_succ, mul_add]

lemma killedEnergy_nonneg {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (f : E → ℝ) (xstar : E) (hmin : ∀ x, f xstar ≤ f x)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (T : ℕ) (ξ : ℕ → Ω) :
    0 ≤ killedEnergy cfg oracle f xstar T ξ := by
  classical
  by_cases hh : ξ ∈ survived cfg oracle (gradient f) (fderiv ℝ (gradient f)) T
  · rw [killedEnergy, Set.indicator_of_mem hh]
    exact add_nonneg (potential_nonneg f xstar _ hmin
      (SymmetricThirdOrderHistory.sampledState_weight_nonneg cfg oracle ξ hL hδ T))
      (accumulated_nonneg cfg oracle ξ T hL hδ)
  · simp only [killedEnergy, Set.indicator_of_notMem hh, le_refl]

lemma killedEnergy_zero {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (f : E → ℝ) (xstar : E) (ξ : ℕ → Ω) :
    killedEnergy cfg oracle f xstar 0 ξ = ‖cfg.x0 - xstar‖ ^ 2 / 2 := by
  simp only [killedEnergy, survived_zero, Set.indicator_univ, accumulated, Finset.range_zero,
    Finset.sum_empty, mul_zero, add_zero, sampledState, outerInitial, potential, zero_mul, zero_add]

lemma killedEnergy_integrable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure (ℕ → Ω)) [IsFiniteMeasure P]
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (f : E → ℝ) (hf : Continuous f) (hg : Measurable (gradient f))
    (hH : Measurable (fderiv ℝ (gradient f))) (xstar : E) (hstar : xstar ∈ cfg.C)
    (hmin : ∀ x, f xstar ≤ f x) (hC : IsCompact cfg.C) (hconv : Convex ℝ cfg.C)
    (hx : cfg.x0 ∈ cfg.C) (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ)
    (hX : 0 ≤ cfg.threshold) (hδX : 1 ≤ cfg.δ * cfg.threshold) (T : ℕ) :
    Integrable (killedEnergy cfg oracle f xstar T) P := by
  have hp := sampled_potential_integrable P cfg oracle ho f hf xstar hstar hmin hC hconv hx hL hδ hX hδX T
  have hd : Integrable (fun ξ => accumulated cfg oracle ξ T) P :=
    (integrable_finsetSum _ (fun t _ => sampled_dissipation_integrable P cfg oracle ho hC hconv hx hL hδ hX hδX t)).const_mul _
  exact (hp.add hd).indicator (measurableSet_survived cfg oracle ho hC ⟨cfg.x0, hx⟩ hconv hL hδ
    (gradient f) hg (fderiv ℝ (gradient f)) hH T)

lemma accumulated_prefix {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (T : ℕ) (ξ η : ℕ → Ω) (heq : ∀ j < roundCalls cfg * T, ξ j = η j) :
    accumulated cfg oracle ξ T = accumulated cfg oracle η T := by
  unfold accumulated
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have htT : t < T := Finset.mem_range.mp ht
  have hstep : roundCalls cfg * (t + 1) ≤ roundCalls cfg * T := Nat.mul_le_mul_left _ htT
  have hstate := SymmetricThirdOrderHistory.sampledState_prefix cfg oracle t ξ η
    (fun j hj => heq j (hj.trans_le (Nat.mul_le_mul_left _ htT.le)))
  have hclean := SymmetricThirdOrderHistory.sampledCleanup_prefix cfg oracle t ξ η (fun j hj => by
    rw [SymmetricThirdOrderHistory.correction_start] at hj
    exact heq j (hj.trans_le ((Nat.sub_le _ _).trans hstep)))
  rw [hstate, hclean]

lemma killedEnergy_prefix {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (f : E → ℝ) (xstar : E) (T : ℕ) (ξ η : ℕ → Ω)
    (heq : ∀ j < roundCalls cfg * T, ξ j = η j) :
    killedEnergy cfg oracle f xstar T ξ = killedEnergy cfg oracle f xstar T η := by
  classical
  have hflag := survived_prefix cfg oracle (gradient f) (fderiv ℝ (gradient f)) T ξ η heq
  by_cases hh : ξ ∈ survived cfg oracle (gradient f) (fderiv ℝ (gradient f)) T
  · simp only [killedEnergy, Set.indicator_of_mem hh, Set.indicator_of_mem (hflag.mp hh)]
    rw [SymmetricThirdOrderHistory.sampledState_prefix cfg oracle T ξ η heq,
      accumulated_prefix cfg oracle T ξ η heq]
  · simp only [killedEnergy, Set.indicator_of_notMem hh, Set.indicator_of_notMem (hflag.not.mp hh)]

lemma killedEnergy_on_survival {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (f : E → ℝ) (xstar : E) (T : ℕ) (ξ : ℕ → Ω)
    (hh : ξ ∈ survived cfg oracle (gradient f) (fderiv ℝ (gradient f)) T) :
    killedEnergy cfg oracle f xstar T ξ =
      potential f xstar (sampledState cfg oracle ξ T) + accumulated cfg oracle ξ T := by
  exact Set.indicator_of_mem hh _

lemma killedEnergy_on_failure {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (f : E → ℝ) (xstar : E) (T : ℕ) (ξ : ℕ → Ω)
    (hh : ξ ∉ survived cfg oracle (gradient f) (fderiv ℝ (gradient f)) T) :
    killedEnergy cfg oracle f xstar T ξ = 0 := by
  exact Set.indicator_of_notMem hh _

omit [CompleteSpace E] in
lemma measurable_potential [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type} [MeasurableSpace Ω] (f : E → ℝ) (hf : Measurable f) (xstar : E)
    (S : Ω → OuterState E) (hS : SymmetricThirdOrderMeasurability.MeasurableState S) :
    Measurable (fun ω => potential f xstar (S ω)) :=
  (hS.weight.mul ((hf.comp hS.point).sub measurable_const)).add
    (((hS.momentum.sub measurable_const).norm.pow_const 2).div_const 2)

lemma measurable_accumulated [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type} [MeasurableSpace Ω]
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (T : ℕ) :
    Measurable (fun ξ => accumulated cfg oracle ξ T) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro t _
  exact measurable_activeDissipation cfg.L cfg.δ cfg.threshold _ _
    (SymmetricThirdOrderHistory.measurable_sampledState cfg oracle ho hC hne hconv hL hδ t)
    (SymmetricThirdOrderHistory.measurable_sampledCleanup cfg oracle ho hC hne hconv hL hδ t).fst

lemma measurable_killedEnergy [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type} [MeasurableSpace Ω]
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (f : E → ℝ) (hf : Measurable f) (hg : Measurable (gradient f))
    (hH : Measurable (fderiv ℝ (gradient f))) (xstar : E)
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (T : ℕ) :
    Measurable (killedEnergy cfg oracle f xstar T) := by
  have hp := measurable_potential f hf xstar _
    (SymmetricThirdOrderHistory.measurable_sampledState cfg oracle ho hC hne hconv hL hδ T)
  exact (hp.add (measurable_accumulated cfg oracle ho hC hne hconv hL hδ T)).indicator
    (measurableSet_survived cfg oracle ho hC hne hconv hL hδ (gradient f) hg (fderiv ℝ (gradient f)) hH T)

lemma accumulated_succ_prefix {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (t : ℕ) (ξ η : ℕ → Ω)
    (heq : ∀ j < roundCalls cfg * (t + 1) - cfg.batch, ξ j = η j) :
    accumulated cfg oracle ξ (t + 1) = accumulated cfg oracle η (t + 1) := by
  have hn : roundCalls cfg * t ≤ roundCalls cfg * (t + 1) - cfg.batch := by
    rw [← SymmetricThirdOrderHistory.correction_start]
    omega
  have hp : ∀ j < roundCalls cfg * t, ξ j = η j := fun j hj => heq j (hj.trans_le hn)
  have hc := SymmetricThirdOrderHistory.sampledCleanup_prefix cfg oracle t ξ η (by
    simpa only [SymmetricThirdOrderHistory.correction_start] using heq)
  rw [accumulated_succ, accumulated_succ, accumulated_prefix cfg oracle t ξ η hp,
    SymmetricThirdOrderHistory.sampledState_prefix cfg oracle t ξ η hp, hc]

open SymmetricThirdOrderSampling

omit [CompleteSpace E] in
lemma correction_end (cfg : Config E) (t : ℕ) :
    roundCalls cfg * (t + 1) - cfg.batch + cfg.batch = roundCalls cfg * (t + 1) := by
  rw [← SymmetricThirdOrderHistory.correction_start]
  unfold roundCalls
  ring

omit [CompleteSpace E] in
lemma round_start_le_correction (cfg : Config E) (t : ℕ) :
    roundCalls cfg * t ≤ roundCalls cfg * (t + 1) - cfg.batch := by
  rw [← SymmetricThirdOrderHistory.correction_start]
  omega

lemma block_round_step {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (f : E → ℝ) (ω0 : Ω) (t : ℕ)
    (u : Fin (roundCalls cfg * (t + 1) - cfg.batch) → Ω) (v : Fin cfg.batch → Ω) :
    let n := roundCalls cfg * (t + 1) - cfg.batch
    let ζ := blockExtend ω0 n cfg.batch u (fun _ => ω0)
    let η := blockExtend ω0 n cfg.batch u v
    let z := (sampledCleanup cfg oracle ζ t).1
    let e := (1 / (cfg.batch : ℝ)) • ∑ i : Fin cfg.batch, (oracle z (v i)).1 - gradient f z
    sampledState cfg oracle η (t + 1) =
      outerAdvance cfg.C cfg.x0 cfg.L cfg.δ cfg.threshold cfg.gridTop (sampledState cfg oracle ζ t) z
        (gradient f z + (sampledCleanup cfg oracle ζ t).2 + e) := by
  let n := roundCalls cfg * (t + 1) - cfg.batch
  let ζ := blockExtend ω0 n cfg.batch u (fun _ => ω0)
  let η := blockExtend ω0 n cfg.batch u v
  have he : ∀ j < n, η j = ζ j := by
    intro j hj
    simp only [η, ζ, blockExtend, dite_eq_left hj]
  have hs := SymmetricThirdOrderHistory.sampledState_prefix cfg oracle t η ζ
    (fun j hj => he j (hj.trans_le (round_start_le_correction cfg t)))
  have hz := SymmetricThirdOrderHistory.sampledCleanup_prefix cfg oracle t η ζ (by
    simpa only [SymmetricThirdOrderHistory.correction_start] using he)
  change sampledState cfg oracle η (t + 1) = _
  rw [SymmetricThirdOrderHistory.sampledState_step, hs, hz, SymmetricThirdOrderExecution.meanPlan_eval]
  simp only [η, n, ζ, blockExtend_tail]
  congr 1
  abel

lemma killed_section_bound [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (f : E → ℝ) (hf : Differentiable ℝ f) (hc : ConvexOn ℝ Set.univ f) (xstar : E)
    (hstar : xstar ∈ cfg.C) (hmin : ∀ x, f xstar ≤ f x)
    (hC : IsCompact cfg.C) (hconv : Convex ℝ cfg.C) (hx : cfg.x0 ∈ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (hX : 0 ≤ cfg.threshold) (hδX : 1 ≤ cfg.δ * cfg.threshold)
    (hm : 0 < cfg.batch) (hgi : ∀ z, Integrable (fun ω => (oracle z ω).1) p)
    (hmean : ∀ z, (∫ ω, (oracle z ω).1 ∂p) = gradient f z)
    (h₂ : ∀ z, Integrable (fun ω => ‖(oracle z ω).1 - gradient f z‖ ^ 2) p)
    {σ : ℝ} (hvar : ∀ z, (∫ ω, ‖(oracle z ω).1 - gradient f z‖ ^ 2 ∂p) ≤ σ ^ 2)
    (t : ℕ)
    (haccuracy : ∀ ξ ∈ goodRound cfg oracle (gradient f) (fderiv ℝ (gradient f)) t,
      let c := sampledCenter cfg oracle ξ t
      let z := (sampledCleanup cfg oracle ξ t).1
      let n := (sampledCleanup cfg oracle ξ t).2
      ‖gradient f z + n + (cfg.δ + 8 * cfg.L * ‖z - c‖ ^ 2) • (z - c)‖ ≤
        (3 / 16 : ℝ) * (cfg.δ + 8 * cfg.L * ‖z - c‖ ^ 2) * ‖z - c‖ + 35 * cfg.tolerance ∧
        ∀ w ∈ cfg.C, ⟪n, w - z⟫ ≤ 0)
    (ω0 : Ω) (u : Fin (roundCalls cfg * (t + 1) - cfg.batch) → Ω)
    (hFi : Integrable (fun v => killedEnergy cfg oracle f xstar (t + 1)
      (blockExtend ω0 (roundCalls cfg * (t + 1) - cfg.batch) cfg.batch u v))
        (Measure.pi fun _ : Fin cfg.batch => p)) :
    (∫ v, killedEnergy cfg oracle f xstar (t + 1)
      (blockExtend ω0 (roundCalls cfg * (t + 1) - cfg.batch) cfg.batch u v)
        ∂(Measure.pi fun _ : Fin cfg.batch => p)) ≤
      killedEnergy cfg oracle f xstar t
        (blockExtend ω0 (roundCalls cfg * (t + 1) - cfg.batch) cfg.batch u (fun _ => ω0)) +
        (3 * cfg.threshold) * (2450 * cfg.tolerance ^ 2 + σ ^ 2 / cfg.batch) / (2 * cfg.δ) := by
  let n := roundCalls cfg * (t + 1) - cfg.batch
  let ζ := blockExtend ω0 n cfg.batch u (fun _ => ω0)
  let η := fun v => blockExtend ω0 n cfg.batch u v
  let Q := Measure.pi fun _ : Fin cfg.batch => p
  have he (v : Fin cfg.batch → Ω) : ∀ j < n, η v j = ζ j := by
    intro j hj
    simp only [η, ζ, blockExtend, dite_eq_left hj]
  have hflag (v : Fin cfg.batch → Ω) :=
    survived_succ_prefix cfg oracle (gradient f) (fderiv ℝ (gradient f)) t (η v) ζ (he v)
  by_cases hs : ζ ∈ survived cfg oracle (gradient f) (fderiv ℝ (gradient f)) (t + 1)
  · have hsplit : ζ ∈ survived cfg oracle (gradient f) (fderiv ℝ (gradient f)) t ∧
        ζ ∈ goodRound cfg oracle (gradient f) (fderiv ℝ (gradient f)) t := by
      rwa [survived_succ] at hs
    let z := (sampledCleanup cfg oracle ζ t).1
    let vtrue := gradient f z + (sampledCleanup cfg oracle ζ t).2
    let e := fun v : Fin cfg.batch → Ω => (1 / (cfg.batch : ℝ)) • ∑ i, (oracle z (v i)).1 - gradient f z
    let Sn := fun v => outerAdvance cfg.C cfg.x0 cfg.L cfg.δ cfg.threshold cfg.gridTop
      (sampledState cfg oracle ζ t) z (vtrue + e v)
    have hstate (v : Fin cfg.batch → Ω) : sampledState cfg oracle (η v) (t + 1) = Sn v :=
      block_round_step cfg oracle f ω0 t u v
    have hacc (v : Fin cfg.batch → Ω) : accumulated cfg oracle (η v) (t + 1) = accumulated cfg oracle ζ (t + 1) :=
      accumulated_succ_prefix cfg oracle t (η v) ζ (he v)
    have hF (v : Fin cfg.batch → Ω) : killedEnergy cfg oracle f xstar (t + 1) (η v) =
        potential f xstar (Sn v) + accumulated cfg oracle ζ (t + 1) := by
      rw [killedEnergy_on_survival cfg oracle f xstar (t + 1) (η v) ((hflag v).mpr hs), hstate, hacc]
    have hEi : Integrable (fun v => potential f xstar (Sn v)) Q := by
      have hi := hFi.sub (integrable_const (accumulated cfg oracle ζ (t + 1)))
      convert hi using 1
      funext v
      change potential f xstar (Sn v) = killedEnergy cfg oracle f xstar (t + 1) (η v) - _
      rw [hF]
      ring
    have hnoise := finite_mean_noise (ho.fst.comp (measurable_const.prodMk measurable_id))
      (hgi z) (gradient f z) (hmean z) (h₂ z) (hvar z) cfg.batch hm
    have hfeas := SymmetricThirdOrderHistory.sampledState_feasible cfg oracle ζ hC hconv hx hL hδ t
    have hz := SymmetricThirdOrderHistory.sampledCleanup_mem cfg oracle ζ hC ⟨cfg.x0, hx⟩ t
    have haccuracy := haccuracy ζ hsplit.2
    have hcC : ConvexOn ℝ cfg.C f := ⟨hconv, fun x _ y _ a b ha hb hab => hc.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab⟩
    have hstep := outer_expected_step Q e hnoise.1 hnoise.2.1 hnoise.2.2.1 hnoise.2.2.2
      f cfg.C cfg.x0 xstar cfg.gridTop hC hcC hstar hL hδ hX hδX (sampledState cfg oracle ζ t) z vtrue
      (SymmetricThirdOrderHistory.sampledState_weight_nonneg cfg oracle ζ hL hδ t)
      (SymmetricThirdOrderHistory.sampledState_weight_bound cfg oracle ζ hL hδ hX hδX t)
      hfeas.1 hz (normal_support hf hc haccuracy.2) haccuracy.1 hEi
    have hstep' : (∫ v, potential f xstar (Sn v) ∂Q) +
        (3 / 8 : ℝ) * activeDissipation cfg.L cfg.δ cfg.threshold (sampledState cfg oracle ζ t) z ≤
        potential f xstar (sampledState cfg oracle ζ t) +
          (3 * cfg.threshold) * (2450 * cfg.tolerance ^ 2 + σ ^ 2 / cfg.batch) / (2 * cfg.δ) := by
      change (∫ v, potential f xstar (Sn v) +
        (3 / 8 : ℝ) * activeDissipation cfg.L cfg.δ cfg.threshold (sampledState cfg oracle ζ t) z ∂Q) ≤ _ at hstep
      simpa only [integral_add hEi (integrable_const _), integral_const, probReal_univ, one_smul] using hstep
    change (∫ v, killedEnergy cfg oracle f xstar (t + 1) (η v) ∂Q) ≤ _
    simp_rw [hF]
    rw [integral_add hEi (integrable_const _), integral_const, probReal_univ, one_smul,
      killedEnergy_on_survival cfg oracle f xstar t ζ hsplit.1, accumulated_succ]
    linarith
  · have hzero (v : Fin cfg.batch → Ω) : killedEnergy cfg oracle f xstar (t + 1) (η v) = 0 :=
      killedEnergy_on_failure cfg oracle f xstar (t + 1) (η v) (fun hv => hs ((hflag v).mp hv))
    change (∫ v, killedEnergy cfg oracle f xstar (t + 1) (η v) ∂Q) ≤ _
    simp_rw [hzero]
    rw [integral_zero]
    exact add_nonneg (killedEnergy_nonneg cfg oracle f xstar hmin hL hδ t ζ) (by positivity)

lemma killed_energy_drift [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]
    {P : Measure (ℕ → Ω)} [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (f : E → ℝ) (hf : Differentiable ℝ f) (hc : ConvexOn ℝ Set.univ f)
    (hg : Measurable (gradient f)) (hH : Measurable (fderiv ℝ (gradient f))) (xstar : E)
    (hstar : xstar ∈ cfg.C) (hmin : ∀ x, f xstar ≤ f x)
    (hC : IsCompact cfg.C) (hconv : Convex ℝ cfg.C) (hx : cfg.x0 ∈ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (hX : 0 ≤ cfg.threshold) (hδX : 1 ≤ cfg.δ * cfg.threshold)
    (hm : 0 < cfg.batch) (hgi : ∀ z, Integrable (fun ω => (oracle z ω).1) p)
    (hmean : ∀ z, (∫ ω, (oracle z ω).1 ∂p) = gradient f z)
    (h₂ : ∀ z, Integrable (fun ω => ‖(oracle z ω).1 - gradient f z‖ ^ 2) p)
    {σ : ℝ} (hvar : ∀ z, (∫ ω, ‖(oracle z ω).1 - gradient f z‖ ^ 2 ∂p) ≤ σ ^ 2)
    (t : ℕ)
    (haccuracy : ∀ ξ ∈ goodRound cfg oracle (gradient f) (fderiv ℝ (gradient f)) t,
      let c := sampledCenter cfg oracle ξ t
      let z := (sampledCleanup cfg oracle ξ t).1
      let n := (sampledCleanup cfg oracle ξ t).2
      ‖gradient f z + n + (cfg.δ + 8 * cfg.L * ‖z - c‖ ^ 2) • (z - c)‖ ≤
        (3 / 16 : ℝ) * (cfg.δ + 8 * cfg.L * ‖z - c‖ ^ 2) * ‖z - c‖ + 35 * cfg.tolerance ∧
        ∀ w ∈ cfg.C, ⟪n, w - z⟫ ≤ 0)
    : (∫ ξ, killedEnergy cfg oracle f xstar (t + 1) ξ ∂P) ≤
      (∫ ξ, killedEnergy cfg oracle f xstar t ξ ∂P) +
        (3 * cfg.threshold) * (2450 * cfg.tolerance ^ 2 + σ ^ 2 / cfg.batch) / (2 * cfg.δ) := by
  obtain ⟨ω0, _⟩ := nonempty_of_measure_ne_zero (show p Set.univ ≠ 0 by simp)
  apply prefix_block_drift hIID ω0 (roundCalls cfg * (t + 1) - cfg.batch) cfg.batch
    (killedEnergy cfg oracle f xstar (t + 1)) (killedEnergy cfg oracle f xstar t)
    (measurable_killedEnergy cfg oracle ho f hf.continuous.measurable hg hH xstar hC ⟨cfg.x0, hx⟩ hconv hL hδ (t + 1))
    (measurable_killedEnergy cfg oracle ho f hf.continuous.measurable hg hH xstar hC ⟨cfg.x0, hx⟩ hconv hL hδ t)
    (fun ζ η he => killedEnergy_prefix cfg oracle f xstar (t + 1) ζ η (by simpa only [correction_end] using he))
    (fun ζ η he => killedEnergy_prefix cfg oracle f xstar t ζ η
      (fun j hj => he j (hj.trans_le (round_start_le_correction cfg t))))
    (killedEnergy_integrable P cfg oracle ho f hf.continuous hg hH xstar hstar hmin hC hconv hx hL hδ hX hδX (t + 1))
    (killedEnergy_integrable P cfg oracle ho f hf.continuous hg hH xstar hstar hmin hC hconv hx hL hδ hX hδX t)
  intro u hu
  exact killed_section_bound p cfg oracle ho f hf hc xstar hstar hmin hC hconv hx hL hδ hX hδX
    hm hgi hmean h₂ hvar t haccuracy ω0 u hu

lemma killed_energy_sum {Ω : Type} [MeasurableSpace Ω] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (cfg : Config E) (oracle : E → Ω → Reply E) (f : E → ℝ) (xstar : E) (T : ℕ) (c : ℝ)
    (hstep : ∀ t < T, (∫ ξ, killedEnergy cfg oracle f xstar (t + 1) ξ ∂P) ≤
      (∫ ξ, killedEnergy cfg oracle f xstar t ξ ∂P) + c) :
    (∫ ξ, killedEnergy cfg oracle f xstar T ξ ∂P) ≤ ‖cfg.x0 - xstar‖ ^ 2 / 2 + T * c := by
  have hb : ∀ t ≤ T, (∫ ξ, killedEnergy cfg oracle f xstar t ξ ∂P) ≤
      ‖cfg.x0 - xstar‖ ^ 2 / 2 + t * c := by
    intro t
    induction t with
    | zero =>
      intro _
      simp only [killedEnergy_zero, integral_const, probReal_univ, one_smul, Nat.cast_zero, zero_mul, add_zero, le_refl]
    | succ t ih =>
      intro ht
      have hp := ih (by omega)
      have hs := hstep t (by omega)
      push_cast
      linarith
  exact hb T le_rfl

lemma killed_energy_bound [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]
    {P : Measure (ℕ → Ω)} [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (f : E → ℝ) (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f) (xstar : E)
    {R Δ : ℝ} (hR : 0 ≤ R) (hball : cfg.C = Metric.closedBall cfg.x0 R)
    (hmin : ∀ x, f xstar ≤ f x) (hdist : ‖cfg.x0 - xstar‖ ≤ R) (hgap : f cfg.x0 - f xstar ≤ Δ)
    (hL : 0 < cfg.L) (hδ : 0 < cfg.δ) (hσ : 0 ≤ cfg.σh) (ha : 0 < cfg.tolerance)
    (hδσ : 288 * cfg.σh ≤ cfg.δ) (hX : 0 ≤ cfg.threshold) (hδX : 1 ≤ cfg.δ * cfg.threshold)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ cfg.L * ‖x - y‖)
    (k : ℕ) (hJ : cfg.innerRounds = k + 1)
    (htune : (6 / 7 : ℝ) ^ k * (8 * (Δ + 3 * cfg.L * R ^ 4 + cfg.δ * R ^ 2)) ≤
      cfg.tolerance ^ 2 / cfg.δ)
    (hcleanup : 262144 * cfg.L * cfg.tolerance ^ 2 ≤ cfg.δ ^ 3)
    (hm : 0 < cfg.batch) (hgi : ∀ z, Integrable (fun ω => (oracle z ω).1) p)
    (hmean : ∀ z, (∫ ω, (oracle z ω).1 ∂p) = gradient f z)
    (h₂ : ∀ z, Integrable (fun ω => ‖(oracle z ω).1 - gradient f z‖ ^ 2) p)
    {σ : ℝ} (hvar : ∀ z, (∫ ω, ‖(oracle z ω).1 - gradient f z‖ ^ 2 ∂p) ≤ σ ^ 2) (T : ℕ) :
    (∫ ξ, killedEnergy cfg oracle f xstar T ξ ∂P) ≤ R ^ 2 / 2 +
      T * ((3 * cfg.threshold) * (2450 * cfg.tolerance ^ 2 + σ ^ 2 / cfg.batch) / (2 * cfg.δ)) := by
  have hC : IsCompact cfg.C := by rw [hball]; exact isCompact_closedBall _ _
  have hconv : Convex ℝ cfg.C := by rw [hball]; exact convex_closedBall _ _
  have hx : cfg.x0 ∈ cfg.C := by rw [hball]; exact Metric.mem_closedBall_self hR
  have hstar : xstar ∈ cfg.C := by
    rw [hball]
    change dist xstar cfg.x0 ≤ R
    simpa only [dist_eq_norm, norm_sub_rev] using hdist
  have hd := GradientDependentLocal.derivative_chain hf
  have hg : Measurable (gradient f) :=
    (continuous_iff_continuousAt.mpr (fun x => (hd.2.1 x).continuousAt)).measurable
  have hH : Measurable (fderiv ℝ (gradient f)) :=
    (continuous_iff_continuousAt.mpr (fun x => (hd.2.2 x).continuousAt)).measurable
  have hb := killed_energy_sum P cfg oracle f xstar T
    ((3 * cfg.threshold) * (2450 * cfg.tolerance ^ 2 + σ ^ 2 / cfg.batch) / (2 * cfg.δ)) (by
      intro t _
      apply killed_energy_drift p hIID cfg oracle ho f (hf.differentiable (by norm_num)) hc hg hH xstar
        hstar hmin hC hconv hx hL.le hδ hX hδX hm hgi hmean h₂ hvar t
      intro ξ hgood
      have hfeas := SymmetricThirdOrderHistory.sampledState_feasible cfg oracle ξ hC hconv hx hL.le hδ t
      have hcent := SymmetricThirdOrderOuter.outerCenter_mem hconv hδ _
        (SymmetricThirdOrderHistory.sampledState_weight_nonneg cfg oracle ξ hL.le hδ t) hfeas.1 hfeas.2
      have hcdist : ‖cfg.x0 - sampledCenter cfg oracle ξ t‖ ≤ R := by
        rw [hball] at hcent
        change dist (sampledCenter cfg oracle ξ t) cfg.x0 ≤ R at hcent
        simpa only [dist_eq_norm, norm_sub_rev] using hcent
      exact goodRound_accuracy hf hc cfg oracle ξ t hL hδ hσ ha hδσ hT hC hconv hx
        xstar Δ R hmin hgap hcdist k hJ htune hcleanup hgood)
  apply hb.trans
  gcongr

lemma killed_energy_tail {Ω : Type} [MeasurableSpace Ω] (P : Measure (ℕ → Ω))
    (cfg : Config E) (oracle : E → Ω → Reply E) (f : E → ℝ) (xstar : E) (T : ℕ)
    (hmin : ∀ x, f xstar ≤ f x) (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ)
    (hi : Integrable (killedEnergy cfg oracle f xstar T) P)
    {D B : ℝ} (hB : 0 < B) (hbound : (∫ ξ, killedEnergy cfg oracle f xstar T ξ ∂P) ≤ D) :
    P {ξ | B < killedEnergy cfg oracle f xstar T ξ} ≤ ENNReal.ofReal (D / B) := by
  have hh := (hi.div_const B).measure_le_integral
    (Filter.Eventually.of_forall (fun ξ => div_nonneg (killedEnergy_nonneg cfg oracle f xstar hmin hL hδ T ξ) hB.le))
    (s := {ξ | B < killedEnergy cfg oracle f xstar T ξ}) (fun ξ hξ => (one_le_div hB).mpr hξ.le)
  apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [integral_div]
  exact div_le_div_of_nonneg_right hbound hB.le

lemma energy_controls_accumulated {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (f : E → ℝ) (xstar : E) (T : ℕ) (ξ : ℕ → Ω)
    (hmin : ∀ x, f xstar ≤ f x) (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ)
    (hs : ξ ∈ survived cfg oracle (gradient f) (fderiv ℝ (gradient f)) T)
    {B : ℝ} (hE : killedEnergy cfg oracle f xstar T ξ ≤ B) :
    (∑ t ∈ Finset.range T, activeDissipation cfg.L cfg.δ cfg.threshold
      (sampledState cfg oracle ξ t) (sampledCleanup cfg oracle ξ t).1) ≤ (8 / 3 : ℝ) * B := by
  rw [killedEnergy_on_survival cfg oracle f xstar T ξ hs] at hE
  have hp := potential_nonneg f xstar _ hmin
    (SymmetricThirdOrderHistory.sampledState_weight_nonneg cfg oracle ξ hL hδ T)
  unfold accumulated at hE
  linarith

lemma energy_controls_gap {Ω : Type} (cfg : Config E) (oracle : E → Ω → Reply E)
    (f : E → ℝ) (xstar : E) (T : ℕ) (ξ : ℕ → Ω)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ)
    (hs : ξ ∈ survived cfg oracle (gradient f) (fderiv ℝ (gradient f)) T)
    {B ε : ℝ} (hE : killedEnergy cfg oracle f xstar T ξ ≤ B)
    (hε : 0 ≤ ε) (hstop : cfg.threshold ≤ (sampledState cfg oracle ξ T).weight)
    (hX : 0 < cfg.threshold) (hbudget : B ≤ cfg.threshold * ε) :
    f (sampledState cfg oracle ξ T).point - f xstar ≤ ε := by
  rw [killedEnergy_on_survival cfg oracle f xstar T ξ hs] at hE
  have hacc := accumulated_nonneg cfg oracle ξ T hL hδ
  have hnorm := sq_nonneg ‖(sampledState cfg oracle ξ T).momentum - xstar‖
  unfold potential at hE
  have hweight : 0 < (sampledState cfg oracle ξ T).weight := hX.trans_le hstop
  have hmul := mul_le_mul_of_nonneg_right hstop hε
  nlinarith

end LongTails.Proofs.SymmetricThirdOrderStochasticEnergy

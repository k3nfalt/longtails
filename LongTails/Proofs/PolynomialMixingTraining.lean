import LongTails.Proofs.PolynomialMixingScore
import LongTails.Proofs.GeneralizedLipschitzWarmStart
import LongTails.Proofs.Clipping
import Mathlib.Analysis.MeanInequalitiesPow

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.PolynomialMixingTraining

open LongTails.Setups.PolynomialMixingSubgradient LongTails.Algorithms.PolynomialMixingSelection
open LongTails.Proofs.PolynomialMixingValidation HeavyTailedProductProcess

variable {q : Params} {f : Space q → ℝ} {g : Point q → ℝ → Space q} {π : Measure ℝ}
  [IsProbabilityMeasure π]

def coords (s : TrainState q) : Point q × Space q × ℝ := (s.x, s.total, s.energy)

instance : MeasurableSpace (TrainState q) := MeasurableSpace.comap coords inferInstance

lemma measurable_coords : Measurable (coords (q := q)) := Measurable.of_comap_le le_rfl

lemma measurable_project : Measurable (project q) :=
  Measurable.subtype_mk (OracleTemplate.measurable_clip q.R)

def start (q : Params) : TrainState q := ⟨origin q, 0, q.G ^ 2⟩

noncomputable def step (g : Point q → ℝ → Space q) (s : TrainState q) (z : ℝ) : TrainState q :=
  trainStep q s (g s.x z)

lemma step_measurable (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (step g)) := by
  apply measurable_iff_comap_le.mpr
  unfold instMeasurableSpaceTrainState
  rw [MeasurableSpace.comap_comp]
  apply Measurable.comap_le
  have hc : Measurable (fun t : TrainState q × ℝ => coords t.1) := measurable_coords.comp measurable_fst
  have hx : Measurable (fun t : TrainState q × ℝ => t.1.x) := measurable_fst.comp hc
  have hr := hg.comp (hx.prodMk measurable_snd)
  have htot := (measurable_fst.comp (measurable_snd.comp hc)).add (measurable_subtype_coe.comp hx)
  have he := (measurable_snd.comp (measurable_snd.comp hc)).add (hr.norm.pow_const (2 : ℕ))
  exact (measurable_project.comp ((measurable_subtype_coe.comp hx).sub
    ((measurable_const.div he.sqrt).smul hr))).prodMk (htot.prodMk he)

noncomputable def state (g : Point q → ℝ → Space q) (n : ℕ) (ξ : ℕ → ℝ) : TrainState q :=
  trajectory (step g) n (start q) ξ

lemma state_succ (n : ℕ) (ξ : ℕ → ℝ) :
    state g (n + 1) ξ = trainStep q (state g n ξ) (g (state g n ξ).x (ξ n)) :=
  trajectory_succ_last _ _ _ _

lemma energy_eq (n : ℕ) (ξ : ℕ → ℝ) :
    (state g n ξ).energy = q.G ^ 2 + ∑ i ∈ Finset.range n, ‖g (state g i ξ).x (ξ i)‖ ^ 2 := by
  induction n with
  | zero => simp [state, trajectory, start]
  | succ n ih => rw [state_succ]; simp [trainStep, ih, Finset.sum_range_succ, add_assoc]

lemma total_eq (n : ℕ) (ξ : ℕ → ℝ) :
    (state g n ξ).total = ∑ i ∈ Finset.range n, (state g i ξ).x.val := by
  induction n with
  | zero => simp [state, trajectory, start]
  | succ n ih => rw [state_succ]; simp [trainStep, ih, Finset.sum_range_succ]

lemma within (x : Point q) : ‖x.val‖ ≤ q.R := by
  simpa only [Domain, Metric.mem_closedBall, dist_zero_right] using x.property

lemma regret (hR : 0 < q.R) (hG : 0 < q.G) (u : Point q) (n : ℕ) (ξ : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, ⟪g (state g i ξ).x (ξ i), (state g i ξ).x.val - u.val⟫) ≤
      3 * q.R * q.G + 3 * q.R * Real.sqrt (∑ i ∈ Finset.range n, ‖g (state g i ξ).x (ξ i)‖ ^ 2) := by
  apply GeneralizedLipschitzWarmStart.adagrad_regret 0 u.val hR hG
    (fun i => (state g i ξ).x.val) (fun i => g (state g i ξ).x (ξ i))
    (by simpa using within u) (fun i => by simpa using within (state g i ξ).x)
  intro i
  rw [state_succ]
  simp [trainStep, project, energy_eq, Finset.sum_range_succ, add_assoc]

lemma sqrt_sum_power {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (n : ℕ) : (Real.sqrt (∑ i ∈ Finset.range n, a i ^ 2)) ^ p ≤ ∑ i ∈ Finset.range n, a i ^ p := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Real.zero_rpow (by positivity : (1 / 2 : ℝ) * p ≠ 0), le_refl]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    apply (Real.rpow_add_le_add_rpow (Finset.sum_nonneg fun i _ => sq_nonneg (a i))
      (sq_nonneg (a n)) (by positivity) (by linarith)).trans
    apply add_le_add ih
    rw [← Real.rpow_natCast (a n) 2, ← Real.rpow_mul (ha n)]
    norm_num
    rw [show (2 : ℝ) * (1 / 2 * p) = p by ring]

noncomputable def average (g : Point q → ℝ → Space q) (n : ℕ) (ξ : ℕ → ℝ) : Point q :=
  project q ((n : ℝ)⁻¹ • (state g n ξ).total)

lemma average_gap (hc : ConvexOn ℝ (Domain q) f) (u : Point q) {n : ℕ} (hn : 0 < n)
    (ξ : ℕ → ℝ) : (n : ℝ) * (f (average g n ξ).val - f u.val) ≤
      ∑ i ∈ Finset.range n, (f (state g i ξ).x.val - f u.val) := by
  let y := fun i => (state g i ξ).x.val
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ∑ _i ∈ Finset.range n, (n : ℝ)⁻¹ = 1 := by simp [hn.ne']
  have hw0 (i : ℕ) (_ : i ∈ Finset.range n) : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hmem (i : ℕ) (_ : i ∈ Finset.range n) : y i ∈ Domain q := (state g i ξ).x.property
  have hm := hc.1.sum_mem hw0 hw hmem
  have hh := hc.map_sum_le hw0 hw hmem
  rw [← Finset.smul_sum] at hm hh
  have hnrm : ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, y i‖ ≤ q.R := by simpa [Domain] using hm
  change _ * (f (OracleTemplate.clip q.R _) - _) ≤ _
  rw [total_eq, OracleTemplate.clip_eq_self hnrm, Finset.sum_sub_distrib]
  simp only [smul_eq_mul, ← Finset.mul_sum] at hh
  have hh' := (le_inv_mul_iff₀ hn').mp hh
  simpa [Finset.sum_const, nsmul_eq_mul, mul_sub, y, mul_comm] using
    sub_le_sub_right hh' ((n : ℝ) * f u.val)

noncomputable def energySum (g : Point q → ℝ → Space q) (n : ℕ) (ξ : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, ‖g (state g i ξ).x (ξ i)‖ ^ q.p

lemma energy_moment (h : SubgradientOracle q f g π) (n : ℕ) :
    Integrable (energySum g n) (Measure.infinitePi (fun _ : ℕ => π)) ∧
      (∫ ξ, energySum g n ξ ∂Measure.infinitePi (fun _ : ℕ => π)) ≤ n * q.G ^ q.p := by
  let D := fun (s : TrainState q) z => ‖g s.x z‖ ^ q.p
  have hx : Measurable (fun s : TrainState q => s.x) := measurable_fst.comp measurable_coords
  have hm : Measurable (Function.uncurry D) :=
    (h.measurable.comp ((hx.comp measurable_fst).prodMk measurable_snd)).norm.pow_const _
  have hi := HeavyTailedFreshProcess.noiseSum_nonnegative_integral π (step_measurable h.measurable) hm
    (fun s z => Real.rpow_nonneg (norm_nonneg _) _) (fun s => h.momentIntegrable s.x)
    (fun s => h.moment s.x) n (start q) (le_refl (0 : ℝ))
  have he : HeavyTailedFreshProcess.noiseSum (step g) D n (start q) 0 = energySum g n := by
    funext ξ
    simp [HeavyTailedFreshProcess.noiseSum_eq_sum, D, state, energySum]
  simpa only [he, zero_add] using hi

noncomputable def deviation (g : Point q → ℝ → Space q) (π : Measure ℝ) (u : Point q)
    (n : ℕ) (ξ : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, let x := (state g i ξ).x
    ⟪g x (ξ i), x.val - u.val⟫ - ∫ z, ⟪g x z, x.val - u.val⟫ ∂π

lemma deviation_moment (h : SubgradientOracle q f g π) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (hG : 0 ≤ q.G) (u : Point q) (n : ℕ) :
    Integrable (fun ξ => ‖deviation g π u n ξ‖ ^ q.p) (Measure.infinitePi (fun _ : ℕ => π)) ∧
      (∫ ξ, ‖deviation g π u n ξ‖ ^ q.p ∂Measure.infinitePi (fun _ : ℕ => π)) ≤
        24 * n * (q.G * (2 * q.R)) ^ q.p := by
  let D := fun (s : TrainState q) z => ⟪g s.x z, s.x.val - u.val⟫
  have hx : Measurable (fun t : TrainState q × ℝ => t.1.x) :=
    (measurable_fst.comp measurable_coords).comp measurable_fst
  have hD : Measurable (Function.uncurry D) := (h.measurable.comp (hx.prodMk measurable_snd)).inner
    ((measurable_subtype_coe.comp hx).sub_const u.val)
  have hv (s : TrainState q) : ‖s.x.val - u.val‖ ≤ 2 * q.R :=
    (norm_sub_le _ _).trans (by linarith [within s.x, within u])
  have hm (s : TrainState q) := PolynomialMixingScore.inner_raw_moment h (by linarith) hG s.x _ (hv s)
  exact PolynomialMixingScore.adaptive_score_moment π (step_measurable h.measurable) hD hp hp2
    (fun s => (h.integrable s.x).inner_const _) (fun s => (hm s).1) (fun s => (hm s).2) (start q) n

omit [IsProbabilityMeasure π] in
lemma path_gap (h : SubgradientOracle q f g π) (hc : ConvexOn ℝ (Domain q) f)
    (hR : 0 < q.R) (hG : 0 < q.G) (u : Point q) {n : ℕ} (hn : 0 < n) (ξ : ℕ → ℝ) :
    (n : ℝ) * (f (average g n ξ).val - f u.val) ≤ 3 * q.R * q.G +
      3 * q.R * Real.sqrt (∑ i ∈ Finset.range n, ‖g (state g i ξ).x (ξ i)‖ ^ 2) + ‖deviation g π u n ξ‖ := by
  apply (average_gap hc u hn ξ).trans
  have hh (x : Point q) : f x.val - f u.val ≤ ∫ z, ⟪g x z, x.val - u.val⟫ ∂π := by
    have he (z : ℝ) : ⟪g x z, x.val - u.val⟫ = ⟪x.val - u.val, g x z⟫ := real_inner_comm _ _
    simp_rw [he]
    rw [integral_inner (h.integrable x), real_inner_comm]
    have hsub := h.support x u
    rw [← neg_sub x.val u.val, inner_neg_right] at hsub
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun i _ => hh (state g i ξ).x)
  have hr := regret (g := g) hR hG u n ξ
  have hd := neg_le_abs (deviation g π u n ξ)
  simp only [deviation, Finset.sum_sub_distrib, Real.norm_eq_abs] at hd hsum ⊢
  linarith

end LongTails.Proofs.PolynomialMixingTraining

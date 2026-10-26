import LongTails.Proofs.ComponentEnvelopeEpochExecution
import LongTails.Proofs.ComponentEnvelopeEpochWork
open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators
namespace OracleTemplate.ComponentEnvelope
open LongTails.Setups.InterpolatedGeneralizedFiniteSum

noncomputable def startPotential (p : Params) (F : p.E → ℝ) (u : p.E)
    (s : ℕ) (snapshot y z : p.E) : ℝ :=
  let τ := (2 : ℝ) / (s + 4)
  ((1 / 2 - τ) * F y + (1 / 2 : ℝ) * p.n * F snapshot) / τ ^ 2 +
    3 * smoothing p * ‖z - u‖ ^ 2

noncomputable def endPotential (p : Params) (g : Fin p.n × p.E → p.E) (F : p.E → ℝ)
    (u : p.E) (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E)
    (samples : Fin p.n → Fin p.n) (state : EpochState p.E) : ℝ :=
  let τ := (2 : ℝ) / (s + 4)
  let final := Program.eval g (epochPlan p s snapshot cache p.n samples state)
  ((τ + 1 / 2) * epochLoss p g F s snapshot cache p.n samples state +
    (1 / 2 - τ) * F final.y) / τ ^ 2 + 3 * smoothing p * ‖final.z - u‖ ^ 2

lemma epoch_end_potential_expect (p : Params) (g : Fin p.n × p.E → p.E) (F : p.E → ℝ)
    (u : p.E) (hR : 0 ≤ p.R) (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E) (δ : ℝ)
    (hstep : ∀ state : EpochState p.E,
      state.y ∈ Metric.closedBall p.x0 p.R → state.z ∈ Metric.closedBall p.x0 p.R →
      (𝔼 i : Fin p.n,
        let next := epochUpdate p s snapshot
          (Program.eval g (componentPlan p i (queryMix s snapshot state)) - cache i + (p.n : ℝ)⁻¹ • ∑ j, cache j) state
        F next.y + 3 * smoothing p * ((2 : ℝ) / (s + 4)) ^ 2 * ‖next.z - u‖ ^ 2) ≤
        (1 / 2 - (2 : ℝ) / (s + 4)) * F state.y + (1 / 2 : ℝ) * F snapshot +
          3 * smoothing p * ((2 : ℝ) / (s + 4)) ^ 2 * ‖state.z - u‖ ^ 2 + δ)
    (state : EpochState p.E) (hy : state.y ∈ Metric.closedBall p.x0 p.R)
    (hz : state.z ∈ Metric.closedBall p.x0 p.R) :
    (𝔼 samples : Fin p.n → Fin p.n, endPotential p g F u s snapshot cache samples state) ≤
      startPotential p F u s snapshot state.y state.z + p.n * δ / ((2 : ℝ) / (s + 4)) ^ 2 := by
  let τ := (2 : ℝ) / (s + 4)
  let V := fun state : EpochState p.E => 3 * smoothing p * τ ^ 2 * ‖state.z - u‖ ^ 2
  let P := fun state : EpochState p.E => state.y ∈ Metric.closedBall p.x0 p.R ∧ state.z ∈ Metric.closedBall p.x0 p.R
  have ht : 0 < τ := (epoch_tau_bounds s).1
  have hav := epoch_loss_potential p g F V s snapshot cache P (1 / 2 - τ)
    ((1 / 2 : ℝ) * F snapshot + δ)
    (fun state _ i => epochUpdate_mem p hR s snapshot _ state)
    (fun state hs => by
      have hh := hstep state hs.1 hs.2
      dsimp [V, τ]
      linarith only [hh]) p.n state ⟨hy, hz⟩
  have hscaled := div_le_div_of_nonneg_right hav (sq_nonneg τ)
  have he : 1 - (1 / 2 - τ) = τ + 1 / 2 := by ring
  rw [he] at hscaled
  dsimp [V] at hscaled
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at hscaled
  dsimp [endPotential, startPotential]
  change (𝔼 samples : Fin p.n → Fin p.n,
    (((τ + 1 / 2) * epochLoss p g F s snapshot cache p.n samples state +
      (1 / 2 - τ) * F (Program.eval g (epochPlan p s snapshot cache p.n samples state)).y) / τ ^ 2 +
      3 * smoothing p * ‖(Program.eval g (epochPlan p s snapshot cache p.n samples state)).z - u‖ ^ 2)) ≤ _
  simp only [Finset.expect_add_distrib, ← Finset.expect_div, ← Finset.mul_expect]
  change _ ≤ ((1 / 2 - τ) * F state.y + (1 / 2 : ℝ) * p.n * F snapshot) / τ ^ 2 +
    3 * smoothing p * ‖state.z - u‖ ^ 2 + p.n * δ / τ ^ 2
  rw [add_div, add_div] at hscaled
  have hnorm : (3 * smoothing p * τ ^ 2 *
      (𝔼 samples : Fin p.n → Fin p.n, ‖(Program.eval g (epochPlan p s snapshot cache p.n samples state)).z - u‖ ^ 2)) / τ ^ 2 =
      3 * smoothing p * (𝔼 samples : Fin p.n → Fin p.n, ‖(Program.eval g (epochPlan p s snapshot cache p.n samples state)).z - u‖ ^ 2) := by
    field_simp
  rw [hnorm] at hscaled
  convert hscaled using 1 <;> field_simp
  all_goals ring

lemma next_start_potential_le (p : Params) (g : Fin p.n × p.E → p.E) (F : p.E → ℝ)
    (u : p.E) (hR : 0 ≤ p.R) (hF : ∀ x ∈ Metric.closedBall p.x0 p.R, 0 ≤ F x)
    (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E)
    (samples : Fin p.n → Fin p.n) (state : EpochState p.E)
    (hy : state.y ∈ Metric.closedBall p.x0 p.R) (hz : state.z ∈ Metric.closedBall p.x0 p.R)
    (hmean : (p.n : ℝ) * F ((p.n : ℝ)⁻¹ •
      (Program.eval g (epochPlan p s snapshot cache p.n samples state)).total) ≤
      epochLoss p g F s snapshot cache p.n samples state) :
    let final := Program.eval g (epochPlan p s snapshot cache p.n samples state)
    startPotential p F u (s + 1) ((p.n : ℝ)⁻¹ • final.total) final.y final.z ≤
      endPotential p g F u s snapshot cache samples state := by
  let final := Program.eval g (epochPlan p s snapshot cache p.n samples state)
  let sum := epochLoss p g F s snapshot cache p.n samples state
  let τ := (2 : ℝ) / ((s : ℝ) + 4 + 1)
  let prev := (2 : ℝ) / ((s : ℝ) + 4)
  have hf := (epoch_eval_bounds p g hR s snapshot cache p.n samples state hy hz).1
  have hlast : 0 ≤ F final.y := hF final.y hf.1
  have hsum : F final.y ≤ sum := epoch_loss_last p g hR F hF s snapshot cache p.n (NeZero.pos _) samples state
  have hc := epoch_coefficient_comparison (t := (s : ℝ) + 4) (by have hn : 0 ≤ (s : ℝ) := Nat.cast_nonneg _; linarith)
  change (1 - τ) / τ ^ 2 ≤ 1 / prev ^ 2 ∧
    (1 / 2 : ℝ) / τ ^ 2 ≤ (prev + 1 / 2) / prev ^ 2 at hc
  have hcoeff := epoch_coefficients_bound hlast hsum hc.1 hc.2
  have hm := mul_le_mul_of_nonneg_left hmean (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hnum : ((1 / 2 - τ) * F final.y + (1 / 2 : ℝ) * p.n * F ((p.n : ℝ)⁻¹ • final.total)) / τ ^ 2 ≤
      ((1 / 2 - τ) * F final.y + (1 / 2 : ℝ) * sum) / τ ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg τ)
    change (1 / 2 - τ) * F final.y + _ ≤ _
    change (1 / 2 : ℝ) * (p.n * F ((p.n : ℝ)⁻¹ • final.total)) ≤ (1 / 2 : ℝ) * sum at hm
    nlinarith
  dsimp [startPotential, endPotential]
  push_cast
  rw [show (s : ℝ) + 1 + 4 = (s : ℝ) + 4 + 1 by ring]
  change ((1 / 2 - τ) * F final.y + (1 / 2 : ℝ) * p.n * F ((p.n : ℝ)⁻¹ • final.total)) / τ ^ 2 +
      3 * smoothing p * ‖final.z - u‖ ^ 2 ≤
    ((prev + 1 / 2) * sum + (1 / 2 - prev) * F final.y) / prev ^ 2 +
      3 * smoothing p * ‖final.z - u‖ ^ 2
  linarith [hnum.trans hcoeff]


lemma end_potential_controls_mean (p : Params) (g : Fin p.n × p.E → p.E) (F : p.E → ℝ)
    (u : p.E) (hR : 0 ≤ p.R) (hμ : 0 ≤ smoothing p)
    (hF : ∀ x ∈ Metric.closedBall p.x0 p.R, 0 ≤ F x)
    (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E)
    (samples : Fin p.n → Fin p.n) (state : EpochState p.E)
    (hy : state.y ∈ Metric.closedBall p.x0 p.R) (hz : state.z ∈ Metric.closedBall p.x0 p.R)
    (hmean : (p.n : ℝ) * F ((p.n : ℝ)⁻¹ •
      (Program.eval g (epochPlan p s snapshot cache p.n samples state)).total) ≤
      epochLoss p g F s snapshot cache p.n samples state) :
    (p.n : ℝ) * F ((p.n : ℝ)⁻¹ •
      (Program.eval g (epochPlan p s snapshot cache p.n samples state)).total) ≤
      2 * ((2 : ℝ) / (s + 4)) ^ 2 * endPotential p g F u s snapshot cache samples state := by
  let final := Program.eval g (epochPlan p s snapshot cache p.n samples state)
  let sum := epochLoss p g F s snapshot cache p.n samples state
  have hf := (epoch_eval_bounds p g hR s snapshot cache p.n samples state hy hz).1
  have hlast : 0 ≤ F final.y := hF final.y hf.1
  have hsum : F final.y ≤ sum := epoch_loss_last p g hR F hF s snapshot cache p.n (NeZero.pos _) samples state
  have hp := epoch_potential_bounds (epoch_tau_bounds s).1 (epoch_tau_bounds s).2 hμ hlast hsum
    (sq_nonneg ‖final.z - u‖) (le_refl (endPotential p g F u s snapshot cache samples state))
  exact hmean.trans hp.1

lemma epoch_potential_transition (p : Params) (g : Fin p.n × p.E → p.E) (F : p.E → ℝ)
    (u : p.E) (hR : 0 ≤ p.R) (hμ : 0 ≤ smoothing p)
    (hF : ∀ x ∈ Metric.closedBall p.x0 p.R, 0 ≤ F x) (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E) (δ : ℝ)
    (hstep : ∀ state : EpochState p.E,
      state.y ∈ Metric.closedBall p.x0 p.R → state.z ∈ Metric.closedBall p.x0 p.R →
      (𝔼 i : Fin p.n,
        let next := epochUpdate p s snapshot
          (Program.eval g (componentPlan p i (queryMix s snapshot state)) - cache i + (p.n : ℝ)⁻¹ • ∑ j, cache j) state
        F next.y + 3 * smoothing p * ((2 : ℝ) / (s + 4)) ^ 2 * ‖next.z - u‖ ^ 2) ≤
        (1 / 2 - (2 : ℝ) / (s + 4)) * F state.y + (1 / 2 : ℝ) * F snapshot +
          3 * smoothing p * ((2 : ℝ) / (s + 4)) ^ 2 * ‖state.z - u‖ ^ 2 + δ)
    (y z : p.E) (hy : y ∈ Metric.closedBall p.x0 p.R) (hz : z ∈ Metric.closedBall p.x0 p.R)
    (hmean : ∀ samples : Fin p.n → Fin p.n,
      (p.n : ℝ) * F ((p.n : ℝ)⁻¹ • (Program.eval g (epochPlan p s snapshot cache p.n samples ⟨y, z, 0⟩)).total) ≤
        epochLoss p g F s snapshot cache p.n samples ⟨y, z, 0⟩) :
    ((𝔼 samples : Fin p.n → Fin p.n,
      let final := Program.eval g (epochPlan p s snapshot cache p.n samples ⟨y, z, 0⟩)
      startPotential p F u (s + 1) ((p.n : ℝ)⁻¹ • final.total) final.y final.z) ≤
        startPotential p F u s snapshot y z + p.n * δ / ((2 : ℝ) / (s + 4)) ^ 2) ∧
    ((p.n : ℝ) * (𝔼 samples : Fin p.n → Fin p.n,
      F ((p.n : ℝ)⁻¹ • (Program.eval g (epochPlan p s snapshot cache p.n samples ⟨y, z, 0⟩)).total)) ≤
      2 * ((2 : ℝ) / (s + 4)) ^ 2 *
        (startPotential p F u s snapshot y z + p.n * δ / ((2 : ℝ) / (s + 4)) ^ 2)) := by
  have he := epoch_end_potential_expect p g F u hR s snapshot cache δ hstep ⟨y, z, 0⟩ hy hz
  constructor
  · have ht := Finset.expect_le_expect (s := Finset.univ) (fun samples _ =>
      next_start_potential_le p g F u hR hF s snapshot cache samples ⟨y, z, 0⟩ hy hz (hmean samples))
    exact ht.trans he
  · have ht := Finset.expect_le_expect (s := Finset.univ) (fun samples _ =>
      end_potential_controls_mean p g F u hR hμ hF s snapshot cache samples ⟨y, z, 0⟩ hy hz (hmean samples))
    simp only [← Finset.mul_expect] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left he (by positivity))

lemma start_potential_bounds (p : Params) (F : p.E → ℝ) (u : p.E)
    (hμ : 0 ≤ smoothing p) (s : ℕ) (hs : 1 ≤ s) (w y z : p.E)
    (hw : 0 ≤ F w) (hy : 0 ≤ F y) :
    0 ≤ startPotential p F u s w y z ∧
    (p.n : ℝ) * F w ≤ 2 * ((2 : ℝ) / (s + 4)) ^ 2 * startPotential p F u s w y z ∧
    F y ≤ 10 * ((2 : ℝ) / (s + 4)) ^ 2 * startPotential p F u s w y z := by
  let τ := (2 : ℝ) / (s + 4)
  have ht : 0 < τ := (epoch_tau_bounds s).1
  have ht4 : τ ≤ 2 / 5 := by
    apply (div_le_iff₀ (by positivity : 0 < (s : ℝ) + 4)).mpr
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hc : 0 ≤ 1 / 2 - τ := by linarith
  have hn : 0 ≤ (p.n : ℝ) := Nat.cast_nonneg _
  have hd : 0 ≤ 3 * smoothing p * ‖z - u‖ ^ 2 := by positivity
  have hid : τ ^ 2 * startPotential p F u s w y z =
      (1 / 2 - τ) * F y + (1 / 2 : ℝ) * p.n * F w +
        τ ^ 2 * (3 * smoothing p * ‖z - u‖ ^ 2) := by
    change τ ^ 2 * (((1 / 2 - τ) * F y + (1 / 2 : ℝ) * p.n * F w) / τ ^ 2 +
      3 * smoothing p * ‖z - u‖ ^ 2) = _
    field_simp
  have hterm : 0 ≤ τ ^ 2 * (3 * smoothing p * ‖z - u‖ ^ 2) := mul_nonneg (sq_nonneg τ) hd
  have hleft : 0 ≤ (1 / 2 - τ) * F y := mul_nonneg hc hy
  have hright : 0 ≤ (1 / 2 : ℝ) * p.n * F w := by positivity
  have hp : 0 ≤ startPotential p F u s w y z := by
    dsimp [startPotential]
    change 0 ≤ ((1 / 2 - τ) * F y + (1 / 2 : ℝ) * p.n * F w) / τ ^ 2 + _
    positivity
  refine ⟨hp, ?_, ?_⟩
  · change (p.n : ℝ) * F w ≤ 2 * τ ^ 2 * _
    nlinarith
  · change F y ≤ 10 * τ ^ 2 * _
    have hcoeff : (1 / 10 : ℝ) * F y ≤ (1 / 2 - τ) * F y := by nlinarith
    nlinarith

open LongTails.Proofs.RecursiveEnvelopeGeometry OracleTemplate.FiniteSum
lemma model_epoch_transition (p : Params) (g : Fin p.n × p.E → p.E)
    (f : Fin p.n → p.E → ℝ) (G : Fin p.n × p.E → p.E)
    (hm : ∀ i, Model (smoothing p) (f i) (fun x => G (i, x)))
    (hR : 0 ≤ p.R) (hζ : 0 ≤ tolerance p) (u : p.E)
    (hu : u ∈ Metric.closedBall p.x0 p.R) (hgu : fullGradient G u = 0)
    (hrad : ∀ a ∈ Metric.closedBall p.x0 p.R, ‖a - u‖ ≤ 2 * p.R)
    (herr : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      ‖Program.eval g (componentPlan p i x) - G (i, x)‖ ≤ tolerance p)
    (s : ℕ) (w y z : p.E)
    (hw : w ∈ Metric.closedBall p.x0 p.R)
    (hy : y ∈ Metric.closedBall p.x0 p.R) (hz : z ∈ Metric.closedBall p.x0 p.R) :
    let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
    let F := fun x => H x - H u
    let cache := fun i => Program.eval g (componentPlan p i w)
    let next := fun samples : Fin p.n → Fin p.n => Program.eval g (epochPlan p s w cache p.n samples ⟨y, z, 0⟩)
    let err := p.n * (4 * p.R * tolerance p) / ((2 : ℝ) / (s + 4)) ^ 2
    ((𝔼 samples : Fin p.n → Fin p.n,
      startPotential p F u (s + 1) ((p.n : ℝ)⁻¹ • (next samples).total) (next samples).y (next samples).z) ≤
        startPotential p F u s w y z + err) ∧
    ((p.n : ℝ) * (𝔼 samples : Fin p.n → Fin p.n, F ((p.n : ℝ)⁻¹ • (next samples).total)) ≤
      2 * ((2 : ℝ) / (s + 4)) ^ 2 * (startPotential p F u s w y z + err)) := by
  let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let F := fun x => H x - H u
  let cache := fun i => Program.eval g (componentPlan p i w)
  have hmodel := finiteSum_model hm
  have hF (x : p.E) : 0 ≤ F x := by
    have hh := hmodel.lower u x
    rw [hgu, inner_zero_left, add_zero] at hh
    exact sub_nonneg.mpr hh
  refine epoch_potential_transition p g F u hR hmodel.pos.le (fun x _ => hF x) s w cache
    (4 * p.R * tolerance p) ?_ y z hy hz ?_
  · intro state hsy hsz
    exact epoch_update_potential p g f G hm hR hζ u hu hgu hrad herr s w cache state hw hsy hsz
      (fun i => herr i w hw)
  · intro samples
    exact epoch_mean_gap p g H (fullGradient G) hmodel.lower s w cache p.n (NeZero.pos _) samples y z u

lemma initial_potential_expect (p : Params) (F : p.E → ℝ) (u : p.E)
    {ι : Type*} [Fintype ι] [Nonempty ι] (w z : ι → p.E)
    (hμ : 0 ≤ smoothing p)
    (hgap : (p.n : ℝ) * (𝔼 i, F (w i)) ≤ smoothing p * p.R ^ 2)
    (hdist : ∀ i, ‖z i - u‖ ≤ 2 * p.R) :
    (𝔼 i, startPotential p F u 0 (w i) (w i) (z i)) ≤ 14 * smoothing p * p.R ^ 2 := by
  have hd := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
    pow_le_pow_left₀ (norm_nonneg (z i - u)) (hdist i) 2)
  simp only [Fintype.expect_const] at hd
  have hid (i : ι) : startPotential p F u 0 (w i) (w i) (z i) =
      2 * p.n * F (w i) + 3 * smoothing p * ‖z i - u‖ ^ 2 := by
    norm_num [startPotential]
    ring
  simp only [hid, Finset.expect_add_distrib, ← Finset.mul_expect]
  have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 3 * smoothing p by positivity)
  nlinarith

lemma epoch_work_potential (p : Params) (g : Fin p.n × p.E → p.E) (F : p.E → ℝ)
    (u : p.E) (hR : 0 ≤ p.R) (hμ : 0 ≤ smoothing p)
    (hF : ∀ x ∈ Metric.closedBall p.x0 p.R, 0 ≤ F x)
    (s : ℕ) (hs : 1 ≤ s) (w : p.E) (cache : Fin p.n → p.E) (C δ : ℝ)
    (hquery : ∀ state : EpochState p.E,
      state.y ∈ Metric.closedBall p.x0 p.R → state.z ∈ Metric.closedBall p.x0 p.R →
      F (queryMix s w state) ≤ F w + F state.y + C)
    (y z : p.E) (hw : w ∈ Metric.closedBall p.x0 p.R)
    (hy : y ∈ Metric.closedBall p.x0 p.R) (hz : z ∈ Metric.closedBall p.x0 p.R)
    (he : (𝔼 samples : Fin p.n → Fin p.n, endPotential p g F u s w cache samples ⟨y, z, 0⟩) ≤
      startPotential p F u s w y z + p.n * δ / ((2 : ℝ) / (s + 4)) ^ 2) :
    (p.n : ℝ) * F w + (𝔼 samples : Fin p.n → Fin p.n,
      epochQueryLoss p g F s w cache p.n samples ⟨y, z, 0⟩) ≤
      16 * ((2 : ℝ) / (s + 4)) ^ 2 * startPotential p F u s w y z + p.n * C + 2 * p.n * δ := by
  let τ := (2 : ℝ) / (s + 4)
  have ht : 0 < τ := (epoch_tau_bounds s).1
  have hpoint samples := epoch_query_sum_bound p g F hR s w cache C hquery p.n samples ⟨y, z, 0⟩ hy hz
  have hlast samples : 0 ≤ F (Program.eval g (epochPlan p s w cache p.n samples ⟨y, z, 0⟩)).y :=
    hF _ (epoch_eval_bounds p g hR s w cache p.n samples ⟨y, z, 0⟩ hy hz).1.1
  have hsum samples := epoch_loss_last p g hR F hF s w cache p.n (NeZero.pos _) samples ⟨y, z, 0⟩
  have hbound samples := (epoch_potential_bounds ht (epoch_tau_bounds s).2 hμ (hlast samples) (hsum samples)
    (sq_nonneg ‖(Program.eval g (epochPlan p s w cache p.n samples ⟨y, z, 0⟩)).z - u‖)
    (le_refl (endPotential p g F u s w cache samples ⟨y, z, 0⟩))).1
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun samples _ => by
    have hp := hpoint samples
    have hb := hbound samples
    have hl := hlast samples
    exact (show epochQueryLoss p g F s w cache p.n samples ⟨y, z, 0⟩ ≤
      p.n * (F w + C) + 2 * τ ^ 2 * endPotential p g F u s w cache samples ⟨y, z, 0⟩ + F y by linarith))
  simp only [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect] at hav
  have hp := start_potential_bounds p F u hμ s hs w y z (hF w hw) (hF y hy)
  have hscaled := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * τ ^ 2 by positivity)
  have hid : 2 * τ ^ 2 * (startPotential p F u s w y z + p.n * δ / τ ^ 2) =
      2 * τ ^ 2 * startPotential p F u s w y z + 2 * p.n * δ := by field_simp
  change _ ≤ 2 * τ ^ 2 * (startPotential p F u s w y z + p.n * δ / τ ^ 2) at hscaled
  rw [hid] at hscaled
  change _ ≤ 16 * τ ^ 2 * startPotential p F u s w y z + p.n * C + 2 * p.n * δ
  nlinarith [hp.2.1, hp.2.2]

lemma model_epoch_nominal_cost (p : Params) (g : Fin p.n × p.E → p.E)
    (f : Fin p.n → p.E → ℝ) (G : Fin p.n × p.E → p.E)
    (hm : ∀ i, Model (smoothing p) (f i) (fun x => G (i, x)))
    (hR : 0 ≤ p.R) (hζ : 0 ≤ tolerance p) (u : p.E)
    (hu : u ∈ Metric.closedBall p.x0 p.R) (hgu : fullGradient G u = 0)
    (hrad : ∀ a ∈ Metric.closedBall p.x0 p.R, ‖a - u‖ ≤ 2 * p.R)
    (herr : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      ‖Program.eval g (componentPlan p i x) - G (i, x)‖ ≤ tolerance p)
    (C β : ℝ) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hcost : ∀ x ∈ Metric.closedBall p.x0 p.R,
      (𝔼 i : Fin p.n, (Program.cost g (componentPlan p i x) : ℝ)) ≤ C * (1 + β *
        (LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f u)))
    (s : ℕ) (hs : 1 ≤ s) (w y z : p.E)
    (hw : w ∈ Metric.closedBall p.x0 p.R)
    (hy : y ∈ Metric.closedBall p.x0 p.R) (hz : z ∈ Metric.closedBall p.x0 p.R) :
    let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
    let F := fun x => H x - H u
    let cache := fun i => Program.eval g (componentPlan p i w)
    (∑ i, (Program.cost g (componentPlan p i w) : ℝ)) +
      (𝔼 samples : Fin p.n → Fin p.n, (Program.cost g (epochPlan p s w cache p.n samples ⟨y, z, 0⟩) : ℝ)) ≤
      C * (2 * p.n + β * (16 * ((2 : ℝ) / (s + 4)) ^ 2 * startPotential p F u s w y z +
        4 * p.n * smoothing p * ((2 : ℝ) / (s + 4)) ^ 2 * p.R ^ 2 + 2 * p.n * (4 * p.R * tolerance p))) := by
  let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let F := fun x => H x - H u
  let cache := fun i => Program.eval g (componentPlan p i w)
  have hmodel := finiteSum_model hm
  have hF (x : p.E) : 0 ≤ F x := by
    have hh := hmodel.lower u x
    rw [hgu, inner_zero_left, add_zero] at hh
    exact sub_nonneg.mpr hh
  have hstep := fun state hy' hz' => epoch_update_potential p g f G hm hR hζ u hu hgu hrad herr s w cache state hw hy' hz'
    (fun i => herr i w hw)
  have he := epoch_end_potential_expect p g F u hR s w cache (4 * p.R * tolerance p)
    hstep ⟨y, z, 0⟩ hy hz
  have hwork := epoch_work_potential p g F u hR hmodel.pos.le (fun x _ => hF x) s hs w cache
    (4 * smoothing p * ((2 : ℝ) / (s + 4)) ^ 2 * p.R ^ 2) (4 * p.R * tolerance p)
    (fun state hy' hz' => query_gap_ball p H (fullGradient G) hmodel u hgu s w state hy' hz') y z hw hy hz he
  have hc := epoch_nominal_cost_from_work p g F hR C β _ hC hβ hcost s w cache y z hw hy hz hwork
  convert hc using 1
  ring

end OracleTemplate.ComponentEnvelope

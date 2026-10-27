import LongTails.Proofs.ComponentEnvelopeWarmupExecution
import LongTails.Proofs.ComponentEnvelopeEpoch
open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators
namespace OracleTemplate.ComponentEnvelope
open LongTails.Setups.InterpolatedGeneralizedFiniteSum

noncomputable def epochLoss (p : Params) (g : Fin p.n × p.E → p.E) (F : p.E → ℝ)
    (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E) :
    (k : ℕ) → (Fin k → Fin p.n) → EpochState p.E → ℝ
  | 0, _, _ => 0
  | k + 1, samples, state =>
      let q := queryMix s snapshot state
      let v := Program.eval g (componentPlan p (samples 0) q) - cache (samples 0) + (p.n : ℝ)⁻¹ • ∑ i, cache i
      let next := epochUpdate p s snapshot v state
      F next.y + epochLoss p g F s snapshot cache k (fun j => samples j.succ) next

lemma epoch_loss_potential (p : Params) (g : Fin p.n × p.E → p.E) (F : p.E → ℝ)
    (V : EpochState p.E → ℝ) (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E)
    (P : EpochState p.E → Prop) (a b : ℝ)
    (hnext : ∀ state, P state → ∀ i,
      P (epochUpdate p s snapshot
        (Program.eval g (componentPlan p i (queryMix s snapshot state)) - cache i + (p.n : ℝ)⁻¹ • ∑ j, cache j) state))
    (hstep : ∀ state, P state →
      (𝔼 i : Fin p.n,
        let next := epochUpdate p s snapshot
          (Program.eval g (componentPlan p i (queryMix s snapshot state)) - cache i + (p.n : ℝ)⁻¹ • ∑ j, cache j) state
        F next.y + V next) ≤ a * F state.y + V state + b)
    (k : ℕ) (state : EpochState p.E) (hstate : P state) :
    (𝔼 samples : Fin k → Fin p.n,
      let final := Program.eval g (epochPlan p s snapshot cache k samples state)
      (1 - a) * epochLoss p g F s snapshot cache k samples state + a * F final.y + V final) ≤
      a * F state.y + V state + k * b := by
  induction k generalizing state with
  | zero => simp [epochPlan, Program.eval, epochLoss]
  | succ k ih =>
      let next := fun i => epochUpdate p s snapshot
        (Program.eval g (componentPlan p i (queryMix s snapshot state)) - cache i + (p.n : ℝ)⁻¹ • ∑ j, cache j) state
      have ht (i : Fin p.n) := ih (next i) (hnext state hstate i)
      rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
      simp only [epochPlan, Program.eval_bind, epochLoss, Fin.cons_zero, Fin.cons_succ]
      have hav := Finset.expect_le_expect (s := Finset.univ)
        (fun i _ => add_le_add_left (ht i) ((1 - a) * F (next i).y))
      have hs := hstep state hstate
      change (𝔼 i : Fin p.n, (F (next i).y + V (next i))) ≤ a * F state.y + V state + b at hs
      change (𝔼 i : Fin p.n, 𝔼 samples : Fin k → Fin p.n,
        ((1 - a) * (F (next i).y + epochLoss p g F s snapshot cache k samples (next i)) +
          a * F (Program.eval g (epochPlan p s snapshot cache k samples (next i))).y +
          V (Program.eval g (epochPlan p s snapshot cache k samples (next i))))) ≤ _
      simp only [mul_add, Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at hav hs ⊢
      rw [Nat.cast_add, Nat.cast_one]
      nlinarith

lemma epoch_tau_bounds (s : ℕ) : 0 < (2 : ℝ) / (s + 4) ∧ (2 : ℝ) / (s + 4) ≤ 1 / 2 := by
  have hd : 0 < (s : ℝ) + 4 := by positivity
  constructor
  · positivity
  · apply (div_le_iff₀ hd).mpr
    have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
    linarith

lemma epochUpdate_mem (p : Params) (hR : 0 ≤ p.R) (s : ℕ) (snapshot v : p.E)
    (state : EpochState p.E) :
    (epochUpdate p s snapshot v state).y ∈ Metric.closedBall p.x0 p.R ∧
      (epochUpdate p s snapshot v state).z ∈ Metric.closedBall p.x0 p.R := by
  constructor <;> apply projectBall_mem p hR

lemma queryMix_mem (p : Params) (s : ℕ) (snapshot : p.E) (state : EpochState p.E)
    (hw : snapshot ∈ Metric.closedBall p.x0 p.R)
    (hy : state.y ∈ Metric.closedBall p.x0 p.R) (hz : state.z ∈ Metric.closedBall p.x0 p.R) :
    queryMix s snapshot state ∈ Metric.closedBall p.x0 p.R :=
  query_mixture_mem (convex_closedBall p.x0 p.R) (epoch_tau_bounds s).1.le
    (epoch_tau_bounds s).2 hy hz hw

open LongTails.Proofs.RecursiveEnvelopeGeometry
open OracleTemplate.FiniteSum
lemma epoch_update_potential (p : Params) (g : Fin p.n × p.E → p.E)
    (f : Fin p.n → p.E → ℝ) (G : Fin p.n × p.E → p.E)
    (hm : ∀ i, Model (smoothing p) (f i) (fun x => G (i, x)))
    (hR : 0 ≤ p.R) (hζ : 0 ≤ tolerance p) (u : p.E)
    (hu : u ∈ Metric.closedBall p.x0 p.R) (hgu : fullGradient G u = 0)
    (hrad : ∀ a ∈ Metric.closedBall p.x0 p.R, ‖a - u‖ ≤ 2 * p.R)
    (herr : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      ‖Program.eval g (componentPlan p i x) - G (i, x)‖ ≤ tolerance p)
    (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E) (state : EpochState p.E)
    (hw : snapshot ∈ Metric.closedBall p.x0 p.R)
    (hy : state.y ∈ Metric.closedBall p.x0 p.R) (hz : state.z ∈ Metric.closedBall p.x0 p.R)
    (hcache : ∀ i, ‖cache i - G (i, snapshot)‖ ≤ tolerance p) :
    let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
    let τ := (2 : ℝ) / (s + 4)
    let next := fun i => epochUpdate p s snapshot
      (Program.eval g (componentPlan p i (queryMix s snapshot state)) - cache i + (p.n : ℝ)⁻¹ • ∑ j, cache j) state
    (𝔼 i : Fin p.n, (H (next i).y - H u + 3 * smoothing p * τ ^ 2 * ‖(next i).z - u‖ ^ 2)) ≤
      (1 / 2 - τ) * (H state.y - H u) + (1 / 2 : ℝ) * (H snapshot - H u) +
      3 * smoothing p * τ ^ 2 * ‖state.z - u‖ ^ 2 + 4 * p.R * tolerance p := by
  let v := fun i => Program.eval g (componentPlan p i (queryMix s snapshot state)) - cache i + (p.n : ℝ)⁻¹ • ∑ j, cache j
  have hq := queryMix_mem p s snapshot state hw hy hz
  have he (i : Fin p.n) : ‖v i - estimator G snapshot (queryMix s snapshot state) i‖ ≤ 3 * tolerance p :=
    cached_estimator_error G cache snapshot (queryMix s snapshot state)
      (Program.eval g (componentPlan p i (queryMix s snapshot state))) i hcache
        (herr i (queryMix s snapshot state) hq)
  have hh := projected_accelerated_inexact ⟨u, hu⟩ (isCompact_closedBall p.x0 p.R)
    (convex_closedBall p.x0 p.R) hm (epoch_tau_bounds s).1 (epoch_tau_bounds s).2
    hR hζ state.y state.z snapshot u v hy hw hu hgu hrad he
  simpa only [epochUpdate, projectBall, v, queryMix] using hh


lemma epoch_support_sum (p : Params) (g : Fin p.n × p.E → p.E)
    (F : p.E → ℝ) (G : p.E → p.E)
    (hlower : ∀ a x, F a + ⟪G a, x - a⟫ ≤ F x)
    (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E)
    (k : ℕ) (samples : Fin k → Fin p.n) (state : EpochState p.E) (a u : p.E) :
    (k : ℝ) * (F a - F u) +
      ⟪G a, (Program.eval g (epochPlan p s snapshot cache k samples state)).total - state.total - (k : ℝ) • a⟫ ≤
      epochLoss p g (fun z => F z - F u) s snapshot cache k samples state := by
  induction k generalizing state with
  | zero => simp [epochPlan, Program.eval, epochLoss]
  | succ k ih =>
      let next := epochUpdate p s snapshot
        (Program.eval g (componentPlan p (samples 0) (queryMix s snapshot state)) - cache (samples 0) + (p.n : ℝ)⁻¹ • ∑ j, cache j) state
      let rest := fun j : Fin k => samples j.succ
      let final := Program.eval g (epochPlan p s snapshot cache k rest next)
      have ht := ih rest next
      have hy := hlower a next.y
      have htotal : next.total = state.total + next.y := rfl
      simp only [epochPlan, Program.eval_bind, epochLoss, Nat.cast_add, Nat.cast_one]
      change ((k : ℝ) + 1) * (F a - F u) +
        ⟪G a, final.total - state.total - ((k : ℝ) + 1) • a⟫ ≤
        F next.y - F u + epochLoss p g (fun z => F z - F u) s snapshot cache k rest next
      have hid : final.total - state.total - ((k : ℝ) + 1) • a =
          (next.y - a) + (final.total - next.total - (k : ℝ) • a) := by rw [htotal]; module
      rw [hid, inner_add_right]
      change (k : ℝ) * (F a - F u) + ⟪G a, final.total - next.total - (k : ℝ) • a⟫ ≤ _ at ht
      linarith

lemma epoch_mean_gap (p : Params) (g : Fin p.n × p.E → p.E)
    (F : p.E → ℝ) (G : p.E → p.E)
    (hlower : ∀ a x, F a + ⟪G a, x - a⟫ ≤ F x)
    (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E)
    (k : ℕ) (hk : 0 < k) (samples : Fin k → Fin p.n) (y z u : p.E) :
    (k : ℝ) * (F ((k : ℝ)⁻¹ • (Program.eval g (epochPlan p s snapshot cache k samples ⟨y, z, 0⟩)).total) - F u) ≤
      epochLoss p g (fun z => F z - F u) s snapshot cache k samples ⟨y, z, 0⟩ := by
  have hh := epoch_support_sum p g F G hlower s snapshot cache k samples ⟨y, z, 0⟩
    ((k : ℝ)⁻¹ • (Program.eval g (epochPlan p s snapshot cache k samples ⟨y, z, 0⟩)).total) u
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  simpa only [sub_zero, smul_smul, mul_inv_cancel₀ hk0, one_smul, sub_self, inner_zero_right, add_zero] using hh


lemma epoch_eval_bounds (p : Params) (g : Fin p.n × p.E → p.E) (hR : 0 ≤ p.R)
    (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E)
    (k : ℕ) (samples : Fin k → Fin p.n) (state : EpochState p.E)
    (hy : state.y ∈ Metric.closedBall p.x0 p.R) (hz : state.z ∈ Metric.closedBall p.x0 p.R) :
    let final := Program.eval g (epochPlan p s snapshot cache k samples state)
    (final.y ∈ Metric.closedBall p.x0 p.R ∧ final.z ∈ Metric.closedBall p.x0 p.R) ∧
      ‖final.total - state.total - (k : ℝ) • p.x0‖ ≤ k * p.R := by
  induction k generalizing state with
  | zero => simpa [epochPlan, Program.eval] using And.intro hy hz
  | succ k ih =>
      let next := epochUpdate p s snapshot
        (Program.eval g (componentPlan p (samples 0) (queryMix s snapshot state)) - cache (samples 0) + (p.n : ℝ)⁻¹ • ∑ j, cache j) state
      let rest := fun j : Fin k => samples j.succ
      let final := Program.eval g (epochPlan p s snapshot cache k rest next)
      have hm : next.y ∈ Metric.closedBall p.x0 p.R ∧ next.z ∈ Metric.closedBall p.x0 p.R :=
        epochUpdate_mem p hR s snapshot _ state
      have ht := ih rest next hm.1 hm.2
      have htotal : next.total = state.total + next.y := rfl
      simp only [epochPlan, Program.eval_bind]
      change (final.y ∈ Metric.closedBall p.x0 p.R ∧ final.z ∈ Metric.closedBall p.x0 p.R) ∧
        ‖final.total - state.total - ((k + 1 : ℕ) : ℝ) • p.x0‖ ≤ (k + 1 : ℕ) * p.R
      refine ⟨ht.1, ?_⟩
      have hc : ‖next.y - p.x0‖ ≤ p.R := by simpa [dist_eq_norm] using hm.1
      have hid : final.total - state.total - ((k + 1 : ℕ) : ℝ) • p.x0 =
          (next.y - p.x0) + (final.total - next.total - (k : ℝ) • p.x0) := by
        rw [htotal]
        push_cast
        module
      rw [hid]
      have hh := norm_add_le (next.y - p.x0) (final.total - next.total - (k : ℝ) • p.x0)
      have hb := ht.2
      change ‖final.total - next.total - (k : ℝ) • p.x0‖ ≤ k * p.R at hb
      push_cast
      linarith

lemma epoch_mean_mem (p : Params) (g : Fin p.n × p.E → p.E) (hR : 0 ≤ p.R)
    (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E)
    (k : ℕ) (hk : 0 < k) (samples : Fin k → Fin p.n) (y z : p.E)
    (hy : y ∈ Metric.closedBall p.x0 p.R) (hz : z ∈ Metric.closedBall p.x0 p.R) :
    (k : ℝ)⁻¹ • (Program.eval g (epochPlan p s snapshot cache k samples ⟨y, z, 0⟩)).total ∈
      Metric.closedBall p.x0 p.R := by
  let total := (Program.eval g (epochPlan p s snapshot cache k samples ⟨y, z, 0⟩)).total
  have hb := (epoch_eval_bounds p g hR s snapshot cache k samples ⟨y, z, 0⟩ hy hz).2
  simp only [sub_zero] at hb
  have hk0 : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hid : (k : ℝ)⁻¹ • total - p.x0 = (k : ℝ)⁻¹ • (total - (k : ℝ) • p.x0) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hk0.ne', one_smul]
  rw [Metric.mem_closedBall, dist_eq_norm]
  change ‖(k : ℝ)⁻¹ • total - p.x0‖ ≤ p.R
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk0)]
  have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hk0.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hk0.ne', one_mul] using hh


lemma epoch_loss_nonneg (p : Params) (g : Fin p.n × p.E → p.E) (hR : 0 ≤ p.R)
    (F : p.E → ℝ) (hF : ∀ x ∈ Metric.closedBall p.x0 p.R, 0 ≤ F x)
    (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E)
    (k : ℕ) (samples : Fin k → Fin p.n) (state : EpochState p.E) :
    0 ≤ epochLoss p g F s snapshot cache k samples state := by
  induction k generalizing state with
  | zero => simp [epochLoss]
  | succ k ih =>
      let next := epochUpdate p s snapshot
        (Program.eval g (componentPlan p (samples 0) (queryMix s snapshot state)) - cache (samples 0) + (p.n : ℝ)⁻¹ • ∑ j, cache j) state
      have hn := hF next.y (epochUpdate_mem p hR s snapshot _ state).1
      exact add_nonneg hn (ih (fun j => samples j.succ) next)

lemma epoch_loss_last (p : Params) (g : Fin p.n × p.E → p.E) (hR : 0 ≤ p.R)
    (F : p.E → ℝ) (hF : ∀ x ∈ Metric.closedBall p.x0 p.R, 0 ≤ F x)
    (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E)
    (k : ℕ) (hk : 0 < k) (samples : Fin k → Fin p.n) (state : EpochState p.E) :
    F (Program.eval g (epochPlan p s snapshot cache k samples state)).y ≤
      epochLoss p g F s snapshot cache k samples state := by
  induction k generalizing state with
  | zero => omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simp [epochPlan, Program.eval_bind, Program.eval, epochLoss]
      · let next := epochUpdate p s snapshot
          (Program.eval g (componentPlan p (samples 0) (queryMix s snapshot state)) - cache (samples 0) + (p.n : ℝ)⁻¹ • ∑ j, cache j) state
        have hn := hF next.y (epochUpdate_mem p hR s snapshot _ state).1
        have ht := ih (Nat.pos_of_ne_zero hk0) (fun j => samples j.succ) next
        simp only [epochPlan, Program.eval_bind, epochLoss]
        change F (Program.eval g (epochPlan p s snapshot cache k (fun j => samples j.succ) next)).y ≤
          F next.y + epochLoss p g F s snapshot cache k (fun j => samples j.succ) next
        linarith

lemma query_gap_ball (p : Params) (F : p.E → ℝ) (G : p.E → p.E)
    (hm : Model (smoothing p) F G) (u : p.E) (hgu : G u = 0)
    (s : ℕ) (w : p.E) (state : EpochState p.E)
    (hy : state.y ∈ Metric.closedBall p.x0 p.R) (hz : state.z ∈ Metric.closedBall p.x0 p.R) :
    F (queryMix s w state) - F u ≤ (F w - F u) + (F state.y - F u) +
      4 * smoothing p * ((2 : ℝ) / (s + 4)) ^ 2 * p.R ^ 2 := by
  have hd : ‖state.z - state.y‖ ≤ 2 * p.R := by
    rw [← dist_eq_norm]
    have ht := dist_triangle state.z p.x0 state.y
    have hz' := Metric.mem_closedBall.mp hz
    have hy' := Metric.mem_closedBall.mp hy
    rw [dist_comm p.x0 state.y] at ht
    linarith
  have hs := pow_le_pow_left₀ (norm_nonneg (state.z - state.y)) hd 2
  have h := model_query_gap hm hgu w state.y state.z ((2 : ℝ) / (s + 4))
  have hμ := hm.pos
  have hmul := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ smoothing p * ((2 : ℝ) / (s + 4)) ^ 2 by positivity)
  change F (queryMix s w state) - F u ≤ _ at h
  nlinarith

end OracleTemplate.ComponentEnvelope

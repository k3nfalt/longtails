import LongTails.Proofs.ComponentEnvelopeOracle
import LongTails.Proofs.ComponentEnvelopeWarmup
import LongTails.Proofs.VarianceReducedWeakMintySampling
open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators
namespace OracleTemplate.ComponentEnvelope
open LongTails.Setups.InterpolatedGeneralizedFiniteSum

noncomputable def warmupLoss (p : Params) (g : Fin p.n × p.E → p.E) (F : p.E → ℝ) :
    (k : ℕ) → (Fin k → Fin p.n) → p.E → ℝ
  | 0, _, _ => 0
  | k + 1, samples, x => F x + warmupLoss p g F k (fun j => samples j.succ)
      (projectBall p (x - (1 / (2 * smoothing p)) • Program.eval g (componentPlan p (samples 0) x)))

lemma warmup_eval_shift (p : Params) (g : Fin p.n × p.E → p.E)
    (k : ℕ) (samples : Fin k → Fin p.n) (x total : p.E) :
    Program.eval g (warmupPlan p k samples x total) =
      let r := Program.eval g (warmupPlan p k samples x 0)
      (r.1, total + r.2) := by
  induction k generalizing x total with
  | zero => simp [warmupPlan, Program.eval]
  | succ k ih =>
      let next := projectBall p (x - (1 / (2 * smoothing p)) • Program.eval g (componentPlan p (samples 0) x))
      let rest := fun j : Fin k => samples j.succ
      have h1 := ih rest next (total + x)
      have h2 := ih rest next x
      simp only [warmupPlan, Program.eval_bind, zero_add]
      change Program.eval g (warmupPlan p k rest next (total + x)) =
        ((Program.eval g (warmupPlan p k rest next x)).1,
          total + (Program.eval g (warmupPlan p k rest next x)).2)
      rw [h1, h2]
      simp only [add_assoc]

lemma warmup_loss_expect (p : Params) (g : Fin p.n × p.E → p.E) (F V : p.E → ℝ)
    (C : Set p.E) (δ : ℝ)
    (hV : ∀ x ∈ C, 0 ≤ V x)
    (hnext : ∀ i x, x ∈ C →
      projectBall p (x - (1 / (2 * smoothing p)) • Program.eval g (componentPlan p i x)) ∈ C)
    (hstep : ∀ x ∈ C, F x + (𝔼 i : Fin p.n,
      V (projectBall p (x - (1 / (2 * smoothing p)) • Program.eval g (componentPlan p i x)))) ≤ V x + δ)
    (k : ℕ) (x : p.E) (hx : x ∈ C) :
    (𝔼 samples : Fin k → Fin p.n, warmupLoss p g F k samples x) ≤ V x + k * δ := by
  induction k generalizing x with
  | zero => simpa [warmupLoss] using hV x hx
  | succ k ih =>
      rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
      simp only [warmupLoss, Fin.cons_zero, Fin.cons_succ]
      let next := fun i => projectBall p (x - (1 / (2 * smoothing p)) • Program.eval g (componentPlan p i x))
      have ht (i : Fin p.n) := ih (next i) (hnext i x hx)
      have hav := Finset.expect_le_expect (s := Finset.univ) (fun i _ => add_le_add_left (ht i) (F x))
      simp only [Finset.expect_add_distrib, Fintype.expect_const] at hav ⊢
      have hs := hstep x hx
      change F x + (𝔼 i : Fin p.n, V (next i)) ≤ V x + δ at hs
      change F x + (𝔼 i : Fin p.n, 𝔼 samples : Fin k → Fin p.n, warmupLoss p g F k samples (next i)) ≤ _
      rw [Nat.cast_add, Nat.cast_one]
      linarith


open scoped RealInnerProductSpace
lemma warmup_support_sum (p : Params) (g : Fin p.n × p.E → p.E)
    (F : p.E → ℝ) (G : p.E → p.E)
    (hlower : ∀ a x, F a + ⟪G a, x - a⟫ ≤ F x)
    (k : ℕ) (samples : Fin k → Fin p.n) (x a u : p.E) :
    (k : ℝ) * (F a - F u) +
      ⟪G a, (Program.eval g (warmupPlan p k samples x 0)).2 - (k : ℝ) • a⟫ ≤
      warmupLoss p g (fun z => F z - F u) k samples x := by
  induction k generalizing x with
  | zero => simp [warmupPlan, Program.eval, warmupLoss]
  | succ k ih =>
      let next := projectBall p (x - (1 / (2 * smoothing p)) • Program.eval g (componentPlan p (samples 0) x))
      let rest := fun j : Fin k => samples j.succ
      let total := (Program.eval g (warmupPlan p k rest next 0)).2
      have ht := ih rest next
      have hx := hlower a x
      simp only [warmupPlan, Program.eval_bind, zero_add, warmupLoss, Nat.cast_add, Nat.cast_one]
      rw [warmup_eval_shift]
      change ((k : ℝ) + 1) * (F a - F u) + ⟪G a, x + total - ((k : ℝ) + 1) • a⟫ ≤
        F x - F u + warmupLoss p g (fun z => F z - F u) k rest next
      have hid : x + total - ((k : ℝ) + 1) • a = (x - a) + (total - (k : ℝ) • a) := by module
      rw [hid, inner_add_right]
      change (k : ℝ) * (F a - F u) + ⟪G a, total - (k : ℝ) • a⟫ ≤ _ at ht
      linarith

lemma warmup_mean_gap (p : Params) (g : Fin p.n × p.E → p.E)
    (F : p.E → ℝ) (G : p.E → p.E)
    (hlower : ∀ a x, F a + ⟪G a, x - a⟫ ≤ F x)
    (k : ℕ) (hk : 0 < k) (samples : Fin k → Fin p.n) (x u : p.E) :
    (k : ℝ) * (F ((k : ℝ)⁻¹ • (Program.eval g (warmupPlan p k samples x 0)).2) - F u) ≤
      warmupLoss p g (fun z => F z - F u) k samples x := by
  have hh := warmup_support_sum p g F G hlower k samples x
    ((k : ℝ)⁻¹ • (Program.eval g (warmupPlan p k samples x 0)).2) u
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  simpa only [smul_smul, mul_inv_cancel₀ hk0, one_smul, sub_self, inner_zero_right, add_zero] using hh


lemma projectBall_mem (p : Params) (hR : 0 ≤ p.R) (x : p.E) :
    projectBall p x ∈ Metric.closedBall p.x0 p.R := by
  apply (SaddlePoint.project_spec ⟨p.x0, Metric.mem_closedBall_self hR⟩
    (isCompact_closedBall p.x0 p.R) (convex_closedBall p.x0 p.R) x).1

lemma warmup_eval_bounds (p : Params) (g : Fin p.n × p.E → p.E) (hR : 0 ≤ p.R)
    (k : ℕ) (samples : Fin k → Fin p.n) (x : p.E) (hx : x ∈ Metric.closedBall p.x0 p.R) :
    let r := Program.eval g (warmupPlan p k samples x 0)
    r.1 ∈ Metric.closedBall p.x0 p.R ∧ ‖r.2 - (k : ℝ) • p.x0‖ ≤ k * p.R := by
  induction k generalizing x with
  | zero => simpa [warmupPlan, Program.eval] using hx
  | succ k ih =>
      let next := projectBall p (x - (1 / (2 * smoothing p)) • Program.eval g (componentPlan p (samples 0) x))
      let rest := fun j : Fin k => samples j.succ
      let r := Program.eval g (warmupPlan p k rest next 0)
      have hnext : next ∈ Metric.closedBall p.x0 p.R := projectBall_mem p hR _
      have ht := ih rest next hnext
      simp only [warmupPlan, Program.eval_bind, zero_add]
      rw [warmup_eval_shift]
      change r.1 ∈ Metric.closedBall p.x0 p.R ∧ ‖x + r.2 - ((k + 1 : ℕ) : ℝ) • p.x0‖ ≤ (k + 1 : ℕ) * p.R
      refine ⟨ht.1, ?_⟩
      have hc : ‖x - p.x0‖ ≤ p.R := by simpa [dist_eq_norm] using hx
      have hid : x + r.2 - ((k + 1 : ℕ) : ℝ) • p.x0 =
          (x - p.x0) + (r.2 - (k : ℝ) • p.x0) := by push_cast; module
      rw [hid]
      have hh := norm_add_le (x - p.x0) (r.2 - (k : ℝ) • p.x0)
      have hb := ht.2
      change ‖r.2 - (k : ℝ) • p.x0‖ ≤ k * p.R at hb
      push_cast
      linarith

lemma warmup_mean_mem (p : Params) (g : Fin p.n × p.E → p.E) (hR : 0 ≤ p.R)
    (k : ℕ) (hk : 0 < k) (samples : Fin k → Fin p.n) (x : p.E)
    (hx : x ∈ Metric.closedBall p.x0 p.R) :
    (k : ℝ)⁻¹ • (Program.eval g (warmupPlan p k samples x 0)).2 ∈ Metric.closedBall p.x0 p.R := by
  let total := (Program.eval g (warmupPlan p k samples x 0)).2
  have hb := (warmup_eval_bounds p g hR k samples x hx).2
  have hk0 : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hid : (k : ℝ)⁻¹ • total - p.x0 = (k : ℝ)⁻¹ • (total - (k : ℝ) • p.x0) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hk0.ne', one_smul]
  rw [Metric.mem_closedBall, dist_eq_norm]
  change ‖(k : ℝ)⁻¹ • total - p.x0‖ ≤ p.R
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk0)]
  have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hk0.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hk0.ne', one_mul] using hh


open LongTails.Proofs.RecursiveEnvelopeGeometry
open OracleTemplate.FiniteSum
lemma warmup_expected_accuracy (p : Params) (g : Fin p.n × p.E → p.E)
    (f : Fin p.n → p.E → ℝ) (G : Fin p.n × p.E → p.E)
    (hm : ∀ i, Model (smoothing p) (f i) (fun x => G (i, x)))
    (hR : 0 ≤ p.R) (u : p.E) (hu : u ∈ Metric.closedBall p.x0 p.R)
    (hgu : ∀ i, G (i, u) = 0)
    (hrad : ∀ a ∈ Metric.closedBall p.x0 p.R, ‖a - u‖ ≤ 2 * p.R)
    (herr : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      ‖Program.eval g (componentPlan p i x) - G (i, x)‖ ≤ tolerance p)
    (k : ℕ) (hk : 0 < k) (x : p.E) (hx : x ∈ Metric.closedBall p.x0 p.R) :
    (k : ℝ) * (𝔼 samples : Fin k → Fin p.n,
      LongTails.Setups.FiniteSumSmoothAndConvex.objective f
        ((k : ℝ)⁻¹ • (Program.eval g (warmupPlan p k samples x 0)).2) -
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f u) ≤
      2 * smoothing p * ‖x - u‖ ^ 2 + k * (4 * p.R * tolerance p) := by
  let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let V := fun x : p.E => 2 * smoothing p * ‖x - u‖ ^ 2
  have hμ := (hm 0).pos
  have hne : (Metric.closedBall p.x0 p.R).Nonempty := ⟨u, hu⟩
  have hco := isCompact_closedBall p.x0 p.R
  have hcv := convex_closedBall p.x0 p.R
  have hstep (a : p.E) (ha : a ∈ Metric.closedBall p.x0 p.R) :
      H a - H u + (𝔼 i : Fin p.n, V (projectBall p
        (a - (1 / (2 * smoothing p)) • Program.eval g (componentPlan p i a)))) ≤
        V a + 4 * p.R * tolerance p := by
    have hi (i : Fin p.n) := projected_warmup_step hne hco hcv (hm i) hR a u
      (Program.eval g (componentPlan p i a)) hu (hgu i) hrad (herr i a ha)
    have hav := Finset.expect_le_expect (s := Finset.univ) (fun i _ => hi i)
    simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
      Fintype.expect_const] at hav
    rw [← objective_eq_expect f a, ← objective_eq_expect f u] at hav
    dsimp [V]
    simp only [← Finset.mul_expect]
    dsimp [H, projectBall]
    linarith
  have hloss := warmup_loss_expect p g (fun a => H a - H u) V
    (Metric.closedBall p.x0 p.R) (4 * p.R * tolerance p)
    (fun a _ => by dsimp [V]; positivity)
    (fun _ _ _ => projectBall_mem p hR _) hstep k x hx
  have hmean (samples : Fin k → Fin p.n) := warmup_mean_gap p g H (fullGradient G)
    (finiteSum_model hm).lower k hk samples x u
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun samples _ => hmean samples)
  rw [← Finset.mul_expect] at hav
  simpa only [Finset.expect_sub_distrib, Fintype.expect_const, H, V] using hav.trans hloss


lemma warmup_cost_bound (p : Params) (g : Fin p.n × p.E → p.E) (hR : 0 ≤ p.R)
    (B : ℝ) (hcost : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      (Program.cost g (componentPlan p i x) : ℝ) ≤ B)
    (k : ℕ) (samples : Fin k → Fin p.n) (x total : p.E)
    (hx : x ∈ Metric.closedBall p.x0 p.R) :
    (Program.cost g (warmupPlan p k samples x total) : ℝ) ≤ k * B := by
  induction k generalizing x total with
  | zero => simp [warmupPlan, Program.cost]
  | succ k ih =>
      simp only [warmupPlan, Program.cost_bind, Nat.cast_add, Nat.cast_one]
      have ht := ih (fun j => samples j.succ)
        (projectBall p (x - (1 / (2 * smoothing p)) • Program.eval g (componentPlan p (samples 0) x)))
        (total + x) (projectBall_mem p hR _)
      have hc := hcost (samples 0) x hx
      nlinarith

end OracleTemplate.ComponentEnvelope

import LongTails.Proofs.Execution
import LongTails.Proofs.MomentumLastIterateDescent
import LongTails.Proofs.LinearDecaySgdExecution

open MeasureTheory

namespace OracleTemplate.MomentumConvex

open LongTails.Setups.MomentumLipschitzConvex

open OracleTemplate.SampledConvex (sampleOracle)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ξ : Type} [MeasurableSpace Ξ]

omit [MeasurableSpace Ξ] in
lemma advance_constantMomentumSgd (Gr : Ξ → E → E) (β γ : ℝ) (N : ℕ) (x0 : E) (ξ : ℕ → Ξ) :
    ∀ K j, StochasticGradient.advance
      (fun k state => (constantMomentumSgd β γ N x0).update state
        (Gr (ξ k) (((constantMomentumSgd β γ N x0).query state).2))) K j
        (j, (traj Gr β γ N x0 ξ j).1, (traj Gr β γ N x0 ξ j).2) =
      (j + K, (traj Gr β γ N x0 ξ (j + K)).1, (traj Gr β γ N x0 ξ (j + K)).2) := by
  intro K
  induction K with
  | zero => intro j; rfl
  | succ K ih =>
    intro j
    have h := ih (j + 1)
    rw [show j + 1 + K = j + (K + 1) by omega] at h
    exact h

lemma execute_constantMomentumSgd (p : ProbabilityMeasure Ξ) (Gr : Ξ → E → E) (β γ : ℝ) (N : ℕ)
    (x0 : E) (K : ℕ) (ξ : ℕ → Ξ) :
    execute (sampleOracle p Gr) (constantMomentumSgd β γ N x0) (fun _ => K) () ξ =
      (traj Gr β γ N x0 ξ K).1 := by
  refine (StochasticGradient.execute_advance (sampleOracle p Gr).law (fun x ω => Gr ω x) (constantMomentumSgd β γ N x0)
    K () ξ).trans ?_
  have h := advance_constantMomentumSgd Gr β γ N x0 ξ K 0
  rw [Nat.zero_add] at h
  change (constantMomentumSgd β γ N x0).output (StochasticGradient.advance (fun k state =>
    (constantMomentumSgd β γ N x0).update state
      (Gr (ξ k) (((constantMomentumSgd β γ N x0).query state).2))) K 0
      (0, (traj Gr β γ N x0 ξ 0).1, (traj Gr β γ N x0 ξ 0).2)) = _
  rw [h]
  rfl

omit [MeasurableSpace Ξ] in
lemma traj_zero_scale (Gr : Ξ → E → E) (β : ℝ) (N : ℕ) (x0 : E) (ξ : ℕ → Ξ) :
    ∀ k, (traj Gr β 0 N x0 ξ k).1 = x0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [traj, stepSize, ih]

noncomputable def horizon (q : spec.Params) : ℕ :=
  ⌈100 * q.G ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊ +
    ⌈4 * (q.β / (1 - q.β)) ^ 2 * (1 + Real.log (1 / (1 - q.β)))⌉₊

theorem convergence : Convergence spec (fun p _ => horizon p) := by
  apply convergence_of_public_budget (S := spec) horizon
  refine ⟨fun q => constantMomentumSgd q.β (scale q.G q.R (horizon q)) (horizon q) q.x0, ?_,
    fun q _ => ⟨_, _, rfl⟩⟩
  rintro q ⟨hG, hR, hβ0, hβ1, hε⟩ M O ⟨hO, hmeas, hconv, hsqi, hsq, hsub, xstar, hmin, hdist⟩
  set N := horizon q with hN
  set γ := scale q.G q.R N with hγdef
  set P := Measure.infinitePi (fun _ : ℕ => (M.law : Measure q.Ξ))
  have hO' : O = sampleOracle M.law M.grad := hO
  subst hO'
  have hexec : ∀ ξ : ℕ → q.Ξ, execute (sampleOracle M.law M.grad)
      (constantMomentumSgd q.β γ N q.x0) (fun _ => N) () ξ = (traj M.grad q.β γ N q.x0 ξ N).1 :=
    fun ξ => execute_constantMomentumSgd M.law M.grad q.β γ N q.x0 N ξ
  change spec.successful q M
      (fun seed : Unit × (ℕ → q.Ξ) =>
        (execute (sampleOracle M.law M.grad) (constantMomentumSgd q.β γ N q.x0) (fun _ => N) seed.1 seed.2))
      ⟨(Measure.dirac ()).prod P, inferInstance⟩
  have hres : (fun seed : Unit × (ℕ → q.Ξ) =>
      (execute (sampleOracle M.law M.grad) (constantMomentumSgd q.β γ N q.x0) (fun _ => N) seed.1 seed.2)) =
      fun seed => (traj M.grad q.β γ N q.x0 seed.2 N).1 := by
    funext ⟨⟨⟩, ξ⟩
    exact (hexec ξ)
  rw [hres]
  refine ⟨xstar, hmin, ?_⟩
  show Integrable (fun seed : Unit × (ℕ → q.Ξ) =>
      (fun ξ => M.f (traj M.grad q.β γ N q.x0 ξ N).1 - M.f xstar) seed.2)
      ((Measure.dirac ()).prod P) ∧
    ∫ seed, (fun ξ => M.f (traj M.grad q.β γ N q.x0 ξ N).1 - M.f xstar) seed.2
      ∂((Measure.dirac ()).prod P) ≤ q.ε
  have hsnd : ∫ seed : Unit × (ℕ → q.Ξ),
      (fun ξ => M.f (traj M.grad q.β γ N q.x0 ξ N).1 - M.f xstar) seed.2
        ∂((Measure.dirac ()).prod P) =
      ∫ ξ, M.f (traj M.grad q.β γ N q.x0 ξ N).1 - M.f xstar ∂P := by
    have := integral_fun_snd (μ := (Measure.dirac () : Measure Unit)) (ν := P)
      (fun ξ => M.f (traj M.grad q.β γ N q.x0 ξ N).1 - M.f xstar)
    simpa using this
  rw [hsnd]
  rcases eq_or_lt_of_le hR with hR0 | hRpos
  · have hx : q.x0 = xstar := by
      have : ‖q.x0 - xstar‖ ≤ 0 := by rw [hR0]; exact hdist
      exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
    have hγ0 : γ = 0 := by simp [hγdef, scale, ← hR0]
    have hp : ∀ ξ : ℕ → q.Ξ, (traj M.grad q.β γ N q.x0 ξ N).1 = xstar := by
      intro ξ; rw [hγ0, traj_zero_scale, hx]
    simp only [hp, sub_self]
    refine ⟨integrable_const _, ?_⟩
    simp only [integral_const, smul_zero]
    exact hε.le
  · have hκ : 0 ≤ q.β / (1 - q.β) := div_nonneg hβ0 (by linarith)
    have hNpos : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
    have hγpos : 0 < γ := by rw [hγdef]; unfold scale; positivity
    have hyp : Hyp (M.law : Measure q.Ξ) M.f M.grad q.G xstar :=
      ⟨hmeas, hconv, hsqi, hsq, hsub, hmin, hG.le⟩
    obtain ⟨hi, hb⟩ := hyp.expected_gap hβ0 hβ1 hγpos N q.x0
    refine ⟨(measurePreserving_snd (μ := Measure.dirac ()) (ν := P)).integrable_comp_of_integrable hi, ?_⟩
    have e2 : (N : ℝ) + 1 + 1 = (N : ℝ) + 2 := by ring
    have hgap := hyp.gap_bounds q.x0
    have ha0' : M.f q.x0 - M.f xstar ≤ q.G * q.R :=
      hgap.2.trans (mul_le_mul_of_nonneg_left hdist hG.le)
    have hD0' : ‖q.x0 - xstar‖ ^ 2 ≤ q.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
    have hfb := final_bound (Tr := (N : ℝ) + 1) hG hRpos hκ hNpos
      (by rw [e2])
      (integral_nonneg (fun ξ => (hyp.gap_bounds _).1)) hgap.1 ha0' hD0'
      (by rw [e2]; exact hb)
    rw [e2] at hfb
    have hA : 100 * q.G ^ 2 * q.R ^ 2 / q.ε ^ 2 ≤ (N : ℝ) + 2 := by
      have h1 : 100 * q.G ^ 2 * q.R ^ 2 / q.ε ^ 2 ≤ (⌈100 * q.G ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊ : ℝ) :=
        Nat.le_ceil _
      have h2 : (⌈100 * q.G ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊ : ℝ) ≤ (N : ℝ) := by
        rw [hN]; unfold horizon; push_cast; linarith [Nat.cast_nonneg (α := ℝ)
          ⌈4 * (q.β / (1 - q.β)) ^ 2 * (1 + Real.log (1 / (1 - q.β)))⌉₊]
      linarith
    have hB : 4 * (q.β / (1 - q.β)) ^ 2 * (1 + Real.log (1 + q.β / (1 - q.β))) ≤ (N : ℝ) + 2 := by
      have e : 1 + q.β / (1 - q.β) = 1 / (1 - q.β) := by
        have : (1 : ℝ) - q.β ≠ 0 := by linarith
        rw [eq_div_iff this, add_mul, div_mul_cancel₀ _ this]; ring
      rw [e]
      have h1 : 4 * (q.β / (1 - q.β)) ^ 2 * (1 + Real.log (1 / (1 - q.β))) ≤
          (⌈4 * (q.β / (1 - q.β)) ^ 2 * (1 + Real.log (1 / (1 - q.β)))⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈4 * (q.β / (1 - q.β)) ^ 2 * (1 + Real.log (1 / (1 - q.β)))⌉₊ : ℝ) ≤ (N : ℝ) := by
        rw [hN]; unfold horizon; push_cast; linarith [Nat.cast_nonneg (α := ℝ)
          ⌈100 * q.G ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊]
      linarith
    exact hfb.trans (budget_bound hG hRpos hκ hε hA hB)

end OracleTemplate.MomentumConvex

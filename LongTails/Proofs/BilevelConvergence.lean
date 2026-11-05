import LongTails.Proofs.BilevelRestartExecution
import LongTails.Proofs.BilevelInner
import LongTails.Proofs.BilevelHyperobjective

set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.BilevelConvergence

open OracleTemplate LongTails.Setups.HigherSmoothBilevel LongTails.Algorithms.BilevelAccelerated
open BilevelTuning BilevelHyperobjective BilevelTrajectory BilevelRestartExecution

lemma outputPlan_accuracy {p : Params} {I : Instance p} {O : Oracle (p.X × p.Y) (Reply p)}
    (hv : spec.valid p) (ha : spec.admissible p I O) (hsmallε : p.ε < 2 * p.L * (p.L / p.μ)) :
    ‖gradient (hyperObjective I) (QueryPlan.eval (firstOrderReply I) (outputPlan p))‖ ≤ p.ε := by
  rcases hv with ⟨hμ, hμL, hΔ, hG0, hε⟩
  rcases ha with ⟨hf, hg, hf0, hf1, hf2, hg1, hg2, hg3, hsc, hgap, hG, _⟩
  have hL : 0 < p.L := hμ.trans_le hμL
  let κ := p.L / p.μ
  let q := Real.sqrt κ
  let L := 32 * p.L * q ^ 5
  let ρ := 512 * p.L * q ^ 8
  let e := p.ε / 1024
  let η := 1 / (4 * L)
  let B := Real.sqrt (e / ρ)
  let σ := e / 100
  let K := ⌊1 / Real.sqrt (32 * η * Real.sqrt (ρ * e))⌋₊
  let E := ⌊p.Δ * Real.sqrt ρ / (e * Real.sqrt e)⌋₊ + 1
  let M := p.L * (1 + κ)
  let R := (E : ℝ) * (2 * B + η * (M + σ)) + 2 * B
  let lam := 1 + 2 * κ + 16 * p.L * κ ^ 3 / σ
  let τ := σ * p.μ / (10 * lam * p.L)
  let t := tuning p
  let F := hyperObjective I
  let g := gradient F
  let A := fderiv ℝ g
  let V := fun x => QueryPlan.eval (firstOrderReply I) (estimate p t x)
  have hκ : 1 ≤ κ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
  have hμκ : p.μ * κ = p.L := by dsimp [κ]; field_simp
  have hq := condition_root hμ hμL
  have hqpos : 0 < q := by have hh : 1 ≤ q := hq.1; linarith
  have hq2 : q ^ 2 = κ := Real.sq_sqrt (by linarith : 0 ≤ κ)
  have hLout : 0 < L := by dsimp [L]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hB : 0 < B := Real.sqrt_pos.mpr (div_pos he hρ)
  have hscale : η * Real.sqrt (ρ * e) ≤ 1 / 128 :=
    bilevel_scale_small hL hq.1 hε (by rw [hq2]; exact hsmallε.le)
  have hK : 2 ≤ K := (epoch_length_bounds hη hρ he hscale).1
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hθ : 0 ≤ t.θ := by change 0 ≤ 1 / (K : ℝ); positivity
  have hθ1 : t.θ ≤ 1 := by
    change 1 / (K : ℝ) ≤ 1
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < K)).mpr
    linarith
  have hBe : ρ * B ^ 2 = e := (radius_drop_identities hρ he).2.2.1
  have hmaster : 32 * η * (K : ℝ) ^ 2 * e ≤ B := outer_master_bound hη hρ he hscale
  have hlower : B ≤ 128 * η * (K : ℝ) ^ 2 * e := outer_accuracy_bound hη hρ he hscale
  have hd : 0 < e * B := mul_pos he hB
  have hEd : E = ⌊p.Δ / (e * B)⌋₊ + 1 := by
    dsimp [E]
    congr 2
    dsimp [B]
    rw [Real.sqrt_div he.le]
    field_simp
  have hR : 0 ≤ R := by
    have hM : 0 ≤ M := by dsimp [M]; positivity
    dsimp [R]
    positivity
  have hp := penalty_parameter_bounds hμ hL hκ hμκ hσ
  have htau := inner_error_tuning hμ hL hκ hμκ hσ
  have horacle : ∀ x, ‖x - p.x0‖ ≤ R → ‖V x - g x‖ ≤ σ := by
    intro x hx
    have hh := BilevelInner.estimate_error_within_radius (hf.differentiable (by norm_num)) hg hμ hL
      hf0 hf1 hg1 hg2 hsc hG hG0 hR htau.1 hκ hμκ t hp.1 hp.2.1
      (inner_length_threshold hμ hμL) rfl x hx
    exact hh.trans htau.2
  have hF : ContDiff ℝ 2 F := BilevelGeometry.hyperObjective_contDiff hf hg hμ hsc
  have hgf : ∀ x, HasGradientAt F (g x) x := fun x => (hF.differentiable (by norm_num) x).hasGradientAt
  have hgA : ∀ x, HasFDerivAt g (A x) x := fun x =>
    ((OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one hF).differentiable (by norm_num) x).hasFDerivAt
  have hgrad : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖ :=
    gradient_lipschitz hf hg hμ hL hsc hf0 hf1 hg1 hg2 hg3 hq.1 hq.2
  have hHess : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖ := by
    intro x y
    exact (gradient_jacobian_sub_norm hF x y).trans
      (hessian_lipschitz hf hg hμ hL hsc hf0 hf1 hf2 hg1 hg2 hg3 hq.1 hq.2 x y)
  have hAnorm : ∀ x, ‖A x‖ ≤ L := by
    intro x
    exact (gradient_jacobian_norm hF x).trans
      (hessian_norm_bound hf hg hμ hL hsc hf0 hf1 hg1 hg2 hg3 hq.1 hq.2 x)
  have hAsym : ∀ x, (A x).toLinearMap.IsSymmetric :=
    OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hF
  have hgnorm : ∀ x, ‖g x‖ ≤ M := by
    intro x
    have hh := gradient_norm_bound (hf.differentiable (by norm_num)) hg hμ hL hsc hf0 hg1 hq.1 hq.2 x
    have hML : p.L * q ^ 2 ≤ M := by dsimp [M]; rw [hq2]; nlinarith only [hL]
    exact hh.trans hML
  have hηL : t.η * L ≤ 1 / 4 := by change (1 / (4 * L)) * L ≤ 1 / 4; field_simp; norm_num
  have htB : t.B = B := rfl
  have htη : t.η = η := rfl
  have hrun := finite_run_accuracy (p := p) (t := t) (F := F) (g := g) (V := V)
    (σ := σ) (d := e * B) (ε := 773 * e) (Δ := p.Δ) (M := M)
    (show 0 < t.K by change 0 < K; omega) hη.le hB.le hθ hθ1 hσ.le hd hgap hgnorm
    (fun x hx => horacle x (by simpa only [← hEd, htB, htη, R] using hx))
    (fun s T v hs hi herr hexit => trace_failure_decrease T v hs hgf hgA hLout.le hρ hη hB he hK rfl hi
      hηL hgrad hHess hBe hmaster (hAsym s.start) (hAnorm s.start) herr hexit)
    (fun s T hi hr => trace_success_accuracy T hgA hη hρ.le hB he hK rfl hHess hBe hlower hi hr)
  rw [BilevelExecution.eval_outputPlan]
  have hN : t.N = t.K * (⌊p.Δ / (e * B)⌋₊ + 1) := by change K * E = _; rw [hEd]; rfl
  change ‖g (((fun s => advance p t s (V (context p t s)))^[t.N] (initial p.x0)).result)‖ ≤ p.ε
  rw [hN]
  exact hrun.trans (by dsimp [e]; linarith)

lemma initial_point_accuracy {p : Params} {I : Instance p} {O : Oracle (p.X × p.Y) (Reply p)}
    (hv : spec.valid p) (ha : spec.admissible p I O) (hlarge : 2 * p.L * (p.L / p.μ) ≤ p.ε) :
    ‖gradient (hyperObjective I) p.x0‖ ≤ p.ε := by
  rcases hv with ⟨hμ, hμL, _, _, _⟩
  rcases ha with ⟨hf, hg, hf0, _, _, hg1, _, _, hsc, _⟩
  have hL : 0 < p.L := hμ.trans_le hμL
  have hq := condition_root hμ hμL
  have hh := gradient_norm_bound (hf.differentiable (by norm_num)) hg hμ hL hsc hf0 hg1 hq.1 hq.2 p.x0
  rw [Real.sq_sqrt (by positivity : 0 ≤ p.L / p.μ)] at hh
  nlinarith [div_pos hL hμ]

lemma execute_accuracy {p : Params} {I : Instance p} {O : Oracle (p.X × p.Y) (Reply p)}
    (hv : spec.valid p) (ha : spec.admissible p I O) (K : ℕ)
    (hcost : p.ε < 2 * p.L * (p.L / p.μ) → estimatorCalls (tuning p) * (tuning p).N ≤ K)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    DifferentiableAt ℝ (hyperObjective I) (execute O (algorithm p) (fun _ => K) seed ξ) ∧
      ‖gradient (hyperObjective I) (execute O (algorithm p) (fun _ => K) seed ξ)‖ ≤ p.ε := by
  have ha' := ha
  rcases ha' with ⟨hf, hg, _, _, _, _, _, _, hsc, _, _, hO⟩
  have hF := BilevelGeometry.hyperObjective_contDiff hf hg hv.1 hsc
  revert seed
  by_cases hlarge : 2 * p.L * (p.L / p.μ) ≤ p.ε
  · have hAlg : algorithm p = initialAlgorithm p := by unfold algorithm; rw [ite_eq_left hlarge]
    rw [hAlg]
    intro seed
    refine ⟨hF.differentiable (by norm_num) _, ?_⟩
    have hresponse : ∀ history query, O.answer history query (ξ history.length) = firstOrderReply I query.2 := by
      intro history ⟨idx, query⟩
      have hi : idx = 0 := Subsingleton.elim _ _
      subst idx
      exact hO history query (ξ history.length)
    erw [StochasticGradient.execute_advance_of_answer O _ K seed ξ (fun _ q => firstOrderReply I q.2) hresponse]
    exact initial_point_accuracy hv ha hlarge
  · have hAlg : algorithm p = QueryPlan.algorithm (S := Unit) ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
        (p.x0, p.y0) p.x0 _ (fun _ => outputPlan p) := by unfold algorithm; rw [ite_eq_right hlarge]
    rw [hAlg]
    intro seed
    refine ⟨hF.differentiable (by norm_num) _, ?_⟩
    have hsmall := lt_of_not_ge hlarge
    erw [execute_eq_of_answer_eq O (firstOrderReply I) hO]
    erw [QueryPlan.execute_plan_of_le _ _ _ _ _ _ _ _ (hcost hsmall)]
    exact outputPlan_accuracy hv ha hsmall

end LongTails.Proofs.BilevelConvergence

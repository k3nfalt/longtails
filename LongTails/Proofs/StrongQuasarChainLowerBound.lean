import LongTails.Proofs.StrongQuasarChainParameters
import LongTails.Proofs.Execution
import LongTails.TemplateLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.StrongQuasarChainLowerBound

open LongTails.Proofs.StrongQuasarChainObjective LongTails.Proofs.StrongQuasarChainHard
open LongTails.Proofs.StrongQuasarChainAveraging LongTails.Proofs.StrongQuasarChainParameters
open LongTails.Setups.HighDimensionalStrongQuasar

section scaling

variable {d : ℕ}

lemma scaled_gradient (h : EuclideanSpace ℝ (Fin d) → ℝ) (dh : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hg : ∀ y, HasGradientAt h (dh y) y) (c S0 : ℝ) (x0 x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (fun x => c * h ((1 / S0) • (x - x0)))
      ((c / S0) • dh ((1 / S0) • (x - x0))) x := by
  have hA : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin d) => (1 / S0) • (x - x0))
      ((1 / S0) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) x :=
    ((hasFDerivAt_id x).sub_const x0).const_smul (1 / S0)
  have hh := (hg ((1 / S0) • (x - x0))).hasFDerivAt
  have hc := (hh.comp x hA).const_mul c
  have e : (fun x => c * h ((1 / S0) • (x - x0))) =
      fun x => c * (h ∘ fun x => (1 / S0) • (x - x0)) x := rfl
  rw [hasGradientAt_iff_hasFDerivAt, e]
  convert hc using 1
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, real_inner_smul_left, real_inner_smul_right]
  ring

end scaling

noncomputable def scaleS0 (p : Params) (b : ℕ) : ℝ :=
  Real.sqrt (512 * p.Δ / (p.L * gapZero (shape p b)))

noncomputable def coef (p : Params) (b : ℕ) : ℝ := p.Δ / gapZero (shape p b)

noncomputable def trueObjective (p : Params) (b : ℕ) (π : Fin ((shape p b).k + 1) ↪ Fin p.d)
    (x : EuclideanSpace ℝ (Fin p.d)) : ℝ :=
  coef p b * hard (shape p b) (radius p) π ((1 / scaleS0 p b) • (x - p.x0))

noncomputable def trueField (p : Params) (b : ℕ) (π : Fin ((shape p b).k + 1) ↪ Fin p.d)
    (x : EuclideanSpace ℝ (Fin p.d)) : EuclideanSpace ℝ (Fin p.d) :=
  (coef p b / scaleS0 p b) • hardField (shape p b) (radius p) π ((1 / scaleS0 p b) • (x - p.x0))

noncomputable def trueOracle (p : Params) (b : ℕ) (π : Fin ((shape p b).k + 1) ↪ Fin p.d) :
    Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) where
  answer _ q _ := trueField p b π q.2

section

variable {p : Params} (hp : spec.valid p)
include hp

lemma gapZero_pos (b : ℕ) (hd : (shape p b).k + 1 ≤ p.d) : 0 < gapZero (shape p b) := by
  have V := shape_valid hp b
  let π : Fin ((shape p b).k + 1) ↪ Fin p.d := Fin.castLEEmb hd
  have h := V.objective_lower π 0
  rw [objective_xstar, objective_zero _ π V.hθ0.le] at h
  have h0 : 0 < ∑ q, (shape p b).μ * (shape p b).scale q ^ 2 *
      StrongQuasarChainScalar.bump ((0 : EuclideanSpace ℝ (Fin p.d)) (π q) / (shape p b).scale q) := by
    apply Finset.sum_pos
    · intro q _
      have hz : (0 : EuclideanSpace ℝ (Fin p.d)) (π q) = 0 := rfl
      rw [hz, zero_div]
      have := StrongQuasarChainScalar.bump_zero_lower
      have := V.scale_pos q
      have := V.hμ0
      positivity
    · exact Finset.univ_nonempty
  unfold gapZero
  apply div_pos (by linarith) (by norm_num)

lemma scale_pos (b : ℕ) (hd : (shape p b).k + 1 ≤ p.d) : 0 < scaleS0 p b := by
  have hg := gapZero_pos hp b hd
  have hΔ := delta_pos hp
  have hL := hp.1
  unfold scaleS0
  exact Real.sqrt_pos.mpr (by positivity)

lemma coef_eq (b : ℕ) (hd : (shape p b).k + 1 ≤ p.d) :
    coef p b = p.L * scaleS0 p b ^ 2 / 512 := by
  have hg := gapZero_pos hp b hd
  have hΔ := delta_pos hp
  have hL := hp.1
  unfold coef scaleS0
  rw [Real.sq_sqrt (by positivity)]
  field_simp

lemma coef_pos (b : ℕ) (hd : (shape p b).k + 1 ≤ p.d) : 0 < coef p b := by
  have hg := gapZero_pos hp b hd
  have hΔ := delta_pos hp
  unfold coef
  positivity

lemma field_lipschitz (b : ℕ) (hd : (shape p b).k + 1 ≤ p.d)
    (π : Fin ((shape p b).k + 1) ↪ Fin p.d) (x y : EuclideanSpace ℝ (Fin p.d)) :
    ‖trueField p b π x - trueField p b π y‖ ≤ p.L * ‖x - y‖ := by
  have V := shape_valid hp b
  have hR := radius_pos hp
  have hxs : ‖xstar (shape p b) π‖ ≤ radius p := (xstar_le hp b π).trans (by linarith)
  have hS := scale_pos hp b hd
  have hc := coef_pos hp b hd
  have hce := coef_eq hp b hd
  have hlip := V.hard_lipschitz π hR hxs ((1 / scaleS0 p b) • (x - p.x0))
    ((1 / scaleS0 p b) • (y - p.x0))
  have e1 : (1 / scaleS0 p b) • (x - p.x0) - (1 / scaleS0 p b) • (y - p.x0) =
      (1 / scaleS0 p b) • (x - y) := by rw [← smul_sub]; congr 1; abel
  rw [e1, norm_smul, Real.norm_of_nonneg (by positivity)] at hlip
  unfold trueField
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc coef p b / scaleS0 p b * ‖_‖
      ≤ coef p b / scaleS0 p b * (512 * (1 / scaleS0 p b * ‖x - y‖)) :=
        mul_le_mul_of_nonneg_left hlip (by positivity)
    _ = p.L * ‖x - y‖ := by rw [hce]; field_simp

lemma admissible (b : ℕ) (hd : (shape p b).k + 1 ≤ p.d)
    (π : Fin ((shape p b).k + 1) ↪ Fin p.d) :
    spec.admissible p (trueObjective p b π) (trueOracle p b π) := by
  have V := shape_valid hp b
  have hR := radius_pos hp
  have hxs2 := xstar_le hp b π
  have hxs : ‖xstar (shape p b) π‖ ≤ radius p := hxs2.trans (by linarith)
  have hS := scale_pos hp b hd
  have hc := coef_pos hp b hd
  have hce := coef_eq hp b hd
  have hg : ∀ x, HasGradientAt (trueObjective p b π) (trueField p b π x) x := fun x =>
    scaled_gradient (hard (shape p b) (radius p) π) (hardField (shape p b) (radius p) π)
      (V.hard_gradient π hR) (coef p b) (scaleS0 p b) p.x0 x
  have hgr : ∀ x, gradient (trueObjective p b π) x = trueField p b π x := fun x => (hg x).gradient
  refine ⟨fun x => by rw [hgr]; exact hg x, fun x y => by rw [hgr, hgr]; exact field_lipschitz hp b hd π x y,
    ⟨trueField p b π, ?_, fun _ _ _ => rfl, fun x => by rw [hgr, sub_self, norm_zero]; simp⟩, ?_⟩
  · have hL := hp.1
    have hlw : LipschitzWith (Real.toNNReal p.L) (trueField p b π) :=
      LipschitzWith.of_dist_le_mul (fun x y => by
        rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le]
        exact field_lipschitz hp b hd π x y)
    let := p.toRelative.measurableE
    have := p.toRelative.borelE
    exact hlw.continuous.measurable
  · have hA : (1 / scaleS0 p b) • ((p.x0 + scaleS0 p b • xstar (shape p b) π) - p.x0) =
        xstar (shape p b) π := by
      rw [add_sub_cancel_left, smul_smul, one_div_mul_cancel hS.ne', one_smul]
    have hstar : trueObjective p b π (p.x0 + scaleS0 p b • xstar (shape p b) π) = 0 := by
      unfold trueObjective
      rw [hA, hard_xstar (shape p b) π hR hxs, mul_zero]
    have hnn : ∀ x, 0 ≤ trueObjective p b π x := fun x =>
      mul_nonneg hc.le (V.hard_nonneg π hR _)
    refine ⟨p.x0 + scaleS0 p b • xstar (shape p b) π,
      fun x _ => by rw [Set.mem_ofPred_eq, hstar]; exact hnn x, ?_, ?_⟩
    · have h0 : trueObjective p b π p.x0 = p.Δ := by
        unfold trueObjective
        rw [sub_self, smul_zero, V.hard_zero π hR, gapFun_zero _ π V.hθ0.le]
        unfold coef
        field_simp [(gapZero_pos hp b hd).ne']
      change trueObjective p b π p.x0 -
        trueObjective p b π (p.x0 + scaleS0 p b • xstar (shape p b) π) ≤ p.Δ
      rw [h0, hstar, sub_zero]
    · intro x
      change p.γ * trueObjective p b π x + ⟪gradient (trueObjective p b π) x,
          p.x0 + scaleS0 p b • xstar (shape p b) π - x⟫ +
          p.γ * p.μ / 2 * ‖p.x0 + scaleS0 p b • xstar (shape p b) π - x‖ ^ 2 ≤
        p.γ * trueObjective p b π (p.x0 + scaleS0 p b • xstar (shape p b) π)
      rw [hgr, hstar, mul_zero]
      obtain ⟨y, hy⟩ : ∃ y, y = (1 / scaleS0 p b) • (x - p.x0) := ⟨_, rfl⟩
      have hsq := V.hard_sq π hR hxs2 hp.2.2.1.le hp.2.2.2.1 (sq_constant hp) y
      rw [hard_xstar (shape p b) π hR hxs, mul_zero] at hsq
      have hdiff : p.x0 + scaleS0 p b • xstar (shape p b) π - x =
          scaleS0 p b • (xstar (shape p b) π - y) := by
        rw [hy, smul_sub, smul_smul, mul_one_div_cancel hS.ne', one_smul]
        abel
      have hin : ⟪trueField p b π x, p.x0 + scaleS0 p b • xstar (shape p b) π - x⟫ =
          coef p b * ⟪hardField (shape p b) (radius p) π y, xstar (shape p b) π - y⟫ := by
        rw [hdiff]
        unfold trueField
        rw [← hy, real_inner_smul_left, real_inner_smul_right]
        field_simp
      have hno : ‖p.x0 + scaleS0 p b • xstar (shape p b) π - x‖ ^ 2 =
          scaleS0 p b ^ 2 * ‖xstar (shape p b) π - y‖ ^ 2 := by
        rw [hdiff, norm_smul, Real.norm_of_nonneg hS.le, mul_pow]
      have hmu : p.μ * scaleS0 p b ^ 2 = coef p b * ((shape p b).μ / 17) := by
        rw [hce]
        change p.μ * scaleS0 p b ^ 2 = p.L * scaleS0 p b ^ 2 / 512 * (muN p / 17)
        have hL := hp.1
        unfold muN
        field_simp
        ring
      have hobj : trueObjective p b π x = coef p b * hard (shape p b) (radius p) π y := by
        rw [hy]; rfl
      rw [hin, hno, hobj]
      have hfin := mul_nonpos_of_nonneg_of_nonpos hc.le hsq
      linear_combination hfin + (p.γ / 2 * ‖xstar (shape p b) π - y‖ ^ 2) * hmu

lemma exists_failure (b : ℕ) (hb : b ≤ lowerBudget p)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p f O ∧
        ¬ spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => b) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  have V := shape_valid hp b
  have hR := radius_pos hp
  obtain ⟨hD, hDs, hsize⟩ := dimension hp b hb
  have hd : (shape p b).k + 1 ≤ p.d := by
    have h1 : (((shape p b).k + 1 : ℕ) : ℝ) ≤ p.d := by linarith
    exact_mod_cast h1
  have hS := scale_pos hp b hd
  have hc := coef_pos hp b hd
  have hbk : b ≤ (shape p b).k := by simp only [shape]; omega
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure A.Seed).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  let query := fun s => (1 / scaleS0 p b) • ((A.query s).2 - p.x0)
  let output := fun s => (1 / scaleS0 p b) • (A.output s - p.x0)
  let update := fun s (r : EuclideanSpace ℝ (Fin p.d)) => A.update s ((coef p b / scaleS0 p b) • r)
  obtain ⟨π, hbad⟩ := chain_failure V (radius p) hR b hbk (tail_upper hp b)
    ((rootKappa p / p.γ) ^ 5 * ratio p ^ 3 / 2) (p.ε / coef p b) hD hDs hsize
    (fun π => (xstar_le hp b π).trans (by linarith)) (accuracy hp b hb)
    query output update (fun w : A.Seed × (ℕ → Unit) => A.initial w.1) P
  refine ⟨trueObjective p b π, trueOracle p b π, admissible hp b hd π, ?_⟩
  rintro ⟨xs, hm, hi, he⟩
  have hnn : ∀ x, 0 ≤ trueObjective p b π x := fun x => mul_nonneg hc.le (V.hard_nonneg π hR _)
  have hxs0 : trueObjective p b π xs = 0 := by
    apply le_antisymm _ (hnn xs)
    have hh := hm (Set.mem_univ (p.x0 + scaleS0 p b • xstar (shape p b) π))
    have hA : (1 / scaleS0 p b) • ((p.x0 + scaleS0 p b • xstar (shape p b) π) - p.x0) =
        xstar (shape p b) π := by
      rw [add_sub_cancel_left, smul_smul, one_div_mul_cancel hS.ne', one_smul]
    have hz : trueObjective p b π (p.x0 + scaleS0 p b • xstar (shape p b) π) = 0 := by
      unfold trueObjective
      rw [hA, hard_xstar (shape p b) π hR ((xstar_le hp b π).trans (by linarith)), mul_zero]
    change trueObjective p b π xs ≤ trueObjective p b π _ at hh
    linarith
  have hiter : ∀ w : A.Seed × (ℕ → Unit),
      execute (trueOracle p b π) A (fun _ => b) w.1 w.2 =
        A.output ((fun s => A.update s (trueField p b π (A.query s).2))^[b] (A.initial w.1)) :=
    fun w => execute_iterate (trueField p b π) A b w.1
  have hstep : (fun s => update s (hardField (shape p b) (radius p) π (query s))) =
      (fun s => A.update s (trueField p b π (A.query s).2)) := rfl
  have hloss : (fun w : A.Seed × (ℕ → Unit) =>
      trueObjective p b π (execute (trueOracle p b π) A (fun _ => b) w.1 w.2) -
        trueObjective p b π xs) =
      fun w => coef p b * hard (shape p b) (radius p) π
        (output ((fun s => update s (hardField (shape p b) (radius p) π (query s)))^[b]
          (A.initial w.1))) := by
    funext w
    rw [hxs0, sub_zero, hiter, hstep]
    rfl
  change Integrable (fun w : A.Seed × (ℕ → Unit) =>
      trueObjective p b π (execute (trueOracle p b π) A (fun _ => b) w.1 w.2) -
        trueObjective p b π xs) (P : Measure _) at hi
  change (∫ w : A.Seed × (ℕ → Unit), trueObjective p b π (execute (trueOracle p b π) A (fun _ => b) w.1 w.2) -
        trueObjective p b π xs ∂(P : Measure (A.Seed × (ℕ → Unit)))) ≤ p.ε at he
  rw [hloss] at hi he
  apply hbad
  refine ⟨?_, ?_⟩
  · have := hi.const_mul (1 / coef p b)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    field_simp
  · rw [integral_const_mul] at he
    rw [le_div_iff₀ hc]
    linarith

end

end LongTails.Proofs.StrongQuasarChainLowerBound

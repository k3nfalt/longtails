import LongTails.Setups.HeavyTailedHighProbabilityStationarity
import LongTails.Proofs.HeavyTailedHighProbabilityPhaseOne
import LongTails.Proofs.HeavyTailedHighProbabilityPhaseTwo
import LongTails.Proofs.HeavyTailedHighProbabilityBlock
import LongTails.Proofs.HeavyTailedHighProbabilityBudget
import LongTails.Proofs.HighProbabilityUpperAssembly
import LongTails.Proofs.IIDBlocks

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.HeavyTailedHighProbabilityUpper

open OracleTemplate QueryPlan LongTails.Algorithms.HighProbabilityStationarity
open LongTails.Setups.HeavyTailedHighProbabilityStationarity
open LongTails.Proofs.HighProbabilityAdapted LongTails.Proofs.HighProbabilityExecution
open LongTails.Proofs.HighProbabilityRounds LongTails.Proofs.HighProbabilityPhaseOne
open LongTails.Proofs.HighProbabilityPhaseTwo LongTails.Proofs.HighProbabilityConstants
open LongTails.Proofs.HighProbabilityStep LongTails.Proofs.HighProbabilityDescent
open LongTails.Algorithms.HeavyTailedHighProbabilityStationarity
open LongTails.Proofs.HeavyTailedHighProbabilityStep LongTails.Proofs.HeavyTailedHighProbabilityPhaseOne
open LongTails.Proofs.HeavyTailedHighProbabilityPhaseTwo LongTails.Proofs.HeavyTailedHighProbabilityBlock
open LongTails.Proofs.HeavyTailedHighProbabilityConstants LongTails.Proofs.HeavyTailedHighProbabilityBudget

section Generic

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

omit [MeasurableSpace X] [MeasurableSpace Z] in
lemma traj_congr (F : X → Z → X) (x0 : X) {b b' : ℕ → Z} {t : ℕ}
    (h : ∀ s < t, b s = b' s) : traj F x0 b t = traj F x0 b' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [traj, traj, ih (fun s hs => h s (by omega)), h t (by omega)]

lemma measurable_traj_joint {F : X → Z → X} (hF : Measurable (Function.uncurry F)) (n : ℕ) :
    Measurable (fun w : X × (ℕ → Z) => traj F w.1 w.2 n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih => exact hF.comp (ih.prodMk ((measurable_pi_apply n).comp measurable_snd))

lemma measurable_traj {F : X → Z → X} (hF : Measurable (Function.uncurry F)) (x0 : X) (n : ℕ) :
    Measurable (fun b : ℕ → Z => traj F x0 b n) :=
  (measurable_traj_joint hF n).comp (measurable_const.prodMk measurable_id)

lemma measurable_blocks {Ω : Type} [MeasurableSpace Ω] (n : ℕ) :
    Measurable (blocks (Ω := Ω) n) :=
  Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_pi_apply _

end Generic

@[simp] lemma vp_L (q : Params) : (varianceParams q).L = q.L := rfl
@[simp] lemma vp_Δ (q : Params) : (varianceParams q).Δ = q.Δ := rfl
@[simp] lemma vp_ε (q : Params) : (varianceParams q).ε = q.ε := rfl
@[simp] lemma vp_δ (q : Params) : (varianceParams q).δ = q.δ := rfl
@[simp] lemma vp_x0 (q : Params) : (varianceParams q).x0 = q.x0 := rfl

section Concrete

variable (q : Params)

noncomputable abbrev blockLen : ℕ := pilotSamples q + clipSize (varianceParams q)

noncomputable abbrev windowLen : ℕ := 8 * (4 + testSize q) * 2 ^ rounds (varianceParams q)

noncomputable abbrev offset : ℕ := blockLen q * steps (varianceParams q)

noncomputable def iterate (g : q.E → q.Ω → q.E) (ξ : ℕ → q.Ω) (t : ℕ) : q.E :=
  traj (stepMap (radius (varianceParams q)) (stepSize (varianceParams q)) (levels (varianceParams q)) (pilotSamples q) (clipSize (varianceParams q)) g) q.x0
    (blocks (blockLen q) ξ) t

noncomputable def candidatesOf (g : q.E → q.Ω → q.E) (τ : Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q)))
    (ξ : ℕ → q.Ω) : Fin (2 ^ rounds (varianceParams q)) → q.E :=
  fun j => iterate q g ξ (τ j)

noncomputable def tailBlocks (ξ : ℕ → q.Ω) : ℕ → Fin (windowLen q) → q.Ω :=
  fun t j => ξ (offset q + t * windowLen q + j.val)

noncomputable def selectOut (g : q.E → q.Ω → q.E) (Y : Fin (2 ^ rounds (varianceParams q)) → q.E)
    (b : ℕ → Fin (windowLen q) → q.Ω) : q.E :=
  (((traj (roundMapH g (ladderTolerance q) (accuracy (varianceParams q)) (rounds (varianceParams q)) 8
      (4 + testSize q) (testEstimate q) (by norm_num) q.x0 Y)
    (0, fun j => some j) b (rounds (varianceParams q) + 1)).2 ⟨0, Nat.two_pow_pos (rounds (varianceParams q))⟩).map Y).getD q.x0

noncomputable def finalOut (g : q.E → q.Ω → q.E) (τ : Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q)))
    (ξ : ℕ → q.Ω) : q.E :=
  selectOut q g (candidatesOf q g τ ξ) (tailBlocks q ξ)

lemma method_eval (g : q.E → q.Ω → q.E) (τ : Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q)))
    (ξ : ℕ → q.Ω) :
    sampledEval g ξ (methodH (radius (varianceParams q)) (stepSize (varianceParams q)) (ladderTolerance q)
      (accuracy (varianceParams q)) (levels (varianceParams q)) (pilotSamples q)
      (clipSize (varianceParams q)) (steps (varianceParams q)) (rounds (varianceParams q)) 8
      (4 + testSize q) (testEstimate q) (by norm_num) q.x0 τ) 0 =
      finalOut q g τ ξ := by
  unfold methodH
  rw [sampledEval_bind]
  obtain ⟨_, _, hpath⟩ := phaseOne_eval (radius (varianceParams q)) (stepSize (varianceParams q)) (levels (varianceParams q)) (pilotSamples q)
    (clipSize (varianceParams q)) (steps (varianceParams q)) q.x0 g ξ
  have hY : (fun j => (sampledEval g ξ (phaseOne (radius (varianceParams q)) (stepSize (varianceParams q)) (levels (varianceParams q)) (pilotSamples q)
      (clipSize (varianceParams q)) (steps (varianceParams q)) q.x0) 0).path (τ j)) = candidatesOf q g τ ξ := by
    funext j
    exact hpath (τ j) (τ j).isLt
  rw [hY, phaseTwo_evalH]
  simp only [zero_add]
  rfl

lemma execute_eq (g : q.E → q.Ω → q.E) (P : ProbabilityMeasure (ℕ → q.Ω)) (hv : spec.valid q)
    (τ : Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) (ξ : ℕ → q.Ω) :
    execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (LongTails.Algorithms.HeavyTailedHighProbabilityStationarity.algorithm q)
      (fun _ => ⌈2 ^ 76 * ((1 + (2 ^ 45 * q.σ / q.ε) ^ (q.p / (q.p - 1))) *
        (q.L * q.Δ / q.ε ^ 2 + Real.log (16 / q.δ) * Real.log (2 + Real.log (16 / q.δ)) ^ (2 + 2 / q.p)) +
          Real.sqrt (q.L * q.Δ) * Real.log (16 / q.δ) / q.ε)⌉₊) τ ξ = finalOut q g τ ξ := by
  unfold LongTails.Algorithms.HeavyTailedHighProbabilityStationarity.algorithm
  rw [execute_sampledPlan_of_le _ _ _ _ _ _ _ g τ ξ (plan_le_budgetH hv)]
  exact method_eval q g τ ξ

end Concrete

section Measurability

variable (q : Params) {g : q.E → q.Ω → q.E} (hg : Measurable (Function.uncurry g))
include hg

lemma measurable_iterate (t : ℕ) : Measurable (fun ξ : ℕ → q.Ω => iterate q g ξ t) :=
  (measurable_traj (measurable_stepMap (radius (varianceParams q)) (stepSize (varianceParams q)) (levels (varianceParams q)) (pilotSamples q)
    (clipSize (varianceParams q)) hg) q.x0 t).comp (measurable_blocks (Ω := q.Ω) _)

lemma measurable_candidates :
    Measurable (fun w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) =>
      candidatesOf q g w.1 w.2) :=
  Measurable.of_eval fun j => measurable_from_prod_countable_right fun τ =>
    measurable_iterate q hg (τ j)

omit hg in
lemma measurable_tailBlocks : Measurable (tailBlocks q) :=
  Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_pi_apply _

lemma measurable_selectOut :
    Measurable (fun w : (Fin (2 ^ rounds (varianceParams q)) → q.E) × (ℕ → Fin (windowLen q) → q.Ω) =>
      selectOut q g w.1 w.2) := by
  let outFn : (Fin (2 ^ rounds (varianceParams q)) → q.E) × Ladder (2 ^ rounds (varianceParams q)) → q.E :=
    fun w => ((w.2.2 ⟨0, Nat.two_pow_pos (rounds (varianceParams q))⟩).map w.1).getD q.x0
  have hout : Measurable outFn := measurable_from_prod_countable_left fun s =>
    measurable_point (s.2 ⟨0, Nat.two_pow_pos (rounds (varianceParams q))⟩) q.x0
  have htraj := (measurable_traj_joint (measurable_chainStepH hg (ladderTolerance q) (accuracy (varianceParams q))
    (rounds (varianceParams q)) 8 (4 + testSize q) (testEstimate q) (measurable_blockEstimate _ _ _ _)
    (by norm_num) q.x0) (rounds (varianceParams q) + 1)).comp
    ((measurable_fst.prodMk (measurable_const (a := ((0, fun j => some j) :
      Ladder (2 ^ rounds (varianceParams q)))))).prodMk measurable_snd)
  have key : ∀ w : (Fin (2 ^ rounds (varianceParams q)) → q.E) × (ℕ → Fin (windowLen q) → q.Ω),
      selectOut q g w.1 w.2 = outFn (traj (chainStepH g (ladderTolerance q) (accuracy (varianceParams q)) (rounds (varianceParams q)) 8
        (4 + testSize q) (testEstimate q) (by norm_num) q.x0) (w.1, ((0, fun j => some j) : Ladder (2 ^ rounds (varianceParams q)))) w.2
          (rounds (varianceParams q) + 1)) := by
    intro w
    rw [traj_chainStepH]
    rfl
  have he : (fun w : (Fin (2 ^ rounds (varianceParams q)) → q.E) × (ℕ → Fin (windowLen q) → q.Ω) =>
      selectOut q g w.1 w.2) = fun w => outFn (traj (chainStepH g (ladderTolerance q) (accuracy (varianceParams q)) (rounds (varianceParams q)) 8
        (4 + testSize q) (testEstimate q) (by norm_num) q.x0) (w.1, ((0, fun j => some j) : Ladder (2 ^ rounds (varianceParams q)))) w.2
          (rounds (varianceParams q) + 1)) := funext key
  rw [he]
  exact hout.comp htraj

lemma measurable_finalOut :
    Measurable (fun w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) =>
      finalOut q g w.1 w.2) := by
  have h := (measurable_selectOut q hg).comp ((measurable_candidates q hg).prodMk
    ((measurable_tailBlocks q).comp measurable_snd))
  unfold finalOut
  exact h

end Measurability

lemma card_fin_filter (T : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun t : Fin T => P t)).card = ((Finset.range T).filter P).card := by
  refine Finset.card_bij (fun t _ => t.val) ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp [ht, t.isLt]
  · intro a _ b _ h
    exact Fin.ext h
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    exact ⟨⟨t, ht.1⟩, by simp [ht.2], rfl⟩

lemma measurableSet_count {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {n : ℕ} {Y : α → Fin n → E} (hY : Measurable Y)
    {G : E → E} (hG : Measurable G) (c : ℝ) (P : ℕ → Prop) :
    MeasurableSet {a | P (Finset.univ.filter (fun i : Fin n => ¬ ‖G (Y a i)‖ ≤ c)).card} := by
  classical
  have hc : Measurable (fun a => (Finset.univ.filter (fun i : Fin n => ¬ ‖G (Y a i)‖ ≤ c)).card) := by
    simp only [Finset.card_filter]
    refine Finset.measurable_sum _ fun i _ => Measurable.ite ?_ measurable_const measurable_const
    exact (measurableSet_le ((hG.comp ((measurable_pi_apply i).comp hY)).norm)
      measurable_const).compl
  exact hc (MeasurableSet.of_discrete (s := {m : ℕ | P m}))

lemma gradient_measurable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) : Measurable (gradient f) := by
  have h : LipschitzWith (Real.toNNReal L) (gradient f) := LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL]; exact hlip x y
  exact h.continuous.measurable

lemma pilot_scale_heavy (q : Params) (hvH : spec.valid q) {f : q.E → ℝ} {g : q.E → q.Ω → q.E}
    {p : Measure q.Ω} [IsProbabilityMeasure p] (hg : Measurable (Function.uncurry g))
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ q.p) p)
    (hpm : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ q.p ∂p ≤ q.σ ^ q.p) (j : ℕ)
    (hj : j ≤ levels (varianceParams q)) (x : q.E) :
    (Measure.pi fun _ : Fin (pilotSamples q + clipSize (varianceParams q)) => p)
      {z | 2 ^ j * radius (varianceParams q) / 2 < ‖pilotOf (radius (varianceParams q))
        (levels (varianceParams q)) (pilotSamples q) (clipSize (varianceParams q)) (g x) z -
          gradient f x‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (2 * halfExp (varianceParams q) j)) := by
  have hv := varianceParams_valid hvH
  have hp := hvH.2.1
  have hσ := hvH.2.2.2.1
  set B := radius (varianceParams q) with hBdef
  set S := noiseScale (varianceParams q) with hSdef
  have hS := noise_pos hv
  have hR : 2 ^ 20 * S ≤ B := radius_ge hv
  have hBpos : 0 < B := radius_pos hv
  have hσs : q.σ ≤ S / 2 ^ 22 := sigma_small hvH
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  set t := 2 ^ j * B / 2 with htdef
  have htpos : 0 < t := by positivity
  set base := 5 * (S / 2 ^ 22) / t with hbase
  have hb0 : 0 < base := by positivity
  have hbsmall : base ≤ (1 / 2 : ℝ) ^ (38 + j) := by
    rw [hbase, div_le_iff₀ htpos, pow_add]
    have h1 : (1 / 2 : ℝ) ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
    have h2 : (1 / 2 : ℝ) ^ 38 * (1 / 2 : ℝ) ^ j * t = B / 2 ^ 39 := by
      rw [htdef]
      have : (1 / 2 : ℝ) ^ 38 * (1 / 2 : ℝ) ^ j * (2 ^ j * B / 2) =
          (1 / 2 : ℝ) ^ 38 * ((1 / 2 : ℝ) ^ j * 2 ^ j) * B / 2 := by ring
      rw [this, h1]
      norm_num
      ring
    rw [h2]
    have : 5 * (S / 2 ^ 22) ≤ 2 ^ 20 * S / 2 ^ 39 := by
      have : (0 : ℝ) ≤ S := hS.le
      have e1 : 5 * (S / 2 ^ 22) = 5 / 2 ^ 22 * S := by ring
      have e2 : 2 ^ 20 * S / 2 ^ 39 = 8 / 2 ^ 22 * S := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (by norm_num) this
    calc 5 * (S / 2 ^ 22) ≤ 2 ^ 20 * S / 2 ^ 39 := this
      _ ≤ B / 2 ^ 39 := div_le_div_of_nonneg_right hR (by norm_num)
  have hb1 : base ≤ 1 := hbsmall.trans (pow_le_one₀ (by norm_num) (by norm_num))
  set θ := base ^ q.p with hθdef
  have hθ : 0 < θ := Real.rpow_pos_of_pos hb0 _
  have hθb : θ ≤ base := by
    have := Real.rpow_le_rpow_of_exponent_ge hb0 hb1 (show (1 : ℝ) ≤ q.p by linarith)
    rwa [Real.rpow_one] at this
  have hθ1 : θ ≤ 1 := hθb.trans hb1
  have htail : p.real {ω | t / 5 < ‖g x ω - gradient f x‖} ≤ θ := by
    have h := far_prob_heavy (by linarith : (0 : ℝ) < q.p) (hpi x) (by positivity : (0 : ℝ) < t / 5)
      (hpm x)
    refine h.trans ?_
    rw [← Real.div_rpow hσ (by positivity)]
    refine Real.rpow_le_rpow (div_nonneg hσ (by positivity)) ?_ (by linarith)
    rw [hbase]
    have : q.σ / (t / 5) = 5 * q.σ / t := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_right (by linarith) htpos.le
  have hgx : Measurable (g x) := hg.comp measurable_prodMk_left
  have hpow : (2 : ℝ) ^ j ≤ 2 ^ levels (varianceParams q) := pow_le_pow_right₀ (by norm_num) hj
  have hblk := block_scale_gen (V := g x) (mp := pilotSamples q) (mc := clipSize (varianceParams q))
    (K := levels (varianceParams q)) (B := B) (t := t) (u := gradient f x) hgx hθ hθ1 htail
    (by rw [htdef]; nlinarith [mul_le_mul_of_nonneg_right h2j hBpos.le])
    (by rw [htdef]; nlinarith [mul_le_mul_of_nonneg_right hpow hBpos.le])
  refine hblk.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsq : (2 * Real.sqrt θ) ^ pilotSamples q = (4 * θ) ^ pilotSize (varianceParams q) := by
    unfold pilotSamples
    rw [pow_mul, mul_pow, Real.sq_sqrt hθ.le]
    norm_num
  rw [hsq]
  have h4 : 4 * θ ≤ (1 / 2 : ℝ) ^ (36 + j) := by
    have : (1 / 2 : ℝ) ^ (38 + j) = (1 / 2 : ℝ) ^ (36 + j) / 4 := by
      rw [show 38 + j = (36 + j) + 2 by omega, pow_add]; norm_num; ring
    rw [this] at hbsmall
    linarith
  calc (4 * θ) ^ pilotSize (varianceParams q) ≤ ((1 / 2 : ℝ) ^ (36 + j)) ^ pilotSize (varianceParams q) :=
        pow_le_pow_left₀ (by positivity) h4 _
    _ = (1 / 2 : ℝ) ^ ((36 + j) * pilotSize (varianceParams q)) := by rw [← pow_mul]
    _ ≤ (1 / 2 : ℝ) ^ (2 * halfExp (varianceParams q) j) := by
        apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
        have := halfExp_two_le (q := varianceParams q) j
        nlinarith

lemma phase_one_fail (q : Params) (hvH : spec.valid q) {f : q.E → ℝ} {g : q.E → q.Ω → q.E}
    {p : Measure q.Ω} [IsProbabilityMeasure p] {fstar : ℝ}
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) (hlow : ∀ x, fstar ≤ f x)
    (hgap : f q.x0 - fstar ≤ q.Δ) (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = gradient f x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ q.p) p)
    (hpm : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ q.p ∂p ≤ q.σ ^ q.p)
    (P : Measure (ℕ → q.Ω)) [IsProbabilityMeasure P]
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      p P) :
    P.real {ξ | ¬ 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
      ¬ ‖gradient f (iterate q g ξ t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q)} ≤
        2 * Real.exp (-confidence (varianceParams q)) := by
  classical
  have hv := varianceParams_valid hvH
  have hgm := gradient_measurable hv.1.le hlip
  have hB := radius_pos hv
  have he := hvH.2.2.2.2.2.1
  have hη := stepSize_nonneg hv
  have hmc := clip_pos hv
  set F := stepMap (radius (varianceParams q)) (stepSize (varianceParams q)) (levels (varianceParams q)) (pilotSamples q) (clipSize (varianceParams q)) g with hFdef
  have hF := measurable_stepMap (radius (varianceParams q)) (stepSize (varianceParams q)) (levels (varianceParams q)) (pilotSamples q) (clipSize (varianceParams q)) hg
  have hb := OracleTemplate.FiniteVariance.infinite_block_law p P hiid.independent hiid.marginal
    (blockLen q)
  set μb := Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (blockLen q) => p
  let Sb : Set (ℕ → Fin (blockLen q) → q.Ω) := {b | ¬ 64 * (Finset.univ.filter
    (fun t : Fin (steps (varianceParams q)) => ¬ ‖gradient f (traj F q.x0 b t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q)}
  have hSb : MeasurableSet Sb :=
    measurableSet_count (Y := fun b : ℕ → Fin (blockLen q) → q.Ω => fun t : Fin (steps (varianceParams q)) =>
      traj F q.x0 b t) (Measurable.of_eval fun t => measurable_traj hF q.x0 t) hgm (q.ε / 2)
      (fun m => ¬ 64 * m ≤ 3 * steps (varianceParams q))
  have hpre : P.real {ξ | ¬ 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
      ¬ ‖gradient f (iterate q g ξ t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q)} = μb.real Sb := by
    have : {ξ : ℕ → q.Ω | ¬ 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
        ¬ ‖gradient f (iterate q g ξ t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q)} =
        (fun ξ : ℕ → q.Ω => fun k : ℕ => fun i : Fin (blockLen q) => ξ (k * blockLen q + i.val)) ⁻¹'
          Sb := rfl
    rw [this, measureReal_def, measureReal_def, hb.measure_preimage hSb.nullMeasurableSet]
  rw [hpre]
  set W := 2 * ((steps (varianceParams q)) * q.ε / 512) + ∑ j ∈ Finset.range ((scales (varianceParams q)) + 1), 8 * (2 ^ j * radius (varianceParams q)) * counts (varianceParams q) j
  have hW : W ≤ (steps (varianceParams q)) * q.ε / 128 := by
    have := W_bound ((steps (varianceParams q)) : ℝ) q.ε (radius (varianceParams q)) (by positivity) he hB (scales (varianceParams q))
    simp only [W, counts]
    exact this
  have hroom0 := descent_room (L := q.L) (Δ := q.Δ) (ε := q.ε) (G := gradientScale (varianceParams q)) (T := steps (varianceParams q))
    hvH.1 hvH.2.2.2.2.1 he le_rfl (by
      have h1 := steps_ge hv
      have h2 := confidence_ge hv
      simp only [vp_L, vp_Δ, vp_ε] at h1 h2
      have : 0 ≤ q.L * q.Δ / q.ε ^ 2 := div_nonneg (mul_nonneg hvH.1.le hvH.2.2.2.2.1) (sq_nonneg _)
      linarith)
  simp only at hroom0
  have hstep : stepSize (varianceParams q) = 128 * (q.Δ + q.ε ^ 2 / q.L) / ((steps (varianceParams q)) * q.ε) := rfl
  rw [← hstep] at hroom0
  obtain ⟨hcount0, hroom1⟩ := hroom0
  have hroom : 2 * q.L * (q.Δ + stepSize (varianceParams q) * W + (steps (varianceParams q)) * (q.L / 2 * stepSize (varianceParams q) ^ 2)) ≤
      (3 * gradientScale (varianceParams q)) ^ 2 := by
    have : stepSize (varianceParams q) * W ≤ stepSize (varianceParams q) * ((steps (varianceParams q)) * q.ε / 128) := mul_le_mul_of_nonneg_left hW hη
    nlinarith [hvH.1]
  have hρ : ∀ j ∈ Finset.range ((scales (varianceParams q)) + 1), ∀ x, (Measure.pi fun _ : Fin (pilotSamples q + clipSize (varianceParams q)) => p)
      {z | 2 ^ j * radius (varianceParams q) / 2 < ‖pilotOf (radius (varianceParams q)) (levels (varianceParams q)) (pilotSamples q) (clipSize (varianceParams q)) (g x) z -
        gradient f x‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (2 * halfExp (varianceParams q) j)) := by
    intro j hj x
    have hjJ : j ≤ (scales (varianceParams q)) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact pilot_scale_heavy q hvH hg hpi hpm j (hjJ.trans (scales_le_levels hv)) x
  have hsub : Sb ⊆ {b | q.Δ + stepSize (varianceParams q) * W + (steps (varianceParams q)) * (q.L / 2 * stepSize (varianceParams q) ^ 2) <
      stepSize (varianceParams q) * ∑ t ∈ Finset.range (steps (varianceParams q)), ‖gradient f (traj F q.x0 b t)‖} := by
    intro b hbS
    simp only [Sb, Set.mem_ofPred_eq] at hbS ⊢
    by_contra hcon
    push Not at hcon
    apply hbS
    have hηpos : 0 < stepSize (varianceParams q) := by
      unfold stepSize; have := hv.1; have := hv.2.2.1; have := steps_pos (q := varianceParams q); positivity
    have hsum : (∑ t ∈ Finset.range (steps (varianceParams q)), ‖gradient f (traj F q.x0 b t)‖) ≤ 3 * (steps (varianceParams q)) * q.ε / 128 := by
      have h1 : stepSize (varianceParams q) * W ≤ stepSize (varianceParams q) * ((steps (varianceParams q)) * q.ε / 128) := mul_le_mul_of_nonneg_left hW hη
      have h2 : stepSize (varianceParams q) * ∑ t ∈ Finset.range (steps (varianceParams q)), ‖gradient f (traj F q.x0 b t)‖ ≤
          stepSize (varianceParams q) * (3 * (steps (varianceParams q)) * q.ε / 128) := by linarith
      exact le_of_mul_le_mul_left h2 hηpos
    have hcl := count_large (fun t => ‖gradient f (traj F q.x0 b t)‖) (fun t => norm_nonneg _)
      (q.ε / 2) (steps (varianceParams q))
    have hcard : (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) => ¬ ‖gradient f (traj F q.x0 b t)‖ ≤ q.ε / 2)).card =
        ((Finset.range (steps (varianceParams q))).filter (fun t => q.ε / 2 < ‖gradient f (traj F q.x0 b t)‖)).card := by
      rw [card_fin_filter (steps (varianceParams q)) (fun t => ¬ ‖gradient f (traj F q.x0 b t)‖ ≤ q.ε / 2)]
      congr 1
      exact Finset.filter_congr fun t _ => not_le
    rw [hcard]
    have hreal : (64 : ℝ) * ((Finset.range (steps (varianceParams q))).filter
        (fun t => q.ε / 2 < ‖gradient f (traj F q.x0 b t)‖)).card ≤ 3 * (steps (varianceParams q)) := by
      nlinarith
    exact_mod_cast hreal
  have hmain := phase_one_prob_heavy (p := p) hg hv.1 hη hB hv.2.1 (K := levels (varianceParams q))
    (J := scales (varianceParams q)) (T := steps (varianceParams q)) hmc hgrad hlip hlow hgm hgi hmean
    hvH.2.1.le hvH.2.2.1 hpi hpm hvH.2.2.2.1 (link_bound hvH) (scales_cover hv)
    (by have := grad_pos hv; positivity) (counts (varianceParams q)) (halfExp (varianceParams q)) hρ q.x0 hgap
    (ra := (steps (varianceParams q)) * q.ε / 512) hroom
  refine (measureReal_mono hsub).trans (hmain.trans ?_)
  have h1 := Real.exp_le_exp.mpr (ok_tail_const hv)
  have h2 := scale_sum hv
  simp only [vp_ε] at h1 h2
  linarith

noncomputable def preBlocks (q : Params) (hN : 0 < offset q) (a : Fin (offset q) → q.Ω) :
    ℕ → Fin (blockLen q) → q.Ω :=
  fun s i => a ⟨(s * blockLen q + i.val) % offset q, Nat.mod_lt _ hN⟩

noncomputable def candidatesPre (q : Params) (g : q.E → q.Ω → q.E) (hN : 0 < offset q)
    (u : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (Fin (offset q) → q.Ω)) :
    Fin (2 ^ rounds (varianceParams q)) → q.E :=
  fun j => traj (stepMap (radius (varianceParams q)) (stepSize (varianceParams q)) (levels (varianceParams q)) (pilotSamples q) (clipSize (varianceParams q)) g) q.x0
    (preBlocks q hN u.2) (u.1 j)

noncomputable def windows (q : Params) (c : ℕ → q.Ω) : ℕ → Fin (windowLen q) → q.Ω :=
  fun t j => c (t * windowLen q + j.val)

lemma candidates_eq_pre (q : Params) (g : q.E → q.Ω → q.E) (hN : 0 < offset q)
    (τ : Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) (ξ : ℕ → q.Ω) :
    candidatesOf q g τ ξ = candidatesPre q g hN (τ, fun i => ξ i.val) := by
  funext j
  unfold candidatesOf iterate candidatesPre
  refine traj_congr _ _ fun s hs => ?_
  funext i
  simp only [blocks, preBlocks]
  congr 1
  have hlt : s * blockLen q + i.val < offset q := by
    unfold offset
    have hsT : s + 1 ≤ steps (varianceParams q) := by have := (τ j).isLt; omega
    have : s * blockLen q + i.val < (s + 1) * blockLen q := by
      have := i.isLt; nlinarith
    nlinarith
  rw [Nat.mod_eq_of_lt hlt]

lemma tail_eq_windows (q : Params) (ξ : ℕ → q.Ω) :
    tailBlocks q ξ = windows q (fun i => ξ (offset q + i)) := by
  funext t j
  simp only [tailBlocks, windows, add_assoc]

lemma part_two (q : Params) (hvH : spec.valid q) {f : q.E → ℝ} {g : q.E → q.Ω → q.E}
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖)
    (hg : Measurable (Function.uncurry g)) (P : Measure (ℕ → q.Ω)) [IsProbabilityMeasure P] :
    ((seedLawH q : Measure (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q)))).prod P).real
      {w | 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
        ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q) ∧
        ¬ 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
          q.ε / 2)).card ≤ 2 ^ rounds (varianceParams q)} ≤ Real.exp (-confidence (varianceParams q)) := by
  classical
  have hv := varianceParams_valid hvH
  have hgm := gradient_measurable hv.1.le hlip
  set ν := (seedLawH q : Measure (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))))
  set S := {w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) |
    64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
        ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q) ∧
        ¬ 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
          q.ε / 2)).card ≤ 2 ^ rounds (varianceParams q)}
  have hS : MeasurableSet S := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_count (Y := fun w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) =>
        fun t : Fin (steps (varianceParams q)) => iterate q g w.2 t)
        (Measurable.of_eval fun t => (measurable_iterate q hg t).comp measurable_snd) hgm (q.ε / 2)
        (fun m => 64 * m ≤ 3 * steps (varianceParams q))
    · exact measurableSet_count (Y := fun w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) =>
        candidatesOf q g w.1 w.2) (measurable_candidates q hg) hgm (q.ε / 2)
        (fun m => ¬ 3 * m ≤ 2 ^ rounds (varianceParams q))
  have hslice (ξ : ℕ → q.Ω) : ν ((fun τ => (τ, ξ)) ⁻¹' S) ≤ ENNReal.ofReal (Real.exp (-confidence (varianceParams q))) := by
    by_cases hξ : 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
        ¬ ‖gradient f (iterate q g ξ t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q)
    · have hset : (fun τ => (τ, ξ)) ⁻¹' S =
          {τ | ¬ 3 * (Finset.univ.filter (fun j =>
            ¬ ‖gradient f (iterate q g ξ (τ j))‖ ≤ q.ε / 2)).card ≤ 2 ^ rounds (varianceParams q)} := by
        ext τ
        exact ⟨fun h => h.2, fun h => ⟨hξ, h⟩⟩
      rw [hset, ← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (LongTails.Proofs.HighProbabilityUpperAssembly.seed_fail (varianceParams q) hv
        (fun t => ¬ ‖gradient f (iterate q g ξ t)‖ ≤ q.ε / 2) hξ)
    · have hset : (fun τ => (τ, ξ)) ⁻¹' S = ∅ := by
        ext τ
        simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, hξ, false_and, Set.mem_empty_iff_false]
      rw [hset, measure_empty]
      positivity
  have hμ : (ν.prod P) S ≤ ENNReal.ofReal (Real.exp (-confidence (varianceParams q))) := by
    rw [Measure.prod_apply_symm hS]
    calc (∫⁻ ξ, ν ((fun τ => (τ, ξ)) ⁻¹' S) ∂P) ≤
          ∫⁻ _ξ, ENNReal.ofReal (Real.exp (-confidence (varianceParams q))) ∂P := lintegral_mono hslice
      _ = ENNReal.ofReal (Real.exp (-confidence (varianceParams q))) := by simp
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hμ

section TestConstants

variable {q : Params} (hvH : spec.valid q)
include hvH

noncomputable def testVariance (q : Params) : ℝ :=
  effectiveSigma q ^ 2 * ((rounds (varianceParams q) : ℝ) + 1) ^ ((2 - q.p) / q.p)

omit hvH in
lemma test_R1 : (1 : ℝ) ≤ (rounds (varianceParams q) : ℝ) + 1 := by
  have : (0 : ℝ) ≤ rounds (varianceParams q) := Nat.cast_nonneg _
  linarith

lemma test_clip_rpow : testClip q ^ (2 - q.p) = radius (varianceParams q) ^ (2 - q.p) *
    ((rounds (varianceParams q) : ℝ) + 1) ^ ((2 - q.p) / q.p) := by
  have hR1 := test_R1 (q := q)
  have hB := radius_pos (varianceParams_valid hvH)
  have hp := hvH.2.1
  unfold testClip
  rw [Real.mul_rpow hB.le (Real.rpow_nonneg (by linarith) _), ← Real.rpow_mul (by linarith)]
  congr 2
  field_simp

lemma test_clip_half_rpow : (testClip q / 2) ^ q.p = (radius (varianceParams q) / 2) ^ q.p *
    ((rounds (varianceParams q) : ℝ) + 1) := by
  have hR1 := test_R1 (q := q)
  have hB := radius_pos (varianceParams_valid hvH)
  have hp := hvH.2.1
  unfold testClip
  rw [show radius (varianceParams q) * ((rounds (varianceParams q) : ℝ) + 1) ^ (1 / q.p) / 2 =
    radius (varianceParams q) / 2 * ((rounds (varianceParams q) : ℝ) + 1) ^ (1 / q.p) by ring,
    Real.mul_rpow (by positivity) (Real.rpow_nonneg (by linarith) _), ← Real.rpow_mul (by linarith),
    one_div_mul_cancel (by linarith), Real.rpow_one]

lemma test_clip_ge : radius (varianceParams q) ≤ testClip q := by
  have hR1 := test_R1 (q := q)
  have hB := radius_pos (varianceParams_valid hvH)
  have hp := hvH.2.1
  unfold testClip
  have : (1 : ℝ) ≤ ((rounds (varianceParams q) : ℝ) + 1) ^ (1 / q.p) :=
    Real.one_le_rpow hR1 (by positivity)
  nlinarith

lemma test_link : 2 * q.σ ^ q.p * testClip q ^ (2 - q.p) ≤ testVariance q := by
  rw [test_clip_rpow hvH]
  have h := link_bound hvH
  have hR := Real.rpow_nonneg (show (0 : ℝ) ≤ (rounds (varianceParams q) : ℝ) + 1 by positivity)
    ((2 - q.p) / q.p)
  unfold testVariance
  calc 2 * q.σ ^ q.p * (radius (varianceParams q) ^ (2 - q.p) *
        ((rounds (varianceParams q) : ℝ) + 1) ^ ((2 - q.p) / q.p)) =
        (2 * q.σ ^ q.p * radius (varianceParams q) ^ (2 - q.p)) *
          ((rounds (varianceParams q) : ℝ) + 1) ^ ((2 - q.p) / q.p) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h hR

lemma test_vB : 8 * testVariance q ≤ testClip q ^ 2 := by
  have hv := varianceParams_valid hvH
  have hR1 := test_R1 (q := q)
  have hp := hvH.2.1
  have hp2 := hvH.2.2.1
  have hB := radius_pos hv
  have hRg : 2 ^ 20 * noiseScale (varianceParams q) ≤ radius (varianceParams q) := radius_ge hv
  have hse : effectiveSigma q ≤ noiseScale (varianceParams q) := sigma_le_noise hv
  have hse0 : 0 ≤ effectiveSigma q := effective_nonneg hvH
  set R := (rounds (varianceParams q) : ℝ) + 1 with hRdef
  have h1 : R ^ ((2 - q.p) / q.p) ≤ R := by
    have := Real.rpow_le_rpow_of_exponent_le hR1 (show (2 - q.p) / q.p ≤ 1 by
      rw [div_le_one (by linarith)]; linarith)
    rwa [Real.rpow_one] at this
  have h2 : R ≤ (R ^ (1 / q.p)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    have := Real.rpow_le_rpow_of_exponent_le hR1 (show (1 : ℝ) ≤ 1 / q.p * ((2 : ℕ) : ℝ) by
      push_cast; rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by linarith)]; linarith)
    rwa [Real.rpow_one] at this
  have hB2 : 8 * effectiveSigma q ^ 2 ≤ radius (varianceParams q) ^ 2 := by
    have : 2 ^ 20 * effectiveSigma q ≤ radius (varianceParams q) := by nlinarith
    nlinarith
  unfold testVariance testClip
  rw [← hRdef, mul_pow]
  have hR0 : 0 ≤ R := by linarith
  calc 8 * (effectiveSigma q ^ 2 * R ^ ((2 - q.p) / q.p)) ≤ 8 * effectiveSigma q ^ 2 * R := by
        nlinarith [sq_nonneg (effectiveSigma q)]
    _ ≤ radius (varianceParams q) ^ 2 * R := mul_le_mul_of_nonneg_right hB2 hR0
    _ ≤ radius (varianceParams q) ^ 2 * (R ^ (1 / q.p)) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

lemma test_var : 1536 * testVariance q ≤ (testSize q : ℝ) * (2 * accuracy (varianceParams q) / 6) ^ 2 := by
  have hv := varianceParams_valid hvH
  have hR1 := test_R1 (q := q)
  have hacc := accuracy_pos hv
  have hse : effectiveSigma q ≤ noiseScale (varianceParams q) := sigma_le_noise hv
  have hse0 : 0 ≤ effectiveSigma q := effective_nonneg hvH
  set R := (rounds (varianceParams q) : ℝ) + 1 with hRdef
  have hRp : 0 ≤ R ^ ((2 - q.p) / q.p) := Real.rpow_nonneg (by linarith) _
  have hceil : 2 ^ 14 * noiseScale (varianceParams q) ^ 2 * R ^ ((2 - q.p) / q.p) /
      accuracy (varianceParams q) ^ 2 ≤ testSize q := Nat.le_ceil _
  have h1 : 2 ^ 14 * noiseScale (varianceParams q) ^ 2 * R ^ ((2 - q.p) / q.p) ≤
      testSize q * accuracy (varianceParams q) ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at hceil
  have h2 : effectiveSigma q ^ 2 ≤ noiseScale (varianceParams q) ^ 2 :=
    pow_le_pow_left₀ hse0 hse 2
  unfold testVariance
  rw [← hRdef]
  have h3 : effectiveSigma q ^ 2 * R ^ ((2 - q.p) / q.p) ≤
      noiseScale (varianceParams q) ^ 2 * R ^ ((2 - q.p) / q.p) := mul_le_mul_of_nonneg_right h2 hRp
  nlinarith

lemma test_sr : 192 * q.σ ≤ testRadius q := by
  unfold testRadius
  have := hvH.2.2.2.1
  have := hvH.2.2.2.2.2.1
  nlinarith

lemma testRadius_pos : 0 < testRadius q := by
  unfold testRadius
  have := hvH.2.2.2.1
  have := hvH.2.2.2.2.2.1
  positivity

lemma testSize_pos : 0 < testSize q := by
  have hv := varianceParams_valid hvH
  have hR1 := test_R1 (q := q)
  have hacc := accuracy_pos hv
  have hS := noise_pos hv
  unfold testSize
  have : 0 < 2 ^ 14 * noiseScale (varianceParams q) ^ 2 *
      ((rounds (varianceParams q) : ℝ) + 1) ^ ((2 - q.p) / q.p) / accuracy (varianceParams q) ^ 2 := by
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < (rounds (varianceParams q) : ℝ) + 1 by linarith)
      ((2 - q.p) / q.p)
    positivity
  exact Nat.ceil_pos.mpr this

lemma test_rB : 2 * testRadius q ≤ testClip q := by
  have hv := varianceParams_valid hvH
  have hRg : 2 ^ 20 * noiseScale (varianceParams q) ≤ radius (varianceParams q) := radius_ge hv
  have hσs := sigma_small hvH
  have hεS : q.ε ≤ noiseScale (varianceParams q) := eps_le_noise hv
  have hS := noise_pos hv
  have hc := test_clip_ge hvH
  unfold testRadius
  nlinarith

lemma test_nu : 2 * (5 * testRadius q / 6) * q.σ ^ q.p / (testClip q / 2) ^ q.p ≤
    2 * accuracy (varianceParams q) / 6 / 2 := by
  have hv := varianceParams_valid hvH
  have hp := hvH.2.1
  have hσ := hvH.2.2.2.1
  have hε := hvH.2.2.2.2.2.1
  have hR1 := test_R1 (q := q)
  have hRg : 2 ^ 20 * noiseScale (varianceParams q) ≤ radius (varianceParams q) := radius_ge hv
  have hReq : radius (varianceParams q) * q.ε = 2 ^ 20 * noiseScale (varianceParams q) ^ 2 :=
    radius_eq hv
  have hσs := sigma_small hvH
  have hεS : q.ε ≤ noiseScale (varianceParams q) := eps_le_noise hv
  have hS := noise_pos hv
  have hB := radius_pos hv
  set B := radius (varianceParams q) with hBdef
  set S := noiseScale (varianceParams q) with hSdef
  set R := (rounds (varianceParams q) : ℝ) + 1 with hRdef
  rw [test_clip_half_rpow hvH, ← hBdef, ← hRdef]
  have hx : q.σ ^ q.p / (B / 2) ^ q.p ≤ 2 * q.σ / B := by
    rw [← Real.div_rpow hσ (by positivity)]
    have hb0 : 0 ≤ q.σ / (B / 2) := div_nonneg hσ (by positivity)
    have hb1 : q.σ / (B / 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : S ≤ B := by nlinarith
      nlinarith
    calc (q.σ / (B / 2)) ^ q.p ≤ (q.σ / (B / 2)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge' hb0 hb1 (by norm_num) (by linarith)
      _ = 2 * q.σ / B := by rw [Real.rpow_one]; field_simp
  have hacc : accuracy (varianceParams q) = q.ε / (64 * R) := rfl
  rw [hacc]
  have hR0 : 0 < R := by linarith
  have hBpow : 0 < (B / 2) ^ q.p := Real.rpow_pos_of_pos (by positivity) _
  have hlhs : 2 * (5 * (2 ^ 10 * (q.σ + q.ε)) / 6) * q.σ ^ q.p / ((B / 2) ^ q.p * R) =
      (5 / 3 * 2 ^ 10 * (q.σ + q.ε)) * (q.σ ^ q.p / (B / 2) ^ q.p) / R := by
    field_simp
    ring
  unfold testRadius
  rw [hlhs]
  have hnum : (5 / 3 * 2 ^ 10 * (q.σ + q.ε)) * (q.σ ^ q.p / (B / 2) ^ q.p) ≤
      (5 / 3 * 2 ^ 10 * (q.σ + q.ε)) * (2 * q.σ / B) :=
    mul_le_mul_of_nonneg_left hx (by positivity)
  have hkey : (5 / 3 * 2 ^ 10 * (q.σ + q.ε)) * (2 * q.σ / B) ≤ q.ε / 384 := by
    rw [mul_div_assoc', div_le_div_iff₀ hB (by norm_num)]
    have h1 : q.σ + q.ε ≤ 2 * S := by nlinarith
    have h2 : 2 * q.σ ≤ 2 * S / 2 ^ 22 := by linarith
    have h3 : (5 / 3 * 2 ^ 10 * (q.σ + q.ε)) * (2 * q.σ) ≤ (5 / 3 * 2 ^ 10 * (2 * S)) * (2 * S / 2 ^ 22) :=
      mul_le_mul (by nlinarith) h2 (by positivity) (by positivity)
    nlinarith
  calc (5 / 3 * 2 ^ 10 * (q.σ + q.ε)) * (q.σ ^ q.p / (B / 2) ^ q.p) / R ≤ (q.ε / 384) / R :=
        div_le_div_of_nonneg_right (hnum.trans hkey) hR0.le
    _ = 2 * (q.ε / (64 * R)) / 6 / 2 := by field_simp; ring

lemma test_bias_alg : 2 * testVariance q / testClip q ≤ q.ε / 2 ^ 19 := by
  have hv := varianceParams_valid hvH
  have hp := hvH.2.1
  have hε := hvH.2.2.2.2.2.1
  have hR1 := test_R1 (q := q)
  have hReq : radius (varianceParams q) * q.ε = 2 ^ 20 * noiseScale (varianceParams q) ^ 2 :=
    radius_eq hv
  have hse : effectiveSigma q ≤ noiseScale (varianceParams q) := sigma_le_noise hv
  have hse0 : 0 ≤ effectiveSigma q := effective_nonneg hvH
  have hB := radius_pos hv
  set R := (rounds (varianceParams q) : ℝ) + 1 with hRdef
  have hRle : R ^ ((2 - q.p) / q.p) ≤ R ^ (1 / q.p) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by
      apply div_le_div_of_nonneg_right (by linarith) (by linarith))
  have hRpos : 0 < R ^ (1 / q.p) := Real.rpow_pos_of_pos (by linarith) _
  unfold testVariance testClip
  rw [← hRdef]
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h2 : effectiveSigma q ^ 2 ≤ noiseScale (varianceParams q) ^ 2 := pow_le_pow_left₀ hse0 hse 2
  have h3 : 2 * (effectiveSigma q ^ 2 * R ^ ((2 - q.p) / q.p)) ≤
      2 * noiseScale (varianceParams q) ^ 2 * R ^ (1 / q.p) := by
    have := mul_le_mul h2 hRle (Real.rpow_nonneg (by linarith) _) (sq_nonneg _)
    linarith
  have h4 : 2 * noiseScale (varianceParams q) ^ 2 * R ^ (1 / q.p) * 2 ^ 19 =
      radius (varianceParams q) * q.ε * R ^ (1 / q.p) := by rw [hReq]; ring
  nlinarith

lemma final_tol : ladderTolerance q / 2 + 2 * ((rounds (varianceParams q) : ℝ) + 1) *
    accuracy (varianceParams q) + q.ε / 2 ^ 19 ≤ q.ε := by
  have hε := hvH.2.2.2.2.2.1
  have hR1 := test_R1 (q := q)
  have hacc : accuracy (varianceParams q) = q.ε / (64 * ((rounds (varianceParams q) : ℝ) + 1)) := rfl
  rw [hacc]
  unfold ladderTolerance
  have : 2 * ((rounds (varianceParams q) : ℝ) + 1) * (q.ε / (64 * ((rounds (varianceParams q) : ℝ) + 1))) =
      q.ε / 32 := by field_simp; ring
  rw [this]
  linarith

omit hvH in
lemma tol_ge : q.ε / 2 + q.ε / 2 ^ 19 ≤ ladderTolerance q / 2 := by
  unfold ladderTolerance
  linarith

end TestConstants

lemma part_three (q : Params) (hvH : spec.valid q) {f : q.E → ℝ} {g : q.E → q.Ω → q.E}
    {p : Measure q.Ω} [IsProbabilityMeasure p]
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = gradient f x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ q.p) p)
    (hpm : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ q.p ∂p ≤ q.σ ^ q.p)
    (P : Measure (ℕ → q.Ω)) [IsProbabilityMeasure P]
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      p P) :
    ((seedLawH q : Measure (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q)))).prod P).real
      {w | 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
          q.ε / 2)).card ≤ 2 ^ rounds (varianceParams q) ∧
        ¬ ‖gradient f (finalOut q g w.1 w.2)‖ ≤ q.ε} ≤
      Real.exp (-confidence (varianceParams q)) := by
  classical
  have hv := varianceParams_valid hvH
  have hgm := gradient_measurable hv.1.le hlip
  have hN : 0 < offset q := by
    unfold offset blockLen
    have := clip_pos hv
    exact Nat.mul_pos (by omega) (Nat.succ_pos _)
  set ν := (seedLawH q : Measure (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))))
  set ε' := q.ε
  have hF := measurable_stepMap (radius (varianceParams q)) (stepSize (varianceParams q)) (levels (varianceParams q)) (pilotSamples q) (clipSize (varianceParams q)) hg
  have hpreB : Measurable (preBlocks q hN) :=
    Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_pi_apply _
  have hcandP : Measurable (candidatesPre q g hN) :=
    Measurable.of_eval fun j => measurable_from_prod_countable_right fun τ =>
      (measurable_traj hF q.x0 (τ j)).comp hpreB
  have hwin : Measurable (windows q) :=
    Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_pi_apply _
  set S' := {u : ((Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (Fin (offset q) → q.Ω)) × (ℕ → q.Ω) |
    3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesPre q g hN u.1 j)‖ ≤
      q.ε / 2)).card ≤ 2 ^ rounds (varianceParams q) ∧
    ¬ ‖gradient f (selectOut q g (candidatesPre q g hN u.1) (windows q u.2))‖ ≤ ε'}
  have hS' : MeasurableSet S' := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_count (Y := fun u : ((Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) ×
        (Fin (offset q) → q.Ω)) × (ℕ → q.Ω) => candidatesPre q g hN u.1)
        (hcandP.comp measurable_fst) hgm (q.ε / 2) (fun m => 3 * m ≤ 2 ^ rounds (varianceParams q))
    · exact (measurableSet_le ((hgm.comp ((measurable_selectOut q hg).comp
        ((hcandP.comp measurable_fst).prodMk (hwin.comp measurable_snd)))).norm)
          measurable_const).compl
  set Ψ : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) →
      ((Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (Fin (offset q) → q.Ω)) × (ℕ → q.Ω) :=
    fun w => ((w.1, fun i => w.2 i.val), fun i => w.2 (offset q + i))
  have hΨ : MeasurePreserving Ψ (ν.prod P)
      ((ν.prod (Measure.pi fun _ : Fin (offset q) => p)).prod (Measure.infinitePi fun _ : ℕ => p)) := by
    have h1 := hiid.prefix_tail_law (offset q)
    have h2 := (MeasurePreserving.id ν).prod h1
    have h3 := MeasurePreserving.symm _ (measurePreserving_prodAssoc ν
      (Measure.pi fun _ : Fin (offset q) => p) (Measure.infinitePi fun _ : ℕ => p))
    exact h3.comp h2
  have hpre : {w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) |
      3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
          q.ε / 2)).card ≤ 2 ^ rounds (varianceParams q) ∧
        ¬ ‖gradient f (finalOut q g w.1 w.2)‖ ≤ ε'} = Ψ ⁻¹' S' := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, S', Ψ, finalOut,
      candidates_eq_pre q g hN w.1 w.2, tail_eq_windows q w.2]
  rw [hpre, measureReal_def, hΨ.measure_preimage hS'.nullMeasurableSet, ← measureReal_def]
  have hblock := OracleTemplate.FiniteVariance.infinite_block_law p
    (Measure.infinitePi fun _ : ℕ => p)
    (OracleTemplate.StochasticGeneralized.infinitePi_iid p).independent
    (OracleTemplate.StochasticGeneralized.infinitePi_iid p).marginal (windowLen q)
  have hslice (x : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (Fin (offset q) → q.Ω)) :
      (Measure.infinitePi fun _ : ℕ => p) (Prod.mk x ⁻¹' S') ≤
        ENNReal.ofReal (Real.exp (-confidence (varianceParams q))) := by
    by_cases hx : 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesPre q g hN x j)‖ ≤
        q.ε / 2)).card ≤ 2 ^ rounds (varianceParams q)
    · set Y := candidatesPre q g hN x
      set T2 : Set (ℕ → Fin (windowLen q) → q.Ω) := {b | ¬ ‖gradient f (selectOut q g Y b)‖ ≤ ε'}
      have hT2 : MeasurableSet T2 :=
        (measurableSet_le ((hgm.comp ((measurable_selectOut q hg).comp
          (measurable_const.prodMk measurable_id))).norm) measurable_const).compl
      have hset : Prod.mk x ⁻¹' S' =
          (fun c : ℕ → q.Ω => fun k : ℕ => fun i : Fin (windowLen q) => c (k * windowLen q + i.val)) ⁻¹'
            T2 := by
        ext c
        exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
      rw [hset, hblock.measure_preimage hT2.nullMeasurableSet, ← ofReal_measureReal]
      refine ENNReal.ofReal_le_ofReal ?_
      set Tt : q.E → q.E := fun x => gradient f x + ∫ ω, clip (testClip q) (g x ω - gradient f x) ∂p
        with hTt
      have hTm : Measurable Tt := by
        have hF : Measurable (fun z : q.E × q.Ω => clip (testClip q) (g z.1 z.2 - gradient f z.1)) :=
          (measurable_clip _).comp (hg.sub (hgm.comp measurable_fst))
        exact hgm.add hF.stronglyMeasurable.integral_prod_right'.measurable
      have hbias (x : q.E) : ‖Tt x - gradient f x‖ ≤ q.ε / 2 ^ 19 := by
        have hgx : Measurable (g x) := hg.comp measurable_prodMk_left
        have hvar0 : 0 ≤ testVariance q := by
          unfold testVariance
          have := effective_nonneg hvH
          have := Real.rpow_nonneg (show (0 : ℝ) ≤ (rounds (varianceParams q) : ℝ) + 1 by positivity)
            ((2 - q.p) / q.p)
          positivity
        have hclipB : 0 < testClip q := lt_of_lt_of_le (radius_pos hv) (test_clip_ge hvH)
        have hmom := centeredClip_moments_heavy hgx (hgi x) (hmean x) hclipB
          (c := gradient f x) (by simp; positivity) hvH.2.1.le hvH.2.2.1 (hpi x) (hpm x) hvH.2.2.2.1
          (σ := Real.sqrt (testVariance q)) (by rw [Real.sq_sqrt hvar0]; exact test_link hvH)
        rw [Real.sq_sqrt hvar0] at hmom
        have hint : (∫ ω, OracleTemplate.RobustGradient.centeredClip (testClip q) (gradient f x) (g x ω) ∂p) - gradient f x =
            Tt x - gradient f x := by
          have hci : Integrable (fun ω => clip (testClip q) (g x ω - gradient f x)) p :=
            integrable_clip (hgx.sub_const _) hclipB.le
          simp only [OracleTemplate.RobustGradient.centeredClip, hTt]
          rw [integral_add (integrable_const _) hci, integral_const, probReal_univ, one_smul]
        rw [← hint]
        exact hmom.2.2.2.trans (test_bias_alg hvH)
      have hblk : ∀ x, (Measure.pi fun _ : Fin (4 + testSize q) => p).real
          {ζ | 2 * accuracy (varianceParams q) / 6 < ‖testEstimate q (fun l => g x (ζ l)) - Tt x‖} ≤
            1 / 16 := by
        intro x
        have hgx : Measurable (g x) := hg.comp measurable_prodMk_left
        exact block_accuracy hgx (hgi x) (hmean x) hvH.2.1.le hvH.2.2.1 (hpi x) (hpm x) hvH.2.2.2.1
          (testSize_pos hvH) (testRadius_pos hvH) (test_sr hvH) (test_rB hvH) (test_link hvH)
          (test_vB hvH) (test_var hvH) (test_nu hvH) (by have := accuracy_pos hv; positivity)
      have hYT : 3 * (Finset.univ.filter (fun j : Fin (2 ^ rounds (varianceParams q)) =>
          ¬ ‖Tt (Y j)‖ ≤ ladderTolerance q / 2)).card ≤ 2 ^ rounds (varianceParams q) := by
        refine le_trans (Nat.mul_le_mul_left 3 (Finset.card_le_card ?_)) hx
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        intro hgood
        apply hj
        have h1 : ‖Tt (Y j)‖ ≤ ‖gradient f (Y j)‖ + ‖Tt (Y j) - gradient f (Y j)‖ := by
          have := norm_add_le (gradient f (Y j)) (Tt (Y j) - gradient f (Y j))
          simpa using this
        have := hbias (Y j)
        have := tol_ge (q := q)
        linarith
      have h2 := phase_twoH (p := p) hg hTm (ε := ladderTolerance q) (α := accuracy (varianceParams q))
        (Λ := rounds (varianceParams q)) (k0 := 8) (r := 4 + testSize q) (est := testEstimate q)
        (measurable_blockEstimate _ _ _ _) hblk (by norm_num) q.x0 Y hYT
      refine (measureReal_mono ?_).trans (h2.trans (rounds_sum hv))
      intro b hb
      simp only [T2, Set.mem_ofPred_eq] at hb ⊢
      intro hT
      apply hb
      have hfinal := final_tol hvH
      have h1 : ‖gradient f (selectOut q g Y b)‖ ≤ ‖Tt (selectOut q g Y b)‖ +
          ‖Tt (selectOut q g Y b) - gradient f (selectOut q g Y b)‖ := by
        have := norm_le_norm_add_norm_sub' (gradient f (selectOut q g Y b)) (Tt (selectOut q g Y b))
        rwa [norm_sub_rev (gradient f _)] at this
      have h3 := hbias (selectOut q g Y b)
      have hT' : ‖Tt (selectOut q g Y b)‖ ≤ ladderTolerance q / 2 +
          2 * ((rounds (varianceParams q) : ℝ) + 1) * accuracy (varianceParams q) := by
        have : (rounds (varianceParams q) : ℝ) + 1 = ((rounds (varianceParams q) : ℕ) : ℝ) + 1 := rfl
        exact hT
      linarith
    · have hset : Prod.mk x ⁻¹' S' = ∅ := by
        ext c
        simp only [S', Set.mem_preimage, Set.mem_ofPred_eq, hx, false_and,
          Set.mem_empty_iff_false]
      rw [hset, measure_empty]
      positivity
  have hμ : ((ν.prod (Measure.pi fun _ : Fin (offset q) => p)).prod
      (Measure.infinitePi fun _ : ℕ => p)) S' ≤ ENNReal.ofReal (Real.exp (-confidence (varianceParams q))) := by
    rw [Measure.prod_apply hS']
    calc (∫⁻ x, (Measure.infinitePi fun _ : ℕ => p) (Prod.mk x ⁻¹' S')
          ∂(ν.prod (Measure.pi fun _ : Fin (offset q) => p))) ≤
          ∫⁻ _x, ENNReal.ofReal (Real.exp (-confidence (varianceParams q)))
            ∂(ν.prod (Measure.pi fun _ : Fin (offset q) => p)) := lintegral_mono hslice
      _ = ENNReal.ofReal (Real.exp (-confidence (varianceParams q))) := by simp
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hμ

theorem convergence : Convergence LongTails.Setups.HeavyTailedHighProbabilityStationarity.spec
    (fun q _ => ⌈2 ^ 76 * ((1 + (2 ^ 45 * q.σ / q.ε) ^ (q.p / (q.p - 1))) *
        (q.L * q.Δ / q.ε ^ 2 + Real.log (16 / q.δ) * Real.log (2 + Real.log (16 / q.δ)) ^ (2 + 2 / q.p)) +
          Real.sqrt (q.L * q.Δ) * Real.log (16 / q.δ) / q.ε)⌉₊) := by
  refine ⟨fun q => LongTails.Algorithms.HeavyTailedHighProbabilityStationarity.algorithm q,
    fun q hvH f O hadm => ?_, fun _ _ => trivial⟩
  obtain ⟨g, p, P, fstar, hiid, hO, hgrad, hlip, hlow, _, hgap, hg, hgi, hmean, hpi, hpm⟩ := hadm
  subst hO
  have hv := varianceParams_valid hvH
  have hgm := gradient_measurable hv.1.le hlip
  have hsucc : LongTails.Setups.HeavyTailedHighProbabilityStationarity.spec.successful q f
      (fun w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) => finalOut q g w.1 w.2)
      ⟨(seedLawH q : Measure (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q)))).prod (P : Measure (ℕ → q.Ω)),
        inferInstance⟩ := by
    refine ⟨measurable_finalOut q hg, ?_⟩
    change 1 - q.δ ≤ ((seedLawH q : Measure (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q)))).prod
      (P : Measure (ℕ → q.Ω))).real {w | ‖gradient f (finalOut q g w.1 w.2)‖ ≤ q.ε}
    have hG : MeasurableSet {w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) |
        ‖gradient f (finalOut q g w.1 w.2)‖ ≤ q.ε} :=
      measurableSet_le (hgm.comp (measurable_finalOut q hg)).norm measurable_const
    have hsub : {w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) |
        ‖gradient f (finalOut q g w.1 w.2)‖ ≤ q.ε}ᶜ ⊆
        ({w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) |
          ¬ 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q)} ∪
        {w | 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q) ∧
          ¬ 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
            q.ε / 2)).card ≤ 2 ^ rounds (varianceParams q)}) ∪
        {w | 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
            q.ε / 2)).card ≤ 2 ^ rounds (varianceParams q) ∧
          ¬ ‖gradient f (finalOut q g w.1 w.2)‖ ≤ q.ε} := by
      intro w hw
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hw
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      by_cases h1 : 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
          ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q)
      · by_cases h2 : 3 * (Finset.univ.filter (fun j =>
            ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤ q.ε / 2)).card ≤ 2 ^ rounds (varianceParams q)
        · right; exact ⟨h2, hw⟩
        · left; right; exact ⟨h1, h2⟩
      · left; left; exact h1
    have hA1 : ((seedLawH q : Measure (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q)))).prod
        (P : Measure (ℕ → q.Ω))).real {w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) |
          ¬ 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q)} ≤
          2 * Real.exp (-confidence (varianceParams q)) := by
      have he : {w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) |
          ¬ 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q)} =
          Set.univ ×ˢ {ξ : ℕ → q.Ω | ¬ 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
            ¬ ‖gradient f (iterate q g ξ t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q)} := by
        ext w
        simp
      rw [he, measureReal_def, Measure.prod_prod, measure_univ, one_mul, ← measureReal_def]
      exact phase_one_fail q hvH hgrad hlip hlow hgap hg hgi hmean hpi hpm (P : Measure _) hiid
    have hA2 := part_two q hvH hlip hg (P : Measure (ℕ → q.Ω)) (f := f)
    have hA3 := part_three q hvH hlip hg hgi hmean hpi hpm (P : Measure (ℕ → q.Ω)) hiid
    have hcompl := probReal_compl_eq_one_sub (μ := (seedLawH q : Measure
      (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q)))).prod (P : Measure (ℕ → q.Ω))) hG
    have hmono := measureReal_mono (μ := (seedLawH q : Measure
      (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q)))).prod (P : Measure (ℕ → q.Ω))) hsub
    have h123 := measureReal_union_le (μ := (seedLawH q : Measure
      (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q)))).prod (P : Measure (ℕ → q.Ω)))
      ({w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) |
          ¬ 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q)} ∪
        {w | 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q) ∧
          ¬ 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
            q.ε / 2)).card ≤ 2 ^ rounds (varianceParams q)})
      {w | 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
            q.ε / 2)).card ≤ 2 ^ rounds (varianceParams q) ∧
          ¬ ‖gradient f (finalOut q g w.1 w.2)‖ ≤ q.ε}
    have h12 := measureReal_union_le (μ := (seedLawH q : Measure
      (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q)))).prod (P : Measure (ℕ → q.Ω)))
      {w : (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) × (ℕ → q.Ω) |
          ¬ 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q)}
        {w | 64 * (Finset.univ.filter (fun t : Fin (steps (varianceParams q)) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps (varianceParams q) ∧
          ¬ 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
            q.ε / 2)).card ≤ 2 ^ rounds (varianceParams q)}
    have hδ := exp_neg_confidence hv
    have hδpos := hvH.2.2.2.2.2.2.1
    simp only [vp_δ] at hδ
    linarith
  intro A result
  have hres : result = fun w => finalOut q g w.1 w.2 :=
    funext fun w => execute_eq q g P hvH w.1 w.2
  rw [hres]
  exact hsucc

end LongTails.Proofs.HeavyTailedHighProbabilityUpper

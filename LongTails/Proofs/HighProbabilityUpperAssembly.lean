import LongTails.Setups.HighProbabilityStationarity
import LongTails.Proofs.HighProbabilityPhaseOne
import LongTails.Proofs.HighProbabilityPhaseTwo
import LongTails.Proofs.HighProbabilityConstants
import LongTails.Proofs.IIDBlocks

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.HighProbabilityUpperAssembly

open OracleTemplate QueryPlan LongTails.Algorithms.HighProbabilityStationarity
open LongTails.Setups.HighProbabilityStationarity
open LongTails.Proofs.HighProbabilityAdapted LongTails.Proofs.HighProbabilityExecution
open LongTails.Proofs.HighProbabilityRounds LongTails.Proofs.HighProbabilityPhaseOne
open LongTails.Proofs.HighProbabilityPhaseTwo LongTails.Proofs.HighProbabilityConstants
open LongTails.Proofs.HighProbabilityStep LongTails.Proofs.HighProbabilityDescent

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

section Concrete

variable (q : Params)

noncomputable abbrev blockLen : ℕ := pilotSize q + clipSize q

noncomputable abbrev windowLen : ℕ := 8 * blockSize q * 2 ^ rounds q

noncomputable abbrev offset : ℕ := blockLen q * steps q

noncomputable def iterate (g : q.E → q.Ω → q.E) (ξ : ℕ → q.Ω) (t : ℕ) : q.E :=
  traj (stepMap (radius q) (stepSize q) (levels q) (pilotSize q) (clipSize q) g) q.x0
    (blocks (blockLen q) ξ) t

noncomputable def candidatesOf (g : q.E → q.Ω → q.E) (τ : Fin (2 ^ rounds q) → Fin (steps q))
    (ξ : ℕ → q.Ω) : Fin (2 ^ rounds q) → q.E :=
  fun j => iterate q g ξ (τ j)

noncomputable def tailBlocks (ξ : ℕ → q.Ω) : ℕ → Fin (windowLen q) → q.Ω :=
  fun t j => ξ (offset q + t * windowLen q + j.val)

noncomputable def selectOut (g : q.E → q.Ω → q.E) (Y : Fin (2 ^ rounds q) → q.E)
    (b : ℕ → Fin (windowLen q) → q.Ω) : q.E :=
  (((traj (roundMap g q.ε (accuracy q) (rounds q) 8 (blockSize q) (by norm_num) q.x0 Y)
    (0, fun j => some j) b (rounds q + 1)).2 ⟨0, Nat.two_pow_pos (rounds q)⟩).map Y).getD q.x0

noncomputable def finalOut (g : q.E → q.Ω → q.E) (τ : Fin (2 ^ rounds q) → Fin (steps q))
    (ξ : ℕ → q.Ω) : q.E :=
  selectOut q g (candidatesOf q g τ ξ) (tailBlocks q ξ)

lemma method_eval (g : q.E → q.Ω → q.E) (τ : Fin (2 ^ rounds q) → Fin (steps q))
    (ξ : ℕ → q.Ω) :
    sampledEval g ξ (method (radius q) (stepSize q) q.ε (accuracy q) (levels q) (pilotSize q)
      (clipSize q) (steps q) (rounds q) 8 (blockSize q) (by norm_num) q.x0 τ) 0 =
      finalOut q g τ ξ := by
  unfold method
  rw [sampledEval_bind]
  obtain ⟨_, _, hpath⟩ := phaseOne_eval (radius q) (stepSize q) (levels q) (pilotSize q)
    (clipSize q) (steps q) q.x0 g ξ
  have hY : (fun j => (sampledEval g ξ (phaseOne (radius q) (stepSize q) (levels q) (pilotSize q)
      (clipSize q) (steps q) q.x0) 0).path (τ j)) = candidatesOf q g τ ξ := by
    funext j
    exact hpath (τ j) (τ j).isLt
  rw [hY, phaseTwo_eval]
  simp only [zero_add]
  rfl

lemma execute_eq (g : q.E → q.Ω → q.E) (P : ProbabilityMeasure (ℕ → q.Ω)) (hv : spec.valid q)
    (τ : Fin (2 ^ rounds q) → Fin (steps q)) (ξ : ℕ → q.Ω) :
    execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω } (algorithm q)
      (fun _ => ⌈2 ^ 71 * ((1 + q.σ ^ 2 / q.ε ^ 2) * (q.L * q.Δ / q.ε ^ 2 + Real.log (16 / q.δ) * Real.log (2 + Real.log (16 / q.δ)) ^ 3) + Real.sqrt (q.L * q.Δ) * Real.log (16 / q.δ) / q.ε)⌉₊) τ ξ = finalOut q g τ ξ := by
  unfold LongTails.Algorithms.HighProbabilityStationarity.algorithm
  rw [execute_sampledPlan_of_le _ _ _ _ _ _ _ g τ ξ (plan_le_budget hv)]
  exact method_eval q g τ ξ

end Concrete

section Measurability

variable (q : Params) {g : q.E → q.Ω → q.E} (hg : Measurable (Function.uncurry g))
include hg

lemma measurable_iterate (t : ℕ) : Measurable (fun ξ : ℕ → q.Ω => iterate q g ξ t) :=
  (measurable_traj (measurable_stepMap (radius q) (stepSize q) (levels q) (pilotSize q)
    (clipSize q) hg) q.x0 t).comp (measurable_blocks (Ω := q.Ω) _)

lemma measurable_candidates :
    Measurable (fun w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) =>
      candidatesOf q g w.1 w.2) :=
  Measurable.of_eval fun j => measurable_from_prod_countable_right fun τ =>
    measurable_iterate q hg (τ j)

omit hg in
lemma measurable_tailBlocks : Measurable (tailBlocks q) :=
  Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_pi_apply _

lemma measurable_selectOut :
    Measurable (fun w : (Fin (2 ^ rounds q) → q.E) × (ℕ → Fin (windowLen q) → q.Ω) =>
      selectOut q g w.1 w.2) := by
  let outFn : (Fin (2 ^ rounds q) → q.E) × Ladder (2 ^ rounds q) → q.E :=
    fun w => ((w.2.2 ⟨0, Nat.two_pow_pos (rounds q)⟩).map w.1).getD q.x0
  have hout : Measurable outFn := measurable_from_prod_countable_left fun s =>
    measurable_point (s.2 ⟨0, Nat.two_pow_pos (rounds q)⟩) q.x0
  have htraj := (measurable_traj_joint (measurable_chainStep hg q.ε (accuracy q) (rounds q) 8
    (blockSize q) (by norm_num) q.x0) (rounds q + 1)).comp
    ((measurable_fst.prodMk (measurable_const (a := ((0, fun j => some j) :
      Ladder (2 ^ rounds q))))).prodMk measurable_snd)
  have key : ∀ w : (Fin (2 ^ rounds q) → q.E) × (ℕ → Fin (windowLen q) → q.Ω),
      selectOut q g w.1 w.2 = outFn (traj (chainStep g q.ε (accuracy q) (rounds q) 8 (blockSize q)
        (by norm_num) q.x0) (w.1, ((0, fun j => some j) : Ladder (2 ^ rounds q))) w.2
          (rounds q + 1)) := by
    intro w
    rw [traj_chainStep]
    rfl
  have he : (fun w : (Fin (2 ^ rounds q) → q.E) × (ℕ → Fin (windowLen q) → q.Ω) =>
      selectOut q g w.1 w.2) = fun w => outFn (traj (chainStep g q.ε (accuracy q) (rounds q) 8
        (blockSize q) (by norm_num) q.x0) (w.1, ((0, fun j => some j) : Ladder (2 ^ rounds q))) w.2
          (rounds q + 1)) := funext key
  rw [he]
  exact hout.comp htraj

lemma measurable_finalOut :
    Measurable (fun w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) =>
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

lemma phase_one_fail (q : Params) (hv : spec.valid q) {f : q.E → ℝ} {g : q.E → q.Ω → q.E}
    {p : Measure q.Ω} [IsProbabilityMeasure p] {fstar : ℝ}
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) (hlow : ∀ x, fstar ≤ f x)
    (hgap : f q.x0 - fstar ≤ q.Δ) (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = gradient f x)
    (hvi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p)
    (hvar : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ q.σ ^ 2)
    (P : Measure (ℕ → q.Ω)) [IsProbabilityMeasure P]
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      p P) :
    P.real {ξ | ¬ 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
      ¬ ‖gradient f (iterate q g ξ t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q} ≤
        2 * Real.exp (-confidence q) := by
  classical
  have hgm := gradient_measurable hv.1.le hlip
  have hB := radius_pos hv
  have he := hv.2.2.2.1
  have hη := stepSize_nonneg hv
  have hmc := clip_pos hv
  set F := stepMap (radius q) (stepSize q) (levels q) (pilotSize q) (clipSize q) g with hFdef
  have hF := measurable_stepMap (radius q) (stepSize q) (levels q) (pilotSize q) (clipSize q) hg
  have hb := OracleTemplate.FiniteVariance.infinite_block_law p P hiid.independent hiid.marginal
    (blockLen q)
  set μb := Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (blockLen q) => p
  let Sb : Set (ℕ → Fin (blockLen q) → q.Ω) := {b | ¬ 64 * (Finset.univ.filter
    (fun t : Fin (steps q) => ¬ ‖gradient f (traj F q.x0 b t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q}
  have hSb : MeasurableSet Sb :=
    measurableSet_count (Y := fun b : ℕ → Fin (blockLen q) → q.Ω => fun t : Fin (steps q) =>
      traj F q.x0 b t) (Measurable.of_eval fun t => measurable_traj hF q.x0 t) hgm (q.ε / 2)
      (fun m => ¬ 64 * m ≤ 3 * steps q)
  have hpre : P.real {ξ | ¬ 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
      ¬ ‖gradient f (iterate q g ξ t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q} = μb.real Sb := by
    have : {ξ : ℕ → q.Ω | ¬ 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
        ¬ ‖gradient f (iterate q g ξ t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q} =
        (fun ξ : ℕ → q.Ω => fun k : ℕ => fun i : Fin (blockLen q) => ξ (k * blockLen q + i.val)) ⁻¹'
          Sb := rfl
    rw [this, measureReal_def, measureReal_def, hb.measure_preimage hSb.nullMeasurableSet]
  rw [hpre]
  set W := 2 * ((steps q) * q.ε / 512) + ∑ j ∈ Finset.range ((scales q) + 1), 8 * (2 ^ j * radius q) * counts q j
  have hW : W ≤ (steps q) * q.ε / 128 := by
    have := W_bound ((steps q) : ℝ) q.ε (radius q) (by positivity) he hB (scales q)
    simpa only [W, counts] using this
  have hroom0 := descent_room (L := q.L) (Δ := q.Δ) (ε := q.ε) (G := gradientScale q) (T := steps q)
    hv.1 hv.2.2.1 he le_rfl (by
      have := steps_ge hv; have := confidence_ge hv
      have : 0 ≤ q.L * q.Δ / q.ε ^ 2 := div_nonneg (mul_nonneg hv.1.le hv.2.2.1) (sq_nonneg _)
      linarith)
  simp only at hroom0
  have hstep : stepSize q = 128 * (q.Δ + q.ε ^ 2 / q.L) / ((steps q) * q.ε) := rfl
  rw [← hstep] at hroom0
  obtain ⟨hcount0, hroom1⟩ := hroom0
  have hroom : 2 * q.L * (q.Δ + stepSize q * W + (steps q) * (q.L / 2 * stepSize q ^ 2)) ≤
      (3 * gradientScale q) ^ 2 := by
    have : stepSize q * W ≤ stepSize q * ((steps q) * q.ε / 128) := mul_le_mul_of_nonneg_left hW hη
    nlinarith [hv.1]
  have hρ : ∀ j ∈ Finset.range ((scales q) + 1), ∀ x, (Measure.pi fun _ : Fin (pilotSize q + clipSize q) => p)
      {z | 2 ^ j * radius q / 2 < ‖pilotOf (radius q) (levels q) (pilotSize q) (clipSize q) (g x) z -
        gradient f x‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (2 * halfExp q j)) := by
    intro j hj x
    have hjJ : j ≤ (scales q) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjK : j ≤ levels q := hjJ.trans (scales_le_levels hv)
    have hgx : Measurable (g x) := hg.comp measurable_prodMk_left
    have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hR := radius_ge hv
    have hS := noise_pos hv
    have hpow : (2 : ℝ) ^ j ≤ 2 ^ levels q := pow_le_pow_right₀ (by norm_num) hjK
    refine (block_scale (V := g x) hgx (hvi x) (sigma_le_noise hv) hv.2.1 hS ?_ (hvar x) ?_ ?_).trans
      (ENNReal.ofReal_le_ofReal (scale_prob hv j))
    · nlinarith
    · nlinarith
    · nlinarith
  have hsub : Sb ⊆ {b | q.Δ + stepSize q * W + (steps q) * (q.L / 2 * stepSize q ^ 2) <
      stepSize q * ∑ t ∈ Finset.range (steps q), ‖gradient f (traj F q.x0 b t)‖} := by
    intro b hbS
    simp only [Sb, Set.mem_ofPred_eq] at hbS ⊢
    by_contra hcon
    push Not at hcon
    apply hbS
    have hηpos : 0 < stepSize q := by
      unfold stepSize; have := hv.1; have := hv.2.2.1; have := steps_pos (q := q); positivity
    have hsum : (∑ t ∈ Finset.range (steps q), ‖gradient f (traj F q.x0 b t)‖) ≤ 3 * (steps q) * q.ε / 128 := by
      have h1 : stepSize q * W ≤ stepSize q * ((steps q) * q.ε / 128) := mul_le_mul_of_nonneg_left hW hη
      have h2 : stepSize q * ∑ t ∈ Finset.range (steps q), ‖gradient f (traj F q.x0 b t)‖ ≤
          stepSize q * (3 * (steps q) * q.ε / 128) := by linarith
      exact le_of_mul_le_mul_left h2 hηpos
    have hcl := count_large (fun t => ‖gradient f (traj F q.x0 b t)‖) (fun t => norm_nonneg _)
      (q.ε / 2) (steps q)
    have hcard : (Finset.univ.filter (fun t : Fin (steps q) => ¬ ‖gradient f (traj F q.x0 b t)‖ ≤ q.ε / 2)).card =
        ((Finset.range (steps q)).filter (fun t => q.ε / 2 < ‖gradient f (traj F q.x0 b t)‖)).card := by
      rw [card_fin_filter (steps q) (fun t => ¬ ‖gradient f (traj F q.x0 b t)‖ ≤ q.ε / 2)]
      congr 1
      exact Finset.filter_congr fun t _ => not_le
    rw [hcard]
    have hreal : (64 : ℝ) * ((Finset.range (steps q)).filter
        (fun t => q.ε / 2 < ‖gradient f (traj F q.x0 b t)‖)).card ≤ 3 * (steps q) := by
      nlinarith
    exact_mod_cast hreal
  have hmain := phase_one_prob (p := p) hg hv.1 hη hB hv.2.1 (K := levels q) (J := scales q) (T := steps q)
    hmc hgrad hlip hlow hgm hgi hmean hvi hvar (scales_cover hv) (by have := grad_pos hv; positivity)
    (counts q) (halfExp q) hρ q.x0 hgap (ra := (steps q) * q.ε / 512) hroom
  refine (measureReal_mono hsub).trans (hmain.trans ?_)
  have h1 := Real.exp_le_exp.mpr (ok_tail_const hv)
  have h2 := scale_sum hv
  linarith

lemma seed_fail (q : Params) (hv : spec.valid q) (B : Fin (steps q) → Prop) [DecidablePred B]
    (h : 64 * (Finset.univ.filter B).card ≤ 3 * steps q) :
    (seedLaw q : Measure (Fin (2 ^ rounds q) → Fin (steps q))).real
      {τ | ¬ 3 * (Finset.univ.filter (fun j => B (τ j))).card ≤ 2 ^ rounds q} ≤
        Real.exp (-confidence q) := by
  set unif := (PMF.uniformOfFintype (Fin (steps q))).toMeasure
  have hA : MeasurableSet {t : Fin (steps q) | B t} := MeasurableSet.of_discrete
  have hT := steps_pos (q := q)
  have hc : Fintype.card {t : Fin (steps q) | B t} = (Finset.univ.filter B).card := by
    simp [Fintype.card_subtype]
  have hp : unif.real {t : Fin (steps q) | B t} ≤ 1 / 16 := by
    rw [measureReal_def, PMF.toMeasure_uniformOfFintype_apply _ hA, hc, Fintype.card_fin,
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      div_le_iff₀ (by exact_mod_cast hT)]
    have : (64 : ℝ) * (Finset.univ.filter B).card ≤ 3 * steps q := by exact_mod_cast h
    linarith
  have hfrac := fraction_failure (P := unif) (A := fun _ : Fin (2 ^ rounds q) =>
    {t : Fin (steps q) | B t}) (fun _ => hA) (θ := 1 / 16) (by norm_num) (by norm_num)
    (fun _ => hp) (2 ^ rounds q / 3 + 1)
  have hsub : {τ : Fin (2 ^ rounds q) → Fin (steps q) |
      ¬ 3 * (Finset.univ.filter (fun j => B (τ j))).card ≤ 2 ^ rounds q} ⊆
      {τ | 2 ^ rounds q / 3 + 1 ≤ (Finset.univ.filter (fun j => τ j ∈
        {t : Fin (steps q) | B t})).card} := by
    intro τ hτ
    have he : (Finset.univ.filter (fun j => τ j ∈ {t : Fin (steps q) | B t})).card =
        (Finset.univ.filter (fun j => B (τ j))).card := rfl
    simp only [Set.mem_ofPred_eq] at hτ ⊢
    omega
  have hseed : (seedLaw q : Measure (Fin (2 ^ rounds q) → Fin (steps q))) =
      Measure.pi fun _ : Fin (2 ^ rounds q) => unif := rfl
  rw [hseed]
  have hle := (measureReal_mono hsub).trans
    (ENNReal.toReal_le_of_le_ofReal (by positivity) hfrac)
  exact hle.trans (seed_bound hv)

noncomputable def preBlocks (q : Params) (hN : 0 < offset q) (a : Fin (offset q) → q.Ω) :
    ℕ → Fin (blockLen q) → q.Ω :=
  fun s i => a ⟨(s * blockLen q + i.val) % offset q, Nat.mod_lt _ hN⟩

noncomputable def candidatesPre (q : Params) (g : q.E → q.Ω → q.E) (hN : 0 < offset q)
    (u : (Fin (2 ^ rounds q) → Fin (steps q)) × (Fin (offset q) → q.Ω)) :
    Fin (2 ^ rounds q) → q.E :=
  fun j => traj (stepMap (radius q) (stepSize q) (levels q) (pilotSize q) (clipSize q) g) q.x0
    (preBlocks q hN u.2) (u.1 j)

noncomputable def windows (q : Params) (c : ℕ → q.Ω) : ℕ → Fin (windowLen q) → q.Ω :=
  fun t j => c (t * windowLen q + j.val)

lemma candidates_eq_pre (q : Params) (g : q.E → q.Ω → q.E) (hN : 0 < offset q)
    (τ : Fin (2 ^ rounds q) → Fin (steps q)) (ξ : ℕ → q.Ω) :
    candidatesOf q g τ ξ = candidatesPre q g hN (τ, fun i => ξ i.val) := by
  funext j
  unfold candidatesOf iterate candidatesPre
  refine traj_congr _ _ fun s hs => ?_
  funext i
  simp only [blocks, preBlocks]
  congr 1
  have hlt : s * blockLen q + i.val < offset q := by
    unfold offset
    have hsT : s + 1 ≤ steps q := by have := (τ j).isLt; omega
    have : s * blockLen q + i.val < (s + 1) * blockLen q := by
      have := i.isLt; nlinarith
    nlinarith
  rw [Nat.mod_eq_of_lt hlt]

lemma tail_eq_windows (q : Params) (ξ : ℕ → q.Ω) :
    tailBlocks q ξ = windows q (fun i => ξ (offset q + i)) := by
  funext t j
  simp only [tailBlocks, windows, add_assoc]

lemma part_two (q : Params) (hv : spec.valid q) {f : q.E → ℝ} {g : q.E → q.Ω → q.E}
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖)
    (hg : Measurable (Function.uncurry g)) (P : Measure (ℕ → q.Ω)) [IsProbabilityMeasure P] :
    ((seedLaw q : Measure (Fin (2 ^ rounds q) → Fin (steps q))).prod P).real
      {w | 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
        ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q ∧
        ¬ 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
          q.ε / 2)).card ≤ 2 ^ rounds q} ≤ Real.exp (-confidence q) := by
  classical
  have hgm := gradient_measurable hv.1.le hlip
  set ν := (seedLaw q : Measure (Fin (2 ^ rounds q) → Fin (steps q)))
  set S := {w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) |
    64 * (Finset.univ.filter (fun t : Fin (steps q) =>
        ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q ∧
        ¬ 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
          q.ε / 2)).card ≤ 2 ^ rounds q}
  have hS : MeasurableSet S := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_count (Y := fun w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) =>
        fun t : Fin (steps q) => iterate q g w.2 t)
        (Measurable.of_eval fun t => (measurable_iterate q hg t).comp measurable_snd) hgm (q.ε / 2)
        (fun m => 64 * m ≤ 3 * steps q)
    · exact measurableSet_count (Y := fun w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) =>
        candidatesOf q g w.1 w.2) (measurable_candidates q hg) hgm (q.ε / 2)
        (fun m => ¬ 3 * m ≤ 2 ^ rounds q)
  have hslice (ξ : ℕ → q.Ω) : ν ((fun τ => (τ, ξ)) ⁻¹' S) ≤ ENNReal.ofReal (Real.exp (-confidence q)) := by
    by_cases hξ : 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
        ¬ ‖gradient f (iterate q g ξ t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q
    · have hset : (fun τ => (τ, ξ)) ⁻¹' S =
          {τ | ¬ 3 * (Finset.univ.filter (fun j =>
            ¬ ‖gradient f (iterate q g ξ (τ j))‖ ≤ q.ε / 2)).card ≤ 2 ^ rounds q} := by
        ext τ
        exact ⟨fun h => h.2, fun h => ⟨hξ, h⟩⟩
      rw [hset, ← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (seed_fail q hv
        (fun t => ¬ ‖gradient f (iterate q g ξ t)‖ ≤ q.ε / 2) hξ)
    · have hset : (fun τ => (τ, ξ)) ⁻¹' S = ∅ := by
        ext τ
        simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, hξ, false_and, Set.mem_empty_iff_false]
      rw [hset, measure_empty]
      positivity
  have hμ : (ν.prod P) S ≤ ENNReal.ofReal (Real.exp (-confidence q)) := by
    rw [Measure.prod_apply_symm hS]
    calc (∫⁻ ξ, ν ((fun τ => (τ, ξ)) ⁻¹' S) ∂P) ≤
          ∫⁻ _ξ, ENNReal.ofReal (Real.exp (-confidence q)) ∂P := lintegral_mono hslice
      _ = ENNReal.ofReal (Real.exp (-confidence q)) := by simp
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hμ

lemma part_three (q : Params) (hv : spec.valid q) {f : q.E → ℝ} {g : q.E → q.Ω → q.E}
    {p : Measure q.Ω} [IsProbabilityMeasure p]
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = gradient f x)
    (hvi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p)
    (hvar : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ q.σ ^ 2)
    (P : Measure (ℕ → q.Ω)) [IsProbabilityMeasure P]
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      p P) :
    ((seedLaw q : Measure (Fin (2 ^ rounds q) → Fin (steps q))).prod P).real
      {w | 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
          q.ε / 2)).card ≤ 2 ^ rounds q ∧
        ¬ ‖gradient f (finalOut q g w.1 w.2)‖ ≤ q.ε / 2 + 2 * ((rounds q : ℝ) + 1) * accuracy q} ≤
      Real.exp (-confidence q) := by
  classical
  have hgm := gradient_measurable hv.1.le hlip
  have hN : 0 < offset q := by
    unfold offset blockLen
    have := clip_pos hv
    exact Nat.mul_pos (by omega) (Nat.succ_pos _)
  set ν := (seedLaw q : Measure (Fin (2 ^ rounds q) → Fin (steps q)))
  set ε' := q.ε / 2 + 2 * ((rounds q : ℝ) + 1) * accuracy q
  have hF := measurable_stepMap (radius q) (stepSize q) (levels q) (pilotSize q) (clipSize q) hg
  have hpreB : Measurable (preBlocks q hN) :=
    Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_pi_apply _
  have hcandP : Measurable (candidatesPre q g hN) :=
    Measurable.of_eval fun j => measurable_from_prod_countable_right fun τ =>
      (measurable_traj hF q.x0 (τ j)).comp hpreB
  have hwin : Measurable (windows q) :=
    Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_pi_apply _
  set S' := {u : ((Fin (2 ^ rounds q) → Fin (steps q)) × (Fin (offset q) → q.Ω)) × (ℕ → q.Ω) |
    3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesPre q g hN u.1 j)‖ ≤
      q.ε / 2)).card ≤ 2 ^ rounds q ∧
    ¬ ‖gradient f (selectOut q g (candidatesPre q g hN u.1) (windows q u.2))‖ ≤ ε'}
  have hS' : MeasurableSet S' := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_count (Y := fun u : ((Fin (2 ^ rounds q) → Fin (steps q)) ×
        (Fin (offset q) → q.Ω)) × (ℕ → q.Ω) => candidatesPre q g hN u.1)
        (hcandP.comp measurable_fst) hgm (q.ε / 2) (fun m => 3 * m ≤ 2 ^ rounds q)
    · exact (measurableSet_le ((hgm.comp ((measurable_selectOut q hg).comp
        ((hcandP.comp measurable_fst).prodMk (hwin.comp measurable_snd)))).norm)
          measurable_const).compl
  set Ψ : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) →
      ((Fin (2 ^ rounds q) → Fin (steps q)) × (Fin (offset q) → q.Ω)) × (ℕ → q.Ω) :=
    fun w => ((w.1, fun i => w.2 i.val), fun i => w.2 (offset q + i))
  have hΨ : MeasurePreserving Ψ (ν.prod P)
      ((ν.prod (Measure.pi fun _ : Fin (offset q) => p)).prod (Measure.infinitePi fun _ : ℕ => p)) := by
    have h1 := hiid.prefix_tail_law (offset q)
    have h2 := (MeasurePreserving.id ν).prod h1
    have h3 := MeasurePreserving.symm _ (measurePreserving_prodAssoc ν
      (Measure.pi fun _ : Fin (offset q) => p) (Measure.infinitePi fun _ : ℕ => p))
    exact h3.comp h2
  have hpre : {w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) |
      3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
          q.ε / 2)).card ≤ 2 ^ rounds q ∧
        ¬ ‖gradient f (finalOut q g w.1 w.2)‖ ≤ ε'} = Ψ ⁻¹' S' := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, S', Ψ, finalOut,
      candidates_eq_pre q g hN w.1 w.2, tail_eq_windows q w.2]
  rw [hpre, measureReal_def, hΨ.measure_preimage hS'.nullMeasurableSet, ← measureReal_def]
  have hblock := OracleTemplate.FiniteVariance.infinite_block_law p
    (Measure.infinitePi fun _ : ℕ => p)
    (OracleTemplate.StochasticGeneralized.infinitePi_iid p).independent
    (OracleTemplate.StochasticGeneralized.infinitePi_iid p).marginal (windowLen q)
  have hslice (x : (Fin (2 ^ rounds q) → Fin (steps q)) × (Fin (offset q) → q.Ω)) :
      (Measure.infinitePi fun _ : ℕ => p) (Prod.mk x ⁻¹' S') ≤
        ENNReal.ofReal (Real.exp (-confidence q)) := by
    by_cases hx : 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesPre q g hN x j)‖ ≤
        q.ε / 2)).card ≤ 2 ^ rounds q
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
      have h2 := phase_two (p := p) hg hgm hgi hmean hvi hvar (accuracy_pos hv) (Λ := rounds q)
        (k0 := 8) (r := blockSize q) (by norm_num) (blockSize_pos hv) (block_accuracy hv) q.x0 Y
        (ε := q.ε) hx
      exact h2.trans (rounds_sum hv)
    · have hset : Prod.mk x ⁻¹' S' = ∅ := by
        ext c
        simp only [S', Set.mem_preimage, Set.mem_ofPred_eq, hx, false_and,
          Set.mem_empty_iff_false]
      rw [hset, measure_empty]
      positivity
  have hμ : ((ν.prod (Measure.pi fun _ : Fin (offset q) => p)).prod
      (Measure.infinitePi fun _ : ℕ => p)) S' ≤ ENNReal.ofReal (Real.exp (-confidence q)) := by
    rw [Measure.prod_apply hS']
    calc (∫⁻ x, (Measure.infinitePi fun _ : ℕ => p) (Prod.mk x ⁻¹' S')
          ∂(ν.prod (Measure.pi fun _ : Fin (offset q) => p))) ≤
          ∫⁻ _x, ENNReal.ofReal (Real.exp (-confidence q))
            ∂(ν.prod (Measure.pi fun _ : Fin (offset q) => p)) := lintegral_mono hslice
      _ = ENNReal.ofReal (Real.exp (-confidence q)) := by simp
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hμ

theorem convergence : Convergence LongTails.Setups.HighProbabilityStationarity.spec
    (fun q _ => ⌈2 ^ 71 * ((1 + q.σ ^ 2 / q.ε ^ 2) * (q.L * q.Δ / q.ε ^ 2 + Real.log (16 / q.δ) * Real.log (2 + Real.log (16 / q.δ)) ^ 3) + Real.sqrt (q.L * q.Δ) * Real.log (16 / q.δ) / q.ε)⌉₊) := by
  refine ⟨fun q => LongTails.Algorithms.HighProbabilityStationarity.algorithm q,
    fun q hv f O hadm => ?_, fun _ _ => trivial⟩
  obtain ⟨g, p, P, fstar, hiid, hO, hgrad, hlip, hlow, _, hgap, hg, hgi, hmean, hvi, hvar⟩ := hadm
  subst hO
  have hgm := gradient_measurable hv.1.le hlip
  have hsucc : LongTails.Setups.HighProbabilityStationarity.spec.successful q f
      (fun w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) => finalOut q g w.1 w.2)
      ⟨(seedLaw q : Measure (Fin (2 ^ rounds q) → Fin (steps q))).prod (P : Measure (ℕ → q.Ω)),
        inferInstance⟩ := by
    refine ⟨measurable_finalOut q hg, ?_⟩
    change 1 - q.δ ≤ ((seedLaw q : Measure (Fin (2 ^ rounds q) → Fin (steps q))).prod
      (P : Measure (ℕ → q.Ω))).real {w | ‖gradient f (finalOut q g w.1 w.2)‖ ≤ q.ε}
    have hε' := accuracy_final hv
    have hG : MeasurableSet {w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) |
        ‖gradient f (finalOut q g w.1 w.2)‖ ≤ q.ε} :=
      measurableSet_le (hgm.comp (measurable_finalOut q hg)).norm measurable_const
    have hsub : {w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) |
        ‖gradient f (finalOut q g w.1 w.2)‖ ≤ q.ε}ᶜ ⊆
        ({w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) |
          ¬ 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q} ∪
        {w | 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q ∧
          ¬ 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
            q.ε / 2)).card ≤ 2 ^ rounds q}) ∪
        {w | 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
            q.ε / 2)).card ≤ 2 ^ rounds q ∧
          ¬ ‖gradient f (finalOut q g w.1 w.2)‖ ≤
            q.ε / 2 + 2 * ((rounds q : ℝ) + 1) * accuracy q} := by
      intro w hw
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hw
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      by_cases h1 : 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
          ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q
      · by_cases h2 : 3 * (Finset.univ.filter (fun j =>
            ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤ q.ε / 2)).card ≤ 2 ^ rounds q
        · right; exact ⟨h2, fun h => hw (h.trans hε')⟩
        · left; right; exact ⟨h1, h2⟩
      · left; left; exact h1
    have hA1 : ((seedLaw q : Measure (Fin (2 ^ rounds q) → Fin (steps q))).prod
        (P : Measure (ℕ → q.Ω))).real {w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) |
          ¬ 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q} ≤
          2 * Real.exp (-confidence q) := by
      have he : {w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) |
          ¬ 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q} =
          Set.univ ×ˢ {ξ : ℕ → q.Ω | ¬ 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
            ¬ ‖gradient f (iterate q g ξ t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q} := by
        ext w
        simp
      rw [he, measureReal_def, Measure.prod_prod, measure_univ, one_mul, ← measureReal_def]
      exact phase_one_fail q hv hgrad hlip hlow hgap hg hgi hmean hvi hvar (P : Measure _) hiid
    have hA2 := part_two q hv hlip hg (P : Measure (ℕ → q.Ω)) (f := f)
    have hA3 := part_three q hv hlip hg hgi hmean hvi hvar (P : Measure (ℕ → q.Ω)) hiid
    have hcompl := probReal_compl_eq_one_sub (μ := (seedLaw q : Measure
      (Fin (2 ^ rounds q) → Fin (steps q))).prod (P : Measure (ℕ → q.Ω))) hG
    have hmono := measureReal_mono (μ := (seedLaw q : Measure
      (Fin (2 ^ rounds q) → Fin (steps q))).prod (P : Measure (ℕ → q.Ω))) hsub
    have h123 := measureReal_union_le (μ := (seedLaw q : Measure
      (Fin (2 ^ rounds q) → Fin (steps q))).prod (P : Measure (ℕ → q.Ω)))
      ({w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) |
          ¬ 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q} ∪
        {w | 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q ∧
          ¬ 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
            q.ε / 2)).card ≤ 2 ^ rounds q})
      {w | 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
            q.ε / 2)).card ≤ 2 ^ rounds q ∧
          ¬ ‖gradient f (finalOut q g w.1 w.2)‖ ≤
            q.ε / 2 + 2 * ((rounds q : ℝ) + 1) * accuracy q}
    have h12 := measureReal_union_le (μ := (seedLaw q : Measure
      (Fin (2 ^ rounds q) → Fin (steps q))).prod (P : Measure (ℕ → q.Ω)))
      {w : (Fin (2 ^ rounds q) → Fin (steps q)) × (ℕ → q.Ω) |
          ¬ 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q}
        {w | 64 * (Finset.univ.filter (fun t : Fin (steps q) =>
            ¬ ‖gradient f (iterate q g w.2 t)‖ ≤ q.ε / 2)).card ≤ 3 * steps q ∧
          ¬ 3 * (Finset.univ.filter (fun j => ¬ ‖gradient f (candidatesOf q g w.1 w.2 j)‖ ≤
            q.ε / 2)).card ≤ 2 ^ rounds q}
    have hδ := exp_neg_confidence hv
    have hδpos := hv.2.2.2.2.1
    linarith
  intro A result
  have hres : result = fun w => finalOut q g w.1 w.2 :=
    funext fun w => execute_eq q g P hv w.1 w.2
  rw [hres]
  exact hsucc

end LongTails.Proofs.HighProbabilityUpperAssembly

import LongTails.Proofs.MinibatchExtragradientStep
import LongTails.Proofs.SampledQueryPlan
import LongTails.Setups.StochasticWeakMinty
import LongTails.Proofs.AdaptiveIID

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace LongTails.Proofs.MinibatchExtragradientRun

open OracleTemplate OracleTemplate.QueryPlan
open OracleTemplate.StochasticCohypomonotone (evalP lintegral_split extendP measurable_extendP)
open LongTails.Algorithms.MinibatchExtragradient LongTails.Proofs.MinibatchExtragradientStep
open LongTails.Setups.StochasticGeneralizedMonotone (IsStochasticOperator)

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma xbar_congr (g : E → Ω → E) (γ : ℝ) (b : ℕ) (x : E) (ξ ξ' : ℕ → Ω)
    (h : ∀ i, i < b + b → ξ i = ξ' i) : xbar g γ b x ξ = xbar g γ b x ξ' := by
  unfold xbar
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h i (by omega)]

lemma xnext_congr (g : E → Ω → E) (γ : ℝ) (b : ℕ) (x : E) (ξ ξ' : ℕ → Ω)
    (h : ∀ i, i < b + b → ξ i = ξ' i) : xnext g γ b x ξ = xnext g γ b x ξ' := by
  unfold xnext
  rw [xbar_congr g γ b x ξ ξ' h]
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h (b + i) (by omega)]

lemma execute_algorithm [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω)) (g : E → Ω → E) (γ : ℝ) (b K : ℕ)
    (x0 : E) (N : ℕ) (ι : Fin (K + 1)) (ξ : ℕ → Ω) (h : stopLen b ι.val ≤ N) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (algorithm γ b K x0) (fun _ => N) ι ξ = evalP g (stoppedPlan γ b ι.val x0) ξ := by
  erw [StochasticGradient.execute_advance]
  change QueryPlan.output x0 (StochasticGradient.advance
    (fun call s => QueryPlan.update s (g (QueryPlan.query x0 s) (ξ call))) N 0
      ⟨stopLen b ι.val, stoppedPlan γ b ι.val x0⟩) = _
  rw [advance_sampledPlan_of_le g ξ x0 _ h]
  rfl

section Recursion

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def residualSum (F : E → E) (g : E → Ω → E) (γ : ℝ) (b n : ℕ) (x : E) : ℝ≥0∞ :=
  ∑ ι ∈ Finset.range n, ∫⁻ ξ, ENNReal.ofReal (‖F (evalP g (stoppedPlan γ b ι x) ξ)‖ ^ 2)
    ∂(Measure.infinitePi fun _ : ℕ => μ)

lemma nonempty_of_prob {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν] :
    Nonempty Ω' := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 : ν Set.univ = 1 := measure_univ
  rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
  exact zero_ne_one h1

lemma residualSum_bound {F : E → E} {g : E → Ω → E} {L ρ γ σ : ℝ}
    (hg : IsStochasticOperator μ F g σ) (hγ : L * γ = 1 / 2) (hγ0 : 0 < γ)
    (hρ : ρ ≤ γ / 10) (hlip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (xs : E)
    (hmin : ∀ x, -ρ * ‖F x‖ ^ 2 ≤ ⟪F x, x - xs⟫) {b : ℕ} (hb : 0 < b) :
    ∀ (n : ℕ) (x : E), ENNReal.ofReal (γ ^ 2 / 11) * residualSum μ F g γ b n x ≤
      ENNReal.ofReal (‖x - xs‖ ^ 2) + n * ENNReal.ofReal (52 * γ ^ 2 * (σ ^ 2 / b)) := by
  have hgm := hg.measurable
  obtain ⟨ω0⟩ := nonempty_of_prob μ
  have hL0 : 0 < L := by
    by_contra h
    push Not at h
    nlinarith
  have hF : Continuous F := (LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0.le]; exact hlip a b).continuous
  have hext : ∀ (x : E) (ξ : ℕ → Ω), xnext g γ b x ξ =
      xnext g γ b x (extendP ω0 (b + b) (fun i : Fin (b + b) => ξ i)) := by
    intro x ξ
    apply xnext_congr
    intro i hi
    simp [extendP, hi]
  have hym : ∀ x, Measurable (fun u : Fin (b + b) → Ω => xnext g γ b x (extendP ω0 (b + b) u)) :=
    fun x => (xnext_measurable hgm γ b).comp (measurable_const.prodMk (measurable_extendP ω0 (b + b)))
  have hterm_m : ∀ ι, Measurable (fun z : E × (ℕ → Ω) =>
      ENNReal.ofReal (‖F (evalP g (stoppedPlan γ b ι z.1) z.2)‖ ^ 2)) := fun ι =>
    ENNReal.measurable_ofReal.comp ((hF.measurable.comp (stopped_measurable hgm γ b ι)).norm.pow_const 2)
  intro n
  induction n with
  | zero =>
      intro x
      simp [residualSum]
  | succ n ih =>
      intro x
      have hsucc : ∀ ι, ∫⁻ ξ, ENNReal.ofReal (‖F (evalP g (stoppedPlan γ b (ι + 1) x) ξ)‖ ^ 2)
            ∂(Measure.infinitePi fun _ : ℕ => μ) =
          ∫⁻ u, ∫⁻ ξ, ENNReal.ofReal (‖F (evalP g (stoppedPlan γ b ι
            (xnext g γ b x (extendP ω0 (b + b) u))) ξ)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ)
            ∂(Measure.pi fun _ : Fin (b + b) => μ) := by
        intro ι
        have hs := lintegral_split μ (b + b)
          (fun u t => ENNReal.ofReal (‖F (evalP g (stoppedPlan γ b ι
            (xnext g γ b x (extendP ω0 (b + b) u))) t)‖ ^ 2))
          ((hterm_m ι).comp ((hym x).prodMap measurable_id))
        beta_reduce at hs
        rw [← hs]
        refine lintegral_congr fun ξ => ?_
        rw [evalP_stopped_succ, hext]
      have hinner_m : ∀ ι, Measurable (fun u : Fin (b + b) → Ω =>
          ∫⁻ ξ, ENNReal.ofReal (‖F (evalP g (stoppedPlan γ b ι
            (xnext g γ b x (extendP ω0 (b + b) u))) ξ)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ)) :=
        fun ι => ((hterm_m ι).comp ((hym x).prodMap measurable_id)).lintegral_prod_right'
      have hsum : residualSum μ F g γ b (n + 1) x =
          ∫⁻ u, residualSum μ F g γ b n (xnext g γ b x (extendP ω0 (b + b) u))
              ∂(Measure.pi fun _ : Fin (b + b) => μ) +
            ∫⁻ ξ, ENNReal.ofReal (‖F (xbar g γ b x ξ)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ) := by
        unfold residualSum
        rw [Finset.sum_range_succ']
        simp_rw [hsucc, evalP_stopped_zero]
        rw [lintegral_finsetSum _ (fun ι _ => hinner_m ι)]
      have hnorm : ∫⁻ u, ENNReal.ofReal (‖xnext g γ b x (extendP ω0 (b + b) u) - xs‖ ^ 2)
            ∂(Measure.pi fun _ : Fin (b + b) => μ) =
          ∫⁻ ξ, ENNReal.ofReal (‖xnext g γ b x ξ - xs‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ) := by
        have hs := lintegral_split μ (b + b)
          (fun u _ => ENNReal.ofReal (‖xnext g γ b x (extendP ω0 (b + b) u) - xs‖ ^ 2))
          ((ENNReal.measurable_ofReal.comp ((((hym x).sub measurable_const).norm).pow_const 2)).comp
            measurable_fst)
        simp only [lintegral_const, measure_univ, mul_one] at hs
        rw [← hs]
        refine lintegral_congr fun ξ => ?_
        rw [← hext]
      have hstep := step_expect hg hγ hγ0 hρ hlip xs hmin hb x (μ := μ)
      have hxm : Measurable (fun ξ : ℕ → Ω => ENNReal.ofReal (‖xnext g γ b x ξ - xs‖ ^ 2)) :=
        ENNReal.measurable_ofReal.comp ((((xnext_measurable hgm γ b).comp
          (measurable_const.prodMk measurable_id)).sub measurable_const).norm.pow_const 2)
      have hfm : Measurable (fun ξ : ℕ → Ω => ENNReal.ofReal (‖F (xbar g γ b x ξ)‖ ^ 2)) :=
        ENNReal.measurable_ofReal.comp ((hF.measurable.comp ((xbar_measurable hgm γ b).comp
          (measurable_const.prodMk measurable_id))).norm.pow_const 2)
      rw [lintegral_add_left hxm, lintegral_const_mul _ hfm] at hstep
      have hres_m : Measurable (fun u : Fin (b + b) → Ω =>
          residualSum μ F g γ b n (xnext g γ b x (extendP ω0 (b + b) u))) := by
        unfold residualSum
        exact Finset.measurable_sum _ fun ι _ => hinner_m ι
      have hrec : ∫⁻ u, ENNReal.ofReal (γ ^ 2 / 11) *
            residualSum μ F g γ b n (xnext g γ b x (extendP ω0 (b + b) u))
            ∂(Measure.pi fun _ : Fin (b + b) => μ) ≤
          ∫⁻ u, ENNReal.ofReal (‖xnext g γ b x (extendP ω0 (b + b) u) - xs‖ ^ 2)
            ∂(Measure.pi fun _ : Fin (b + b) => μ) +
            n * ENNReal.ofReal (52 * γ ^ 2 * (σ ^ 2 / b)) := by
        refine (lintegral_mono fun u => ih _).trans ?_
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      rw [hsum, mul_add, ← lintegral_const_mul _ hres_m]
      calc ∫⁻ u, ENNReal.ofReal (γ ^ 2 / 11) *
              residualSum μ F g γ b n (xnext g γ b x (extendP ω0 (b + b) u))
              ∂(Measure.pi fun _ : Fin (b + b) => μ) +
            ENNReal.ofReal (γ ^ 2 / 11) *
              ∫⁻ ξ, ENNReal.ofReal (‖F (xbar g γ b x ξ)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ)
          ≤ (∫⁻ ξ, ENNReal.ofReal (‖xnext g γ b x ξ - xs‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ) +
              n * ENNReal.ofReal (52 * γ ^ 2 * (σ ^ 2 / b))) +
              ENNReal.ofReal (γ ^ 2 / 11) *
                ∫⁻ ξ, ENNReal.ofReal (‖F (xbar g γ b x ξ)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ) := by
            rw [← hnorm]
            exact add_le_add hrec le_rfl
        _ = (∫⁻ ξ, ENNReal.ofReal (‖xnext g γ b x ξ - xs‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ) +
              ENNReal.ofReal (γ ^ 2 / 11) *
                ∫⁻ ξ, ENNReal.ofReal (‖F (xbar g γ b x ξ)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ)) +
              n * ENNReal.ofReal (52 * γ ^ 2 * (σ ^ 2 / b)) := by ring
        _ ≤ (ENNReal.ofReal (‖x - xs‖ ^ 2) + ENNReal.ofReal (52 * γ ^ 2 * (σ ^ 2 / b))) +
              n * ENNReal.ofReal (52 * γ ^ 2 * (σ ^ 2 / b)) := add_le_add hstep le_rfl
        _ = ENNReal.ofReal (‖x - xs‖ ^ 2) + ((n + 1 : ℕ) : ℝ≥0∞) *
              ENNReal.ofReal (52 * γ ^ 2 * (σ ^ 2 / b)) := by push_cast; ring

end Recursion

section Tuning

open LongTails.Setups.StochasticWeakMinty

noncomputable def stepSize (q : Params) : ℝ := 1 / (2 * q.L)

noncomputable def batch (q : Params) : ℕ := ⌈2048 * q.σ ^ 2 / q.ε ^ 2⌉₊ + 1

noncomputable def iters (q : Params) : ℕ := ⌈128 * q.L ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊

noncomputable def upperBudget (q : Params) : ℕ :=
  ⌈2 ^ 19 * (1 + q.L ^ 2 * q.R ^ 2 / q.ε ^ 2) * (1 + q.σ ^ 2 / q.ε ^ 2)⌉₊

noncomputable def minibatchAlgorithm (q : Params) : Algorithm q.E q.E q.E :=
  algorithm (stepSize q) (batch q) (iters q) q.x0

lemma stopLen_le_budget (q : Params) (hv : spec.valid q) (ι : Fin (iters q + 1)) :
    stopLen (batch q) ι.val ≤ upperBudget q := by
  obtain ⟨hL, -, -, hσ, hR, hε⟩ := hv
  have hx : 0 ≤ q.L ^ 2 * q.R ^ 2 / q.ε ^ 2 := by positivity
  have hy : 0 ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
  have hb : (batch q : ℝ) ≤ 2048 * (q.σ ^ 2 / q.ε ^ 2) + 2 := by
    have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2048 * q.σ ^ 2 / q.ε ^ 2)
    have e : 2048 * q.σ ^ 2 / q.ε ^ 2 = 2048 * (q.σ ^ 2 / q.ε ^ 2) := by ring
    unfold batch
    push_cast
    linarith
  have hK : (iters q : ℝ) ≤ 128 * (q.L ^ 2 * q.R ^ 2 / q.ε ^ 2) + 1 := by
    have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 128 * q.L ^ 2 * q.R ^ 2 / q.ε ^ 2)
    have e : 128 * q.L ^ 2 * q.R ^ 2 / q.ε ^ 2 = 128 * (q.L ^ 2 * q.R ^ 2 / q.ε ^ 2) := by ring
    unfold iters
    linarith
  have hι : (ι.val : ℝ) ≤ iters q := by exact_mod_cast Nat.lt_succ_iff.mp ι.isLt
  have hlen : (stopLen (batch q) ι.val : ℝ) = batch q + 2 * batch q * ι.val := by
    rw [stopLen_eq]; push_cast; ring
  have hbp : (0 : ℝ) ≤ batch q := Nat.cast_nonneg _
  have h1 : (stopLen (batch q) ι.val : ℝ) ≤ (2048 * (q.σ ^ 2 / q.ε ^ 2) + 2) *
      (256 * (q.L ^ 2 * q.R ^ 2 / q.ε ^ 2) + 3) := by
    rw [hlen]
    have : (batch q : ℝ) * (1 + 2 * ι.val) ≤ (2048 * (q.σ ^ 2 / q.ε ^ 2) + 2) *
        (256 * (q.L ^ 2 * q.R ^ 2 / q.ε ^ 2) + 3) := by
      apply mul_le_mul hb (by linarith) (by positivity) (by positivity)
    linarith
  have h2 : (2048 * (q.σ ^ 2 / q.ε ^ 2) + 2) * (256 * (q.L ^ 2 * q.R ^ 2 / q.ε ^ 2) + 3) ≤
      2 ^ 19 * (1 + q.L ^ 2 * q.R ^ 2 / q.ε ^ 2) * (1 + q.σ ^ 2 / q.ε ^ 2) := by
    nlinarith [mul_nonneg hx hy]
  have h3 := Nat.le_ceil (2 ^ 19 * (1 + q.L ^ 2 * q.R ^ 2 / q.ε ^ 2) * (1 + q.σ ^ 2 / q.ε ^ 2))
  have h4 : (stopLen (batch q) ι.val : ℝ) ≤ (upperBudget q : ℝ) := by
    unfold upperBudget
    linarith
  exact_mod_cast h4

end Tuning

section Final

open LongTails.Setups.StochasticWeakMinty

lemma lintegral_uniform_fin (K : ℕ) (f : Fin (K + 1) → ℝ≥0∞) :
    ∫⁻ ι, f ι ∂(PMF.uniformOfFintype (Fin (K + 1))).toMeasure =
      ((K + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ ι, f ι := by
  rw [lintegral_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply,
    Fintype.card_fin, mul_comm]

lemma success (q : Params) (hv : spec.valid q) (F : q.E → q.E)
    (O : Oracle q.E q.E) (had : spec.admissible q F O) :
    spec.successful q F
      (fun w : (minibatchAlgorithm q).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (minibatchAlgorithm q) (fun _ => upperBudget q) w.1 w.2)
      ⟨((minibatchAlgorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hv' := hv
  obtain ⟨hL, -, hρ, hσ, hR, hε⟩ := hv
  obtain ⟨g, μ, P, hIID, rfl, hlip, ⟨xs, hxs0, hxsR, hmin⟩, hgm, hint, hunb, hvi, hvar⟩ := had
  have hg : IsStochasticOperator (μ : Measure q.Ω) F g q.σ := ⟨hgm, hint, hunb, hvi, hvar⟩
  set γ := stepSize q with hγdef
  set b := batch q with hbdef
  set K := iters q with hKdef
  have hγ0 : 0 < γ := by simp only [hγdef, stepSize]; positivity
  have hγ : q.L * γ = 1 / 2 := by simp only [hγdef, stepSize]; field_simp
  have hργ : q.ρ ≤ γ / 10 := by
    simp only [hγdef, stepSize]
    have e : 1 / (2 * q.L) / 10 = 1 / (20 * q.L) := by field_simp; ring
    rw [e]
    exact hρ
  have hb : 0 < b := Nat.succ_pos _
  have hF : Continuous F := (LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le]; exact hlip a b).continuous
  have hexec : ∀ (ι : Fin (K + 1)) (ξ : ℕ → q.Ω),
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω } :
        Oracle q.E q.E) (minibatchAlgorithm q) (fun _ => upperBudget q) ι ξ =
      evalP g (stoppedPlan γ b ι.val q.x0) ξ := by
    intro ι ξ
    exact execute_algorithm P g γ b K q.x0 (upperBudget q) ι ξ (stopLen_le_budget q hv' ι)
  set out : Fin (K + 1) × (ℕ → q.Ω) → q.E := fun z => evalP g (stoppedPlan γ b z.1.val q.x0) z.2
  change Integrable (fun w : Fin (K + 1) × (ℕ → q.Ω) => ‖F (execute
      ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω } : Oracle q.E q.E)
      (minibatchAlgorithm q) (fun _ => upperBudget q) w.1 w.2)‖)
      (((PMF.uniformOfFintype (Fin (K + 1))).toMeasure).prod (P : Measure (ℕ → q.Ω))) ∧
    ∫ w : Fin (K + 1) × (ℕ → q.Ω), ‖F (execute
      ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω } : Oracle q.E q.E)
      (minibatchAlgorithm q) (fun _ => upperBudget q) w.1 w.2)‖
      ∂(((PMF.uniformOfFintype (Fin (K + 1))).toMeasure).prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
  simp_rw [hexec]
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (μ : Measure q.Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
  rw [hP]
  set Q := ((PMF.uniformOfFintype (Fin (K + 1))).toMeasure).prod
    (Measure.infinitePi fun _ : ℕ => (μ : Measure q.Ω))
  have hom : Measurable out := by
    apply measurable_from_prod_countable_right
    intro ι
    exact (stopped_measurable hgm γ b ι.val).comp (measurable_const.prodMk measurable_id)
  have hm : Measurable (fun z => ‖F (out z)‖) := (hF.measurable.comp hom).norm
  have hL2 : ∫⁻ z, ENNReal.ofReal (‖F (out z)‖ ^ 2) ∂Q ≤ ENNReal.ofReal (q.ε ^ 2) := by
    have hm2 : Measurable (fun z => ENNReal.ofReal (‖F (out z)‖ ^ 2)) :=
      ENNReal.measurable_ofReal.comp (hm.pow_const 2)
    rw [lintegral_prod _ hm2.aemeasurable, lintegral_uniform_fin]
    have hsumeq : (∑ ι : Fin (K + 1), ∫⁻ ξ, ENNReal.ofReal (‖F (out (ι, ξ))‖ ^ 2)
        ∂(Measure.infinitePi fun _ : ℕ => (μ : Measure q.Ω))) =
        residualSum (μ : Measure q.Ω) F g γ b (K + 1) q.x0 := by
      unfold residualSum
      rw [Finset.sum_range (fun ι => ∫⁻ ξ, ENNReal.ofReal
        (‖F (evalP g (stoppedPlan γ b ι q.x0) ξ)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => (μ : Measure q.Ω)))]
    rw [hsumeq]
    have hrb := residualSum_bound (μ : Measure q.Ω) hg hγ hγ0 hργ hlip xs hmin hb (K + 1) q.x0
    have hR2 : ‖q.x0 - xs‖ ^ 2 ≤ q.R ^ 2 := by
      rw [norm_sub_rev]
      exact pow_le_pow_left₀ (norm_nonneg _) hxsR 2
    have hc0 : ENNReal.ofReal (γ ^ 2 / 11) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hKx : 128 * q.L ^ 2 * q.R ^ 2 / q.ε ^ 2 ≤ (K : ℝ) + 1 := by
      have := Nat.le_ceil (128 * q.L ^ 2 * q.R ^ 2 / q.ε ^ 2)
      simp only [hKdef, iters]
      linarith
    have hbσ : 2048 * q.σ ^ 2 / q.ε ^ 2 ≤ (b : ℝ) := by
      have := Nat.le_ceil (2048 * q.σ ^ 2 / q.ε ^ 2)
      simp only [hbdef, batch]
      push_cast
      linarith
    have hreal : q.R ^ 2 + ((K : ℝ) + 1) * (52 * γ ^ 2 * (q.σ ^ 2 / b)) ≤
        γ ^ 2 / 11 * (((K : ℝ) + 1) * q.ε ^ 2) := by
      have hγ2 : γ ^ 2 = 1 / (4 * q.L ^ 2) := by simp only [hγdef, stepSize]; field_simp; ring
      have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
      have h1 : q.R ^ 2 ≤ γ ^ 2 / 22 * (((K : ℝ) + 1) * q.ε ^ 2) := by
        rw [hγ2]
        have hε2 : 0 < q.ε ^ 2 := by positivity
        have : 128 * q.L ^ 2 * q.R ^ 2 ≤ ((K : ℝ) + 1) * q.ε ^ 2 := by
          rwa [div_le_iff₀ hε2] at hKx
        rw [show 1 / (4 * q.L ^ 2) / 22 * (((K : ℝ) + 1) * q.ε ^ 2) =
          ((K : ℝ) + 1) * q.ε ^ 2 / (88 * q.L ^ 2) by field_simp; ring]
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg q.R, sq_nonneg q.L]
      have h2 : 52 * γ ^ 2 * (q.σ ^ 2 / b) ≤ γ ^ 2 / 22 * q.ε ^ 2 := by
        have hε2 : 0 < q.ε ^ 2 := by positivity
        have : 2048 * q.σ ^ 2 ≤ b * q.ε ^ 2 := by rwa [div_le_iff₀ hε2] at hbσ
        have h3 : q.σ ^ 2 / b ≤ q.ε ^ 2 / 2048 := by
          rw [div_le_div_iff₀ hbpos (by norm_num)]
          linarith
        have hγp : 0 ≤ γ ^ 2 := sq_nonneg γ
        nlinarith [mul_le_mul_of_nonneg_left h3 hγp]
      have h4 := mul_le_mul_of_nonneg_left h2 hK1.le
      nlinarith
    have hfinal : ENNReal.ofReal (γ ^ 2 / 11) * residualSum (μ : Measure q.Ω) F g γ b (K + 1) q.x0 ≤
        ENNReal.ofReal (γ ^ 2 / 11) * (((K + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (q.ε ^ 2)) := by
      refine hrb.trans ?_
      have hC : ((K + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (52 * γ ^ 2 * (q.σ ^ 2 / b)) =
          ENNReal.ofReal (((K : ℝ) + 1) * (52 * γ ^ 2 * (q.σ ^ 2 / b))) := by
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (K : ℝ) + 1 by positivity),
          show ((K : ℝ) + 1) = ((K + 1 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
      have hR' : ENNReal.ofReal (‖q.x0 - xs‖ ^ 2) ≤ ENNReal.ofReal (q.R ^ 2) :=
        ENNReal.ofReal_le_ofReal hR2
      rw [hC]
      calc ENNReal.ofReal (‖q.x0 - xs‖ ^ 2) + ENNReal.ofReal (((K : ℝ) + 1) *
            (52 * γ ^ 2 * (q.σ ^ 2 / b)))
          ≤ ENNReal.ofReal (q.R ^ 2) + ENNReal.ofReal (((K : ℝ) + 1) *
            (52 * γ ^ 2 * (q.σ ^ 2 / b))) := by gcongr
        _ = ENNReal.ofReal (q.R ^ 2 + ((K : ℝ) + 1) * (52 * γ ^ 2 * (q.σ ^ 2 / b))) :=
            (ENNReal.ofReal_add (sq_nonneg q.R)
              (show (0 : ℝ) ≤ ((K : ℝ) + 1) * (52 * γ ^ 2 * (q.σ ^ 2 / b)) by positivity)).symm
        _ ≤ ENNReal.ofReal (γ ^ 2 / 11 * (((K : ℝ) + 1) * q.ε ^ 2)) := ENNReal.ofReal_le_ofReal hreal
        _ = _ := by
            rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ γ ^ 2 / 11 by positivity),
              ENNReal.ofReal_mul (show (0 : ℝ) ≤ (K : ℝ) + 1 by positivity),
              show ((K : ℝ) + 1) = ((K + 1 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    have hW := (ENNReal.mul_le_mul_iff_right hc0 ENNReal.ofReal_ne_top).mp hfinal
    have hKne : ((K + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero K
    calc ((K + 1 : ℕ) : ℝ≥0∞)⁻¹ * residualSum (μ : Measure q.Ω) F g γ b (K + 1) q.x0
        ≤ ((K + 1 : ℕ) : ℝ≥0∞)⁻¹ * (((K + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (q.ε ^ 2)) := by gcongr
      _ = ENNReal.ofReal (q.ε ^ 2) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hKne (ENNReal.natCast_ne_top _), one_mul]
  have hQ1 : Q Set.univ ≤ 1 := by simp [Q]
  have hL1 := OracleTemplate.StochasticCohypomonotone.enn_l1_of_l2 Q (fun z => ‖F (out z)‖) hm
    (sq_nonneg q.ε) (by simpa using hL2) hQ1
  rw [Real.sqrt_sq hε.le] at hL1
  have hfin : ∫⁻ z, ENNReal.ofReal ‖F (out z)‖ ∂Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL1
  refine ⟨?_, ?_⟩
  · have := integrable_toReal_of_lintegral_ne_top (ENNReal.measurable_ofReal.comp hm).aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (norm_nonneg _)] using this
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hL1

end Final

end LongTails.Proofs.MinibatchExtragradientRun

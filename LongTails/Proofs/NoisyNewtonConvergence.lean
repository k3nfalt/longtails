import LongTails.Proofs.NoisyNewtonCost

namespace LongTails.Proofs.NoisyNewtonConvergence

open LongTails.Setups.StochasticLocalHessianConvex
open LongTails.Algorithms.NoisyDampedNewton
open LongTails.Proofs.NoisyNewtonProcess
open LongTails.Proofs.NoisyNewtonCounting
open LongTails.Proofs.NoisyNewtonTuning
open OracleTemplate.GeneralizedAccelerated (Iterate)
open OracleTemplate.StochasticGeneralized (blockTrace blockTrace_succ)

noncomputable def DoneValid (p : Params) (s : State (Point p.d)) : Prop :=
  ∀ it, s = .done it → (it = initialIterate p ∧ p.Δ ≤ p.ε) ∨ target p / 2 ≤ it.A

lemma phaseNext_doneValid (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : State (Point p.d)) (ξ : Fin n → p.Ω) (hs : DoneValid p s) :
    DoneValid p (phaseNext p g H n s ξ) := by
  cases s with
  | model it k v => intro it' he; cases he
  | hessian it v => intro it' he; cases he
  | done it => exact hs
  | correction t k v =>
    intro it he
    change resume p (finish (curvatureFloor p) t
      (updateEstimate p t (sampleReplies p n g (trialPoint t) ξ))) = .done it at he
    unfold resume at he
    split_ifs at he with h
    · cases he
      exact Or.inr h

lemma ghostNext_doneValid (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) (hs : DoneValid p s.1) :
    DoneValid p (ghostNext p f u grad g H n s ξ).1 := by
  classical
  by_cases hstop : stopped p s
  · rw [ghostNext_of_stopped p f u grad g H n s ξ hstop]
    exact hs
  · rw [ghostNext_state p f u grad g H n s ξ hstop]
    exact phaseNext_doneValid p g H n s.1 ξ hs

lemma initial_doneValid (p : Params) (hp : spec.valid p) : DoneValid p (initialGhost p).1 := by
  classical
  intro it he
  by_cases hΔ : p.Δ ≤ p.ε
  · have hi : (initialGhost p).1 = .done (initialIterate p) := by
      change (if p.Δ ≤ p.ε then .done (initialIterate p) else resume p (initialIterate p)) = _
      exact ite_eq_left hΔ
    rw [hi] at he
    cases he
    exact Or.inl ⟨rfl, hΔ⟩
  · rw [initial_model p hp hΔ] at he
    cases he

lemma initialTrace_doneValid (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (u : Point p.d) (grad : Point p.d → Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (ξ : ℕ → p.Ω) (n : ℕ) :
    DoneValid p (blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ n).1.1 := by
  induction n with
  | zero => exact initial_doneValid p hp
  | succ n ih =>
    rw [blockTrace_succ]
    exact ghostNext_doneValid p f u grad g H _ _ _ ih

lemma done_accuracy (p : Params) (hp : spec.valid p) (f : Point p.d → ℝ) (u : Point p.d)
    (s : State (Point p.d)) (it : Iterate (Point p.d)) (hd : s = .done it)
    (hv : DoneValid p s) (he : stateEnergy p f u s ≤ 4 * p.R ^ 2)
    (hgap : f p.x0 - f u ≤ p.Δ) : f it.x - f u ≤ p.ε := by
  rcases hv it hd with ⟨rfl, hΔ⟩ | hcap
  · exact hgap.trans hΔ
  · have hW := target_pos p hp
    have hA : 0 < it.A := by linarith
    have hR := hp.2.2.2.2.2.1
    have hε := hp.2.2.2.2.2.2.2.1
    rw [hd] at he
    change it.A * (f it.x - f u) + ‖it.z - u‖ ^ 2 / 2 ≤ 4 * p.R ^ 2 at he
    have hscale : target p / 2 * p.ε = 16 * p.R ^ 2 := by unfold target; field_simp; ring
    have hm := mul_le_mul_of_nonneg_right hcap hε.le
    rw [hscale] at hm
    by_contra hh
    have hh' := mul_lt_mul_of_pos_left (lt_of_not_ge hh) hA
    nlinarith only [hm, he, hh', sq_nonneg ‖it.z - u‖, sq_pos_of_pos hR]

lemma phase_horizon_exp_bound (p : Params) (hp : spec.valid p) :
    (3 * horizon p : ℝ) ≤ Real.exp (3 * confidence p) := by
  have hl := confidence_lower p hp
  have hl0 : 0 < confidence p := by linarith
  have hX := (scaleBase_bounds p hp).1
  have hX0 : 0 < scaleBase p := by linarith
  have hs := shape_le_scaleBase p hp
  have hN := LongTails.Proofs.NoisyNewtonCost.horizon_upper p hp
  have hs' := mul_le_mul_of_nonneg_right hs (sq_nonneg (confidence p))
  have hx := mul_nonneg hX0.le (sq_nonneg (confidence p))
  have hb : (3 * horizon p : ℝ) ≤ (2 : ℝ) ^ 35 * scaleBase p * confidence p ^ 2 := by
    nlinarith only [hN, hs', hx]
  have hlogℓ := Real.log_le_sub_one_of_pos hl0
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have he : confidence p = 100 * Real.log (scaleBase p) := rfl
  have hb0 : 0 < (2 : ℝ) ^ 35 * scaleBase p * confidence p ^ 2 := by positivity
  have hlog : Real.log ((2 : ℝ) ^ 35 * scaleBase p * confidence p ^ 2) ≤ 3 * confidence p := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hX0.ne',
      Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  calc
    _ ≤ (2 : ℝ) ^ 35 * scaleBase p * confidence p ^ 2 := hb
    _ = Real.exp (Real.log ((2 : ℝ) ^ 35 * scaleBase p * confidence p ^ 2)) := (Real.exp_log hb0).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

lemma modelGroups_exp_bound (p : Params) (hp : spec.valid p) :
    (1 / 2 : ℝ) ^ modelGroups p ≤ Real.exp (-8 * confidence p) := by
  have hl := confidence_lower p hp
  have hg : 16 * confidence p ≤ (modelGroups p : ℝ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (le_max_right 1 ⌈16 * confidence p⌉₊)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have he : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (modelGroups p))
  calc
    _ = Real.exp ((modelGroups p : ℝ) * (-Real.log 2)) := by rw [Real.exp_nat_mul, he]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hm, hg])

lemma model_tail_probability_bound (p : Params) (hp : spec.valid p) :
    (3 * horizon p : ℝ) * (1 / 2 : ℝ) ^ modelGroups p ≤ p.β / 4 := by
  have hN := phase_horizon_exp_bound p hp
  have hg := modelGroups_exp_bound p hp
  have hl := confidence_lower p hp
  have hb := confidence_log_inv_beta p hp
  have hβ := hp.2.2.2.2.2.2.2.2.1
  have hlog4 : Real.log 4 ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have he : Real.log (p.β / 4) = -Real.log (1 / p.β) - Real.log 4 := by
    rw [Real.log_div hβ.ne' (by norm_num), Real.log_div (by norm_num) hβ.ne', Real.log_one]
    ring
  calc
    _ ≤ Real.exp (3 * confidence p) * Real.exp (-8 * confidence p) :=
      mul_le_mul hN hg (by positivity) (by positivity)
    _ = Real.exp (-5 * confidence p) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (Real.log (p.β / 4)) := Real.exp_le_exp.mpr (by rw [he]; linarith)
    _ = _ := Real.exp_log (by positivity)

open MeasureTheory
open LongTails.Proofs.NoisyNewtonConcentration
open OracleTemplate.StochasticGeneralized (accumulated)

noncomputable def badEvent (p : Params) (f : Point p.d → ℝ) (grad : Point p.d → Point p.d)
    (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) : Set (ℕ → p.Ω) :=
  {ξ | (blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ
      (3 * horizon p)).1.2.2.1 = true ∨
    2 * p.R ^ 2 < accumulated (ghostCost p) (ghostNext p f u grad g H)
      (ghostNoise p grad u g) (3 * horizon p) (initialGhost p) ξ}

lemma badEvent_probability (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d) (u : Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (P : Measure p.Ω) [IsProbabilityMeasure P]
    (hf : Measurable f) (hgrad : Measurable grad) (hH : Measurable H)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hg2i : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - grad x‖ ^ 2 ∂P) ≤ p.σ ^ 2) :
    (Measure.infinitePi fun _ : ℕ => P) (badEvent p f grad u g H) ≤ ENNReal.ofReal p.β := by
  have hβ := hp.2.2.2.2.2.2.2.2.1
  have hm := modelFailure_probability p hp f grad u g H P hf hgrad hH hg hgi hmean hg2i hvar
    (3 * horizon p) (initialGhost p) (initial_bounds p hp) rfl
  have hn := ghostNoise_tail p hp f grad u g H P hf hgrad hH hg hgi hmean hg2i hvar
    (3 * horizon p) (initialGhost p) (initial_bounds p hp)
  have hm' : ((3 * horizon p : ℕ) : ℝ) * (1 / 2 : ℝ) ^ modelGroups p ≤ p.β / 4 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using model_tail_probability_bound p hp
  have he : ENNReal.ofReal (p.β / 4) + ENNReal.ofReal (p.β / 4) = ENNReal.ofReal (p.β / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hhalf : ENNReal.ofReal (p.β / 2) ≤ ENNReal.ofReal p.β :=
    ENNReal.ofReal_le_ofReal (by linarith)
  exact (measure_union_le _ _).trans
    ((add_le_add (hm.trans (ENNReal.ofReal_le_ofReal hm'))
      (hn.trans (ENNReal.ofReal_le_ofReal (noise_tail_probability_bound p hp)))).trans
      (he.le.trans hhalf))

open scoped RealInnerProductSpace
open LongTails.Proofs.NoisyNewtonDescent

lemma goodTrace_done_accuracy (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d)
    (A H : Point p.d → Point p.d →L[ℝ] Point p.d) (u : Point p.d)
    (hc : ConvexOn ℝ Set.univ f) (hgrad : ∀ x, HasGradientAt f (grad x) x)
    (hderiv : ∀ x, HasFDerivAt grad (A x) x)
    (hA : ∀ x v, 0 ≤ ⟪A x v, v⟫) (hmin : ∀ x, f u ≤ f x)
    (hLip : ∀ x y, ‖y - x‖ ≤ p.ρ →
      ‖A y - A x‖ ≤ (p.M₀ + p.M₁ * ‖grad x‖) * ‖y - x‖)
    (hH : ∀ x, ‖H x - A x‖ ≤ p.δ)
    (hdist : ‖p.x0 - u‖ ≤ p.R) (hgap : f p.x0 - f u ≤ p.Δ)
    (g : Point p.d → p.Ω → Point p.d) (ξ : ℕ → p.Ω)
    (hgood : ξ ∉ badEvent p f grad u g H) :
    let T := blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ (3 * horizon p)
    ∃ it, T.1.1 = .done it ∧ f it.x - f u ≤ p.ε ∧ ¬ stopped p T.1 := by
  have hh := not_or.mp hgood
  have hm : (blockTrace (ghostCost p) (ghostNext p f u grad g H)
      (initialGhost p) ξ (3 * horizon p)).1.2.2.1 = false := by
    simpa using hh.1
  have he := initialTrace_energy_bound p hp f grad A H u hc hgrad hderiv hA hmin hLip hH
    hdist hgap g ξ (3 * horizon p) (le_of_not_gt hh.2)
  have hcons := energy_bound_consequences p hp f grad u g H hmin ξ (3 * horizon p) he
  have hlive : ¬ stopped p (blockTrace (ghostCost p) (ghostNext p f u grad g H)
      (initialGhost p) ξ (3 * horizon p)).1 := by
    simp only [stopped, hm, hcons.1, Bool.false_eq_true, or_self, not_false_eq_true]
  have hshift : ∀ x w, 0 ≤ inner ℝ (shifted (H x) p.δ w) w := fun x w =>
    LongTails.Proofs.NoisyNewtonModel.shifted_nonnegative (A x) (H x) (hA x) p.δ (hH x) w
  obtain ⟨it, hd⟩ := initialTrace_done p hp f u grad g H hshift ξ hlive hcons.2.1
  exact ⟨it, hd, done_accuracy p hp f u _ it hd
    (initialTrace_doneValid p hp f u grad g H ξ (3 * horizon p)) hcons.2.2 hgap, hlive⟩

open LongTails.Proofs.NoisyNewtonCost
open LongTails.Proofs.NoisyNewtonExecution
open OracleTemplate.StochasticGeneralized (blockCalls)

lemma good_execute_accuracy (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d)
    (A H : Point p.d → Point p.d →L[ℝ] Point p.d) (u : Point p.d)
    (hc : ConvexOn ℝ Set.univ f) (hgrad : ∀ x, HasGradientAt f (grad x) x)
    (hderiv : ∀ x, HasFDerivAt grad (A x) x)
    (hA : ∀ x v, 0 ≤ ⟪A x v, v⟫) (hmin : ∀ x, f u ≤ f x)
    (hLip : ∀ x y, ‖y - x‖ ≤ p.ρ →
      ‖A y - A x‖ ≤ (p.M₀ + p.M₁ * ‖grad x‖) * ‖y - x‖)
    (hH : ∀ x, ‖H x - A x‖ ≤ p.δ)
    (hdist : ‖p.x0 - u‖ ≤ p.R) (hgap : f p.x0 - f u ≤ p.Δ)
    (g : Point p.d → p.Ω → Point p.d) (P : ProbabilityMeasure (ℕ → p.Ω))
    (budget : Fin 2 → ℕ)
    (hbudget : ∀ ch, 1208925819614629174706176 *
      (shape p + if ch = 0 then p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 else 0) *
      Real.log (scaleBase p) ^ 3 ≤ (budget ch : ℝ))
    (ξ : ℕ → p.Ω) (hgood : ξ ∉ badEvent p f grad u g H) :
    let O : OracleTemplate.Oracle (Point p.d) (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)) 2 :=
      { Seed := fun _ => p.Ω, law := P,
        answer := fun _ q ω => if q.1 = 0 then .inl (g q.2 ω) else .inr (H q.2) }
    f (output p budget O ξ) - f u ≤ p.ε := by
  intro O
  obtain ⟨it, hd, hacc, hlive⟩ := goodTrace_done_accuracy p hp f grad A H u hc hgrad hderiv
    hA hmin hLip hH hdist hgap g ξ hgood
  let s := (initialGhost p).1
  let S := fun i => (blockTrace (phaseCost p) (phaseNext p g H) s ξ i).1
  have hcouple : ∀ i ≤ 3 * horizon p,
      (blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ i).1.1 = S i := by
    intro i hi
    exact (ghostTrace_coupling p f u grad g H (initialGhost p) ξ i
      (ghostTrace_prefix_live p f u grad g H (initialGhost p) ξ (3 * horizon p) i hi hlive)).1
  have hstep : ∀ i < 3 * horizon p, PhaseStep p g H (S i) (S (i + 1)) := by
    intro i hi
    dsimp only [S]
    rw [blockTrace_succ]
    exact ⟨_, rfl⟩
  have h₀ : (∃ it, S 0 = .model it 0 (fun _ => 0)) ∨ ∃ it, S 0 = .done it := by
    by_cases hΔ : p.Δ ≤ p.ε
    · right
      refine ⟨initialIterate p, ?_⟩
      change (if p.Δ ≤ p.ε then .done (initialIterate p) else resume p (initialIterate p)) = _
      exact ite_eq_left hΔ
    · exact Or.inl ⟨initialIterate p, initial_model p hp hΔ⟩
  have hinit : cycleIterate S 0 = initialIterate p := initial_baseIterate p
  have hb : ∀ i ≤ 3 * horizon p, StateBounds p (S i) := by
    intro i hi
    rw [← hcouple i hi]
    exact ghostTrace_bounds p hp f u grad g H (initialGhost p) ξ i (initial_bounds p hp)
  let calls := blockCalls (phaseCost p) (phaseNext p g H) s ξ (3 * horizon p)
  have hcounts : ∀ ch, oracleCount p (fun n => rawAdvance p g H ξ n 0 s) ch calls ≤ budget ch := by
    intro ch
    have hh := (phase_oracle_rate p hp g H S hstep h₀ hinit hb ch).trans
      ((oracle_rate_log_bound p hp ch).trans (hbudget ch))
    have he := blockTrace_oracleCount p g H ξ s (initial_phaseStart p) (3 * horizon p) ch
    change oracleCount p (fun n => rawAdvance p g H ξ n 0 s) ch calls = _ at he
    rw [he]
    exact_mod_cast hh
  have hraw : rawAdvance p g H ξ calls 0 s = .done it := by
    rw [← blockTrace_eq_rawAdvance p g H ξ s (initial_phaseStart p) (3 * horizon p)]
    exact (hcouple (3 * horizon p) le_rfl).symm.trans hd
  have hex := execute_of_done p g H P ξ budget calls it hraw hcounts
  change OracleTemplate.execute O (algorithm p) budget () ξ = it.x at hex
  change f (OracleTemplate.execute O (algorithm p) budget () ξ) - f u ≤ p.ε
  rw [hex]
  exact hacc

lemma admissible_success (p : Params) (hp : spec.valid p) (I : Instance p)
    (O : OracleTemplate.Oracle (Point p.d) (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)) 2)
    (ha : spec.admissible p I O) (budget : Fin 2 → ℕ)
    (hbudget : ∀ ch, 1208925819614629174706176 *
      (shape p + if ch = 0 then p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 else 0) *
      Real.log (scaleBase p) ^ 3 ≤ (budget ch : ℝ)) :
    spec.successful p I
      (fun seed : (algorithm p).Seed × ((k : ℕ) → O.Seed k) =>
        OracleTemplate.execute O (algorithm p) budget seed.1 seed.2)
      ⟨((algorithm p).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  rcases ha with ⟨hf, hc, hmin, hdist, hgap, hLip, g, H, p0, P, hIID, rfl,
    hg, hHmeas, hgi, hmean, hg2i, hvar, hH⟩
  let O : OracleTemplate.Oracle (Point p.d) (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)) 2 :=
    { Seed := fun _ => p.Ω, law := P,
      answer := fun _ q ω => if q.1 = 0 then .inl (g q.2 ω) else .inr (H q.2) }
  have hgrad := OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one hf
  have hgAt : ∀ x, HasGradientAt I.f (gradient I.f x) x :=
    fun x => (hf.differentiable (by norm_num) x).hasGradientAt
  have hderiv : ∀ x, HasFDerivAt (gradient I.f) (fderiv ℝ (gradient I.f) x) x :=
    fun x => (hgrad.differentiable (by norm_num) x).hasFDerivAt
  have hA := (LongTails.Proofs.NoisyNewtonModel.convex_hessian_facts hf hc).2
  have hminimum : ∀ x, I.f I.xstar ≤ I.f x := fun x => hmin (Set.mem_univ x)
  have hlaw : (P : Measure (ℕ → p.Ω)) = Measure.infinitePi (fun _ : ℕ => (p0 : Measure p.Ω)) := by
    have hh := hIID.stream_law.map_eq
    change Measure.map id (P : Measure (ℕ → p.Ω)) = _ at hh
    simpa only [Measure.map_id] using hh
  have hm := LongTails.Proofs.NoisyNewtonMeasurability.measurable_execute_output
    p g H hg hHmeas P budget
  have hprob : (P : Measure _) {ξ | p.ε < I.f (output p budget O ξ) - I.f I.xstar} ≤
      ENNReal.ofReal p.β := by
    have hbad := badEvent_probability p hp I.f (gradient I.f) I.xstar g H
      (p0 : Measure _) hf.continuous.measurable hgrad.continuous.measurable hHmeas hg hgi hmean hg2i hvar
    rw [← hlaw] at hbad
    apply (measure_mono ?_).trans hbad
    intro ξ hξ
    by_contra hn
    exact (not_lt_of_ge (good_execute_accuracy p hp I.f (gradient I.f)
      (fderiv ℝ (gradient I.f)) H I.xstar hc hgAt hderiv hA hminimum hLip hH
      hdist hgap g P budget hbudget ξ hn)) hξ
  change Measurable (fun seed : Unit × (ℕ → p.Ω) =>
      OracleTemplate.execute O (algorithm p) budget seed.1 seed.2) ∧
    ((Measure.dirac ()).prod (P : Measure _)) {seed : Unit × (ℕ → p.Ω) |
      p.ε < I.f (OracleTemplate.execute O (algorithm p) budget seed.1 seed.2) - I.f I.xstar} ≤ _
  have he (seed : Unit × (ℕ → p.Ω)) :
      OracleTemplate.execute O (algorithm p) budget seed.1 seed.2 = output p budget O seed.2 := by
    rcases seed with ⟨⟨⟩, ξ⟩
    rfl
  simp_rw [he]
  refine ⟨hm.comp measurable_snd, ?_⟩
  have hs : MeasurableSet {ξ | p.ε < I.f (output p budget O ξ) - I.f I.xstar} :=
    measurableSet_lt measurable_const ((hf.continuous.measurable.comp hm).sub measurable_const)
  have hmp := measurePreserving_snd (μ := Measure.dirac ()) (ν := (P : Measure (ℕ → p.Ω)))
  rw [← hmp.measure_preimage hs.nullMeasurableSet] at hprob
  exact hprob

end LongTails.Proofs.NoisyNewtonConvergence

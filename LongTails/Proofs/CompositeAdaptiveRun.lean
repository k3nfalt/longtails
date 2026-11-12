import LongTails.Proofs.CompositeAdaptiveExecution
import LongTails.Proofs.CompositeAdaptiveCounting

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeAdaptive

open LongTails.Setups.RadiusCompositeGeneralizedSmooth
open LongTails.Algorithms.RadiusCompositeAccelerated
open OracleTemplate.CompositeGeneralized

structure Conditions (q : Params) (I : Instance q.toPublic) (xs : q.E) : Prop extends
    Hyp I.f I.ψ I.grad I.Q I.prox q.L0 q.L1 where
  radiusPositive : 0 < q.R
  accuracyPositive : 0 < q.ε
  start_mem : q.x0 ∈ I.Q
  solution_mem : xs ∈ I.Q
  minimizer : IsMinOn (objective I) I.Q xs
  initial_radius : ‖q.x0 - xs‖ ≤ q.R
  gradient_bound : ‖I.grad xs‖ ≤ q.G

lemma conditions_of_admissible (q : Params) (I : Instance q.toPublic)
    (O : Oracle (Query q.toPublic) q.E) (hq : spec.valid q) (hI : spec.admissible q I O) :
    ∃ xs : q.E, Conditions q I xs := by
  obtain ⟨hL0, hL1, hR, hε, _⟩ := hq
  obtain ⟨_, _, hc, hf, hg, hs, hQ, hψ, hp, hx0, xs, hxs, hmin, hr, hG⟩ := hI
  exact ⟨xs, ⟨⟨hL0, hL1, hc, hf, hg, hs, hQ, hψ, hp⟩, hR, hε, hx0, hxs, hmin, hr, hG⟩⟩

lemma admissible_answers (q : Params) (I : Instance q.toPublic)
    (O : Oracle (Query q.toPublic) q.E) (hI : spec.admissible q I O) :
    ∀ history query seed, O.answer history (0, query) seed = answerOf q.toPublic I query := by
  intro history query seed
  cases query with
  | gradient x => exact hI.1 history seed x
  | prox a z v => exact hI.2.1 history seed a z v

noncomputable def energy {p : Public} (I : Instance p) (xs : p.E) (s : Iterate p.E) : ℝ :=
  s.weight * (objective I s.point - objective I xs) + ‖s.momentum - xs‖ ^ 2 / 2

structure ValidIterate (q : Params) (I : Instance q.toPublic) (xs : q.E)
    (s : Iterate q.E) : Prop where
  weightPositive : 0 < s.weight
  point_mem : s.point ∈ I.Q
  momentum_mem : s.momentum ∈ I.Q
  point_radius : ‖s.point - xs‖ ≤ 4 * q.R
  energy_bound : energy I xs s ≤ 3 * q.R ^ 2

lemma objective_gap_nonneg {q : Params} {I : Instance q.toPublic} {xs : q.E}
    (h : Conditions q I xs) {x : q.E} (hx : x ∈ I.Q) :
    0 ≤ objective I x - objective I xs := sub_nonneg.mpr (h.minimizer hx)

lemma valid_momentum_radius {q : Params} {I : Instance q.toPublic} {xs : q.E}
    (h : Conditions q I xs) {s : Iterate q.E} (hv : ValidIterate q I xs s) :
    ‖s.momentum - xs‖ ≤ 4 * q.R := by
  have hg := objective_gap_nonneg h hv.point_mem
  have hm := mul_nonneg hv.weightPositive.le hg
  have he := hv.energy_bound
  dsimp only [energy] at he
  have hR := h.radiusPositive
  nlinarith [norm_nonneg (s.momentum - xs)]

lemma initial_valid {q : Params} {I : Instance q.toPublic} {xs : q.E}
    (h : Conditions q I xs) :
    let a := initialStep q.toPublic (I.grad q.x0)
    let A := initialWeight q.toPublic (I.grad q.x0)
    let u := I.prox a q.x0 (I.grad q.x0)
    ValidIterate q I xs ⟨A, u, u⟩ := by
  intro a A u
  have hL0 := h.hL0
  have hL1 := h.hL1
  have hR := h.radiusPositive
  have hS : 0 < q.L0 + q.L1 * ‖I.grad q.x0‖ := by positivity
  have ha : 0 < a := by dsimp [a, initialStep]; positivity
  have hA : 0 < A := by dsimp [A, initialWeight]; positivity
  have hp := h.proxSpec a ha q.x0 (I.grad q.x0)
  have hu : ‖u - xs‖ ≤ 2 * q.R := initial_prox_radius hL0 hL1 hR.le h.convex h.grad
    h.cont h.smooth h.setConvex h.regConvex h.solution_mem h.minimizer h.initial_radius hp.1 hp.2
  have hgap := initial_gap_certificate hL0 hL1 hR.le h.grad h.cont h.smooth
    h.solution_mem h.initial_radius hu hp.2
  have hgap' : objective I u - objective I xs ≤
      5 * (q.L0 + q.L1 * ‖I.grad q.x0‖) * q.R ^ 2 * Real.exp (3 * (q.L1 * q.R)) := by
    simpa only [objective, mul_assoc] using hgap
  have he := initial_energy_certificate hS (mul_nonneg hL1 hR.le) hR.le
    (norm_nonneg (u - xs)) hu hgap'
  refine ⟨hA, hp.1, hp.1, by dsimp; linarith, ?_⟩
  change A * (objective I u - objective I xs) + ‖u - xs‖ ^ 2 / 2 ≤ 3 * q.R ^ 2
  simpa only [A, initialWeight, mul_assoc] using he

lemma accepted_valid {q : Params} {I : Instance q.toPublic} {xs : q.E}
    (h : Conditions q I xs) {s : Iterate q.E} (hv : ValidIterate q I xs s)
    {a : ℝ} (ha : 0 < a) (haccept : accepts q.toPublic s (evaluatedTrial q.toPublic I s a)) :
    let t := evaluatedTrial q.toPublic I s a
    let next : Iterate q.E := ⟨s.weight + a, mix s.weight a s.point t.proximalPoint, t.proximalPoint⟩
    ValidIterate q I xs next ∧
      energy I xs next + ‖t.proximalPoint - s.momentum‖ ^ 2 / 4 +
        a * (I.f xs - I.f (mix s.weight a s.point s.momentum) -
          ⟪t.gradient, xs - mix s.weight a s.point s.momentum⟫) ≤ energy I xs s := by
  intro t next
  have hA := hv.weightPositive
  have hsum : 0 < s.weight + a := by positivity
  have hp := h.proxSpec a ha s.momentum t.gradient
  obtain ⟨hc, hd⟩ := haccept
  change a ^ 2 * (q.L0 + q.L1 * ‖I.grad (mixPoint s.weight a s.point s.momentum)‖) /
    (s.weight + a) ≤ 1 / 32 at hc
  have hcurv : 4 * (q.L0 + q.L1 * ‖I.grad (mixPoint s.weight a s.point s.momentum)‖) *
      a ^ 2 ≤ s.weight + a := by
    have hh := (div_le_iff₀ hsum).mp hc
    nlinarith
  have hdesc : q.L1 * ‖mixPoint s.weight a s.point t.proximalPoint -
      mixPoint s.weight a s.point s.momentum‖ ≤ 1 / 2 := by
    rw [mix_sub_mix, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ha hsum)]
    change q.L1 * (a / (s.weight + a)) * ‖t.proximalPoint - s.momentum‖ ≤ 1 / 32 at hd
    nlinarith
  have he := accepted_energy_surplus h.toHyp hA ha hv.point_mem h.solution_mem hcurv hdesc
  change energy I xs next + ‖t.proximalPoint - s.momentum‖ ^ 2 / 4 +
    a * (I.f xs - I.f (mix s.weight a s.point s.momentum) -
      ⟪t.gradient, xs - mix s.weight a s.point s.momentum⟫) ≤ energy I xs s at he
  have hsurplus : 0 ≤ I.f xs - I.f (mix s.weight a s.point s.momentum) -
      ⟪t.gradient, xs - mix s.weight a s.point s.momentum⟫ := by
    dsimp only [t, evaluatedTrial]
    linarith [Gradient.convex_support h.convex h.grad (mix s.weight a s.point s.momentum) xs]
  have hpayment := mul_nonneg ha.le hsurplus
  have heNext : energy I xs next ≤ 3 * q.R ^ 2 := by
    nlinarith [hv.energy_bound, sq_nonneg ‖t.proximalPoint - s.momentum‖]
  have hpoint : next.point ∈ I.Q := mix_mem h.setConvex hA.le ha.le hsum hv.point_mem hp.1
  have hgap := objective_gap_nonneg h hpoint
  have hgapWeight := mul_nonneg hsum.le hgap
  have hmomentum : ‖t.proximalPoint - xs‖ ≤ 4 * q.R := by
    have hR := h.radiusPositive
    dsimp only [energy, next] at heNext hgapWeight
    nlinarith [norm_nonneg (t.proximalPoint - xs)]
  refine ⟨⟨hsum, hpoint, hp.1, ?_, heNext⟩, he⟩
  exact mix_dist hA.le ha.le hsum s.point t.proximalPoint xs hv.point_radius hmomentum

lemma resolved_boundary {q : Params} {I : Instance q.toPublic} {xs : q.E}
    (h : Conditions q I xs) {s : Iterate q.E} (hv : ValidIterate q I xs s)
    {t : Trial q.E} (hr : ResolvedTrial q.toPublic I s t) :
    t.weight = s.weight ∨
      1 / 64 ≤ t.weight ^ 2 * (q.L0 + q.L1 * ‖t.gradient‖) / (s.weight + t.weight) ∨
      1 / 64 ≤ q.L1 * (t.weight / (s.weight + t.weight)) * ‖t.proximalPoint - s.momentum‖ := by
  obtain ⟨hcanon, _, ht, htA, hcase⟩ := hr
  rcases hcase with hcap | ⟨b, htb, hbA, hunsafe, hratio⟩
  · exact Or.inl hcap
  by_cases hc : 1 / 64 ≤ t.weight ^ 2 * (q.L0 + q.L1 * ‖t.gradient‖) / (s.weight + t.weight)
  · exact Or.inr (Or.inl hc)
  by_cases hd : 1 / 64 ≤ q.L1 * (t.weight / (s.weight + t.weight)) * ‖t.proximalPoint - s.momentum‖
  · exact Or.inr (Or.inr hd)
  exfalso
  have hC := (lt_of_not_ge hc).le
  have hD := (lt_of_not_ge hd).le
  have hge : t.gradient = I.grad (mix s.weight t.weight s.point s.momentum) :=
    congrArg Trial.gradient hcanon
  have hpe : t.proximalPoint = I.prox t.weight s.momentum
      (I.grad (mix s.weight t.weight s.point s.momentum)) := congrArg Trial.proximalPoint hcanon
  rw [hge] at hC
  rw [hpe] at hD
  have hL1 := h.hL1
  have hR := h.radiusPositive
  let δ := 1 / (1000 * (1 + 4 * q.L1 * q.R))
  have hden : 0 < 1000 * (1 + 4 * q.L1 * q.R) := by positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ 1 / 10 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10)
    nlinarith [mul_nonneg hL1 hR.le]
  have hlocal : q.L1 * (4 * q.R) * δ ≤ 1 / 4 := by
    change q.L1 * (4 * q.R) * (1 / (1000 * (1 + 4 * q.L1 * q.R))) ≤ 1 / 4
    rw [mul_one_div, div_le_iff₀ hden]
    nlinarith [mul_nonneg hL1 hR.le]
  have hb : 0 < b := ht.trans_le htb
  have hp := h.proxSpec t.weight ht s.momentum (I.grad (mix s.weight t.weight s.point s.momentum))
  have hq := h.proxSpec b hb s.momentum (I.grad (mix s.weight b s.point s.momentum))
  have hsafe := nearby_trial_safe h.hL0.le hL1 h.cont h.smooth h.setConvex h.regConvex
    hv.weightPositive ht htA htb hδ hδsmall hratio hlocal hv.point_radius
    (valid_momentum_radius h hv) hp.1 hq.1 hp.2 hq.2 hC (by simpa only [mul_assoc] using hD)
  apply hunsafe
  simpa only [accepts, evaluatedTrial, mixPoint, mix, mul_assoc] using hsafe

lemma mix_same {p : Public} {A a : ℝ} (h : 0 < A + a) (x : p.E) :
    mix A a x x = x := by
  unfold mix
  rw [← add_smul, show A / (A + a) + a / (A + a) = 1 by field_simp, one_smul]

lemma initial_ready {q : Params} {I : Instance q.toPublic} {xs : q.E}
    (h : Conditions q I xs) :
    let a := initialStep q.toPublic (I.grad q.x0)
    let A := initialWeight q.toPublic (I.grad q.x0)
    let u := I.prox a q.x0 (I.grad q.x0)
    let s : Iterate q.E := ⟨A, u, u⟩
    ValidIterate q I xs s ∧ 0 < A / 16 ∧ A / 16 ≤ A ∧
      accepts q.toPublic s (evaluatedTrial q.toPublic I s (A / 16)) := by
  intro a A u s
  have hv := initial_valid h
  change ValidIterate q I xs s at hv
  have hL0 := h.hL0
  have hL1 := h.hL1
  have hR := h.radiusPositive
  have hA : 0 < A := hv.weightPositive
  have ha : 0 < a := by dsimp [a, initialStep]; positivity
  have hp := h.proxSpec a ha q.x0 (I.grad q.x0)
  have hu : ‖u - xs‖ ≤ 2 * q.R := initial_prox_radius hL0 hL1 hR.le h.convex h.grad
    h.cont h.smooth h.setConvex h.regConvex h.solution_mem h.minimizer h.initial_radius hp.1 hp.2
  have hd : ‖u - q.x0‖ ≤ 3 * q.R := by
    have hh := norm_sub_le (u - xs) (q.x0 - xs)
    rw [show (u - xs) - (q.x0 - xs) = u - q.x0 by abel] at hh
    linarith [h.initial_radius]
  have hb : 0 < A / 16 := by positivity
  have hnew := h.proxSpec (A / 16) hb u (I.grad u)
  have hfirst := first_query_safe hL0 hL1 hR.le h.cont h.smooth h.setConvex h.regConvex hp.1 hnew.1 hd
  dsimp only at hfirst
  have hAeq : A = 1 / (8 * (q.L0 + q.L1 * ‖I.grad q.x0‖) * Real.exp (4 * (q.L1 * q.R))) := by
    simp only [A, initialWeight, mul_assoc]
  rw [← hAeq] at hfirst
  have hsafe := hfirst hp.2 hnew.2
  refine ⟨hv, hb, by linarith, ?_⟩
  have hmix : mix A (A / 16) u u = u := mix_same (by positivity) u
  simpa only [accepts, evaluatedTrial, s, hmix] using hsafe

lemma valid_accuracy {q : Params} {I : Instance q.toPublic} {xs : q.E}
    (h : Conditions q I xs) {s : Iterate q.E} (hv : ValidIterate q I xs s)
    (hstop : targetWeight q.toPublic ≤ s.weight) :
    s.point ∈ I.Q ∧ objective I s.point - objective I xs ≤ q.ε := by
  have hε := h.accuracyPositive
  change 4 * q.R ^ 2 / q.ε ≤ s.weight at hstop
  have hs := (div_le_iff₀ hε).mp hstop
  have he := hv.energy_bound
  have hA := hv.weightPositive
  dsimp only [energy] at he
  exact ⟨hv.point_mem, by nlinarith [sq_nonneg ‖s.momentum - xs‖, sq_nonneg q.R]⟩

lemma accepted_ready {q : Params} {I : Instance q.toPublic} {xs : q.E}
    (h : Conditions q I xs) {s : Iterate q.E} (hv : ValidIterate q I xs s)
    {a : ℝ} (ha : 0 < a) (haccept : accepts q.toPublic s (evaluatedTrial q.toPublic I s a)) :
    let t := evaluatedTrial q.toPublic I s a
    let next : Iterate q.E := ⟨s.weight + a, mix s.weight a s.point t.proximalPoint, t.proximalPoint⟩
    let b := a / restartFactor q.toPublic
    ValidIterate q I xs next ∧ 0 < b ∧ b ≤ next.weight ∧
      accepts q.toPublic next (evaluatedTrial q.toPublic I next b) := by
  intro t next b
  have hvNext := (accepted_valid h hv ha haccept).1
  change ValidIterate q I xs next at hvNext
  have hA := hv.weightPositive
  have hsum : 0 < s.weight + a := by positivity
  have hL1 := h.hL1
  have hR := h.radiusPositive
  have hQone : 1 ≤ restartFactor q.toPublic := by
    unfold restartFactor
    nlinarith [mul_nonneg hL1 hR.le]
  have hQ : 0 < restartFactor q.toPublic := lt_of_lt_of_le zero_lt_one hQone
  have hb : 0 < b := div_pos ha hQ
  have hba : b ≤ a := div_le_self ha.le hQone
  have hbNext : b ≤ next.weight := by dsimp [next]; linarith
  obtain ⟨hc, hd⟩ := haccept
  change a ^ 2 * (q.L0 + q.L1 * ‖I.grad (mix s.weight a s.point s.momentum)‖) / (s.weight + a) ≤ 1 / 32 at hc
  change q.L1 * (a / (s.weight + a)) * ‖t.proximalPoint - s.momentum‖ ≤ 1 / 32 at hd
  have hprevious : q.L1 * ‖next.point - mix s.weight a s.point s.momentum‖ ≤ 1 / 32 := by
    change q.L1 * ‖mixPoint s.weight a s.point t.proximalPoint - mixPoint s.weight a s.point s.momentum‖ ≤ 1 / 32
    rw [mix_sub_mix, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ha hsum)]
    nlinarith
  have hmovement : q.L1 * a * ‖t.proximalPoint - s.momentum‖ / (s.weight + a) ≤ 1 / 32 := by
    convert hd using 1
    ring
  have hold := h.proxSpec a ha s.momentum t.gradient
  have hnew := h.proxSpec b hb next.momentum (I.grad (mix next.weight b next.point next.momentum))
  have hrestart := restart_query_safe h.hL0.le hL1 h.cont h.smooth h.setConvex h.regConvex
    hvNext.weightPositive ha (by dsimp [next]; linarith : a ≤ next.weight)
    hvNext.point_radius (valid_momentum_radius h hvNext) hprevious hold.1 hnew.1 hold.2 hc hmovement
  have hfactor : 128 * (1 + q.L1 * (4 * q.R)) = restartFactor q.toPublic := by
    unfold restartFactor
    ring
  rw [hfactor] at hrestart
  have hsafe := hrestart hnew.2
  refine ⟨hvNext, hb, hbNext, ?_⟩
  simpa only [accepts, evaluatedTrial, mixPoint, mix] using hsafe

structure ReadyState (q : Params) (I : Instance q.toPublic) (xs : q.E) where
  iterate : Iterate q.E
  start : ℝ
  valid : ValidIterate q I xs iterate
  startPositive : 0 < start
  start_le : start ≤ iterate.weight
  safe : accepts q.toPublic iterate (evaluatedTrial q.toPublic I iterate start)

structure Successor (q : Params) (I : Instance q.toPublic) (xs : q.E)
    (r : ReadyState q I xs) where
  next : ReadyState q I xs
  trial : Trial q.E
  pairs : ℕ
  resolved : ResolvedTrial q.toPublic I r.iterate trial
  next_iterate : next.iterate = advance r.iterate trial
  next_start : next.start = trial.weight / restartFactor q.toPublic
  execution : (transition q.toPublic I)^[2 * pairs] (beginSearch r.iterate r.start) =
    commit q.toPublic r.iterate trial
  lower_weight : r.start ≤ trial.weight
  pairsPositive : 0 < pairs
  cost : (pairs : ℝ) ≤ Real.log (trial.weight / r.start) / Real.log 2 + 2 + refinementSteps q.toPublic

lemma successor_exists {q : Params} {I : Instance q.toPublic} {xs : q.E}
    (h : Conditions q I xs) (r : ReadyState q I xs) : Nonempty (Successor q I xs r) := by
  have hL1 := h.hL1
  have hR := h.radiusPositive
  have hscale : 0 < 1000 * (1 + 4 * q.L1 * q.R) := by positivity
  obtain ⟨t, k, hrun, hres, hlower, hk, hcost⟩ :=
    growing_completes q.toPublic I r.iterate r.start none hscale r.startPositive r.start_le r.safe
  have hcanon := hres.1
  have ht := hres.2.2.1
  have hsafe : accepts q.toPublic r.iterate (evaluatedTrial q.toPublic I r.iterate t.weight) := by
    rw [← hcanon]
    exact hres.2.1
  have hnext := accepted_ready h r.valid ht hsafe
  dsimp only at hnext
  rw [← hcanon] at hnext
  change ValidIterate q I xs (advance r.iterate t) ∧ 0 < t.weight / restartFactor q.toPublic ∧
    t.weight / restartFactor q.toPublic ≤ (advance r.iterate t).weight ∧
    accepts q.toPublic (advance r.iterate t)
      (evaluatedTrial q.toPublic I (advance r.iterate t) (t.weight / restartFactor q.toPublic)) at hnext
  let next : ReadyState q I xs := ⟨advance r.iterate t, t.weight / restartFactor q.toPublic,
    hnext.1, hnext.2.1, hnext.2.2.1, hnext.2.2.2⟩
  exact ⟨⟨next, t, k, hres, rfl, rfl, hrun, hlower, hk, hcost⟩⟩

structure Trajectory (q : Params) (I : Instance q.toPublic) (xs : q.E)
    (r0 : ReadyState q I xs) where
  ready : ℕ → ReadyState q I xs
  steps : ∀ n, Successor q I xs (ready n)
  initial : ready 0 = r0
  next : ∀ n, ready (n + 1) = (steps n).next

lemma trajectory_exists {q : Params} {I : Instance q.toPublic} {xs : q.E}
    (h : Conditions q I xs) (r0 : ReadyState q I xs) : Nonempty (Trajectory q I xs r0) := by
  classical
  let step := fun r : ReadyState q I xs => Classical.choice (successor_exists h r)
  let next := fun r : ReadyState q I xs => (step r).next
  let seq := fun n : ℕ => next^[n] r0
  refine ⟨⟨seq, fun n => step (seq n), rfl, ?_⟩⟩
  intro n
  exact Function.iterate_succ_apply' next n r0

end OracleTemplate.CompositeAdaptive

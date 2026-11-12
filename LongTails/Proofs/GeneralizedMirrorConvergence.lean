import LongTails.Proofs.GeneralizedMirrorBudget

open MeasureTheory Set ProbabilityTheory
open LongTails.Setups.StochasticGeneralizedMirror
open LongTails.Algorithms.StochasticGeneralizedMirror
open LongTails.Proofs.GeneralizedMirrorExecution
open LongTails.Proofs.GeneralizedMirrorProcess
open LongTails.Proofs.GeneralizedMirrorStopped
open LongTails.Proofs.GeneralizedMirrorWeights
open LongTails.Proofs.GeneralizedMirrorConcentration
open LongTails.Proofs.GeneralizedMirrorRun
open LongTails.Proofs.GeneralizedMirrorBudget

namespace LongTails.Proofs.GeneralizedMirrorConvergence

lemma execute_after_target (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 1 ≤ ell)
    (m : ℕ) (hm : 0 < m) (I : Instance q) (g : q.E → q.Ω → Dual q)
    (P : ProbabilityMeasure (ℕ → q.Ω)) (K N : ℕ) (hK : horizonScale q * ell ≤ K)
    (hN : K * (m + 2) ≤ N) (ξ : ℕ → q.Ω) :
    OracleTemplate.execute
      { Seed := fun _ => q.Ω, law := P,
        answer := fun _ (_, request) seed => oracleReply I g request seed }
      (algorithm q ell m) (fun _ => N) () ξ =
      (trace q ell m I g (initialState q m) ξ K).1.x := by
  have hell0 : 0 < ell := by linarith
  have hA0 := GeneralizedMirrorTuning.initialWeight_pos q hq.2.2.1 hq.2.2.2.1
    hq.2.2.2.2.2.2.2.2.1
  have ht := trace_reaches_target q hq hell m I g ξ K hK
  have he := trace_eq_rawAdvance q hq hell0 m hm I g (initialState q m) ⟨rfl, rfl, rfl⟩ hA0 ξ K
  rw [execute_eq_rawAdvance]
  conv_lhs => rw [show N = K * (m + 2) + (N - K * (m + 2)) by omega]
  rw [rawAdvance_add, ← he, rawAdvance_frozen q ell m I g ξ _ _ _ ht]

lemma execution_success (q : Public) (hq : spec.valid q) (I : Instance q)
    (O : OracleTemplate.Oracle (Query q) (Reply q)) (hI : spec.admissible q I O) (N : ℕ)
    (hN : ⌈horizonScale q * confidence (horizonScale q) q.δ⌉₊ *
      (⌈8 * confidence (horizonScale q) q.δ⌉₊ + 2) ≤ N) :
    let ell := confidence (horizonScale q) q.δ
    let m := ⌈8 * ell⌉₊
    spec.successful q I
      (fun w : Unit × ((k : ℕ) → O.Seed k) => OracleTemplate.execute O (algorithm q ell m)
        (fun _ => N) w.1 w.2)
      ⟨(Measure.dirac ()).prod (O.law : Measure _), inferInstance⟩ := by
  have hIc := hI
  rcases hIc with ⟨g, μ, P, hIID, rfl, hfc, hfd, hcont, hgen, hQc, hQm, hψc, hψm,
    hUo, hUc, hhd, hstrong, hpm, hprox, hx, ⟨xs, hxs, hmin, hD, hgap, hG⟩,
    hgm, hgi, hgmean, hgmi, hgmoment⟩
  let ell := confidence (horizonScale q) q.δ
  let m := ⌈8 * ell⌉₊
  let K := ⌈horizonScale q * ell⌉₊
  have hH := horizonScale_lower q hq
  have hH2 : 2 ≤ horizonScale q := by linarith
  have hδ := hq.2.2.2.2.2.2.2.2.2.1
  have hδ1 := hq.2.2.2.2.2.2.2.2.2.2
  have hell : 1 ≤ ell := confidence_lower hH2 hδ hδ1
  have hell0 : 0 < ell := by linarith
  have hm : 0 < m := pilotSize_pos hell
  have hK : horizonScale q * ell ≤ K := Nat.le_ceil _
  change K * (m + 2) ≤ N at hN
  have hinit := initial_ready hq m I xs hxs hx hhd hstrong hD hgap
  have hA : 0 ≤ (initialState q m).A := hinit.1.1.le
  have hcap : (initialState q m).A ≤ 2 * q.R ^ 2 / q.ε := by
    have ht := hinit.1.2.1
    rw [mul_div_assoc]
    linarith [hinit.1.1]
  have hf : Measurable I.f :=
    (continuous_iff_continuousAt.mpr (fun x => (hfd x).continuousAt)).measurable
  have hr := measurableSet_ready I hQm hUo hhd hf hψm xs m
  have hproxM : Measurable (fun t : ℝ × q.E × Dual q => guardedProx q I t.1 t.2.1 t.2.2) := hpm
  have hS (k : ℕ) := signed_tail q hq hell m I hQc hUc hhd hcont.measurable hstrong hgm hproxM
    (μ : Measure _) hgi hgmean hgmi hgmoment xs hxs hmin hr (initialState q m) hA hcap k
  have hV (k : ℕ) := energy_tail q hq hell m I hQc hUc hcont.measurable hgm hproxM
    (μ : Measure _) hgmi hgmoment xs hr (initialState q m) hA hcap k
  have hF := failure_tail q hq hell0 m I hQc hUc hcont.measurable hgm hproxM
    (μ : Measure _) hgmi hgmoment xs hr (initialState q m) K
  have hBad := bad_probability q ell m I g xs (initialState q m) K
    (Measure.infinitePi fun _ : ℕ => (μ : Measure _)) (fun k _ => hS k) (fun k _ => hV k) hF
  have hpilot : (1 / 2 : ℝ) ^ m ≤ Real.exp (-4 * ell) := pilotSize_tail
  have hfail : (Measure.infinitePi fun _ : ℕ => (μ : Measure _)).real
      {ξ | Bad q ell m I g xs (initialState q m) K ξ} ≤ q.δ := by
    have hp := mul_le_mul_of_nonneg_left hpilot (Nat.cast_nonneg K)
    have hc := confidence_failure hH2 hδ hδ1
    change 3 * (K : ℝ) * Real.exp (-4 * ell) ≤ q.δ at hc
    linarith
  have hlaw : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi (fun _ : ℕ => (μ : Measure q.Ω)) := by
    have hh := hIID.stream_law.map_eq
    change (P : Measure (ℕ → q.Ω)).map id = _ at hh
    simpa only [Measure.map_id] using hh
  let out := fun ξ => (trace q ell m I g (initialState q m) ξ K).1.x
  have hout : Measurable out := (measurable_state_x q m).comp
    (measurable_trace q ell m I hgm hproxM (initialState q m) K).fst
  have he (ξ : ℕ → q.Ω) := execute_after_target q hq hell m hm I g P K N hK hN ξ
  have hfun : (fun w : Unit × (ℕ → q.Ω) => OracleTemplate.execute
      { Seed := fun _ => q.Ω, law := P,
        answer := fun _ (_, query) seed => match query with
          | .gradient x => Sum.inl (g x seed)
          | .prox a z v => Sum.inr (I.prox a z v) }
      (algorithm q ell m) (fun _ => N) w.1 w.2) = out ∘ Prod.snd := by
    funext w
    rcases w with ⟨⟨⟩, ξ⟩
    exact he ξ
  change spec.successful q I _ _
  erw [hfun]
  refine ⟨hout.comp measurable_snd, xs, hxs, hmin, ?_⟩
  let F := {ξ | out ξ ∉ I.Q ∨ q.ε < objective I (out ξ) - objective I xs}
  have hFm : MeasurableSet F := ((hQm.preimage hout).compl).union
    (measurableSet_lt measurable_const (((hf.add hψm).comp hout).sub_const _))
  have hsnd : HasLaw (Prod.snd : Unit × (ℕ → q.Ω) → ℕ → q.Ω) (P : Measure _)
      ((Measure.dirac ()).prod (P : Measure _)) :=
    ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩
  change ((Measure.dirac ()).prod (P : Measure _)) (Prod.snd ⁻¹' F) ≤ ENNReal.ofReal q.δ
  have hmeasure : ((Measure.dirac ()).prod (P : Measure _)) (Prod.snd ⁻¹' F) =
      (P : Measure _) F := hsnd.measure_eq hFm
  rw [hmeasure]
  calc
    _ ≤ (P : Measure _) {ξ | Bad q ell m I g xs (initialState q m) K ξ} := by
      apply measure_mono
      intro ξ hξ
      by_contra hn
      have ha := accuracy_of_not_bad q hq hell m I _ hI g xs hxs hmin hG hD hgap ξ K hK hn
      exact hξ.elim (fun h => h ha.1) (not_lt_of_ge ha.2)
    _ ≤ ENNReal.ofReal q.δ := by
      rw [hlaw, ← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal hfail

end LongTails.Proofs.GeneralizedMirrorConvergence

import LongTails.Proofs.StochasticQuasarProgramCleanup

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticQuasar

open LongTails.Setups.StochasticConstrainedQuasar

lemma successful_execution (q : Params) (hv : spec.valid q) (I : Instance q)
    (O : Oracle q.E q.E 2) (hO : spec.admissible q I O) (budget : Fin 2 → ℕ)
    (hbudget : ∀ seed i, (program q seed).1 ≤ budget i) :
    spec.successful q I (fun w : ProgramSeed q × ((k : ℕ) → O.Seed k) => output q O budget w.1 w.2)
      ⟨(programLaw q : Measure (ProgramSeed q)).prod (O.law : Measure _), inferInstance⟩ := by
  rcases hO with ⟨g, p, ν, P, hIID, rfl, hproj, hQ, hcv, hx0, hu, hD, hG, hlip, hmin,
    hquasar, hgm, hgi, hmean, hg2, hvar⟩
  have hP : ConstrainedMonotone.Proj I.X P := ⟨fun y => (hproj y).1, fun y => (hproj y).2⟩
  have hlaw : (ν : Measure (ℕ → q.Ω)) = Measure.infinitePi (fun _ : ℕ => (p : Measure q.Ω)) := by
    have hh := hIID.stream_law.map_eq
    change Measure.map id (ν : Measure (ℕ → q.Ω)) = Measure.infinitePi (fun _ : ℕ => (p : Measure q.Ω)) at hh
    simpa only [Measure.map_id] using hh
  let oracle : Oracle q.E q.E 2 :=
    { Seed := fun _ => q.Ω
      law := ν
      answer := fun _ (i, x) seed => if i = 0 then g x seed else P x }
  have hexec (seed : ProgramSeed q) (ξ : ℕ → q.Ω) :
      output q oracle budget seed ξ = QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (program q seed).2 0 := by
    exact execute_program q (ProjectedClippedExtragradient.channelReply P g) oracle (fun _ => rfl)
      budget seed (hbudget seed) (fun _ _ _ => rfl) ξ
  change Measurable (fun w : ProgramSeed q × (ℕ → q.Ω) => output q oracle budget w.1 w.2) ∧
    ((programLaw q : Measure _).prod (ν : Measure _))
      {w | ¬(output q oracle budget w.1 w.2 ∈ I.X ∧ I.f (output q oracle budget w.1 w.2) - I.f I.xstar ≤ q.ε)} ≤
      ENNReal.ofReal q.δ
  simp_rw [hexec]
  refine ⟨measurable_program_execution hv hP.lipschitz.continuous.measurable hgm, ?_⟩
  rw [hlaw]
  have hmem (w : ProgramSeed q × (ℕ → q.Ω)) := sampled_program_mem q hP.mem hx0 g w.1 w.2
  simp only [hmem, true_and, not_le]
  exact program_failure q hv hP hx0 hu hQ hcv hD hG hlip hmin hquasar hgm hgi hmean hg2 hvar

end OracleTemplate.StochasticQuasar

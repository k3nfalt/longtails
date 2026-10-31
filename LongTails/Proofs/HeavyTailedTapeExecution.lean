import LongTails.Algorithms.HeavyTailedFreshTape
import LongTails.Proofs.HeavyTailedProductProcess
import LongTails.Proofs.Execution

open MeasureTheory
open LongTails.Algorithms.HeavyTailedFreshTape

namespace LongTails.Proofs.HeavyTailedTapeExecution

lemma taped_indexed_trajectory {S Aux Ω : Type} (step : S → Aux → Ω → S)
    (tape : ℕ → Aux) (ξ : ℕ → Ω) (s : S) (K : ℕ) :
    ((fun sc : State S Aux × ℕ =>
      (⟨step sc.1.value (sc.1.tape sc.1.index) (ξ sc.2),
        sc.1.index + 1, sc.1.tape⟩, sc.2 + 1))^[K] (⟨s, 0, tape⟩, 0)) =
      (⟨HeavyTailedProductProcess.trajectory (fun s (z : Aux × Ω) => step s z.1 z.2)
        K s (fun k => (tape k, ξ k)), K, tape⟩, K) := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [Function.iterate_succ_apply', ih, HeavyTailedProductProcess.trajectory_succ_last]

lemma execute_fresh_tape {Query Reply Output S Initial Aux Ω : Type}
    [MeasurableSpace Initial] [MeasurableSpace Aux] [MeasurableSpace Ω]
    (initialLaw : ProbabilityMeasure Initial) (auxLaw : ProbabilityMeasure Aux)
    (oracleLaw : ProbabilityMeasure (ℕ → Ω))
    (initial : Initial → S) (query : S → Aux → Query)
    (update : S → Aux → Reply → S) (output : S → Output)
    (answer : Query → Ω → Reply) (seed : Initial × (ℕ → Aux)) (ξ : ℕ → Ω) (K : ℕ) :
    let O : OracleTemplate.Oracle Query Reply :=
      { Seed := fun _ => Ω
        law := oracleLaw
        answer := fun _ q ω => answer q.2 ω }
    OracleTemplate.execute O (algorithm initialLaw auxLaw initial query update output)
      (fun _ => K) seed ξ =
      output (HeavyTailedProductProcess.trajectory
        (fun s (z : Aux × Ω) => update s z.1 (answer (query s z.1) z.2))
        K (initial seed.1) (fun k => (seed.2 k, ξ k))) := by
  intro O
  let A := algorithm initialLaw auxLaw initial query update output
  have hh := OracleTemplate.execute_indexed_of_answer O A K seed ξ
    (fun k q => answer q.2 (ξ k)) (by intro history q; rfl)
  rw [hh]
  change output (((fun sc : State S Aux × ℕ =>
      (⟨update sc.1.value (sc.1.tape sc.1.index)
        (answer (query sc.1.value (sc.1.tape sc.1.index)) (ξ sc.2)),
        sc.1.index + 1, sc.1.tape⟩, sc.2 + 1))^[K]
      (⟨initial seed.1, 0, seed.2⟩, 0)).1.value) = _
  rw [taped_indexed_trajectory (fun s a ω => update s a (answer (query s a) ω))]


lemma zip_streams_preserving {Aux Ω : Type*} [MeasurableSpace Aux] [MeasurableSpace Ω]
    (Q : Measure Aux) (P : Measure Ω) [IsProbabilityMeasure Q] [IsProbabilityMeasure P] :
    MeasurePreserving (fun z : (ℕ → Aux) × (ℕ → Ω) => fun k => (z.1 k, z.2 k))
      ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => P))
      (Measure.infinitePi fun _ : ℕ => Q.prod P) := by
  have hm : Measurable (fun z : (ℕ → Aux) × (ℕ → Ω) => fun k => (z.1 k, z.2 k)) := by fun_prop
  refine ⟨hm, Measure.eq_infinitePi _ (fun I t ht => ?_)⟩
  classical
  have hQ : MeasurePreserving I.restrict (Measure.infinitePi fun _ : ℕ => Q)
      (Measure.pi fun _ : I => Q) := ⟨I.measurable_restrict, Measure.infinitePi_map_restrict _⟩
  have hP : MeasurePreserving I.restrict (Measure.infinitePi fun _ : ℕ => P)
      (Measure.pi fun _ : I => P) := ⟨I.measurable_restrict, Measure.infinitePi_map_restrict _⟩
  have he := (measurePreserving_arrowProdEquivProdArrow Aux Ω I
    (fun _ => Q) (fun _ => P)).symm (MeasurableEquiv.arrowProdEquivProdArrow Aux Ω I)
  have hp := he.comp (hQ.prod hP)
  let B := Set.univ.pi (fun i : I => t i.val)
  have hB : MeasurableSet B := MeasurableSet.univ_pi (fun i => ht i.val)
  have heq := hp.measure_preimage hB.nullMeasurableSet
  rw [Measure.map_apply hm (MeasurableSet.pi I.countable_toSet (fun i _ => ht i))]
  have hs : (fun z : (ℕ → Aux) × (ℕ → Ω) => fun k => (z.1 k, z.2 k)) ⁻¹' Set.pi I t =
      ((MeasurableEquiv.arrowProdEquivProdArrow Aux Ω I).symm ∘
        (fun z : (ℕ → Aux) × (ℕ → Ω) => (I.restrict z.1, I.restrict z.2))) ⁻¹' B := by
    ext z
    change (∀ i ∈ I, (z.1 i, z.2 i) ∈ t i) ↔
      (∀ i : I, i ∈ Set.univ → (z.1 i.val, z.2 i.val) ∈ t i.val)
    simp
  rw [hs]
  refine heq.trans ?_
  change (Measure.pi fun _ : I => Q.prod P) (Set.univ.pi (fun i : I => t i.val)) = _
  rw [Measure.pi_pi]
  exact Finset.prod_attach I (fun i => (Q.prod P) (t i))


lemma initial_zip_streams_preserving {Initial Aux Ω : Type*}
    [MeasurableSpace Initial] [MeasurableSpace Aux] [MeasurableSpace Ω]
    (R : Measure Initial) (Q : Measure Aux) (P : Measure Ω)
    [IsProbabilityMeasure R] [IsProbabilityMeasure Q] [IsProbabilityMeasure P] :
    MeasurePreserving
      (fun z : (Initial × (ℕ → Aux)) × (ℕ → Ω) =>
        (z.1.1, fun k => (z.1.2 k, z.2 k)))
      ((R.prod (Measure.infinitePi fun _ : ℕ => Q)).prod
        (Measure.infinitePi fun _ : ℕ => P))
      (R.prod (Measure.infinitePi fun _ : ℕ => Q.prod P)) := by
  exact ((MeasurePreserving.id R).prod (zip_streams_preserving Q P)).comp
    (measurePreserving_prodAssoc R (Measure.infinitePi fun _ : ℕ => Q)
      (Measure.infinitePi fun _ : ℕ => P))

end LongTails.Proofs.HeavyTailedTapeExecution

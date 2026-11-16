import LongTails.Proofs.AsgoFixedRadiusExecution
import LongTails.Proofs.AsgoFixedRadiusMeasurability
import LongTails.Proofs.AsgoFixedRadiusBudget
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory OracleTemplate OracleTemplate.Muon

namespace OracleTemplate.AsgoFixedRadius

open LongTails.Setups.AsgoFixedRadius
open LongTails.Algorithms.AsgoFixedRadiusOutput

lemma source_representation {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (p : LongTails.Setups.AsgoFixedRadius.Params) (hp : Valid p)
    (I : Core.Problem p.m p.n) (hS : Core.SourceAssumptions I p.Wstar)
    (hL : I.L.trace ≤ p.ell) (hV : I.V.trace ≤ p.v)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (hRad : Core.RadiusEnvelope (publicInput p) p.Wstar p.F I.g ξ
      P.toMeasure (horizon p)) :
    Admissible p I (sourceOracle I P ξ) ∧
      ∀ ω, execute (sourceOracle I P ξ) (Core.method (publicInput p))
        (fun _ => p.M * horizon p) () (fun j => ξ j ω) =
        output (publicInput p) I.g (fun j => ξ j ω) (horizon p) := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    classical
    let Path := ℕ → I.Sample
    let enc : Ω → Path := fun ω j => ξ j ω
    let O := sourceOracle I P ξ
    let samples : ℕ → Path → I.Sample := fun j s => s j
    have he : Measurable enc := measurable_pi_iff.2 hξ.measurable
    have hm (j : ℕ) : Measurable (samples j) := measurable_pi_apply j
    have hExact : Core.OracleExact p.toPublic I O (fun _ x => x) := by
      intro history query sample
      rfl
    have hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        samples I.law.toMeasure O.law.toMeasure := by
      refine ⟨hm, ?_, ?_⟩
      · change iIndepFun samples (P.toMeasure.map enc)
        apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
        intro S sets hsets
        have hinter : MeasurableSet (⋂ t ∈ S, samples t ⁻¹' sets t) := by
          apply MeasurableSet.iInter
          intro t
          apply MeasurableSet.iInter
          intro ht
          exact hm t (hsets t ht)
        rw [Measure.map_apply he hinter]
        have hsingle (t : ℕ) (ht : t∈S) :
            P.toMeasure.map enc (samples t ⁻¹' sets t)=P.toMeasure (ξ t ⁻¹' sets t) := by
          rw [Measure.map_apply he (hm t (hsets t ht))]
          rfl
        rw [Finset.prod_congr rfl hsingle]
        have hset : enc ⁻¹' (⋂ t ∈ S, samples t ⁻¹' sets t)=⋂ t∈S, ξ t ⁻¹' sets t := by
          ext ω
          simp only [Set.mem_preimage,Set.mem_iInter]
          rfl
        rw [hset]
        exact hξ.independent.measure_inter_preimage_eq_mul S hsets
      · intro j
        change (P.toMeasure.map enc).map (samples j)=I.law.toMeasure
        rw [Measure.map_map (hm j) he]
        exact hξ.marginal j
    have hsn : Continuous (@spectralNorm p.m p.n) := by
      let f : Mat p.m p.n →ₗ[ℝ] Matrix (Fin p.m) (Fin p.n) ℝ :=
        { toFun := toMatrix, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      let g := ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin p.m) (n := Fin p.n)).trans
        LinearMap.toContinuousLinearMap).toLinearMap
      exact (g.comp f).continuous_of_finiteDimensional.norm
    have hEvt : MeasurableSet {s : Path | ∀ t<horizon p,
        spectralNorm ((Core.point p.toPublic I.g s t : Mat p.m p.n)-p.Wstar) ≤ p.R ∧
          ‖(Core.point p.toPublic I.g s t : Mat p.m p.n)-p.Wstar‖ ≤ p.F} := by
      simp only [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro t
      apply MeasurableSet.iInter
      intro ht
      have hpoint : Measurable (fun s : Path => (Core.point p.toPublic I.g s t : Mat p.m p.n)-p.Wstar) :=
        (trajectory_measurable p.toPublic I.g hS.gradientMeasurable samples hm t).fst.sub measurable_const
      exact (measurableSet_le (hsn.measurable.comp hpoint) measurable_const).inter
        (measurableSet_le hpoint.norm measurable_const)
    have hRadius : Core.RadiusEnvelope p.toPublic p.Wstar p.F I.g samples
        O.law.toMeasure (horizon p) := by
      refine ⟨hRad.1, ?_⟩
      change ∀ᵐ s ∂P.toMeasure.map enc, ∀ t<horizon p,
        spectralNorm ((Core.point p.toPublic I.g s t : Mat p.m p.n)-p.Wstar) ≤ p.R ∧
          ‖(Core.point p.toPublic I.g s t : Mat p.m p.n)-p.Wstar‖ ≤ p.F
      exact (ae_map_iff he.aemeasurable hEvt).2 hRad.2
    constructor
    · exact ⟨hS,hL,hV,(fun _ x => x),hExact,⟨(fun _ => measurable_id),hIID⟩,hRadius⟩
    · intro ω
      exact execute_correspondence p.toPublic I O (fun _ x => x) hp.2.2.1 hExact
        (horizon p) () (fun j => ξ j ω)
  )

lemma oracle_conditions (p : LongTails.Setups.AsgoFixedRadius.Params) (I : Core.Problem p.m p.n)
    (O : Oracle (Mat p.m p.n) (Mat p.m p.n)) (hO : Admissible p I O) :
    Core.SourceAssumptions I p.Wstar ∧ I.L.trace ≤ p.ell ∧ I.V.trace ≤ p.v ∧
      ∃ decode : (j : ℕ) → O.Seed j → I.Sample,
        Core.OracleExact (publicInput p) I O decode ∧
        (∀ j, Measurable (decode j)) ∧
        LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
          (fun j ω => decode j (ω j)) I.law.toMeasure O.law.toMeasure ∧
        Core.RadiusEnvelope (publicInput p) p.Wstar p.F I.g
          (fun j ω => decode j (ω j)) O.law.toMeasure (horizon p) := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    rcases hO with ⟨hS, hL, hV, decode, hexact, ⟨hmeas, hiid⟩, hrad⟩
    exact ⟨hS, hL, hV, decode, hexact, hmeas, hiid, hrad⟩
  )

end OracleTemplate.AsgoFixedRadius

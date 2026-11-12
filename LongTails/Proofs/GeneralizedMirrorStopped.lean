import LongTails.Proofs.GeneralizedMirrorProcess
import LongTails.Proofs.GeneralizedMirrorInvariant
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open MeasureTheory Set
open LongTails.Setups.StochasticGeneralizedMirror
open LongTails.Algorithms.StochasticGeneralizedMirror
open LongTails.Proofs.GeneralizedMirrorExecution
open LongTails.Proofs.GeneralizedMirrorProcess

namespace LongTails.Proofs.GeneralizedMirrorStopped

noncomputable def mirrorValue {q : Public} (I : Instance q) : q.E → ℝ := by
  classical
  exact I.U.piecewise I.h (fun _ => 0)

noncomputable def measurableDivergence {q : Public} (I : Instance q) (u z : q.E) : ℝ :=
  I.h u - mirrorValue I z - (fderiv ℝ I.h z) (u - z)

noncomputable def potential {q : Public} {m : ℕ} (I : Instance q) (u : q.E) (s : State q m) : ℝ :=
  s.A * (objective I s.x - objective I u) + measurableDivergence I u s.z

lemma measurable_mirrorValue {q : Public} (I : Instance q) (hU : IsOpen I.U)
    (hd : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z) : Measurable (mirrorValue I) := by
  classical
  have hc : ContinuousOn I.h I.U := fun z hz => (hd z hz).continuousAt.continuousWithinAt
  exact hc.measurable_piecewise continuousOn_const hU.measurableSet

lemma measurable_divergence {q : Public} (I : Instance q) (hU : IsOpen I.U)
    (hd : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z) (u : q.E) :
    Measurable (measurableDivergence I u) := by
  have he : Continuous (fun t : (q.E →L[ℝ] ℝ) × q.E => t.1 t.2) := by fun_prop
  have hf : Measurable (fun z : q.E => (fderiv ℝ I.h z) (u - z)) :=
    he.measurable.comp ((measurable_fderiv ℝ I.h).prodMk (measurable_const.sub measurable_id))
  exact (measurable_const.sub (measurable_mirrorValue I hU hd)).sub hf

lemma measurableDivergence_eq {q : Public} (I : Instance q)
    (hd : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z) (u z : q.E) (hz : z ∈ I.U) :
    measurableDivergence I u z = divergence I u z := by
  simp [measurableDivergence, mirrorValue, divergence, hz, (hd z hz).fderiv]

lemma measurable_potential {q : Public} (I : Instance q) (hU : IsOpen I.U)
    (hd : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z) (hf : Measurable I.f)
    (hψ : Measurable I.ψ) (u : q.E) (m : ℕ) : Measurable (potential (m := m) I u) := by
  have hF : Measurable (objective I) := hf.add hψ
  exact ((measurable_state_A q m).mul
    ((hF.comp (measurable_state_x q m)).sub_const (objective I u))).add
      ((measurable_divergence I hU hd u).comp (measurable_state_z q m))

noncomputable def Ready {q : Public} {m : ℕ} (I : Instance q) (u : q.E) (s : State q m) : Prop :=
  0 < s.A ∧ s.A < q.R ^ 2 / q.ε ∧ s.x ∈ I.Q ∩ I.U ∧ s.z ∈ I.Q ∩ I.U ∧
    potential I u s ≤ q.R ^ 2 ∧ ‖s.x - u‖ ≤ 2 * q.R

lemma measurableSet_ready {q : Public} (I : Instance q) (hQ : MeasurableSet I.Q)
    (hU : IsOpen I.U) (hd : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z)
    (hf : Measurable I.f) (hψ : Measurable I.ψ) (u : q.E) (m : ℕ) :
    MeasurableSet {s : State q m | Ready I u s} := by
  exact (measurableSet_lt measurable_const (measurable_state_A q m)).inter
    ((measurableSet_lt (measurable_state_A q m) measurable_const).inter
      (((hQ.inter hU.measurableSet).preimage (measurable_state_x q m)).inter
        (((hQ.inter hU.measurableSet).preimage (measurable_state_z q m)).inter
          ((measurableSet_le (measurable_potential I hU hd hf hψ u m) measurable_const).inter
            (measurableSet_le ((measurable_state_x q m).sub_const u).norm measurable_const)))))

noncomputable def GoodPilot (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (s : State q m) (b : Fin (m + 2) → q.Ω) : Prop :=
  ‖blockCenter q ell m g s b - I.df (queryPoint q ell s)‖ ≤ clipRadius q / 2

noncomputable def stoppedError (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m) (b : Fin (m + 2) → q.Ω) : Dual q := by
  classical
  exact if Ready I u s ∧ GoodPilot q ell m I g s b then
    blockDirection q ell m g s b - I.df (queryPoint q ell s) else 0

lemma measurableSet_goodPilot (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g)) (hd : Measurable I.df) :
    MeasurableSet {w : State q m × (Fin (m + 2) → q.Ω) | GoodPilot q ell m I g w.1 w.2} := by
  have hdf := hd.comp ((measurable_queryPoint q ell m).comp
    (show Measurable (Prod.fst : State q m × (Fin (m + 2) → q.Ω) → State q m) from measurable_fst))
  exact measurableSet_le ((measurable_blockCenter q ell m hg).sub hdf).norm measurable_const

lemma measurable_stoppedError (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g)) (hd : Measurable I.df)
    (u : q.E) (hr : MeasurableSet {s : State q m | Ready I u s}) :
    Measurable (Function.uncurry (stoppedError q ell m I g u)) := by
  have hdf := hd.comp ((measurable_queryPoint q ell m).comp
    (show Measurable (Prod.fst : State q m × (Fin (m + 2) → q.Ω) → State q m) from measurable_fst))
  exact ((measurable_blockDirection q ell m hg).sub hdf).ite
    ((hr.preimage measurable_fst).inter (measurableSet_goodPilot q ell m I hg hd)) measurable_const

lemma stoppedError_bound (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m) (b : Fin (m + 2) → q.Ω)
    (hB : 0 ≤ clipRadius q) : ‖stoppedError q ell m I g u s b‖ ≤ 3 * clipRadius q / 2 := by
  unfold stoppedError
  split_ifs with h
  · exact GeneralizedMirrorNoise.centered_error_bounded hB
      (blockCenter q ell m g s b) (I.df (queryPoint q ell s))
      (g (queryPoint q ell s) (b ⟨m, by omega⟩)) h.2
  · simp only [norm_zero]
    positivity

lemma potential_zradius {q : Public} {m : ℕ} (I : Instance q) (u : q.E) (hu : u ∈ I.Q)
    (hmin : IsMinOn (objective I) I.Q u) (hR : 0 < q.R)
    (hd : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z)
    (hstrong : ∀ z ∈ I.Q ∩ I.U, ∀ v ∈ I.Q, ‖v - z‖ ^ 2 / 2 ≤ divergence I v z)
    (s : State q m) (hA : 0 ≤ s.A) (hx : s.x ∈ I.Q) (hz : s.z ∈ I.Q ∩ I.U)
    (hp : potential I u s ≤ q.R ^ 2) : ‖s.z - u‖ ≤ 2 * q.R := by
  have hgap : 0 ≤ objective I s.x - objective I u := sub_nonneg.mpr (hmin hx)
  unfold potential at hp
  rw [measurableDivergence_eq I hd u s.z hz.2] at hp
  have hD := hstrong s.z hz u hu
  rw [norm_sub_rev]
  nlinarith [mul_nonneg hA hgap, norm_nonneg (u - s.z)]


lemma ready_zradius {q : Public} {m : ℕ} (I : Instance q) (u : q.E) (hu : u ∈ I.Q)
    (hmin : IsMinOn (objective I) I.Q u) (hR : 0 < q.R)
    (hd : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z)
    (hstrong : ∀ z ∈ I.Q ∩ I.U, ∀ v ∈ I.Q, ‖v - z‖ ^ 2 / 2 ≤ divergence I v z)
    {s : State q m} (hs : Ready I u s) : ‖s.z - u‖ ≤ 2 * q.R := by
  exact potential_zradius I u hu hmin hR hd hstrong s hs.1.le hs.2.2.1.1
    hs.2.2.2.1 hs.2.2.2.2.1

lemma ready_query_mem {q : Public} (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    {m : ℕ} (I : Instance q) (hQ : Convex ℝ I.Q) (hU : Convex ℝ I.U)
    (u : q.E) {s : State q m} (hs : Ready I u s) : queryPoint q ell s ∈ I.Q ∩ I.U := by
  have ha := GeneralizedMirrorTuning.stepWeight_pos q hq hell hs.1
  exact ⟨GeneralizedMirrorStep.mix_mem hQ hs.1.le ha hs.2.2.1.1 hs.2.2.2.1.1,
    GeneralizedMirrorStep.mix_mem hU hs.1.le ha hs.2.2.1.2 hs.2.2.2.1.2⟩

lemma initial_ready {q : Public} (hq : spec.valid q) (m : ℕ) (I : Instance q)
    (u : q.E) (hu : u ∈ I.Q) (hx : q.x0 ∈ I.Q ∩ I.U)
    (hd : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z)
    (hstrong : ∀ z ∈ I.Q ∩ I.U, ∀ v ∈ I.Q, ‖v - z‖ ^ 2 / 2 ≤ divergence I v z)
    (hD : divergence I u q.x0 ≤ q.R ^ 2 / 2)
    (hgap : objective I q.x0 - objective I u ≤ q.Δ) :
    Ready I u (initialState q m) ∧ potential I u (initialState q m) ≤ 5 * q.R ^ 2 / 8 := by
  rcases hq with ⟨_, _, hR, hΔ, _, _, _, _, hε, _⟩
  have hA := GeneralizedMirrorTuning.initialWeight_pos q hR hΔ hε
  have hAgap := GeneralizedMirrorTuning.initialWeight_gap q hΔ hε
  have ht : initialWeight q < q.R ^ 2 / q.ε := by
    unfold initialWeight
    apply (div_lt_div_iff₀ (by positivity : 0 < 8 * (q.Δ + q.ε)) hε).mpr
    nlinarith [sq_pos_of_pos hR]
  have hp : potential I u (initialState q m) ≤ 5 * q.R ^ 2 / 8 := by
    change initialWeight q * (objective I q.x0 - objective I u) +
      measurableDivergence I u q.x0 ≤ _
    rw [measurableDivergence_eq I hd u q.x0 hx.2]
    have hh := mul_le_mul_of_nonneg_left hgap hA.le
    linarith
  refine ⟨⟨hA, ht, hx, hx, hp.trans (by nlinarith [sq_nonneg q.R]), ?_⟩, hp⟩
  change ‖q.x0 - u‖ ≤ 2 * q.R
  rw [norm_sub_rev]
  have hh := hstrong q.x0 hx u hu
  nlinarith [norm_nonneg (u - q.x0)]

end LongTails.Proofs.GeneralizedMirrorStopped

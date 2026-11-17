import LongTails.Algorithms.DistributedBatchedSgd
import LongTails.Proofs.AdaptiveIID

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.DistributedSampling

open LongTails.Setups.DistributedSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Algorithms.DistributedBatchedSgd

lemma worker_batch_law (p : Params) (cfg : Config p) (P : Measure (Samples p))
    (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hIID : ∀ i, IID (fun k (samples : Samples p) => samples i k) (μ i : Measure _) P)
    (k : ℕ) (i : Fin p.n) :
    HasLaw (fun samples : Samples p => fun j : Fin (cfg.batch i) =>
      samples i (k * cfg.batch i + j)) (Measure.pi fun _ : Fin (cfg.batch i) => (μ i : Measure _)) P := by
  have hinj : Function.Injective (fun j : Fin (cfg.batch i) => k * cfg.batch i + j.val) := by
    intro j j' he
    exact Fin.ext (Nat.add_left_cancel he)
  refine ⟨(Measurable.of_eval (fun j => (hIID i).measurable _)).aemeasurable, ?_⟩
  have h := ((hIID i).independent.precomp hinj).map_fun_eq_pi_map
    (fun j : Fin (cfg.batch i) => ((hIID i).measurable (k * cfg.batch i + j.val)).aemeasurable)
  simpa only [(hIID i).marginal] using h

lemma joint_stream_law (p : Params) (P : Measure (Samples p))
    (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hworkers : iIndepFun (fun i (samples : Samples p) => samples i) P)
    (hIID : ∀ i, IID (fun k (samples : Samples p) => samples i k) (μ i : Measure _) P) :
    P = Measure.pi (fun i => Measure.infinitePi (fun _ : ℕ => (μ i : Measure _))) := by
  have hmarg (i : Fin p.n) : P.map (fun samples : Samples p => samples i) =
      Measure.infinitePi (fun _ : ℕ => (μ i : Measure _)) := (hIID i).stream_law.map_eq
  have h := hworkers.map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)
  change P.map id = _ at h
  simpa only [hmarg, Measure.map_id] using h

lemma independent_coordinates (p : Params) (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hworkers : iIndepFun (fun i (samples : Samples p) => samples i) P)
    (hIID : ∀ i, IID (fun k (samples : Samples p) => samples i k) (μ i : Measure _) P) :
    iIndepFun (fun v : Fin p.n × ℕ => fun samples : Samples p => samples v.1 v.2) P := by
  have hm (v : Fin p.n × ℕ) : Measurable (fun samples : Samples p => samples v.1 v.2) :=
    (measurable_pi_apply v.2).comp (measurable_pi_apply v.1)
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map hm).mpr
  have h := Measure.infinitePi_map_curry_symm (fun i (_ : ℕ) => (μ i : Measure p.Ω))
  have hmarg (v : Fin p.n × ℕ) :
      P.map (fun samples : Samples p => samples v.1 v.2) = μ v.1 := (hIID v.1).marginal v.2
  simp_rw [hmarg]
  rw [joint_stream_law p P μ hworkers hIID]
  simp only [Measure.infinitePi_eq_pi, MeasurableEquiv.coe_curry_symm] at h
  convert h using 1
  congr 1

def tail (p : Params) (cfg : Config p) (k : ℕ) (samples : Samples p) : Samples p :=
  fun i j => samples i (k * cfg.batch i + j)

lemma tail_preserving (p : Params) (cfg : Config p) (P : Measure (Samples p))
    (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hworkers : iIndepFun (fun i (samples : Samples p) => samples i) P)
    (hIID : ∀ i, IID (fun k (samples : Samples p) => samples i k) (μ i : Measure _) P)
    (k : ℕ) : MeasurePreserving (tail p cfg k) P P := by
  have hshift := hworkers.comp (fun i (ξ : ℕ → p.Ω) j => ξ (k * cfg.batch i + j))
    (fun i => Measurable.of_eval (fun j => measurable_pi_apply _))
  have hmarg (i : Fin p.n) :
      P.map (fun samples : Samples p => fun j => samples i (k * cfg.batch i + j)) =
        Measure.infinitePi (fun _ : ℕ => (μ i : Measure _)) := by
    have hinj : Function.Injective (fun j : ℕ => k * cfg.batch i + j) :=
      fun _ _ he => Nat.add_left_cancel he
    have h := ((hIID i).independent.precomp hinj).map_fun_eq_infinitePi_map
      (fun j => (hIID i).measurable _)
    simpa only [(hIID i).marginal] using h
  refine ⟨by unfold tail; fun_prop, ?_⟩
  have heq : P.map (tail p cfg k) =
      Measure.pi (fun i => Measure.infinitePi (fun _ : ℕ => (μ i : Measure _))) := by
    have he := hshift.map_fun_eq_pi_map
      (fun i => (Measurable.of_eval (fun j => (hIID i).measurable _)).aemeasurable)
    simp only [hmarg] at he
    convert he using 1
    congr 1
  exact heq.trans (joint_stream_law p P μ hworkers hIID).symm

end LongTails.Proofs.DistributedSampling

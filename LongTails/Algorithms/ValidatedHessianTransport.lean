import LongTails.Algorithms.GuardedHessianTransport

open MeasureTheory

namespace LongTails.Algorithms.ValidatedHessianTransport

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.GuardedHessianTransport

structure State (p : Params) (c : Config) (K : ℕ) where
  trials : Fin K → GuardedHessianTransport.State p c
  candidates : Fin (K + 1) → Space p
  sums : Fin (K + 1) → Space p
  count : ℕ

noncomputable def initial (p : Params) (c : Config) (K : ℕ)
    (targets : Fin K → Fin (c.steps + 1)) : State p c K where
  trials j := ⟨p.x0, 0, 0, targets j, p.x0, true, .reset 0 0⟩
  candidates _ := p.x0
  sums _ := 0
  count := 0

noncomputable def query (p : Params) (c : Config) (K B : ℕ)
    (s : State p c K) (u : ℝ) : Space p × Option (Space p) :=
  if hj : s.count / trialCalls c < K then
    GuardedHessianTransport.query p c (s.trials ⟨s.count / trialCalls c, hj⟩) u
  else
    if hj : (s.count - K * trialCalls c) / B < K + 1 then
      (s.candidates ⟨(s.count - K * trialCalls c) / B, hj⟩, none)
    else (p.x0, none)

noncomputable def update (p : Params) (c : Config) (K B : ℕ)
    (s : State p c K) (u : ℝ) (reply : Space p) : State p c K :=
  if hj : s.count / trialCalls c < K then
    let j : Fin K := ⟨s.count / trialCalls c, hj⟩
    let next := GuardedHessianTransport.update p c (s.trials j) u reply
    { s with trials := Function.update s.trials j next
             candidates := Function.update s.candidates j.succ
               (if next.alive then next.selected else p.x0)
             count := s.count + 1 }
  else
    if hj : (s.count - K * trialCalls c) / B < K + 1 then
      let j : Fin (K + 1) := ⟨(s.count - K * trialCalls c) / B, hj⟩
      { s with sums := Function.update s.sums j (s.sums j + reply)
               count := s.count + 1 }
    else { s with count := s.count + 1 }

noncomputable def output (p : Params) (c : Config) (K B : ℕ)
    (s : State p c K) : Space p :=
  s.candidates (bestEstimate (fun j => (B : ℝ)⁻¹ • s.sums j))

def calls (c : Config) (K B : ℕ) : ℕ := K * trialCalls c + (K + 1) * B

noncomputable def algorithm (p : Params) (c : Config) (K B : ℕ) :
    OracleTemplate.Algorithm (Space p × Option (Space p)) (Space p) (Space p) :=
  HeavyTailedFreshTape.algorithm
    ⟨Measure.pi (fun _ : Fin K => (PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure),
      inferInstance⟩ uniformLaw
    (initial p c K) (query p c K B) (update p c K B) (output p c K B)

noncomputable def repeatCount (p : Params) : ℕ :=
  ⌈Real.log (8 * guardRadius p / p.ε) / Real.log 3⌉₊ + 1

noncomputable def validationCount (p : Params) : ℕ :=
  ⌈(1048576 * (repeatCount p + 1 : ℕ) * (p.σg + p.αg * guardRadius p) / p.ε) ^
    (p.p / (p.p - 1))⌉₊ + 1

noncomputable def tunedAlgorithm (p : Params) :
    OracleTemplate.Algorithm (Space p × Option (Space p)) (Space p) (Space p) :=
  algorithm p (tunedConfig p) (repeatCount p) (validationCount p)

end LongTails.Algorithms.ValidatedHessianTransport

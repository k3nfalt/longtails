import LongTails.Setups.RipmGeneral

open MeasureTheory
open LongTails.Setups.RipmGeneral

namespace LongTails.Algorithms.RipmOutput

noncomputable section

def method (p : Core.Public) :
    OracleTemplate.Algorithm (ℝ × Core.Vec p.d) (Core.Vec p.d) (Core.Vec p.d) 2 :=
  Core.method p

def output (p : Core.Public) (s : (method p).State) : Core.Vec p.d :=
  (method p).output s

def lastIterate {d m : ℕ} {Ω : Type*} (I : Core.Problem d m)
    (eta : ℝ) (x0 : Core.Vec d) (i : ℕ → Ω → I.Sample)
    (j : ℕ → Ω → Fin m) (T : ℕ) : Ω → Core.Vec d :=
  Core.trajectory I eta x0 i j (T + 1)

def sourceOracle {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (I : Core.Problem d m)
    (P : ProbabilityMeasure Ω) (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m) :
    OracleTemplate.Oracle (ℝ × Core.Vec d) (Core.Vec d) 2 where
  Seed _ := I.Sample × Fin m
  law := P.map (fun omega k => (i (k / 2) omega, j (k / 2) omega))
  answer := fun _ q seed =>
    if q.1 = 0 then I.grad seed.1 q.2.2
    else Core.prox (I.regularizers seed.2) q.2.1 q.2.2

end

end LongTails.Algorithms.RipmOutput

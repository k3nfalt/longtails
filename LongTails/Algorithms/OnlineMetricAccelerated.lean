import LongTails.Setups.DiagonalSmoothStronglyConvex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

open LongTails.Setups.DiagonalSmoothStronglyConvex

variable {d : ℕ}

noncomputable def scale (p : Fin d → ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => p i * v i)

noncomputable def cutVector (g g' : EuclideanSpace ℝ (Fin d)) (i : Fin d) : ℝ :=
  max (g i ^ 2 / 2 - g i * g' i) 0

noncomputable def cutLevel (q : Fin d → ℝ) (fy fx : ℝ) (g g' : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fy - fx - ∑ i, q i * g i * g' i

noncomputable def clampBand (lo hi : ℝ) (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => max lo (min hi (v i))

structure BandLearner (d : ℕ) where
  φ : Fin d → ℝ
  G : ℝ

noncomputable def learnerStep (lo hi D : ℝ) (Λ : BandLearner d) (γ : Fin d → ℝ) : BandLearner d :=
  ⟨clampBand lo hi (fun i => Λ.φ i - D / Real.sqrt (Λ.G + ∑ i, γ i ^ 2) * γ i),
    Λ.G + ∑ i, γ i ^ 2⟩

noncomputable def lossEll (c φ : Fin d → ℝ) : ℝ := ∑ i, c i * Real.exp (-φ i)

noncomputable def cutValue (a φ : Fin d → ℝ) : ℝ := ∑ i, a i * Real.exp (φ i)

noncomputable def bestCut (cuts : List (Fin d → ℝ)) (φ : Fin d → ℝ) : ℝ × (Fin d → ℝ) :=
  cuts.foldr (fun a acc => if acc.1 < cutValue a φ then (cutValue a φ, a) else acc) (1, 0)

noncomputable def lossL (c : Fin d → ℝ) (cuts : List (Fin d → ℝ)) (φ : Fin d → ℝ) : ℝ :=
  Real.sqrt (8 * lossEll c φ * (bestCut cuts φ).1)

noncomputable def lossGrad (c : Fin d → ℝ) (cuts : List (Fin d → ℝ)) (φ : Fin d → ℝ)
    (i : Fin d) : ℝ :=
  lossL c cuts φ / 2 * ((bestCut cuts φ).2 i * Real.exp (φ i) / (bestCut cuts φ).1 -
    c i * Real.exp (-φ i) / lossEll c φ)

structure Record (d : ℕ) where
  xs : EuclideanSpace ℝ (Fin d)
  fs : ℝ
  b : Fin d → ℝ
  φ : Fin d → ℝ
  cuts : List (Fin d → ℝ)
  seg : ℕ
  steps : ℕ

structure Core (d : ℕ) where
  stage : ℕ
  b : Fin d → ℝ
  learner0 : BandLearner d
  learner1 : BandLearner d
  seg : ℕ
  ep : ℕ
  xs : EuclideanSpace ℝ (Fin d)
  fs : ℝ
  φ : Fin d → ℝ
  x : EuclideanSpace ℝ (Fin d)
  z : EuclideanSpace ℝ (Fin d)
  A : ℝ
  k : ℕ
  cuts : List (Fin d → ℝ)
  prev : Option (Record d)

noncomputable def bandLo (d : ℕ) : ℝ := -Real.log (4 * d)

noncomputable def bandHi : ℝ := -Real.log 2

noncomputable def bandWidth (d : ℕ) : ℝ := Real.sqrt d * Real.log (2 * d)

noncomputable def freshLearner (d : ℕ) : BandLearner d := ⟨fun _ => bandHi, 0⟩

noncomputable def stepScale (s : Core d) : ℝ := (1 / 2 : ℝ) ^ s.cuts.length

noncomputable def metric (s : Core d) (i : Fin d) : ℝ := s.b i * Real.exp (s.φ i)

noncomputable def weight (s : Core d) : ℝ := stepScale s * (s.k + 1) / 2

noncomputable def extrapolate (s : Core d) : EuclideanSpace ℝ (Fin d) :=
  (s.A / (s.A + weight s)) • s.x + (weight s / (s.A + weight s)) • s.z

noncomputable def trialPoint (s : Core d) (y g : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  y - scale (fun i => stepScale s * metric s i) g

noncomputable def learnerFor (s : Core d) (r : ℕ) : BandLearner d :=
  if r % 2 = 0 then s.learner0 else s.learner1

noncomputable def feedLearner (s : Core d) (r : ℕ) (γ : Fin d → ℝ) : Core d :=
  if r % 2 = 0 then { s with learner0 := learnerStep (bandLo d) bandHi (bandWidth d) s.learner0 γ }
  else { s with learner1 := learnerStep (bandLo d) bandHi (bandWidth d) s.learner1 γ }

noncomputable def recordLoss (fstar : ℝ) (R : Record d) (u : EuclideanSpace ℝ (Fin d)) :
    Fin d → ℝ :=
  fun i => (R.xs i - u i) ^ 2 / ((R.fs - fstar) * R.b i)

noncomputable def resolvePrev (fstar : ℝ) (s : Core d) (u : EuclideanSpace ℝ (Fin d)) : Core d :=
  match s.prev with
  | none => s
  | some R =>
      if R.seg = s.seg then
        feedLearner s (s.ep + 1) (lossGrad (recordLoss fstar R u) R.cuts R.φ)
      else s

noncomputable def endEpoch (fstar : ℝ) (s : Core d) (xn : EuclideanSpace ℝ (Fin d)) (fn : ℝ) :
    Core d :=
  let t := resolvePrev fstar s xn
  { t with
    ep := s.ep + 1
    xs := xn
    fs := fn
    φ := (learnerFor t (s.ep + 1)).φ
    x := xn
    z := xn
    A := 0
    k := 0
    cuts := []
    prev := some ⟨s.xs, s.fs, s.b, s.φ, s.cuts, s.seg, s.k + 1 + s.cuts.length⟩ }

noncomputable def cutIndex [NeZero d] (s : Core d) (g g' : EuclideanSpace ℝ (Fin d)) : Fin d :=
  Classical.choose (Finset.exists_max_image Finset.univ
    (fun i => cutVector g g' i * s.b i) Finset.univ_nonempty)

noncomputable def mainResolve [NeZero d] (fstar : ℝ) (s : Core d)
    (y : EuclideanSpace ℝ (Fin d)) (fy : ℝ) (g : EuclideanSpace ℝ (Fin d))
    (fx : ℝ) (g' : EuclideanSpace ℝ (Fin d)) : Core d := by
  classical
  exact
    if fx ≤ fy - (∑ i, stepScale s * metric s i * g i ^ 2) / 2 then
      if fx - fstar ≤ (s.fs - fstar) / 2 then endEpoch fstar s (trialPoint s y g) fx
      else { s with
        x := trialPoint s y g
        z := s.z - weight s • scale (metric s) g
        A := s.A + weight s
        k := s.k + 1 }
    else
      if 2 * d * cutLevel (fun i => stepScale s * metric s i) fy fx g g' <
          ∑ i, cutVector g g' i * s.b i then
        { s with
          b := Function.update s.b (cutIndex s g g') (s.b (cutIndex s g g') / 2)
          learner0 := freshLearner d
          learner1 := freshLearner d
          seg := s.seg + 1
          φ := (freshLearner d).φ
          x := s.xs
          z := s.xs
          A := 0
          k := 0
          cuts := [] }
      else
        { s with
          cuts := (fun i => 2 * cutVector g g' i * s.b i /
            cutLevel (fun i => stepScale s * metric s i) fy fx g g') :: s.cuts }

noncomputable def initResolve (s : Core d) (fy : ℝ) (g g' : EuclideanSpace ℝ (Fin d)) :
    Core d :=
  { s with
    stage := s.stage + 1
    fs := fy
    b := fun i => if i.val = s.stage then 1 / (g' i - g i) else s.b i }

inductive State (d : ℕ) where
  | ready (s : Core d)
  | probing (s : Core d) (y : EuclideanSpace ℝ (Fin d)) (fy : ℝ) (g : EuclideanSpace ℝ (Fin d))

noncomputable def firstQuery (x0 : EuclideanSpace ℝ (Fin d)) (s : Core d) :
    EuclideanSpace ℝ (Fin d) :=
  if s.stage < d then x0 else extrapolate s

noncomputable def secondQuery (x0 : EuclideanSpace ℝ (Fin d)) (s : Core d)
    (y g : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := by
  classical
  exact if h : s.stage < d then x0 + EuclideanSpace.single (⟨s.stage, h⟩ : Fin d) 1
    else trialPoint s y g

noncomputable def resolve [NeZero d] (fstar : ℝ) (s : Core d) (y : EuclideanSpace ℝ (Fin d))
    (fy : ℝ) (g : EuclideanSpace ℝ (Fin d)) (fx : ℝ) (g' : EuclideanSpace ℝ (Fin d)) : Core d :=
  if s.stage < d then initResolve s fy g g' else mainResolve fstar s y fy g fx g'

noncomputable def initialCore (x0 : EuclideanSpace ℝ (Fin d)) : Core d :=
  ⟨0, fun _ => 1, freshLearner d, freshLearner d, 0, 0, x0, 0, (freshLearner d).φ,
    x0, x0, 0, 0, [], none⟩

noncomputable def algorithm (p : Public) :
    Algorithm (EuclideanSpace ℝ (Fin p.d)) (ℝ × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d)) where
  State := State p.d
  initial _ := .ready (initialCore p.x0)
  query := fun state => (0, match state with
    | .ready s => firstQuery p.x0 s
    | .probing s y _ g => secondQuery p.x0 s y g)
  update
    | .ready s, r => .probing s (firstQuery p.x0 s) r.1 r.2
    | .probing s y fy g, r => .ready (resolve p.fstar s y fy g r.1 r.2)
  output
    | .ready s => s.xs
    | .probing s _ _ _ => s.xs

end OracleTemplate.OnlineMetricAccelerated

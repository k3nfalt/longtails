import LongTails.Algorithms.LeonTuning
import LongTails.Algorithms.LeonAggregate

namespace LongTails.Algorithms.LeonTrajectory

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LeonTuning LeonAggregate

structure Model (p : Params) where
  point : Point p
  anchors : ℕ → Point p
  history : List (Point p × ℝ)

def initial (p : Params) : Model p := ⟨p.x0, fun _ => 0, []⟩

noncomputable def mean (p : Params) (values : List (Point p)) : Point p :=
  ((values.length : ℝ)⁻¹) • values.sum

noncomputable def applyEstimate (p : Params) (s : Model p) (l : ℕ) (v : Point p) : Model p :=
  if l = 0 then
    { s with point := s.point - (resolution p / p.L / ‖v‖) • v
             history := (s.point, ‖v‖) :: s.history }
  else { s with anchors := Function.update s.anchors l v }

noncomputable def advance (p : Params) (s : Model p) (l : ℕ) (received : Fin p.d → ℤ) :
    Model p :=
  let anchor := s.anchors (l + 1)
  let estimate := decode p.n (width p l) (spacing p) (radius p l) anchor received
  applyEstimate p s l estimate

noncomputable def output (p : Params) (s : Model p) (i j : ℕ) : Point p :=
  let a := s.history[i]?.getD (p.x0, 0)
  let b := s.history[j]?.getD (p.x0, 0)
  if a.2 ≤ b.2 then a.1 else b.1

noncomputable def spent (p : Params) (prior : List ℕ) (i : Fin p.n) : ℕ :=
  (prior.map (fun l => (batch p i l : ℕ))).sum

noncomputable def samplesAt (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (used : Fin p.n → ℕ) (l : ℕ) (x : Point p) (i : Fin p.n) :
    List (Point p) :=
  (List.range (batch p i l)).map (fun j => g i x (samples i (used i + j)))

noncomputable def totalCodes (p : Params) (s : Model p) (l : ℕ)
    (values : Fin p.n → List (Point p)) : Fin p.d → ℤ :=
  fun j => ∑ i, localCodes (spacing p) (s.anchors (l + 1)) (mean p (values i)) j

noncomputable def trajectory (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (levels : List ℕ) : ℕ → Model p
  | 0 => initial p
  | t + 1 =>
    let s := trajectory p g samples levels t
    let l := levels[t]?.getD 0
    let values := samplesAt p g samples (spent p (levels.take t)) l s.point
    advance p s l (totalCodes p s l values)

end LongTails.Algorithms.LeonTrajectory

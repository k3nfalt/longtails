import LongTails.Proofs.RobustGeneralizedStoppedEnergy

open MeasureTheory Set

namespace OracleTemplate.RobustGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

open StochasticGeneralized
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex hiding Params spec

open GeneralizedAccelerated (Iterate tentativeWeight energy)
open StochasticGeneralized (proofActive proofWeight target firstHalf secondHalf run dissipation)

noncomputable def traceFirst (p : Params) (f : p.E → ℝ) (u : p.E) (g : p.E → p.Ω → p.E)
    (s : Iterate p.E) (ξ : ℕ → p.Ω) (n : ℕ) (x : p.E) : p.E :=
  let q := blockTrace (proofCost p f u) (proofNext p f u g) s ξ n
  guardedReply p f (tentativeWeight q.1) g x (firstHalf (fun i : Fin (proofCost p f u q.1) => q.2 i))

noncomputable def traceSecond (p : Params) (f : p.E → ℝ) (u : p.E) (g : p.E → p.Ω → p.E)
    (s : Iterate p.E) (ξ : ℕ → p.Ω) (n : ℕ) (x : p.E) : p.E :=
  let q := blockTrace (proofCost p f u) (proofNext p f u g) s ξ n
  guardedReply p f (tentativeWeight q.1) g x (secondHalf (fun i : Fin (proofCost p f u q.1) => q.2 i))

lemma trace_run_eq (p : Params) (f : p.E → ℝ) (u : p.E) (g : p.E → p.Ω → p.E)
    (s : Iterate p.E) (ξ : ℕ → p.Ω) (n : ℕ)
    (ha : ∀ i < n, proofActive p f u (blockTrace (proofCost p f u) (proofNext p f u g) s ξ i).1) :
    run p.L0 p.L1 (traceFirst p f u g s ξ) (traceSecond p f u g s ξ) s n =
      (blockTrace (proofCost p f u) (proofNext p f u g) s ξ n).1 := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, ih (fun i hi => ha i (by omega)), blockTrace_succ]
    dsimp only [blockAdvance]
    rw [proofNext, ite_eq_left (ha n (by omega))]
    rfl

lemma trace_run_dissipation (p : Params) (f : p.E → ℝ) (u : p.E) (g : p.E → p.Ω → p.E)
    (s : Iterate p.E) (ξ : ℕ → p.Ω) (n : ℕ)
    (ha : ∀ i < n, proofActive p f u (blockTrace (proofCost p f u) (proofNext p f u g) s ξ i).1) :
    (∑ i ∈ Finset.range n, dissipation p.L0 p.L1 (traceFirst p f u g s ξ i)
      (run p.L0 p.L1 (traceFirst p f u g s ξ) (traceSecond p f u g s ξ) s i)) =
      accumulated (proofCost p f u) (proofNext p f u g) (proofDissipation p f u g) n s ξ := by
  classical
  rw [accumulated_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Finset.mem_range.mp hi
  rw [trace_run_eq p f u g s ξ i (fun j hj => ha j (by omega)), proofDissipation, ite_eq_left (ha i hin)]
  rfl

lemma trace_run_before_target (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0+p.L1*‖gradient f x‖)
    (u : p.E) (hmin : IsMinOn f univ u) (g : p.E → p.Ω → p.E) (s : Iterate p.E)
    (hA : 0 ≤ s.A) (hG : 0 < s.guess) (hw : tentativeWeight s ≤ 2*target p.R p.ε)
    (hinit : energy f u s ≤ p.R^2) (ξ : ℕ → p.Ω) (n : ℕ)
    (hnoise : accumulated (proofCost p f u) (proofNext p f u g) (proofNoise p f u g) n s ξ ≤ 2*p.R^2)
    (hT : (blockTrace (proofCost p f u) (proofNext p f u g) s ξ n).1.A < target p.R p.ε) :
    run p.L0 p.L1 (traceFirst p f u g s ξ) (traceSecond p f u g s ξ) s n =
      (blockTrace (proofCost p f u) (proofNext p f u g) s ξ n).1 ∧
    (∑ i ∈ Finset.range n, dissipation p.L0 p.L1 (traceFirst p f u g s ξ i)
      (run p.L0 p.L1 (traceFirst p f u g s ξ) (traceSecond p f u g s ξ) s i)) ≤ 3*p.R^2 := by
  have ha : ∀ i < n, proofActive p f u (blockTrace (proofCost p f u) (proofNext p f u g) s ξ i).1 := by
    intro i hi
    have he := proofTrace_no_energy_crossing p hp hc hg hdiff hH u g s hinit ξ n hnoise i hi.le
    have hAi := (proofTrace_weight_mono p hp f u g s ξ hi.le).trans_lt hT
    exact proofTrace_active p hp f u g s hA hG hw ξ i hAi he
  refine ⟨trace_run_eq p f u g s ξ n ha, ?_⟩
  rw [trace_run_dissipation p f u g s ξ n ha]
  exact proofTrace_dissipation_le p hp hc hg hdiff hH u hmin g s hA hG hinit ξ n hnoise

end OracleTemplate.RobustGeneralized

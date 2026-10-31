import LongTails.Proofs.KnownValueNondualGeometry
import LongTails.Proofs.NondualLineSearch

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.KnownValueNondualControl

open LongTails.Setups.KnownValueNondualGeneralizedConvex
open LongTails.Algorithms.KnownValueNondual
open KnownValueNondualGeometry

structure Invariant (p : Public) (f : Point p → ℝ) (xstar : Point p) (c : Control p) : Prop where
  compact : IsCompact c.body
  convex : Convex ℝ c.body
  subset : c.body ⊆ initialBody p
  minimizer_mem : xstar - p.x0 ∈ c.body
  radius : ‖c.incumbent - xstar‖ ≤ 2 * p.R
  target_floor : p.ε ≤ c.target
  warm_target : c.warm = true → 4 * p.L0 * p.R / p.L1 * Real.exp (warmScale p) ≤ c.target
  certified : c.finished = true → f c.incumbent - f xstar ≤ p.ε
  low_gap : c.warm = false → f c.incumbent - f xstar ≤ 2 * c.target

lemma initial_invariant (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar)
    (hprior : ∑ i, |p.x0 i - xstar i| ≤ p.R) : Invariant p f xstar (initialControl p) := by
  have hdist : ‖p.x0 - xstar‖ ≤ p.R := initialBody_norm p hprior
  refine ⟨initialBody_compact p, initialBody_convex p, Subset.refl _,
    minimizer_displacement_mem p xstar hprior, ?_, ?_, ?_, ?_, ?_⟩
  · change ‖p.x0 - xstar‖ ≤ 2 * p.R
    linarith
  · dsimp [initialControl]
    split_ifs <;> exact le_max_left _ _
  · intro hw
    have hB : 1 < p.L1 * p.R := of_decide_eq_true hw
    simp [initialControl, hB]
  · intro hf
    have hf' : p.L1 * p.R ≤ 1 ∧ 2 * p.L0 * p.R ^ 2 ≤ p.ε := of_decide_eq_true hf
    exact (small_curvature_initial_gap p hgrad hg hL0 hL1 hgs xstar hmin hdist hf'.1).trans hf'.2
  · intro hw
    have hB : p.L1 * p.R ≤ 1 := by
      have hn : ¬1 < p.L1 * p.R := of_decide_eq_false hw
      exact le_of_not_gt hn
    have hgap := small_curvature_initial_gap p hgrad hg hL0 hL1 hgs xstar hmin hdist hB
    change f p.x0 - f xstar ≤ 2 * (if 1 < p.L1 * p.R then _ else _)
    rw [ite_eq_right (not_lt.mpr hB)]
    nlinarith [le_max_right p.ε (p.L0 * p.R ^ 2)]

lemma finishLine_invariant (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hd : 0 < p.d) (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ‖p.x0 - xstar‖ ≤ p.R) (c : Control p) (hc : Invariant p f xstar c)
    (out : Point p × LongTails.Algorithms.NondualLineSearch.Reply (Point p) × Bool)
    (hout : NondualLineSearch.Guarantee f g p.L0 p.L1 (4 * p.R) (p.ε / 2)
      (selector p c.body) c.incumbent out) : Invariant p f xstar (finishLine p c out) := by
  rcases out with ⟨x, ⟨value, grad⟩, small⟩
  rcases hout with ⟨hrep, hseg, hsearch⟩
  dsimp only at hrep hseg hsearch
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrep
  have hz := selector_distance p hd xstar hprior ⟨_, hc.minimizer_mem⟩
    hc.compact hc.convex hc.subset
  have hx := segment_distance p xstar _ _ x hz hc.radius hseg
  cases small with
  | true =>
    have ha := small_gradient_accuracy p hconv hgrad hε xstar x hx hsearch
    dsimp only [finishLine]
    simp only [ite_true]
    refine ⟨hc.compact, hc.convex, hc.subset, hc.minimizer_mem, hx,
      hc.target_floor, hc.warm_target, fun _ => ha, ?_⟩
    intro _
    dsimp
    linarith [hc.target_floor]
  | false =>
    have hdes := SymmetricGeneralizedDescent.normalized_descent hgrad hg hL0 hL1 hgs x
    have hrad := (SymmetricGeneralizedDescent.normalized_distance_le
      hgrad hg hconv hL0 hL1 hgs xstar x hmin).trans hx
    have hD : 0 ≤ 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) := by positivity
    have hmono : f (x - (1 / (4 * (p.L0 + p.L1 * ‖g x‖))) • g x) ≤ f c.incumbent := by
      linarith [hsearch.1]
    dsimp only [finishLine]
    simp only [Bool.false_eq_true, ite_false]
    split_ifs with hdone hphase
    · have ha : f (x - (1 / (4 * (p.L0 + p.L1 * ‖g x‖))) • g x) - f xstar ≤ p.ε := by
        rw [hval]
        linarith
      refine ⟨hc.compact, hc.convex, hc.subset, hc.minimizer_mem, hrad,
        hc.target_floor, hc.warm_target, fun _ => ha, ?_⟩
      intro _
      dsimp
      linarith [hc.target_floor]
    · refine ⟨hc.compact, hc.convex, hc.subset, hc.minimizer_mem, hrad,
        le_max_left _ _, ?_, ?_, ?_⟩
      · simp
      · intro hf
        exact (sub_le_sub_right hmono _).trans (hc.certified hf)
      · intro _
        dsimp
        rw [hval]
        linarith [le_max_right p.ε (c.target / 2)]
    · refine ⟨rootCut_compact p c hc.compact x (f x) (g x),
        rootCut_convex p c hc.convex x (f x) (g x),
        fun _ hu => hc.subset hu.1, ?_, hrad, hc.target_floor, hc.warm_target, ?_, ?_⟩
      · exact failed_cut_retains_minimizer p hgrad hg hconv hL0 hL1 hR hgs c xstar x
          hmin hval hc.minimizer_mem hx hc.warm_target (lt_of_not_ge hphase)
      · intro hf
        exact (sub_le_sub_right hmono _).trans (hc.certified hf)
      · intro hw
        exact (sub_le_sub_right hmono _).trans (hc.low_gap hw)

end LongTails.Proofs.KnownValueNondualControl

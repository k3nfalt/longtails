import LongTails.Proofs.AffineSoftmaxAmplification
import LongTails.Proofs.ClippedSubgradientStep

namespace LongTails.Proofs.SmoothFiniteMaximumOracle

open MeasureTheory

lemma exists_measurable_reply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) {X : Set E} (hne : X.Nonempty) (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ i x, x ∈ X → HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, x ∈ X → y ∈ X → ‖gradient (f i) x - gradient (f i) y‖ ≤ L * ‖x - y‖) :
    ∃ reply : Fin m × E → ℝ × E, Measurable reply ∧
      ∀ i x, x ∈ X → reply (i, x) = (f i x, gradient (f i) x) := by
  let proj := OracleTemplate.SaddlePoint.project X
  have hp : Continuous proj := (NondualProjection.project_lipschitz hne hcompact hX).continuous
  have hpX x : proj x ∈ X := (OracleTemplate.SaddlePoint.project_spec hne hcompact hX x).1
  have hfixed x (hx : x ∈ X) : proj x = x :=
    OracleTemplate.WeaklyConvexHeavyTailed.projection_fixed
      (fun y => (OracleTemplate.SaddlePoint.project_spec hne hcompact hX y).2) hx
  let reply := fun q : Fin m × E => (f q.1 (proj q.2), gradient (f q.1) (proj q.2))
  refine ⟨reply, ?_, ?_⟩
  · apply measurable_from_prod_countable_right
    intro i
    have hc : ContinuousOn (f i) X := fun x hx => (hg i x hx).continuousAt.continuousWithinAt
    have hgl : LipschitzOnWith ⟨L, hL⟩ (gradient (f i)) X :=
      lipschitzOnWith_iff_norm_sub_le.mpr (fun x hx y hy => hlip i x y hx hy)
    exact ((hc.comp_continuous hp hpX).measurable).prodMk
      ((hgl.continuousOn.comp_continuous hp hpX).measurable)
  · intro i x hx
    dsimp only [reply]
    rw [hfixed x hx]

lemma exists_smooth_minimizer {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (m : ℕ) [NeZero m] {X : Set E} (hne : X.Nonempty) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hg : ∀ i x, x ∈ X → HasGradientAt (f i) (gradient (f i) x) x) :
    ∃ xs ∈ X, IsMinOn (fun x => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i x)) X xs := by
  apply hcompact.exists_isMinOn hne
  intro x hx
  exact (SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) x)
    hτ.ne' (fun i => hg i x hx)).continuousAt.continuousWithinAt

lemma maximum_value_difference_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (m : ℕ) [NeZero m] {X : Set E} (f : Fin m → E → ℝ) (G : ℝ)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i x, x ∈ X → HasGradientAt (f i) (gradient (f i) x) x)
    (hb : ∀ i x, x ∈ X → ‖gradient (f i) x‖ ≤ G)
    {x y : E} (hx : x ∈ X) (hy : y ∈ X) :
    LongTails.Algorithms.AffineSoftmaxAmplification.maximumValue (fun i => f i x) -
      LongTails.Algorithms.AffineSoftmaxAmplification.maximumValue (fun i => f i y) ≤ G * ‖x - y‖ := by
  apply sub_le_iff_le_add.mpr
  apply csSup_le (Set.range_nonempty (fun i => f i x))
  rintro _ ⟨i, rfl⟩
  have hh := SmoothFiniteMaximumGeometry.bounded_gradient_value_difference (hc i) (hg i) (hb i) hx hy
  have hm : f i y ≤ LongTails.Algorithms.AffineSoftmaxAmplification.maximumValue (fun i => f i y) :=
    le_csSup (Set.finite_range (fun i => f i y)).bddAbove (Set.mem_range_self i)
  have ha := (abs_le.mp hh).2
  linarith

end LongTails.Proofs.SmoothFiniteMaximumOracle

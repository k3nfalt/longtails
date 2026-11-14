import LongTails.Proofs.AffineResidualGap
import LongTails.Proofs.AffineResidualRegret

namespace LongTails.Proofs.AffineResidualOutput

open LongTails.Algorithms.AffineResidualSaddle
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Proofs.AffineResidualSaddle
open LongTails.Proofs.AffineResidualGap
open LongTails.Proofs.RecursiveEnvelopeGeometry

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma uniform_initial_potential {μ τ r : ℝ} (hμ : 0 ≤ μ) (hτ : 0 ≤ τ)
    (u initial : State ι E) (hu : ∀ i, 0 ≤ u.probability i)
    (husum : ∑ i, u.probability i = 1)
    (hi : ∀ i, initial.probability i = (Fintype.card ι : ℝ)⁻¹)
    (hd : ‖u.point - initial.point‖ ≤ 2 * r) :
    potential μ τ u initial ≤ 2 * μ * r ^ 2 + τ * Real.log (Fintype.card ι) := by
  have he := AffineResidualEntropy.uniform_divergence_bound hu husum
  have hp : initial.probability = fun _ => (Fintype.card ι : ℝ)⁻¹ := funext hi
  unfold potential
  rw [hp]
  have hs : ‖u.point - initial.point‖ ^ 2 ≤ 4 * r ^ 2 := by
    nlinarith [norm_nonneg (u.point - initial.point)]
  have h1 := mul_le_mul_of_nonneg_left hs hμ
  have h2 := mul_le_mul_of_nonneg_left he hτ
  nlinarith

noncomputable def saddleValue (f : ι → E → ℝ) (anchor : E) (μ τ : ℝ)
    (x : E) (p : ι → ℝ) : ℝ :=
  regularized (fun y => ∑ i, p i * f i y) μ anchor x - τ * ∑ i, p i * Real.log (p i)

omit [InnerProductSpace ℝ E] in
lemma gap_eq_saddleValues (f : ι → E → ℝ) (anchor : E) (μ τ : ℝ) (v u : State ι E) :
    saddleGap f anchor μ τ v u = saddleValue f anchor μ τ v.point u.probability -
      saddleValue f anchor μ τ u.point v.probability := by
  unfold saddleGap saddleValue regularizer regularized
  ring

omit [InnerProductSpace ℝ E] in
lemma saddleValue_upper [Nonempty ι] (f : ι → E → ℝ) (anchor : E) (μ : ℝ)
    {τ : ℝ} (hτ : 0 < τ) (x : E) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    saddleValue f anchor μ τ x p ≤ regularized (fun y => smoothValue τ (fun i => f i y)) μ anchor x := by
  have he := AffineResidualEntropy.gibbs_variational_bound hτ (fun i => f i x) p hp hpsum
  unfold saddleValue regularized
  linarith

omit [InnerProductSpace ℝ E] in
lemma saddleValue_gibbs [Nonempty ι] (f : ι → E → ℝ) (anchor : E) (μ : ℝ)
    {τ : ℝ} (hτ : τ ≠ 0) (x : E) :
    saddleValue f anchor μ τ x (gibbsWeight τ (fun i => f i x)) =
      regularized (fun y => smoothValue τ (fun i => f i y)) μ anchor x := by
  have he := AffineResidualEntropy.gibbs_variational_eq hτ (fun i => f i x)
  unfold saddleValue regularized
  linarith

set_option backward.isDefEq.respectTransparency false in
lemma weighted_components_convex {C : Set E} (hC : Convex ℝ C) (f : ι → E → ℝ)
    (hf : ∀ i, ConvexOn ℝ C (f i)) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    ConvexOn ℝ C (fun x => ∑ i, p i * f i x) := by
  classical
  have hh (t : Finset ι) : ConvexOn ℝ C (fun x => ∑ i ∈ t, p i * f i x) := by
    induction t using Finset.induction_on with
    | empty => simpa using convexOn_const (0 : ℝ) hC
    | @insert i t hi ih =>
        convert (ConvexOn.smul (hp i) (hf i)).add ih using 1
        ext x
        simp [Finset.sum_insert hi]
  exact hh Finset.univ

set_option backward.isDefEq.respectTransparency false in
lemma saddleValue_convex {C : Set E} (hC : Convex ℝ C) (f : ι → E → ℝ)
    (hf : ∀ i, ConvexOn ℝ C (f i)) (anchor : E) {μ : ℝ} (hμ : 0 ≤ μ)
    (τ : ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    ConvexOn ℝ C (fun x => saddleValue f anchor μ τ x p) := by
  have hh := AffineSoftmaxRegularization.regularized_convexOn
    (weighted_components_convex hC f hf p hp) hμ anchor
  convert hh.add (convexOn_const (-(τ * ∑ i, p i * Real.log (p i))) hC) using 1
  ext x
  simp [saddleValue, sub_eq_add_neg]

lemma weighted_output_gap [Nonempty ι] {κ : Type*} [Fintype κ] {C : Set E}
    (hC : Convex ℝ C) (f : ι → E → ℝ) (hf : ∀ i, ConvexOn ℝ C (f i))
    (anchor : E) {μ τ : ℝ} (hμ : 0 ≤ μ) (hτ : 0 < τ)
    (v : κ → State ι E) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (hwsum : ∑ k, w k = 1)
    (hvmem : ∀ k, (v k).point ∈ C) (hv : ∀ k i, 0 ≤ (v k).probability i)
    (hvsum : ∀ k, ∑ i, (v k).probability i = 1) (z : E) :
    let x := ∑ k, w k • (v k).point
    let u : State ι E := ⟨z, gibbsWeight τ (fun i => f i x)⟩
    regularized (fun y => smoothValue τ (fun i => f i y)) μ anchor x -
      regularized (fun y => smoothValue τ (fun i => f i y)) μ anchor z ≤
        ∑ k, w k * saddleGap f anchor μ τ (v k) u := by
  let x := ∑ k, w k • (v k).point
  let p := gibbsWeight τ (fun i => f i x)
  have hp := AffineSoftmaxResidual.gibbsWeight_pos τ (fun i => f i x)
  have hc := saddleValue_convex hC f hf anchor hμ τ p (fun i => (hp i).le)
  have hj := hc.map_sum_le (fun k _ => hw k) hwsum (fun k _ => hvmem k)
  simp only [smul_eq_mul] at hj
  have hu : (∑ k, w k * saddleValue f anchor μ τ z (v k).probability) ≤
      regularized (fun y => smoothValue τ (fun i => f i y)) μ anchor z := by
    calc
      _ ≤ ∑ k, w k * regularized (fun y => smoothValue τ (fun i => f i y)) μ anchor z :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (saddleValue_upper f anchor μ hτ z (v k).probability (hv k) (hvsum k)) (hw k)
      _ = _ := by rw [← Finset.sum_mul, hwsum, one_mul]
  have he := saddleValue_gibbs f anchor μ hτ.ne' x
  dsimp only
  simp_rw [gap_eq_saddleValues, mul_sub, Finset.sum_sub_distrib]
  change regularized _ μ anchor x - regularized _ μ anchor z ≤
    (∑ k, w k * saddleValue f anchor μ τ (v k).point p) -
      ∑ k, w k * saddleValue f anchor μ τ z (v k).probability
  change saddleValue f anchor μ τ x p ≤ ∑ k, w k * saddleValue f anchor μ τ (v k).point p at hj
  change saddleValue f anchor μ τ x p = _ at he
  linarith

lemma weighted_output_gap_sum [Nonempty ι] {κ : Type*} [Fintype κ] {C : Set E}
    (hC : Convex ℝ C) (f : ι → E → ℝ) (hf : ∀ i, ConvexOn ℝ C (f i))
    (anchor : E) {μ τ : ℝ} (hμ : 0 ≤ μ) (hτ : 0 < τ)
    (v : κ → State ι E) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (hW : 0 < ∑ k, w k)
    (hvmem : ∀ k, (v k).point ∈ C) (hv : ∀ k i, 0 ≤ (v k).probability i)
    (hvsum : ∀ k, ∑ i, (v k).probability i = 1) (z : E) :
    let W := ∑ k, w k
    let x := W⁻¹ • ∑ k, w k • (v k).point
    let u : State ι E := ⟨z, gibbsWeight τ (fun i => f i x)⟩
    W * (regularized (fun y => smoothValue τ (fun i => f i y)) μ anchor x -
      regularized (fun y => smoothValue τ (fun i => f i y)) μ anchor z) ≤
        ∑ k, w k * saddleGap f anchor μ τ (v k) u := by
  let W := ∑ k, w k
  have hq : ∑ k, w k / W = 1 := by rw [← Finset.sum_div]; exact div_self hW.ne'
  have hx : (∑ k, (w k / W) • (v k).point) = W⁻¹ • ∑ k, w k • (v k).point := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [smul_smul, div_eq_mul_inv, mul_comm]
  have hg := weighted_output_gap hC f hf anchor hμ hτ v (fun k => w k / W)
    (fun k => div_nonneg (hw k) hW.le) hq hvmem hv hvsum z
  dsimp only at hg ⊢
  rw [hx] at hg
  have hh := mul_le_mul_of_nonneg_left hg hW.le
  rw [Finset.mul_sum] at hh
  have hW' : W ≠ 0 := hW.ne'
  have he (k : κ) (a : ℝ) : W * (w k / W * a) = w k * a := by field_simp [hW']
  dsimp only [W] at he hh
  simpa only [he] using hh

omit [Fintype ι] in
lemma averageOutput_mem {C : Set E} (hC : Convex ℝ C) {β : ℝ} (hβ : 0 < β)
    (initial : E) (N : ℕ) (hN : 0 < N) (points : ℕ → E)
    (hpoints : ∀ k < N, points k ∈ C) :
    averageOutput β initial N (∑ k ∈ Finset.range N, iterationWeight β k • points k) ∈ C := by
  let W := ∑ k ∈ Finset.range N, iterationWeight β k
  have hW : 0 < W :=
    Finset.sum_pos (fun k _ => AffineResidualRegret.weight_positive hβ k) (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN))
  have hs : (∑ k ∈ Finset.range N, W⁻¹ * iterationWeight β k) = 1 := by
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ hW.ne'
  have hm := hC.sum_mem (fun k _ => mul_nonneg (inv_pos.mpr hW).le
    (AffineResidualRegret.weight_positive hβ k).le) hs
    (fun k hk => hpoints k (Finset.mem_range.mp hk))
  simpa only [averageOutput, ite_eq_right (Nat.ne_of_gt hN), Finset.smul_sum, smul_smul] using hm

end LongTails.Proofs.AffineResidualOutput

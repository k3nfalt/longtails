import LongTails.Setups.CompositeGapSmooth
import LongTails.Proofs.CompositeGapGeometry
import LongTails.Proofs.CompositeExtrapolation

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CompositeGapModel

open LongTails.Setups.CompositeGapSmooth
open CompositeGapGeometry

variable {p : Params} {I : Instance p} {s : p.E}

noncomputable def smoothShift (I : Instance p) (s x : p.E) : ℝ :=
  I.f x - I.f s - ⟪I.grad s, x - s⟫

noncomputable def regularizerShift (I : Instance p) (s x : p.E) : ℝ :=
  I.ψ x - I.ψ s + ⟪I.grad s, x - s⟫

lemma shift_sum (x : p.E) :
    smoothShift I s x + regularizerShift I s x = objective I x - objective I s := by
  unfold smoothShift regularizerShift objective
  ring

lemma smoothShift_nonneg (h : Conditions p I s) (x : p.E) : 0 ≤ smoothShift I s x := by
  have hh := OracleTemplate.Gradient.convex_support h.convex_f h.gradient s x
  dsimp [smoothShift]
  linarith

lemma regularizerShift_nonneg (h : Conditions p I s) {x : p.E} (hx : x ∈ I.Q) :
    0 ≤ regularizerShift I s x := by
  have hh := CompositeExtrapolation.composite_optimality h.convex_regularizer
    h.minimizer_feasible (h.gradient s) (fun u hu => h.minimizer hu) hx
  dsimp [regularizerShift]
  linarith

lemma smoothShift_le_gap (h : Conditions p I s) {x : p.E} (hx : x ∈ I.Q) :
    smoothShift I s x ≤ objective I x - objective I s := by
  have hh := regularizerShift_nonneg h hx
  rw [← shift_sum]
  linarith

lemma regularizerShift_le_gap (h : Conditions p I s) (x : p.E) :
    regularizerShift I s x ≤ objective I x - objective I s := by
  have hh := smoothShift_nonneg h x
  rw [← shift_sum]
  linarith

lemma shifted_upper (h : Conditions p I s) {x y : p.E} (hx : x ∈ I.Q)
    (hr : Real.sqrt p.H1 * ‖y - x‖ ≤ 1) :
    smoothShift I s y ≤ smoothShift I s x + ⟪I.grad x - I.grad s, y - x⟫ +
      (p.H0 + p.H1 * (objective I x - objective I s)) * ‖y - x‖ ^ 2 := by
  have hh := h.model x hx y hr
  simp only [smoothShift, inner_sub_left, inner_sub_right] at ⊢
  simp only [inner_sub_right] at hh
  linarith

lemma shifted_gradient_sq (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    {x : p.E} (hx : x ∈ I.Q) {Δ M : ℝ} (hΔ : 0 < Δ)
    (hgap : objective I x - objective I s ≤ Δ) (hM : p.H0 + p.H1 * Δ ≤ M) :
    ‖I.grad x - I.grad s‖ ^ 2 ≤ 16 * M * Δ := by
  have hMn : 0 ≤ M := (show 0 ≤ p.H0 + p.H1 * Δ by positivity).trans hM
  apply model_gradient_bound hMn h1 hΔ (by linarith) (smoothShift_nonneg h)
    ((smoothShift_le_gap h hx).trans hgap)
  intro y hy
  have hh := shifted_upper h hx hy
  have hc : p.H0 + p.H1 * (objective I x - objective I s) ≤ M := by
    nlinarith [mul_le_mul_of_nonneg_left hgap h1]
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg ‖y - x‖)])

lemma prox_is_model_min (h : Conditions p I s) {A : ℝ} (hA : 0 < A)
    (x0 v : p.E) (c : ℝ) :
    I.prox A x0 ((1 / A) • v) ∈ I.Q ∧
    IsMinOn (model I.ψ x0 A v c) I.Q (I.prox A x0 ((1 / A) • v)) := by
  have hh := h.prox A hA x0 ((1 / A) • v)
  refine ⟨hh.1, ?_⟩
  have he (u : p.E) : model I.ψ x0 A v c u =
      A * LongTails.Setups.CompositeGeneralizedSmooth.proxObjective I A x0 ((1 / A) • v) u + c := by
    unfold model LongTails.Setups.CompositeGeneralizedSmooth.proxObjective
    rw [real_inner_smul_left]
    field_simp
  intro u hu
  change model I.ψ x0 A v c (I.prox A x0 ((1 / A) • v)) ≤ model I.ψ x0 A v c u
  rw [he, he]
  have hmin : LongTails.Setups.CompositeGeneralizedSmooth.proxObjective I A x0 ((1 / A) • v)
      (I.prox A x0 ((1 / A) • v)) ≤
      LongTails.Setups.CompositeGeneralizedSmooth.proxObjective I A x0 ((1 / A) • v) u := hh.2 hu
  linarith [mul_le_mul_of_nonneg_left hmin hA.le]

lemma shifted_model_min {x0 z v : p.E} {A c : ℝ}
    (hm : IsMinOn (model I.ψ x0 A v c) I.Q z) :
    IsMinOn (model (regularizerShift I s) x0 A (v - A • I.grad s) c) I.Q z := by
  intro u hu
  have he (w : p.E) : model (regularizerShift I s) x0 A (v - A • I.grad s) c w =
      model I.ψ x0 A v c w + A * (-I.ψ s + ⟪I.grad s, x0 - s⟫) :=
    model_shift I.ψ x0 v (I.grad s) w s A c
  change model (regularizerShift I s) x0 A (v - A • I.grad s) c z ≤
    model (regularizerShift I s) x0 A (v - A • I.grad s) c u
  rw [he, he]
  have hmin : model I.ψ x0 A v c z ≤ model I.ψ x0 A v c u := hm hu
  linarith

lemma shifted_support (h : Conditions p I s) (x y : p.E) :
    smoothShift I s y + ⟪I.grad y - I.grad s, x - y⟫ ≤ smoothShift I s x := by
  have hh := OracleTemplate.Gradient.convex_support h.convex_f h.gradient y x
  simp only [smoothShift, inner_sub_left, inner_sub_right] at ⊢
  simp only [inner_sub_right] at hh
  linarith

lemma shifted_regularizer_convex (h : Conditions p I s) :
    ConvexOn ℝ I.Q (regularizerShift I s) := by
  refine ⟨h.convex_domain, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := h.convex_regularizer.2 hx hy ha hb hab
  simp only [regularizerShift, inner_sub_right, inner_add_right,
    inner_smul_right, smul_eq_mul] at ⊢
  simp only [smul_eq_mul] at hh
  have he := congrArg (fun t : ℝ => t * (I.ψ s + ⟪I.grad s, s⟫)) hab
  nlinarith only [hh, he]

lemma model_energy {x0 x z v u : p.E} {A c : ℝ}
    (h : Conditions p I s) (hA : 0 ≤ A) (hz : z ∈ I.Q) (hu : u ∈ I.Q)
    (hm : IsMinOn (model (regularizerShift I s) x0 A v c) I.Q z)
    (hlower : A * (objective I x - objective I s) ≤
      model (regularizerShift I s) x0 A v c z)
    (hupper : model (regularizerShift I s) x0 A v c u ≤
      ‖u - x0‖ ^ 2 / 2 + A * (objective I u - objective I s)) :
    A * (objective I x - objective I u) + ‖z - u‖ ^ 2 / 2 ≤ ‖u - x0‖ ^ 2 / 2 := by
  have hh := model_growth h.convex_domain (shifted_regularizer_convex h) hA hz hu hm
  rw [norm_sub_rev u z] at hh
  linarith

end LongTails.Proofs.CompositeGapModel

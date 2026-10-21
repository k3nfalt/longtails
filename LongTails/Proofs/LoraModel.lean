import LongTails.Proofs.LoraErrorBounds
import LongTails.Setups.LocalSmoothStronglyConvexLora

namespace LongTails.Proofs.LoraModel

open LongTails.Algorithms.LoraGd LongTails.Setups.LocalSmoothStronglyConvexLora
open scoped RealInnerProductSpace

structure Model (p : Params) (f : MatrixSpace p.m p.n → ℝ) (c : Factors p.m p.n p.r) : Prop where
  mu_pos : 0 < p.μ
  mu_le : p.μ ≤ p.ρ
  s_pos : 0 < p.s
  s_le : p.s ≤ p.R
  grad : ∀ X, HasGradientAt f (gradient f X) X
  strong : ∀ X Y, f X + ⟪gradient f X, Y - X⟫ + p.μ / 2 * ‖Y - X‖ ^ 2 ≤ f Y
  lip : ∀ X Y, ‖gradient f X - gradient f Y‖ ≤ p.ρ * ‖X - Y‖
  min : IsMinOn f Set.univ (product c)
  reference : ∀ h, ‖linearization c h‖ ≤ p.R * ‖h‖
  left_lower : ∀ w, p.s * ‖w‖ ≤ ‖leftAction c w‖
  right_lower : ∀ w, p.s * ‖w‖ ≤ ‖rightTransposeAction c w‖

noncomputable def smoothness (p : Params) : ℝ := 8 * p.ρ * p.R ^ 2
noncomputable def growth (p : Params) : ℝ := p.μ * p.s ^ 2 / 8
noncomputable def condition (p : Params) : ℝ := 64 * p.ρ * p.R ^ 2 / (p.μ * p.s ^ 2)
noncomputable def radius (p : Params) : ℝ := p.μ * p.s ^ 2 / (128 * p.ρ * p.R)

namespace Model

variable {p : Params} {f : MatrixSpace p.m p.n → ℝ} {c : Factors p.m p.n p.r}

lemma rho_pos (H : Model p f c) : 0 < p.ρ := H.mu_pos.trans_le H.mu_le
lemma R_pos (H : Model p f c) : 0 < p.R := H.s_pos.trans_le H.s_le
lemma smoothness_pos (H : Model p f c) : 0 < smoothness p := by
  have := H.rho_pos
  have := H.R_pos
  unfold smoothness
  positivity
lemma growth_pos (H : Model p f c) : 0 < growth p := by
  have := H.mu_pos
  have := H.s_pos
  unfold growth
  positivity
lemma growth_le (H : Model p f c) : growth p ≤ smoothness p := by
  have hh : p.μ * p.s ^ 2 ≤ p.ρ * p.R ^ 2 :=
    mul_le_mul H.mu_le (pow_le_pow_left₀ (le_of_lt H.s_pos) H.s_le 2)
      (sq_nonneg _) (le_of_lt H.rho_pos)
  unfold growth smoothness
  have hnon : 0 ≤ p.ρ * p.R ^ 2 := by have := H.rho_pos; positivity
  nlinarith
lemma condition_eq (H : Model p f c) : condition p = smoothness p / growth p := by
  have := ne_of_gt H.mu_pos
  have := ne_of_gt H.s_pos
  unfold condition smoothness growth
  field_simp
  ring
lemma gradient_zero (H : Model p f c) : gradient f (product c) = 0 :=
  LongTails.Proofs.LoraObjective.gradient_min_zero H.rho_pos H.grad H.lip H.min
lemma gap_nonneg (H : Model p f c) (x : Factors p.m p.n p.r) :
    0 ≤ f (product x) - f (product c) := sub_nonneg.mpr (H.min (Set.mem_univ _))
lemma convex (H : Model p f c) : ConvexOn ℝ Set.univ f := by
  apply LongTails.Proofs.LoraObjective.support_convex (g := gradient f)
  intro X Y
  have hh := H.strong X Y
  have hn : 0 ≤ p.μ / 2 * ‖Y - X‖ ^ 2 := by have := H.mu_pos; positivity
  linarith
lemma self_bound (H : Model p f c) (x : Factors p.m p.n p.r) :
    ‖gradient f (product x)‖ ^ 2 ≤ 2 * p.ρ * (f (product x) - f (product c)) :=
  LongTails.Proofs.LoraObjective.self_bound H.rho_pos H.grad H.lip H.min _
lemma repair (H : Model p f c) (x : Factors p.m p.n p.r) (hx : ‖x - c‖ ≤ p.s / 2) :
    ∃ z : Factors p.m p.n p.r, product z = product c ∧
      growth p * ‖x - z‖ ^ 2 ≤ 2 * (f (product x) - f (product c)) := by
  obtain ⟨z, hz, _, hgap⟩ := LongTails.Proofs.LoraErrorBounds.repair_gap x c
    H.mu_pos H.s_pos H.strong H.gradient_zero H.left_lower H.right_lower hx
  exact ⟨z, hz, hgap⟩
lemma domination (H : Model p f c) (x : Factors p.m p.n p.r) (hx : ‖x - c‖ ≤ p.s / 2)
    (hM : ‖gradient f (product x)‖ ≤ growth p) :
    growth p * (f (product x) - f (product c)) ≤
      2 * ‖pullback x (gradient f (product x))‖ ^ 2 :=
  LongTails.Proofs.LoraErrorBounds.local_gradient_domination x c H.mu_pos H.s_pos H.strong
    H.gradient_zero H.left_lower H.right_lower hx hM

end Model
end LongTails.Proofs.LoraModel

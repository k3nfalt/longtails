import LongTails.Proofs.TerminalClippingSingleLogExecution
import LongTails.Proofs.NondualProjection
import LongTails.Proofs.TerminalClippingEnergy

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.TerminalClippingSingleLog

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

def region (X : Set E) (x : E) (R : ℝ) := X ∩ Metric.closedBall x (4 * R)

lemma region_spec {X : Set E} {x : E} {R : ℝ} (hx : x ∈ X) (hR : 0 ≤ R)
    (hc : Convex ℝ X) (hclosed : IsClosed X) :
    (region X x R).Nonempty ∧ IsCompact (region X x R) ∧ Convex ℝ (region X x R) :=
  ⟨⟨x, hx, Metric.mem_closedBall_self (by positivity)⟩,
    (isCompact_closedBall _ _).inter_left hclosed, hc.inter (convex_closedBall _ _)⟩

omit [InnerProductSpace ℝ E] [ProperSpace E] in
lemma region_moment {X : Set E} {x y : E} {R B G v : ℝ} (hy : y ∈ region X x R)
    (hv : v ≤ B^2 * ‖y-x‖^2 + G^2) :
    v ≤ (Real.sqrt (G^2 + 16*B^2*R^2))^2 := by
  have hd : ‖y-x‖ ≤ 4*R := by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hy.2
  rw [Real.sq_sqrt (by positivity)]
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 2) (sq_nonneg B)
  linarith only [hv, hh]

omit [ProperSpace E] in
lemma interior_projection {X : Set E} (hc : Convex ℝ X) {x w p a : E} {R : ℝ}
    (hp : p ∈ X) (ha : a ∈ X) (hd : ‖p-x‖ < 4*R)
    (hv : ∀ z ∈ region X x R, ⟪w-p,z-p⟫ ≤ 0) :
    ⟪w-p,a-p⟫ ≤ 0 := by
  let θ := min 1 ((4*R-‖p-x‖)/(‖a-p‖+1))
  have hden : 0 < ‖a-p‖+1 := by positivity
  have ht : 0 < θ := lt_min zero_lt_one (div_pos (sub_pos.mpr hd) hden)
  have hu : θ ≤ 1 := min_le_left _ _
  have hb := (le_div_iff₀ hden).mp (min_le_right 1 ((4*R-‖p-x‖)/(‖a-p‖+1)))
  change θ * _ ≤ _ at hb
  let z := (1-θ) • p + θ • a
  have hz : z-p = θ • (a-p) := by dsimp [z]; module
  have hx : z ∈ region X x R := by
    refine ⟨hc hp ha (sub_nonneg.mpr hu) ht.le (by ring), ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, ← sub_add_sub_cancel z p x]
    apply (norm_add_le _ _).trans
    rw [hz, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    linarith
  have hh := hv z hx
  rw [hz, real_inner_smul_right] at hh
  exact nonpos_of_mul_nonpos_right hh ht

lemma projection_agrees {X : Set E} {x : E} {R : ℝ} (hx : x ∈ X) (hR : 0 ≤ R)
    (hc : Convex ℝ X) (hclosed : IsClosed X) (proj : E → E) (hm : ∀ w, proj w ∈ X)
    (hv : ∀ w, ∀ a ∈ X, ⟪w-proj w,a-proj w⟫ ≤ 0) (w : E)
    (hd : ‖SaddlePoint.project (region X x R) w - x‖ < 4*R) :
    proj w = SaddlePoint.project (region X x R) w := by
  let p := SaddlePoint.project (region X x R) w
  obtain ⟨hn,hk,hvex⟩ := region_spec hx hR hc hclosed
  have hs := SaddlePoint.project_spec hn hk hvex w
  have h1 := interior_projection hc hs.1.1 (hm w) hd hs.2
  have h2 := hv w p hs.1.1
  change ⟪w-p,proj w-p⟫ ≤ 0 at h1
  rw [show p-proj w = -(proj w-p) by abel, inner_neg_right] at h2
  have he : w-p = (w-proj w)+(proj w-p) := by abel
  rw [he, inner_add_left, real_inner_self_eq_norm_sq] at h1
  change proj w = p
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (proj w-p)]

variable {Ω : Type*}

lemma path_coupled {X : Set E} {x : E} {R : ℝ} (hx : x ∈ X) (hR : 0 ≤ R)
    (hc : Convex ℝ X) (hclosed : IsClosed X) (proj : E → E) (hm : ∀ w, proj w ∈ X)
    (hv : ∀ w, ∀ a ∈ X, ⟪w-proj w,a-proj w⟫ ≤ 0)
    (g : E → Ω → E) (k C : ℝ) (T : ℕ) (ξ : ℕ → Ω) (n : ℕ)
    (hd : ∀ i < n, ‖path g (SaddlePoint.project (region X x R)) k C T x ξ (i+1)-x‖ < 4*R) :
    path g proj k C T x ξ n = path g (SaddlePoint.project (region X x R)) k C T x ξ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [path]
    rw [ih (fun i hi => hd i (by omega))]
    exact projection_agrees hx hR hc hclosed proj hm hv _ (hd n (by omega))

end OracleTemplate.TerminalClippingSingleLog

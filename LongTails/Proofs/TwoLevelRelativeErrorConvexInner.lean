import LongTails.Algorithms.TwoLevelRelativeErrorConvex
import LongTails.Proofs.RecursiveEnvelopeExecution
import LongTails.Proofs.RecursiveEnvelopeInner

open scoped RealInnerProductSpace
namespace LongTails.Proofs.TwoLevelRelativeErrorConvex
open OracleTemplate LongTails.Algorithms.TwoLevelRelativeErrorConvex
open RecursiveEnvelopeExecution RecursiveEnvelopeGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma transient {L α : ℝ} (hL : 0 < L) (ha : 0 < α) (hb : α ≤ 1/32) :
    let μ := L * α^4
    (1 - InexactGradient.momentum (L+μ) μ (2*α) / 2) ^ innerCount α * (L+μ) ≤ 32*α^2*μ := by
  let μ := L * α^4
  let θ := InexactGradient.momentum (L+μ) μ (2*α)
  let r := (1 + 1/α^4)/(1-2*α)
  let b := (1 + 1/α^4)/(32*α^2)
  change (1-θ/2)^innerCount α * (L+μ) ≤ _
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hd : 0 < 1-2*α := by linarith
  obtain ⟨ht, ht1, _, _, _, he⟩ := InexactGradient.momentum_bounds hμ (by linarith : μ ≤ L+μ)
    (by positivity : 0 ≤ 2*α) (by linarith : 2*α < 1)
  change 0 < θ at ht
  change θ ≤ 1 at ht1
  have hr : (L+μ)/(μ*(1-2*α)) = r := by
    dsimp [μ,r]; field_simp; ring
  have heq : 2/θ = 8 * Real.sqrt r + 128 * α^2 * r := by
    change 2/θ = _ at he
    rw [he, hr, ← hr]; ring
  have hc : (2/θ)*Real.log b ≤ innerCount α := by
    rw [heq]; exact Nat.le_ceil _
  have hex : -(θ/2)*(innerCount α : ℝ) ≤ -Real.log b := by
    have hh := mul_le_mul_of_nonneg_left hc ht.le
    field_simp at hh
    linarith
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1-θ/2) (Real.one_sub_le_exp_neg (θ/2)) (innerCount α)
  rw [← Real.exp_nat_mul] at hp
  have he2 : (1-θ/2)^innerCount α ≤ 1/b := by
    apply hp.trans
    rw [one_div, ← Real.exp_log (show 0 < b by dsimp [b]; positivity), ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    linarith
  have hh := mul_le_mul_of_nonneg_right he2 (show 0 ≤ L+μ by linarith)
  apply hh.trans
  dsimp [b, μ]; field_simp; ring_nf; rfl

lemma solve_bounds {L α : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g)
    (ha : 0 < α) (hb : α ≤ 1/32) (ans : ℕ → E → E)
    (herr : ∀ k t, ‖ans k t - g t‖ ≤ α * ‖g t‖) (y : E) (call : ℕ) :
    let μ := L * α^4
    let d := y - prox g μ y
    let u := evalAt ans (solve L α (innerCount α) y) call
    ‖d - (y-u)‖ ≤ 16*α*‖d‖ ∧
      ∀ t, (f u - f t)/μ ≤ ⟪d,y-t⟫ - 3/8*‖d‖^2 := by
  let μ := L * α^4
  let p := prox g μ y
  let u := evalAt ans (solve L α (innerCount α) y) call
  let d := y-p
  have hL := h.pos
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hin := RecursiveEnvelopeInner.inner_accuracy h hμ ha.le hb
    (fun k t => ans (call + 1*k) t) (fun _ _ => herr _ _) y (innerCount α) 0 (transient hL ha hb)
  have he := evalAt_innerPlan ans physical (L+μ) μ (2*α) y (innerCount α) call 0 (y,y)
  simp only [mul_zero, add_zero, physical, evalAt] at he
  change regularized f μ y _ - envelope f g μ y ≤ (16*α)^2 * μ/2 * ‖d‖^2 at hin
  rw [← he] at hin
  change regularized f μ y u - envelope f g μ y ≤ _ at hin
  have hg := h.prox_growth hμ y u
  change _ + μ/2*‖u-p‖^2 ≤ _ at hg
  have hs : ‖u-p‖^2 ≤ (16*α*‖d‖)^2 := by nlinarith only [hin,hg,hμ]
  change ‖d-(y-u)‖ ≤ _ ∧ ∀ t, (f u - f t)/μ ≤ _
  constructor
  · have hid : d-(y-u) = u-p := by dsimp [d]; abel
    rw [hid]; exact le_of_sq_le_sq hs (by positivity)
  intro t
  have hc := h.lower p t
  have hfield : g p = μ • d := h.prox_field hμ y
  rw [hfield, real_inner_smul_left] at hc
  have hid : t-p = d-(y-t) := by dsimp [d]; abel
  rw [hid, inner_sub_right, real_inner_self_eq_norm_sq] at hc
  change f u + μ/2*‖u-y‖^2 - (f p + μ/2*‖p-y‖^2) ≤ _ at hin
  rw [norm_sub_rev p y] at hin
  change f u + μ/2*‖u-y‖^2 - (f p + μ/2*‖d‖^2) ≤ _ at hin
  have hh : (16*α)^2 ≤ 1/4 := by nlinarith [mul_nonneg ha.le (show 0 ≤ 1/32-α by linarith)]
  have hcoef := mul_le_mul_of_nonneg_right hh (show 0 ≤ μ*‖d‖^2 by positivity)
  rw [div_le_iff₀ hμ]
  nlinarith only [hin,hc,hcoef,mul_nonneg hμ.le (sq_nonneg ‖u-y‖)]

end LongTails.Proofs.TwoLevelRelativeErrorConvex

import LongTails.Algorithms.AcceleratedZerothOrderConvex
import LongTails.Proofs.AcceleratedMarkovRun
import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.IIDBlocks
import LongTails.Proofs.ZerothOrderEstimator

section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

open HeavyTailedMarkovGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma unit_point_ball {R : ℝ} (hR : 0 ≤ R) (x0 y : E) (hy : ‖y‖ ≤ 1) :
    ‖x0 + (2*R) • y - x0‖ ≤ 2*R := by
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2*R)]
  nlinarith

lemma centered_unit_range {f : E → ℝ} {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u x0 : E} (hm : IsMinOn f univ u) (hu : ‖u-x0‖ ≤ R)
    (y : E) (hy : ‖y‖ ≤ 1) :
    (f (x0 + (2*R) • y) - f x0) / (16*L*R^2) + 1/2 ∈ Icc (0 : ℝ) 1 := by
  have hB : 0 < 16*L*R^2 := by positivity
  have hu' : ‖u-x0‖ ≤ 2*R := hu.trans (by linarith)
  have hx := smooth_gap_ball hL (by positivity : 0 ≤ 2*R) hg hlip hm hu' (unit_point_ball hR.le x0 y hy)
  have h0 := smooth_gap_ball hL hR.le hg hlip hm hu (show ‖x0-x0‖ ≤ R by simpa using hR.le)
  have hl : -(1/2 : ℝ) ≤ (f (x0 + (2*R) • y) - f x0) / (16*L*R^2) := by
    apply (le_div_iff₀ hB).mpr
    nlinarith [mul_nonneg hL.le (sq_nonneg R)]
  have hh : (f (x0 + (2*R) • y) - f x0) / (16*L*R^2) ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hB).mpr
    nlinarith
  exact ⟨by linarith, by linarith⟩

lemma value_difference_le {f : E → ℝ} (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x) {G : ℝ} {x y : E}
    (hx : ‖gradient f x‖ ≤ G) (hy : ‖gradient f y‖ ≤ G) :
    |f x - f y| ≤ G * ‖x-y‖ := by
  have hsx := Gradient.convex_support hc hg x y
  have hsy := Gradient.convex_support hc hg y x
  have hix := (real_inner_le_norm (gradient f x) (x-y)).trans
    (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hiy := (real_inner_le_norm (gradient f y) (y-x)).trans
    (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
  rw [norm_sub_rev y x] at hiy
  have he : y-x = -(x-y) := by module
  rw [he, inner_neg_right] at hsx hiy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma centered_unit_lipschitz {f : E → ℝ} {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u x0 : E} (hm : IsMinOn f univ u) (hu : ‖u-x0‖ ≤ R)
    (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |((f (x0 + (2*R) • x) - f x0) / (16*L*R^2) + 1/2) -
      ((f (x0 + (2*R) • y) - f x0) / (16*L*R^2) + 1/2)| ≤ ‖x-y‖ := by
  have hB : 0 < 16*L*R^2 := by positivity
  have hu' : ‖u-x0‖ ≤ 2*R := hu.trans (by linarith)
  have hgx := gradient_ball hL hg hlip hm hu' (unit_point_ball hR.le x0 x hx)
  have hgy := gradient_ball hL hg hlip hm hu' (unit_point_ball hR.le x0 y hy)
  have hf := value_difference_le hc hg hgx hgy
  have he : x0 + (2*R) • x - (x0 + (2*R) • y) = (2*R) • (x-y) := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2*R)] at hf
  rw [add_sub_add_right_eq_sub, ← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hB]
  apply (div_le_iff₀ hB).mpr
  nlinarith [mul_nonneg (mul_nonneg hL.le (sq_nonneg R)) (norm_nonneg (x-y))]

omit [CompleteSpace E] in
lemma centered_unit_convex {f : E → ℝ} {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hc : ConvexOn ℝ univ f) (x0 : E) :
    ConvexOn ℝ univ (fun y => (f (x0 + (2*R) • y) - f x0) / (16*L*R^2) + 1/2) := by
  let A : E →ᵃ[ℝ] E := AffineMap.const ℝ E x0 +
    (2*R) • (LinearMap.id : E →ₗ[ℝ] E).toAffineMap
  have hF : ConvexOn ℝ univ (fun y => f (x0 + (2*R) • y)) := by
    have h := hc.comp_affineMap A
    simp only [Set.preimage_univ] at h
    exact h
  have h := (ConvexOn.smul (by positivity : 0 ≤ (16*L*R^2)⁻¹)
    (hF.add_const (-f x0))).add_const (1/2 : ℝ)
  convert h using 1
  ext y
  simp [smul_eq_mul, sub_eq_add_neg, div_eq_mul_inv, mul_comm]

omit [CompleteSpace E] in
lemma centered_unit_minimizer {f : E → ℝ} {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    {u x0 : E} (hm : IsMinOn f univ u) (hu : ‖u-x0‖ ≤ R) :
    let v := (2*R)⁻¹ • (u-x0)
    ‖v‖ ≤ (1/2 : ℝ) ∧ x0 + (2*R) • v = u ∧
      IsMinOn (fun y => (f (x0 + (2*R) • y) - f x0) / (16*L*R^2) + 1/2) univ v := by
  dsimp only
  have hp : 0 < 2*R := by positivity
  have hv : x0 + (2*R) • ((2*R)⁻¹ • (u-x0)) = u := by
    rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul, add_sub_cancel]
  refine ⟨?_, hv, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    have h := mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hp.le)
    have he : (2*R)⁻¹ * R = (1/2 : ℝ) := by field_simp
    exact h.trans_eq he
  · intro y hy
    change (f (x0 + (2*R) • ((2*R)⁻¹ • (u-x0))) - f x0) / (16*L*R^2) + 1/2 ≤
      (f (x0 + (2*R) • y) - f x0) / (16*L*R^2) + 1/2
    rw [hv]
    have hmin : f u ≤ f (x0 + (2*R) • y) := hm (mem_univ _)
    exact add_le_add (div_le_div_of_nonneg_right
      (sub_le_sub_right hmin (f x0)) (by positivity : 0 ≤ 16*L*R^2)) le_rfl

omit [CompleteSpace E] in
lemma centered_accuracy_transfer {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {f : E → ℝ} {R B ε : ℝ} (hB : 0 < B)
    (x0 u v : E) (hv : x0 + (2*R) • v = u) (output : Ω → E)
    (hi : Integrable (fun ω => ((f (x0 + (2*R) • output ω) - f x0) / B + 1/2) -
      ((f (x0 + (2*R) • v) - f x0) / B + 1/2)) P)
    (ha : (∫ ω, ((f (x0 + (2*R) • output ω) - f x0) / B + 1/2) -
      ((f (x0 + (2*R) • v) - f x0) / B + 1/2) ∂P) ≤ ε/B) :
    Integrable (fun ω => f (x0 + (2*R) • output ω) - f u) P ∧
      (∫ ω, f (x0 + (2*R) • output ω) - f u ∂P) ≤ ε := by
  have he (ω : Ω) : f (x0 + (2*R) • output ω) - f u =
      B * (((f (x0 + (2*R) • output ω) - f x0) / B + 1/2) -
      ((f (x0 + (2*R) • v) - f x0) / B + 1/2)) := by
    rw [hv]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · simpa only [he] using hi.const_mul B
  · simp_rw [he]
    rw [integral_const_mul]
    have h := mul_le_mul_of_nonneg_left ha hB.le
    have hc : B * (ε/B) = ε := by field_simp
    exact h.trans_eq hc

end OracleTemplate.ZerothOrder

end

section

open OracleTemplate.StochasticGradient OracleTemplate.HeavyTailedMarkovGradient
open LongTails.Setups.StochasticSmoothAndConvex

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma execute_rescaled {Ω : Type} [MeasurableSpace Ω]
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (g : E → Ω → ℝ)
    (A : Algorithm E ℝ E) (R B : ℝ) (x0 : E) (K : ℕ) (seed : A.Seed) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (rescaled A R B x0) (fun _ => (K*2)) seed ξ =
      x0 + (2*R) • A.output (advance (fun call state => A.update state
        ((g (x0 + (2*R) • (A.query state).2) (ξ (call*2)) - g x0 (ξ (call*2+1))) / B + 1/2))
        K 0 (A.initial seed)) := by
  have h := execute_batched (by decide : 0 < 2) A
    (fun s i => if i = 0 then x0 + (2*R) • (A.query s).2 else x0)
    (fun _ v => (v 0 - v 1) / B + 1/2) 0 P g ξ K seed
  have he := congrArg (fun v : E => x0 + (2*R) • v) h
  erw [execute_advance] at he
  erw [execute_advance]
  simpa [rescaled] using he

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory ProbabilityTheory OracleTemplate.StochasticGradient
open LongTails.Setups.StochasticSmoothAndConvex

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma execute_rescaled_pair {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (P2 : ProbabilityMeasure (ℕ → Ω × Ω))
    (g : Point d → Ω → ℝ) (A : Algorithm (Point d) ℝ (Point d))
    (R B : ℝ) (x0 : Point d) (K : ℕ) (seed : A.Seed) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (rescaled A R B x0) (fun _ => (K*2)) seed ξ =
      x0 + (2*R) • (execute
        { Seed := fun _ => Ω × Ω, law := P2, answer := fun _ (_, x) ω => centeredOracle g R B x0 x ω }
        A (fun _ => K) seed (fun k => (ξ (k*2), ξ (k*2+1)))) := by
  rw [execute_rescaled, execute_advance]
  rfl

lemma paired_accuracy_transfer {d : ℕ} {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    (Q : Measure S) [IsProbabilityMeasure Q] (p : Measure Ω) [IsProbabilityMeasure p]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) P)
    (hmarg : ∀ k, P.map (fun ξ => ξ k) = p)
    {f : Point d → ℝ} {R B ε : ℝ} (hB : 0 < B)
    (x0 u v : Point d) (hv : x0 + (2*R) • v = u)
    (output : S × (ℕ → Ω × Ω) → Point d)
    (hi : Integrable (fun ω => ((f (x0 + (2*R) • output ω) - f x0) / B + 1/2) -
      ((f (x0 + (2*R) • v) - f x0) / B + 1/2))
      (Q.prod (Measure.infinitePi fun _ : ℕ => p.prod p)))
    (ha : (∫ ω, ((f (x0 + (2*R) • output ω) - f x0) / B + 1/2) -
      ((f (x0 + (2*R) • v) - f x0) / B + 1/2)
      ∂Q.prod (Measure.infinitePi fun _ : ℕ => p.prod p)) ≤ ε/B) :
    Integrable (fun ω : S × (ℕ → Ω) =>
      f (x0 + (2*R) • output (ω.1, fun k => (ω.2 (k*2), ω.2 (k*2+1)))) - f u) (Q.prod P) ∧
    (∫ ω : S × (ℕ → Ω),
      f (x0 + (2*R) • output (ω.1, fun k => (ω.2 (k*2), ω.2 (k*2+1)))) - f u ∂Q.prod P) ≤ ε := by
  have hp := (MeasurePreserving.id Q).prod (FiniteVariance.paired_stream_law p P hind hmarg)
  have hip := hp.integrable_comp_of_integrable hi
  have hap := (integral_comp_preserving hp hi).trans_le ha
  exact centered_accuracy_transfer (Q.prod P) hB x0 u v hv
    (fun ω : S × (ℕ → Ω) => output (ω.1, fun k => (ω.2 (k*2), ω.2 (k*2+1)))) hip hap

end OracleTemplate.ZerothOrder

end

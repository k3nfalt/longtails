import LongTails.Setups.StochasticProximalEf21
import LongTails.Proofs.ProximalEf21Regularization

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21SetupGeometry

open LongTails.Setups.StochasticProximalEf21
open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21ConvexAnalysis
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21Regularization

variable {p : Params} {I : Instance p}

lemma line_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : E → E) (hg : ∀ x, HasGradientAt f (g x) x)
    (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • d)) ⟪g (x + t • d), d⟫_ℝ t := by
  have hp : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  simpa using (hg (x + t • d)).hasFDerivAt.comp_hasDerivAt t hp

lemma convex_gradient_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : E → E)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (x y : E) : f x + ⟪g x, y - x⟫_ℝ ≤ f y := by
  have hc' : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • (y - x))) := by
    refine ⟨convex_univ, ?_⟩
    intro a ha b hb u v hu hv huv
    have h := hc.2 (Set.mem_univ (x + a • (y - x)))
      (Set.mem_univ (x + b • (y - x))) hu hv huv
    have hid : u • (x + a • (y - x)) + v • (x + b • (y - x)) =
        x + (u * a + v * b) • (y - x) := by
      rw [smul_add, smul_add, smul_smul, smul_smul]
      calc
        u • x + (u * a) • (y - x) + (v • x + (v * b) • (y - x)) =
            (u + v) • x + (u * a + v * b) • (y - x) := by module
        _ = _ := by rw [huv, one_smul]
    simpa [hid, smul_eq_mul] using h
  have hd := line_gradient f g hg x (y - x) 0
  simp only [zero_smul, add_zero] at hd
  have h := hc'.le_slope_of_hasDerivAt
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) (by norm_num) hd
  simp only [slope, zero_smul, one_smul, add_zero, add_sub_cancel,
    sub_zero, div_one] at h
  linarith

lemma smooth_gradient_upper {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : E → E) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hl : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (x y : E) :
    f y ≤ f x + ⟪g x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  have hf : Continuous (fun t : ℝ => f (x + t • d)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (line_gradient f g hg x d t).continuousAt
  have hB (t : ℝ) : HasDerivAt
      (fun s : ℝ => f x + s * ⟪g x, d⟫_ℝ + L / 2 * s ^ 2 * ‖d‖ ^ 2)
      (⟪g x, d⟫_ℝ + L * t * ‖d‖ ^ 2) t := by
    convert (((hasDerivAt_id t).mul_const ⟪g x, d⟫_ℝ).const_add (f x)).add
      ((((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖d‖ ^ 2)) using 1 <;> ring
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ⟪g (x + t • d), d⟫_ℝ ≤ ⟪g x, d⟫_ℝ + L * t * ‖d‖ ^ 2 := by
    intro t ht
    have hi := real_inner_le_norm (g (x + t • d) - g x) d
    have hn := hl (x + t • d) x
    have hd : x + t • d - x = t • d := by abel
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hn
    have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg d)
    rw [inner_sub_left] at hi
    nlinarith only [hi, hm]
  have h := image_le_of_deriv_right_le_deriv_boundary
    (a := (0 : ℝ)) (b := 1) hf.continuousOn
    (fun t ht => (line_gradient f g hg x d t).hasDerivWithinAt)
    (by simp)
    (by fun_prop)
    (fun t ht => (hB t).hasDerivWithinAt) hbound
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  simpa [d] using h

noncomputable def domain (I : Instance p) : Set (Point p) := {x | I.ψ x ≠ ⊤}
noncomputable def psiValue (I : Instance p) (x : Point p) : ℝ := (I.ψ x).toReal

lemma finite_psi_coe (h : ProblemAssumptions p I) (x : Point p)
    (hx : x ∈ domain I) : (psiValue I x : EReal) = I.ψ x :=
  EReal.coe_toReal hx (h.regularizerNoBottom x)

lemma finite_psi_convex (h : ProblemAssumptions p I) :
    ConvexOn ℝ (domain I) (psiValue I) := by
  have hpair (x : Point p) (hx : x ∈ domain I) :
      (x, psiValue I x) ∈ {z : Point p × ℝ | I.ψ z.1 ≤ (z.2 : EReal)} := by
    change I.ψ x ≤ (psiValue I x : EReal)
    rw [finite_psi_coe h x hx]
  have hm (x : Point p) (hx : x ∈ domain I) (y : Point p) (hy : y ∈ domain I)
      (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
      I.ψ (a • x + b • y) ≤ ((a * psiValue I x + b * psiValue I y : ℝ) : EReal) := by
    have hc := h.regularizerConvex (hpair x hx) (hpair y hy) ha hb hab
    simpa only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul, Set.mem_setOf_eq] using hc
  have hdom : Convex ℝ (domain I) := by
    intro x hx y hy a b ha hb hab
    have hc := hm x hx y hy a b ha hb hab
    exact ne_top_of_le_ne_top EReal.coe_ne_top hc
  refine ⟨hdom, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := hm x hx y hy a b ha hb hab
  have hr := EReal.toReal_le_toReal hc (h.regularizerNoBottom _) EReal.coe_ne_top
  simpa only [EReal.toReal_coe, smul_eq_mul, psiValue] using hr

lemma finite_prox_min (h : ProblemAssumptions p I) {τ : ℝ} (hτ : 0 < τ)
    (u z : Point p) (hz : z ∈ domain I) :
    psiValue I (I.prox τ u) + ‖I.prox τ u - u‖ ^ 2 / (2 * τ) ≤
      psiValue I z + ‖z - u‖ ^ 2 / (2 * τ) := by
  have hmin := h.proximalMinimizer τ hτ u z
  rw [← finite_psi_coe h (I.prox τ u) (h.proximalFinite τ hτ u),
    ← finite_psi_coe h z hz, ← EReal.coe_add, ← EReal.coe_add] at hmin
  exact EReal.coe_le_coe_iff.mp hmin

lemma finite_optimum (h : ProblemAssumptions p I) (x : Point p)
    (hx : x ∈ domain I) : finiteObjective I I.xstar ≤ finiteObjective I x := by
  have ho := h.optimum x
  unfold objective at ho
  rw [← finite_psi_coe h I.xstar h.optimumFinite,
    ← finite_psi_coe h x hx, ← EReal.coe_add, ← EReal.coe_add] at ho
  exact EReal.coe_le_coe_iff.mp ho

lemma average_upper (h : ProblemAssumptions p I) (hn : 0 < p.workers)
    (x y : Point p) :
    smoothObjective I y ≤ smoothObjective I x +
      ⟪workerMean (fun i => gradient (I.f i) x), y - x⟫_ℝ +
      ((p.workers : ℝ)⁻¹ * ∑ i, I.localL i) / 2 * ‖y - x‖ ^ 2 := by
  have hi (i : Fin p.workers) := smooth_gradient_upper (I.f i)
    (gradient (I.f i)) (I.localL i) (h.localNonnegative i)
    (h.localGradient i) (h.localSmooth i) x y
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i))
    (inv_nonneg.mpr (Nat.cast_nonneg p.workers))
  simpa only [Finset.sum_add_distrib, ← Finset.sum_div,
    ← Finset.sum_mul, mul_add, smoothObjective, workerMean,
    real_inner_smul_left, sum_inner, mul_div_assoc] using hs

lemma composite_optimum_support (h : ProblemAssumptions p I)
    (hn : 0 < p.workers) (x : Point p) (hx : x ∈ domain I) :
    psiValue I I.xstar +
      ⟪-workerMean (fun i => gradient (I.f i) I.xstar), x - I.xstar⟫_ℝ ≤
      psiValue I x := by
  let A : ℝ := (p.workers : ℝ)⁻¹ * ∑ i, I.localL i
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun i _ => h.localNonnegative i))
  have hψ := finite_psi_convex h
  have hnonpos : psiValue I I.xstar - psiValue I x -
      ⟪workerMean (fun i => gradient (I.f i) I.xstar), x - I.xstar⟫_ℝ ≤ 0 := by
    apply nonpositive_of_segment_bounds (c := A / 2 * ‖x - I.xstar‖ ^ 2)
      (by positivity)
    intro t ht ht1
    have hmem := hψ.1 h.optimumFinite hx (sub_nonneg.mpr ht1) ht.le (by ring)
    have hc := hψ.2 h.optimumFinite hx (sub_nonneg.mpr ht1) ht.le (by ring)
    have hmin := finite_optimum h _ hmem
    have hs := average_upper h hn I.xstar ((1 - t) • I.xstar + t • x)
    have he : (1 - t) • I.xstar + t • x - I.xstar = t • (x - I.xstar) := by module
    rw [he, real_inner_smul_right, square_smul] at hs
    simp only [smul_eq_mul] at hc
    unfold finiteObjective at hmin
    change _ + psiValue I I.xstar ≤ _ + psiValue I _ at hmin
    change _ ≤ _ + _ + A / 2 * (t ^ 2 * _) at hs
    apply (mul_le_mul_left ht).mp
    nlinarith only [hmin, hc, hs]
  rw [inner_neg_left]
  linarith

noncomputable def geometry (hp : spec.valid p) (h : ProblemAssumptions p I) :
    ConvexCompositeGeometry (E := Point p) p.workers p.L where
  domain := domain I
  ψ := psiValue I
  f := I.f
  grad i := gradient (I.f i)
  localL := I.localL
  prox := I.prox
  xstar := I.xstar
  hn := hp.1
  hL := hp.2.1
  localL_nonnegative := h.localNonnegative
  rms_bound := by
    have hnonneg : 0 ≤ (p.workers : ℝ)⁻¹ * ∑ i, I.localL i ^ 2 := by positivity
    rw [h.rmsSmoothness, Real.sq_sqrt hnonneg]
  local_lower i := convex_gradient_lower (I.f i) (gradient (I.f i))
    (h.localConvex i) (h.localGradient i)
  local_upper i := smooth_gradient_upper (I.f i) (gradient (I.f i))
    (I.localL i) (h.localNonnegative i) (h.localGradient i) (h.localSmooth i)
  local_lipschitz := h.localSmooth
  regularizer_convex := finite_psi_convex h
  optimum_mem := h.optimumFinite
  optimum_support := composite_optimum_support h hp.1
  prox_mem := h.proximalFinite
  prox_min τ hτ u z hz := finite_prox_min h hτ u z hz

lemma geometry_gap (hp : spec.valid p) (h : ProblemAssumptions p I) (x : Point p) :
    (geometry hp h).gap x = finiteObjective I x - finiteObjective I I.xstar := rfl

lemma prox_nonexpansive (hp : spec.valid p) (h : ProblemAssumptions p I)
    {τ : ℝ} (hτ : 0 < τ) (u v : Point p) :
    ‖I.prox τ u - I.prox τ v‖ ≤ ‖u - v‖ := by
  let G := (geometry hp h).regularized (2 * p.L) (by linarith [hp.2.1]) (by rfl)
  have h₁ := G.prox_support hτ u (I.prox τ v) (h.proximalFinite τ hτ v)
  have h₂ := G.prox_support hτ v (I.prox τ u) (h.proximalFinite τ hτ u)
  change psiValue I (I.prox τ u) +
    ⟪τ⁻¹ • (u - I.prox τ u), I.prox τ v - I.prox τ u⟫_ℝ ≤ psiValue I (I.prox τ v) at h₁
  change psiValue I (I.prox τ v) +
    ⟪τ⁻¹ • (v - I.prox τ v), I.prox τ u - I.prox τ v⟫_ℝ ≤ psiValue I (I.prox τ u) at h₂
  have he : ⟪u - I.prox τ u, I.prox τ v - I.prox τ u⟫_ℝ +
      ⟪v - I.prox τ v, I.prox τ u - I.prox τ v⟫_ℝ =
      ‖I.prox τ u - I.prox τ v‖ ^ 2 -
        ⟪u - v, I.prox τ u - I.prox τ v⟫_ℝ := by
    rw [← inner_self_eq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  simp only [real_inner_smul_left] at h₁ h₂
  have hsum : τ⁻¹ * (‖I.prox τ u - I.prox τ v‖ ^ 2 -
      ⟪u - v, I.prox τ u - I.prox τ v⟫_ℝ) ≤ 0 := by nlinarith only [h₁, h₂, he]
  have hfirm : ‖I.prox τ u - I.prox τ v‖ ^ 2 ≤
      ⟪u - v, I.prox τ u - I.prox τ v⟫_ℝ := by
    have hi : 0 < τ⁻¹ := inv_pos.mpr hτ
    nlinarith only [hsum, hi]
  have hc := real_inner_le_norm (u - v) (I.prox τ u - I.prox τ v)
  by_cases hz : ‖I.prox τ u - I.prox τ v‖ = 0
  · rw [hz]
    exact norm_nonneg _
  · have hz' : 0 < ‖I.prox τ u - I.prox τ v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith only [hfirm, hc, hz']

end LongTails.Proofs.ProximalEf21SetupGeometry

import LongTails.Proofs.RelativeGrowthProfile
import LongTails.Proofs.AcceleratedFiniteSum
import LongTails.Proofs.WeakInterpolationGeometry
import LongTails.Setups.DistributedRelativeGrowth

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.RelativeGrowthGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gap_comparison {F H : E → ℝ} {g v : E → E} {L M I : ℝ} (hI : 0 < I)
    (hc : ConvexOn ℝ univ F) (hg : ∀ x, HasGradientAt F (g x) x)
    (hl : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖)
    (hu : ∀ x y, H y ≤ H x + ⟪v x,y-x⟫ + M/2*‖y-x‖^2)
    (halign : ∀ x, I*‖g x‖^2 ≤ ⟪v x,g x⟫)
    (x z : E) (hmin : ∀ y, H z ≤ H y) :
    I * (F x-F z) ≤ H x-H z := by
  by_cases hgap : 0 < F x-F z
  swap
  · exact (mul_nonpos_of_nonneg_of_nonpos hI.le (le_of_not_gt hgap)).trans (sub_nonneg.mpr (hmin x))
  by_contra! hbad
  obtain ⟨s, hs₁, hs₂⟩ := exists_between ((div_lt_iff₀ hgap).mpr (by linarith only [hbad]) :
    (H x-H z)/(F x-F z) < I)
  have hs : 0 < s := (div_nonneg (sub_nonneg.mpr (hmin x)) hgap.le).trans_lt hs₁
  have hx : H x-H z < s*(F x-F z) := (div_lt_iff₀ hgap).mp hs₁
  let K := max 1 (max L (M/(I-s)))
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hKL : L ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKM : M ≤ K * (I-s) := (div_le_iff₀ (sub_pos.mpr hs₂)).mp
    ((le_max_right _ _).trans (le_max_right _ _))
  let T := fun y => y - (1/K) • g y
  have hstep (y : E) : s * (F y - F (T y)) ≤ H y - H (T y) := by
    have e : T y-y = -(1/K) • g y := by dsimp [T]; module
    have h₁ := OracleTemplate.Gradient.convex_support hc hg y (T y)
    have h₂ := hu y (T y)
    rw [e, real_inner_smul_right, real_inner_self_eq_norm_sq] at h₁
    rw [e, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos (one_div_pos.mpr hK)] at h₂
    have h₃ := halign y
    field_simp [hK.ne', hK] at h₁ h₂
    have h₄ := mul_le_mul_of_nonneg_right hKM (sq_nonneg ‖g y‖)
    have h₅ := mul_le_mul_of_nonneg_left h₃ hK.le
    have h₆ := mul_le_mul_of_nonneg_left h₁ (mul_nonneg hs.le hK.le)
    apply le_of_mul_le_mul_left (a := 2*K^2) _ (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hK.le (sub_nonneg.mpr hs₂.le)) (sq_nonneg ‖g y‖)]
  have ht (k : ℕ) : s*(F x-F (T^[k] x)) ≤ H x-H (T^[k] x) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      linarith only [ih, hstep (T^[k] x)]
  let e := (s*(F x-F z)-(H x-H z))/(2*s)
  have he : 0 < e := div_pos (sub_pos.mpr hx) (by positivity)
  let k := max 1 ⌈K*‖x-z‖^2/(2*e)⌉₊
  have ha := OracleTemplate.Gradient.gd_accuracy F g K ‖x-z‖ e x z hK (norm_nonneg _) he
    hc hg (fun x y => (hl x y).trans (mul_le_mul_of_nonneg_right hKL (norm_nonneg _))) le_rfl k le_rfl
  rw [OracleTemplate.Gradient.execute_gd] at ha
  change F (T^[k] x)-F z ≤ e at ha
  have hb := mul_le_mul_of_nonneg_left ha hs.le
  have heq : 2*s*e = s*(F x-F z)-(H x-H z) := by dsimp [e]; field_simp
  linarith only [ht k, hmin (T^[k] x), hb, heq, hx]

open LongTails.Setups.DistributedRelativeGrowth
open LongTails.Setups.DistributedWeakInterpolation (objective solutions)
open LongTails.Algorithms.GrowthProfile

variable {p : Params} {f : Functions p}

private lemma obj_eq (p : Params) (f : Functions p) :
    objective p.toParams f = LongTails.Setups.FiniteSumSmoothAndConvex.objective f := by
  funext x
  simp [objective, LongTails.Setups.FiniteSumSmoothAndConvex.objective, div_eq_inv_mul]

lemma gradient_eq (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (x : Point p) :
    gradient (objective p.toParams f) x = (p.n : ℝ)⁻¹ • ∑ i, gradient (f i) x := by
  rw [obj_eq]
  exact (OracleTemplate.FiniteSum.objective_gradient (f := f)
    (oracle := fun ix : Fin p.n × Point p => gradient (f ix.1) ix.2) hg x).gradient

lemma solutions_eq (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hr : ∀ x, ∑ i, ‖gradient (f i) x‖^2 ≤ (p.n : ℝ)*p.ρ*‖gradient (objective p.toParams f) x‖^2) :
    minimizers p f = solutions p.toParams f := by
  ext z
  constructor
  · intro hz i
    change IsMinOn (objective p.toParams f) univ z at hz
    have h0 : gradient (objective p.toParams f) z = 0 := by
      simp [gradient, (hz.isLocalMin Filter.univ_mem).fderiv_eq_zero]
    have hsum := hr z
    rw [h0, norm_zero, zero_pow (by decide), mul_zero] at hsum
    have hi := (Finset.single_le_sum (s := Finset.univ)
      (fun j _ => sq_nonneg ‖gradient (f j) z‖) (Finset.mem_univ i)).trans hsum
    have hz' : gradient (f i) z = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (gradient (f i) z)])
    intro y _
    have := OracleTemplate.Gradient.convex_support (hc i) (hg i) z y
    rw [hz', inner_zero_left] at this
    exact sub_nonneg.mp this
  · intro hz y _
    change (∑ i, f i z) / (p.n : ℝ) ≤ (∑ i, f i y) / (p.n : ℝ)
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hz i (mem_univ y)) (by positivity)

lemma alignment {h : Fin p.n → ℝ} (hh : ∀ i, 0 < h i) (hρ : 1 ≤ p.ρ)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hr : ∀ x, ∑ i, ‖gradient (f i) x‖^2 ≤ (p.n : ℝ)*p.ρ*‖gradient (objective p.toParams f) x‖^2)
    (x : Point p) :
    let u := profile h p.ρ
    let G := gradient (objective p.toParams f) x
    (∑ i, u i / h i * u i) * ‖G‖^2 ≤ ⟪∑ i, (u i / h i) • gradient (f i) x, G⟫ := by
  intro u G
  by_cases hz : G = 0
  · simp [hz]
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hG : 0 < ‖G‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  let a := fun i => ⟪gradient (f i) x,G⟫ / ‖G‖^2
  have he : (∑ i, gradient (f i) x) = (p.n : ℝ) • G := by
    dsimp only [G]
    rw [gradient_eq hg, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hm : ∑ i, a i = p.n := by
    simp only [a, ← Finset.sum_div, ← sum_inner, he, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have ha : ∑ i, a i ^ 2 ≤ p.n * p.ρ := by
    simp only [a, div_pow, ← Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos hG)).mpr
    have H (i : Fin p.n) : ⟪gradient (f i) x,G⟫^2 ≤ ‖gradient (f i) x‖^2 * ‖G‖^2 := by
      rw [← mul_pow, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
    have hh' := Finset.sum_le_sum (s := Finset.univ) (fun i _ => H i)
    rw [← Finset.sum_mul] at hh'
    exact hh'.trans (by simpa only [sq, mul_assoc] using mul_le_mul_of_nonneg_right (hr x) hG.le)
  have hs := RelativeGrowthProfile.weighted_support hh hρ a hm ha
  change (∑ i, u i / h i * u i) ≤ ∑ i, u i / h i * (_ / ‖G‖^2) at hs
  simp only [← mul_div_assoc, ← Finset.sum_div] at hs
  simpa only [sum_inner, real_inner_smul_left] using (le_div_iff₀ hG).mp hs

end LongTails.Proofs.RelativeGrowthGeometry

import LongTails.Algorithms.DimensionAdaptiveMinty
import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped RealInnerProductSpace
noncomputable section

namespace LongTails.Proofs.MintySeparatingCut

open LongTails.Setups.FiniteDimensionalWeakMinty LongTails.Algorithms.DimensionAdaptiveMinty

lemma margin_pos (p : Params) (hp : spec.valid p) : 0 < margin p :=
  div_pos hp.2.2.2.2.1 (mul_pos (by norm_num) hp.2.1)

lemma separation (p : Params) (hp : spec.valid p) (F : E p → E p)
    (hlip : ∀ x y, ‖F x - F y‖ ≤ p.L * ‖x-y‖) (z : E p)
    (hm : ∀ x, -p.ρ * ‖F x‖^2 ≤ ⟪F x, x-z⟫)
    (r : Round p) (hbad : p.ε < ‖F (output p r)‖) :
    let h := F (look p r (F (output p r)))
    let u := ‖h‖⁻¹ • h
    ‖u‖ = 1 ∧ margin p ≤ ⟪u, r.x - (z-p.x0)⟫ := by
  let x := output p r
  let g := F x
  let η := 1 / (2*p.L)
  let y := look p r g
  let h := F y
  have hL := hp.2.1
  have hρ := hp.2.2.1
  have hρL := hp.2.2.2.1
  have hε := hp.2.2.2.2.1
  have hη : 0 < η := by dsimp [η]; positivity
  have heta : p.L * η = 1/2 := by dsimp [η]; field_simp
  have hdiff : ‖h-g‖ ≤ ‖g‖ / 2 := by
    have hh := hlip y x
    have he : y - x = -(η • g) := by change x-η • g-x = _; abel
    rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη, ← mul_assoc, heta] at hh
    exact hh.trans_eq (by ring)
  have hn : ‖h‖ ≤ 3 * ‖g‖ / 2 := by linarith [norm_sub_norm_le h g]
  have hgpos : 0 < ‖g‖ := hε.trans hbad
  have hhpos : 0 < ‖h‖ := by
    have h := norm_sub_norm_le g h
    rw [norm_sub_rev] at h
    linarith
  have hinner : ‖g‖ ^ 2 / 2 ≤ ⟪h,g⟫ := by
    have e := abs_real_inner_le_norm (h-g) g
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at e
    have b := (abs_le.mp e).1
    nlinarith [mul_le_mul_of_nonneg_right hdiff hgpos.le]
  have hdecomp : ⟪h,x-z⟫ = ⟪h,y-z⟫ + η * ⟪h,g⟫ := by
    rw [show x-z = y-z + η • g by change x-z = x-η • g-z+η • g; abel,
      inner_add_right, real_inner_smul_right]
  have hmult : 20 * p.L * p.ρ ≤ 1 := by
    have e := (le_div_iff₀ (by positivity : 0 < 20 * p.L)).mp hρL
    linarith
  have hmint := mul_le_mul_of_nonneg_left (hm y) hL.le
  change p.L * (-p.ρ * ‖h‖^2) ≤ p.L * ⟪h,y-z⟫ at hmint
  have hgain : ‖g‖ ^ 2 / 8 ≤ p.L * ⟪h,x-z⟫ := by
    rw [hdecomp, mul_add, ← mul_assoc, heta]
    have he := pow_le_pow_left₀ hhpos.le hn 2
    nlinarith [mul_le_mul_of_nonneg_right hmult (sq_nonneg ‖h‖)]
  change ‖‖h‖⁻¹ • h‖ = 1 ∧ _
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hhpos), inv_mul_cancel₀ hhpos.ne']
  · change margin p ≤ ⟪‖h‖⁻¹ • h, r.x - (z-p.x0)⟫
    rw [real_inner_smul_left, show r.x - (z-p.x0) = x-z by dsimp [x, output]; abel,
      ← div_eq_inv_mul, le_div_iff₀ hhpos]
    unfold margin
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 16*p.L)).mp
    have e : 16*p.L * (p.ε / (16*p.L) * ‖h‖) = p.ε * ‖h‖ := by field_simp
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hn hε.le,
      mul_lt_mul_of_pos_right hbad hgpos]

end LongTails.Proofs.MintySeparatingCut

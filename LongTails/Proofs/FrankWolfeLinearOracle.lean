import LongTails.Proofs.FrankWolfeHardInstance
import Mathlib.Analysis.InnerProductSpace.NormPow

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.FrankWolfe.HardInstance

open LongTails.Setups.UniformlyConvexHolder

lemma convex_abs_power {q : ℝ} (hq : 1 ≤ q) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x| ^ q) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hs := abs_add_le (a * x) (b * y)
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at hs
  have hp := Real.rpow_le_rpow (abs_nonneg _) hs (by linarith : 0 ≤ q)
  have hc := (convexOn_rpow hq).2 (abs_nonneg x) (abs_nonneg y) ha hb hab
  exact hp.trans hc

lemma abs_power_support {q : ℝ} (hq : 1 < q) (a b : ℝ) :
    q * |a| ^ (q - 2) * a * (b - a) ≤ |b| ^ q - |a| ^ q := by
  have h := convex_support_on (convex_abs_power hq.le) (Set.mem_univ a) (Set.mem_univ b)
    (hasDerivAt_abs_rpow a hq).hasGradientAt
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

lemma power_ball_lmo_certificate {q scale : ℝ} (hq : 2 ≤ q) (hscale : 0 ≤ scale)
    (g atom : Plane) (hboundary : |atom 0| ^ q + |atom 1| ^ q = 1)
    (hg0 : g 0 = -scale * (q * |atom 0| ^ (q - 2) * atom 0))
    (hg1 : g 1 = -scale * (q * |atom 1| ^ (q - 2) * atom 1)) :
    atom ∈ twoBall q ∧ ∀ x ∈ twoBall q, ⟪g, atom⟫ ≤ ⟪g, x⟫ := by
  have hqpos : 0 < q := by linarith
  refine ⟨(mem_twoBall_iff hqpos atom).mpr hboundary.le, ?_⟩
  intro x hx
  have h0 := abs_power_support (by linarith : 1 < q) (atom 0) (x 0)
  have h1 := abs_power_support (by linarith : 1 < q) (atom 1) (x 1)
  have hball := (mem_twoBall_iff hqpos x).mp hx
  have hs : q * |atom 0| ^ (q - 2) * atom 0 * (x 0 - atom 0) +
      q * |atom 1| ^ (q - 2) * atom 1 * (x 1 - atom 1) ≤ 0 := by linarith
  have hm := mul_nonpos_of_nonneg_of_nonpos hscale hs
  have heq : ⟪g, x⟫ - ⟪g, atom⟫ = -scale *
      (q * |atom 0| ^ (q - 2) * atom 0 * (x 0 - atom 0) +
       q * |atom 1| ^ (q - 2) * atom 1 * (x 1 - atom 1)) := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
    rw [hg0, hg1]
    ring
  linarith

lemma linear_minimizer_unique {q : ℝ} (hq : 2 ≤ q) {g a b : Plane}
    (hg : g ≠ 0) (ha : a ∈ twoBall q) (hb : b ∈ twoBall q)
    (hmina : ∀ x ∈ twoBall q, ⟪g, a⟫ ≤ ⟪g, x⟫)
    (hminb : ∀ x ∈ twoBall q, ⟪g, b⟫ ≤ ⟪g, x⟫) : a = b := by
  by_contra hab
  have h := uniformly_convex_gap (twoBall_uniformly_convex hq) ha hb hminb
  have heq : ⟪g, a - b⟫ = 0 := by
    rw [inner_sub_right]
    linarith [hmina b hb, hminb a ha]
  rw [heq] at h
  have hpos : 0 < twoBallModulus q / 2 * ‖g‖ * ‖a - b‖ ^ q :=
    mul_pos (mul_pos (div_pos (twoBallModulus_pos hq) (by norm_num)) (norm_pos_iff.mpr hg))
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hab)) _)
  linarith

lemma exists_lmo {q : ℝ} (hq : 2 ≤ q) (g : Plane) :
    ∃ atom ∈ twoBall q, ∀ x ∈ twoBall q, ⟪g, atom⟫ ≤ ⟪g, x⟫ := by
  exact (twoBall_compact hq).exists_isMinOn (f := fun x => ⟪g, x⟫) ⟨optimum, optimum_mem (by linarith)⟩
    (by fun_prop)

noncomputable def lmo (q : ℝ) (hq : 2 ≤ q) (g : Plane) : Plane :=
  Classical.choose (exists_lmo hq g)

lemma lmo_spec (q : ℝ) (hq : 2 ≤ q) (g : Plane) :
    lmo q hq g ∈ twoBall q ∧ ∀ x ∈ twoBall q, ⟪g, lmo q hq g⟫ ≤ ⟪g, x⟫ :=
  Classical.choose_spec (exists_lmo hq g)

noncomputable def oracle (q r : ℝ) (hq : 2 ≤ q) : Oracle (Plane ⊕ Plane) Plane where
  answer := fun _ (_, query) _ => query.elim (grad r) (lmo q hq)

lemma signed_atom_lmo {q A T sign c : ℝ} (hq : 2 ≤ q) (hA : 0 < A) (hT : 0 < T)
    (hsign : |sign| = 1) (hc : 0 ≤ c) (hboundary : A ^ q + T ^ q = 1) :
    let a : Plane := WithLp.toLp 2 ![A, -sign * T]
    let g : Plane := WithLp.toLp 2 ![-c * A ^ (q - 1), sign * c * T ^ (q - 1)]
    a ∈ twoBall q ∧ ∀ x ∈ twoBall q, ⟪g, a⟫ ≤ ⟪g, x⟫ := by
  dsimp only
  have hqpos : 0 < q := by linarith
  have hAshift : A ^ (q - 2) * A = A ^ (q - 1) := by
    rw [← Real.rpow_add_one hA.ne', show q - 2 + 1 = q - 1 by ring]
  have hTshift : T ^ (q - 2) * T = T ^ (q - 1) := by
    rw [← Real.rpow_add_one hT.ne', show q - 2 + 1 = q - 1 by ring]
  apply power_ball_lmo_certificate hq (scale := c / q) (div_nonneg hc hqpos.le)
  · simpa [abs_of_pos hA, abs_mul, abs_neg, hsign, abs_of_pos hT] using hboundary
  · simp only [Matrix.cons_val_zero]
    rw [abs_of_pos hA]
    calc
      -c * A ^ (q - 1) = -c * (A ^ (q - 2) * A) := by rw [hAshift]
      _ = -(c / q) * (q * A ^ (q - 2) * A) := by field_simp
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [abs_mul, abs_neg, hsign, abs_of_pos hT, one_mul]
    calc
      sign * c * T ^ (q - 1) = sign * c * (T ^ (q - 2) * T) := by rw [hTshift]
      _ = -(c / q) * (q * T ^ (q - 2) * (-sign * T)) := by field_simp

end OracleTemplate.FrankWolfe.HardInstance

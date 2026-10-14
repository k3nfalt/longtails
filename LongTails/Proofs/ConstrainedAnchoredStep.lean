import LongTails.Algorithms.ConstrainedAnchoredExtragradient
import LongTails.Proofs.AnchoredExtragradientStep

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ConstrainedMonotone

open GeneralizedMonotone (Hyp anchored_identity distance_identity)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Proj (X : Set E) (P : E → E) : Prop where
  mem : ∀ z, P z ∈ X
  var : ∀ z, ∀ w ∈ X, ⟪z - P z, w - P z⟫ ≤ 0

def Normal (X : Set E) (x ξ : E) : Prop := ∀ w ∈ X, ⟪ξ, w - x⟫ ≤ 0

lemma Proj.dist_le {X : Set E} {P : E → E} (hP : Proj X P) (z : E) {y : E} (hy : y ∈ X) :
    ‖P z - y‖ ≤ ‖z - y‖ := by
  have hv := hP.var z y hy
  have he : z - y = (z - P z) + (P z - y) := by abel
  have hsq : ‖z - y‖ ^ 2 = ‖z - P z‖ ^ 2 + 2 * ⟪z - P z, P z - y⟫ + ‖P z - y‖ ^ 2 := by
    rw [he, norm_add_sq_real]
  have hi : ⟪z - P z, P z - y⟫ = -⟪z - P z, y - P z⟫ := by
    rw [← inner_neg_right, neg_sub]
  have h2 : ‖P z - y‖ ^ 2 ≤ ‖z - y‖ ^ 2 := by nlinarith [sq_nonneg ‖z - P z‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

lemma Proj.normal {X : Set E} {P : E → E} (hP : Proj X P) (z : E) {γ : ℝ} (hγ : 0 < γ) :
    Normal X (P z) (γ⁻¹ • (z - P z)) := by
  intro w hw
  rw [real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hγ.le) (hP.var z w hw)

lemma normal_monotone {X : Set E} {x y ξ ζ : E} (hx : x ∈ X) (hy : y ∈ X)
    (hξ : Normal X x ξ) (hζ : Normal X y ζ) : 0 ≤ ⟪ξ - ζ, x - y⟫ := by
  have h1 := hξ y hy
  have h2 := hζ x hx
  have e : ⟪ξ - ζ, x - y⟫ = -⟪ξ, y - x⟫ - ⟪ζ, x - y⟫ := by
    rw [inner_sub_left, ← inner_neg_right, neg_sub]
  linarith

lemma one_point {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) (x y : E) {ε : ℝ} (hε : 0 < ε)
    (hcap : L1 * ε ≤ 1 / 2) :
    ‖F x - F y‖ * ε ≤ ⟪F x - F y, x - y⟫ + 2 * (L0 + L1 * ‖F y‖) * ε * (‖x - y‖ + ε) := by
  have hL0 := h.L0_pos
  have hL1 := h.L1_nonneg
  have hLy : 0 ≤ L0 + L1 * ‖F y‖ := by positivity
  set d := F x - F y with hd
  by_cases hd0 : d = 0
  · rw [hd0, norm_zero, zero_mul, inner_zero_left, zero_add]
    positivity
  · have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd0
    set v := ‖d‖⁻¹ • d with hv
    have hvn : ‖v‖ = 1 := by
      rw [hv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hdn, inv_mul_cancel₀ hdn.ne']
    have hdv : ⟪d, v⟫ = ‖d‖ := by
      rw [hv, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    set w := y + ε • v with hw
    have hyw : ‖y - w‖ = ε := by
      rw [hw, sub_add_cancel_left, norm_neg, norm_smul, hvn, Real.norm_eq_abs, abs_of_pos hε,
        mul_one]
    have hloc := h.local y w (by rw [hyw]; linarith)
    rw [hyw] at hloc
    set e := F w - F y with he
    have hen : ‖e‖ ≤ 2 * (L0 + L1 * ‖F y‖) * ε := by
      rw [he, norm_sub_rev]
      have : 0 ≤ ‖F y - F w‖ := norm_nonneg _
      nlinarith
    have hmono := h.mono x w
    have e1 : F x - F w = d - e := by rw [hd, he]; abel
    have e2 : x - w = (x - y) - ε • v := by rw [hw]; abel
    rw [e1, e2] at hmono
    have hexp : ⟪d - e, (x - y) - ε • v⟫ =
        ⟪d, x - y⟫ - ε * ⟪d, v⟫ - ⟪e, x - y⟫ + ε * ⟪e, v⟫ := by
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_right]
      ring
    rw [hexp, hdv] at hmono
    have c1 : -⟪e, x - y⟫ ≤ ‖e‖ * ‖x - y‖ := by
      have := real_inner_le_norm (-e) (x - y)
      rw [inner_neg_left, norm_neg] at this
      exact this
    have c2 : ⟪e, v⟫ ≤ ‖e‖ := by
      have := real_inner_le_norm e v
      rw [hvn, mul_one] at this
      exact this
    have hu := norm_nonneg (x - y)
    have c3 : ‖e‖ * ‖x - y‖ ≤ 2 * (L0 + L1 * ‖F y‖) * ε * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right hen hu
    have c4 : ε * ‖e‖ ≤ ε * (2 * (L0 + L1 * ‖F y‖) * ε) := mul_le_mul_of_nonneg_left hen hε.le
    nlinarith [mul_le_mul_of_nonneg_left c2 hε.le]

noncomputable def potential (a x p : E) (S : ℝ) : ℝ :=
  S ^ 2 / 2 * ‖p‖ ^ 2 + S * ⟪p, x - a⟫

section step

variable {F P : E → E} {X : Set E} {L0 L1 : ℝ} {a x ξ : E} {S γ m : ℝ}

lemma anchor_mem (hX : Convex ℝ X) (ha : a ∈ X) (hx : x ∈ X) (hS : 0 ≤ S) (hγ : 0 < γ) :
    anchorPoint a x S γ ∈ X := by
  have hΓ : 0 < S + γ := by linarith
  have e : anchorPoint a x S γ = (S / (S + γ)) • x + (γ / (S + γ)) • a := by
    unfold anchorPoint
    match_scalars <;> field_simp; ring
  rw [e]
  exact hX hx ha (by positivity) (by positivity) (by field_simp)

lemma half_close (h : Hyp F L0 L1) (hS : 0 ≤ S) (hγ : 0 < γ)
    (hD : ‖x - a‖ ≤ (S + γ) * (m - ‖F x‖ - ‖F x + ξ‖))
    (hstep : γ * (L0 + L1 * m) ≤ 1 / 4) :
    ‖halfPoint a x (F x) ξ S γ - x‖ ≤ γ * (m - ‖F x‖) ∧
    ‖F (halfPoint a x (F x) ξ S γ) - F x‖ ≤ m / 3 := by
  have hΓ : 0 < S + γ := by linarith
  have hb0 : 0 ≤ γ / (S + γ) := by positivity
  have ht0 : 0 ≤ S / (S + γ) := by positivity
  have ht1 : S / (S + γ) ≤ 1 := (div_le_one hΓ).mpr (by linarith)
  have hD0 := norm_nonneg (x - a)
  have hp0 := norm_nonneg (F x + ξ)
  have hg0 := norm_nonneg (F x)
  have hm : ‖F x‖ + ‖F x + ξ‖ ≤ m := by
    by_contra hlt
    push Not at hlt
    nlinarith [mul_pos hΓ (sub_pos.mpr hlt)]
  have hm0 : 0 ≤ m := by linarith
  have hL0 := h.L0_pos
  have hL1 := h.L1_nonneg
  have h1 : ‖halfPoint a x (F x) ξ S γ - x‖ ≤ γ * (m - ‖F x‖) := by
    have he : halfPoint a x (F x) ξ S γ - x =
        (γ / (S + γ)) • (a - x) - (S / (S + γ) * γ) • (F x + ξ) := by
      unfold halfPoint anchorPoint
      abel
    rw [he]
    calc ‖(γ / (S + γ)) • (a - x) - (S / (S + γ) * γ) • (F x + ξ)‖
        ≤ ‖(γ / (S + γ)) • (a - x)‖ + ‖(S / (S + γ) * γ) • (F x + ξ)‖ := norm_sub_le _ _
      _ = γ / (S + γ) * ‖x - a‖ + S / (S + γ) * γ * ‖F x + ξ‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb0,
          abs_of_nonneg (mul_nonneg ht0 hγ.le), norm_sub_rev a x]
      _ ≤ γ * (m - ‖F x‖ - ‖F x + ξ‖) + γ * ‖F x + ξ‖ := by
        have k1 : γ / (S + γ) * ‖x - a‖ ≤ γ * (m - ‖F x‖ - ‖F x + ξ‖) := by
          calc γ / (S + γ) * ‖x - a‖ ≤ γ / (S + γ) * ((S + γ) * (m - ‖F x‖ - ‖F x + ξ‖)) :=
                mul_le_mul_of_nonneg_left hD hb0
            _ = γ * (m - ‖F x‖ - ‖F x + ξ‖) := by field_simp
        have k2 : S / (S + γ) * γ * ‖F x + ξ‖ ≤ γ * ‖F x + ξ‖ :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hγ.le ht1) hp0
        linarith
      _ = γ * (m - ‖F x‖) := by ring
  refine ⟨h1, ?_⟩
  have h2 : ‖halfPoint a x (F x) ξ S γ - x‖ ≤ γ * m := h1.trans (by nlinarith)
  have hd0 := norm_nonneg (halfPoint a x (F x) ξ S γ - x)
  have hLd : L1 * ‖x - halfPoint a x (F x) ξ S γ‖ ≤ 1 / 4 := by
    rw [norm_sub_rev]
    have := mul_le_mul_of_nonneg_left h2 hL1
    nlinarith [mul_pos hγ hL0]
  have hloc := h.local x (halfPoint a x (F x) ξ S γ) (by linarith)
  rw [norm_sub_rev x, norm_sub_rev (F x)] at hloc
  rw [norm_sub_rev x] at hLd
  have hN0 := norm_nonneg (F (halfPoint a x (F x) ξ S γ) - F x)
  have hgm : L0 + L1 * ‖F x‖ ≤ L0 + L1 * m := by nlinarith
  have a1 : 3 / 4 * ‖F (halfPoint a x (F x) ξ S γ) - F x‖ ≤
      (L0 + L1 * m) * ‖halfPoint a x (F x) ξ S γ - x‖ := by
    have := mul_le_mul_of_nonneg_right hgm hd0
    nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hLd)]
  have a2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ L0 + L1 * m)
  have a3 := mul_le_mul_of_nonneg_right hstep hm0
  nlinarith


lemma full_bounds (h : Hyp F L0 L1) {X : Set E} (hP : Proj X P) (hX : Convex ℝ X)
    (ha : a ∈ X) (hx : x ∈ X) (hS : 0 ≤ S) (hγ : 0 < γ)
    (hD : ‖x - a‖ ≤ (S + γ) * (m - ‖F x‖ - ‖F x + ξ‖))
    (hstep : γ * (L0 + L1 * m) ≤ 1 / 4) :
    P (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ) = anchorPoint a x S γ -
        γ • (F (halfPoint a x (F x) ξ S γ) +
          γ⁻¹ • (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ -
            P (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ))) ∧
    ‖P (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ) - halfPoint a x (F x) ξ S γ‖ ≤
      4 / 3 * (γ * m) ∧
    ‖F (P (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ)) -
        F (halfPoint a x (F x) ξ S γ)‖ ≤
      ‖P (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ) - halfPoint a x (F x) ξ S γ‖ /
        (2 * γ) := by
  obtain ⟨hz1, hz2⟩ := half_close h hS hγ hD hstep
  set z := halfPoint a x (F x) ξ S γ with hzdef
  set y := anchorPoint a x S γ with hydef
  set w := targetPoint a x (F z) S γ with hwdef
  have hΓ : 0 < S + γ := by linarith
  have ht0 : 0 ≤ S / (S + γ) := by positivity
  have ht1 : S / (S + γ) ≤ 1 := (div_le_one hΓ).mpr (by linarith)
  have hL0 := h.L0_pos
  have hL1 := h.L1_nonneg
  have hg0 := norm_nonneg (F x)
  have hp0 := norm_nonneg (F x + ξ)
  have hm : ‖F x‖ + ‖F x + ξ‖ ≤ m := by
    by_contra hlt
    push Not at hlt
    nlinarith [mul_pos hΓ (sub_pos.mpr hlt), norm_nonneg (x - a)]
  have hm0 : 0 ≤ m := by linarith
  have hy : y ∈ X := anchor_mem hX ha hx hS hγ
  refine ⟨?_, ?_, ?_⟩
  · rw [smul_add, smul_smul, mul_inv_cancel₀ hγ.ne', one_smul, hwdef]
    unfold targetPoint
    rw [← hydef]
    abel
  · have hFz : ‖F z‖ ≤ ‖F x‖ + m / 3 := by
      have := norm_le_insert' (F z) (F x)
      linarith
    have hPy : ‖P w - y‖ ≤ γ * ‖F z‖ := by
      have := hP.dist_le w hy
      have e : w - y = -(γ • F z) := by rw [hwdef]; unfold targetPoint; rw [← hydef]; abel
      rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hγ] at this
      exact this
    have hyz : ‖y - z‖ ≤ γ * ‖F x + ξ‖ := by
      have e : y - z = (S / (S + γ) * γ) • (F x + ξ) := by
        rw [hzdef]; unfold halfPoint; rw [← hydef]; abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 hγ.le)]
      have := mul_le_of_le_one_left hγ.le ht1
      exact mul_le_mul_of_nonneg_right this hp0
    calc ‖P w - z‖ = ‖(P w - y) + (y - z)‖ := by congr 1; abel
      _ ≤ ‖P w - y‖ + ‖y - z‖ := norm_add_le _ _
      _ ≤ γ * (‖F x‖ + m / 3) + γ * ‖F x + ξ‖ := by
          gcongr
          exact hPy.trans (mul_le_mul_of_nonneg_left hFz hγ.le)
      _ ≤ 4 / 3 * (γ * m) := by nlinarith
  · have hFz : ‖F z‖ ≤ 4 / 3 * m := by
      have := norm_le_insert' (F z) (F x)
      linarith
    have hlen : ‖P w - z‖ ≤ 4 / 3 * (γ * m) := by
      have hPy : ‖P w - y‖ ≤ γ * ‖F z‖ := by
        have := hP.dist_le w hy
        have e : w - y = -(γ • F z) := by rw [hwdef]; unfold targetPoint; rw [← hydef]; abel
        rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hγ] at this
        exact this
      have hyz : ‖y - z‖ ≤ γ * ‖F x + ξ‖ := by
        have e : y - z = (S / (S + γ) * γ) • (F x + ξ) := by
          rw [hzdef]; unfold halfPoint; rw [← hydef]; abel
        rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 hγ.le)]
        have := mul_le_of_le_one_left hγ.le ht1
        exact mul_le_mul_of_nonneg_right this hp0
      have hFz' : ‖F z‖ ≤ ‖F x‖ + m / 3 := by
        have := norm_le_insert' (F z) (F x)
        linarith
      calc ‖P w - z‖ = ‖(P w - y) + (y - z)‖ := by congr 1; abel
        _ ≤ ‖P w - y‖ + ‖y - z‖ := norm_add_le _ _
        _ ≤ γ * (‖F x‖ + m / 3) + γ * ‖F x + ξ‖ := by
            gcongr
            exact hPy.trans (mul_le_mul_of_nonneg_left hFz' hγ.le)
        _ ≤ 4 / 3 * (γ * m) := by nlinarith
    have hγm : L1 * (γ * m) ≤ 1 / 4 := by nlinarith [mul_pos hγ hL0]
    have hLd : L1 * ‖z - P w‖ ≤ 1 / 3 := by
      rw [norm_sub_rev]
      have := mul_le_mul_of_nonneg_left hlen hL1
      nlinarith
    have hloc := h.local z (P w) (by linarith)
    rw [norm_sub_rev z, norm_sub_rev (F z)] at hloc
    rw [norm_sub_rev z] at hLd
    have hd0 := norm_nonneg (P w - z)
    have hN0 := norm_nonneg (F (P w) - F z)
    have b1 : (L0 + L1 * ‖F z‖) ≤ 4 / 3 * (L0 + L1 * m) := by nlinarith
    have b2 : 2 / 3 * ‖F (P w) - F z‖ ≤ 4 / 3 * (L0 + L1 * m) * ‖P w - z‖ := by
      have := mul_le_mul_of_nonneg_right b1 hd0
      nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hLd)]
    have b3 : 2 * (L0 + L1 * m) * ‖P w - z‖ ≤ ‖P w - z‖ / (2 * γ) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith

lemma potential_step (h : Hyp F L0 L1) {X : Set E} (hP : Proj X P) (hX : Convex ℝ X)
    (ha : a ∈ X) (hx : x ∈ X) (hξ : Normal X x ξ) (hS : 0 ≤ S) (hγ : 0 < γ)
    (hD : ‖x - a‖ ≤ (S + γ) * (m - ‖F x‖ - ‖F x + ξ‖))
    (hstep : γ * (L0 + L1 * m) ≤ 1 / 4) :
    potential a (P (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ))
        (F (P (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ)) +
          γ⁻¹ • (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ -
            P (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ))) (S + γ) +
      3 / 8 * (S + γ) ^ 2 * ‖(F (halfPoint a x (F x) ξ S γ) +
          γ⁻¹ • (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ -
            P (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ))) -
          (S / (S + γ)) • (F x + ξ)‖ ^ 2 ≤
      potential a x (F x + ξ) S := by
  obtain ⟨hplus, -, hlip⟩ := full_bounds h hP hX ha hx hS hγ hD hstep
  set z := halfPoint a x (F x) ξ S γ with hzdef
  set y := anchorPoint a x S γ with hydef
  set w := targetPoint a x (F z) S γ with hwdef
  set ζ := γ⁻¹ • (w - P w) with hζ
  set q := F z + ζ with hq
  set r := F (P w) + ζ with hr
  set p := F x + ξ with hp
  have hΓ : 0 < S + γ := by linarith
  have hid := anchored_identity (x - a) p q r S γ hΓ.ne' hγ.ne'
  have e1 : (S / (S + γ)) • (x - a) - γ • q = P w - a := by
    rw [hplus, hydef]; unfold anchorPoint
    match_scalars <;> field_simp <;> ring
  have e2 : -((γ / (S + γ)) • (x - a)) - γ • q = P w - x := by
    rw [hplus, hydef]; unfold anchorPoint
    module
  rw [e1, e2] at hid
  have hzw : P w - z = -(γ • (q - (S / (S + γ)) • p)) := by
    rw [hplus, hzdef]; unfold halfPoint; rw [← hydef]
    module
  have hWn : ‖P w - z‖ = γ * ‖q - (S / (S + γ)) • p‖ := by
    rw [hzw, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
  have hrq : r - q = F (P w) - F z := by rw [hr, hq]; abel
  have hlip' : ‖r - q‖ ≤ ‖q - (S / (S + γ)) • p‖ / 2 := by
    rw [hrq]
    have := hlip
    rw [hWn] at this
    calc ‖F (P w) - F z‖ ≤ γ * ‖q - (S / (S + γ)) • p‖ / (2 * γ) := this
      _ = ‖q - (S / (S + γ)) • p‖ / 2 := by field_simp
  have hmono : 0 ≤ ⟪r - p, P w - x⟫ := by
    have hPw : P w ∈ X := hP.mem w
    have hnorm := hP.normal w hγ
    have h1 := h.mono (P w) x
    have h2 := normal_monotone hPw hx hnorm hξ
    have e : r - p = (F (P w) - F x) + (ζ - ξ) := by rw [hr, hp]; abel
    rw [e, inner_add_left]
    linarith
  have hsq : ‖r - q‖ ^ 2 ≤ (‖q - (S / (S + γ)) • p‖ / 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hlip' 2
  have hc1 : 0 ≤ S * (S + γ) / γ := by positivity
  have := mul_nonneg hc1 hmono
  have hc2 : 0 ≤ (S + γ) ^ 2 / 2 := by positivity
  have hW0 := sq_nonneg ‖q - (S / (S + γ)) • p‖
  unfold potential
  nlinarith [mul_le_mul_of_nonneg_left hsq hc2]

lemma distance_step (h : Hyp F L0 L1) {X : Set E} (hP : Proj X P) (hX : Convex ℝ X)
    (ha : a ∈ X) (hx : x ∈ X) (hS : 0 ≤ S) (hγ : 0 < γ)
    (hD : ‖x - a‖ ≤ (S + γ) * (m - ‖F x‖ - ‖F x + ξ‖))
    (hstep : γ * (L0 + L1 * m) ≤ 1 / 4) {xs : E} (hxs : xs ∈ X)
    (hsol : ∀ v ∈ X, 0 ≤ ⟪F xs, v - xs⟫) :
    ‖P (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ) - xs‖ ^ 2 ≤
      γ / (S + γ) * ‖a - xs‖ ^ 2 + S / (S + γ) * ‖x - xs‖ ^ 2 +
        γ * ‖(F (halfPoint a x (F x) ξ S γ) +
          γ⁻¹ • (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ -
            P (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ))) -
          (S / (S + γ)) • (F x + ξ)‖ *
          ‖P (targetPoint a x (F (halfPoint a x (F x) ξ S γ)) S γ) - xs‖ := by
  obtain ⟨hplus, -, hlip⟩ := full_bounds h hP hX ha hx hS hγ hD hstep
  set z := halfPoint a x (F x) ξ S γ with hzdef
  set y := anchorPoint a x S γ with hydef
  set w := targetPoint a x (F z) S γ with hwdef
  set ζ := γ⁻¹ • (w - P w) with hζ
  set q := F z + ζ with hq
  set r := F (P w) + ζ with hr
  set p := F x + ξ with hp
  set t := S / (S + γ) with ht
  have hΓ : 0 < S + γ := by linarith
  have hb : γ / (S + γ) = 1 - t := by rw [ht]; field_simp; ring
  have hid := distance_identity (a - xs) (x - xs) p q t γ
  have e1 : (1 - t) • (a - xs) + t • (x - xs) - γ • q = P w - xs := by
    rw [hplus, hydef, ← hb]; unfold anchorPoint
    rw [ht]
    match_scalars <;> field_simp <;> ring
  have e2 : (1 - t) • (a - xs) + t • (x - xs) - (t * γ) • p = z - xs := by
    rw [hzdef]; unfold halfPoint anchorPoint
    rw [← hb, ht]
    match_scalars <;> field_simp <;> ring
  rw [e1, e2] at hid
  have hzw : z - P w = γ • (q - t • p) := by
    rw [hplus, hzdef]; unfold halfPoint; rw [← hydef, ht]
    module
  have hWn : ‖P w - z‖ = γ * ‖q - t • p‖ := by
    rw [norm_sub_rev, hzw, norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
  have hrq : r - q = F (P w) - F z := by rw [hr, hq]; abel
  have hlip' : ‖r - q‖ ≤ ‖q - t • p‖ / 2 := by
    rw [hrq]
    have := hlip
    rw [hWn] at this
    calc ‖F (P w) - F z‖ ≤ γ * ‖q - t • p‖ / (2 * γ) := this
      _ = ‖q - t • p‖ / 2 := by field_simp
  have hPw : P w ∈ X := hP.mem w
  have hr0 : 0 ≤ ⟪r, P w - xs⟫ := by
    have h1 := h.mono (P w) xs
    have h2 := hsol (P w) hPw
    have h3 := hP.normal w hγ xs hxs
    have e1 : ⟪r, P w - xs⟫ = ⟪F (P w), P w - xs⟫ + ⟪ζ, P w - xs⟫ := by
      rw [hr, inner_add_left]
    have e2 : ⟪F (P w) - F xs, P w - xs⟫ = ⟪F (P w), P w - xs⟫ - ⟪F xs, P w - xs⟫ :=
      inner_sub_left _ _ _
    have e3 : ⟪ζ, xs - P w⟫ = -⟪ζ, P w - xs⟫ := by rw [← inner_neg_right, neg_sub]
    linarith
  have hqx : ⟪q, P w - xs⟫ ≥ -(‖q - t • p‖ / 2 * ‖P w - xs‖) := by
    have e : ⟪q, P w - xs⟫ = ⟪r, P w - xs⟫ - ⟪r - q, P w - xs⟫ := by
      rw [inner_sub_left]; ring
    have := real_inner_le_norm (r - q) (P w - xs)
    have := mul_le_mul_of_nonneg_right hlip' (norm_nonneg (P w - xs))
    linarith
  have hsplit : ⟪q, z - xs⟫ = ⟪q, P w - xs⟫ + γ * ⟪q, q - t • p⟫ := by
    have e : z - xs = (P w - xs) + γ • (q - t • p) := by rw [← hzw]; abel
    rw [e, inner_add_right, real_inner_smul_right]
  have halg : γ ^ 2 * ‖q - t • p‖ ^ 2 - γ ^ 2 * t ^ 2 * ‖p‖ ^ 2 -
      2 * γ * (γ * ⟪q, q - t • p⟫) = -(γ ^ 2 * ‖q‖ ^ 2) := by
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm q p]
    ring
  have hAB : 0 ≤ (1 - t) * t * ‖a - xs - (x - xs)‖ ^ 2 := by
    have : 0 ≤ t := by rw [ht]; positivity
    have : 0 ≤ 1 - t := by rw [← hb]; positivity
    positivity
  rw [hb]
  nlinarith [sq_nonneg ‖q‖, mul_le_mul_of_nonneg_left (le_of_eq rfl : γ ≤ γ) hγ.le]

end step

end OracleTemplate.ConstrainedMonotone

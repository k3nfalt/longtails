import LongTails.Algorithms.AcceleratedDouglasRachford
import Mathlib.Tactic

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.DouglasRachford

open LongTails.Setups.DouglasRachfordSmoothConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma limit_nonneg {A B : ℝ} (hB : 0 ≤ B) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ A + t * B) :
    0 ≤ A := by
  by_contra hA
  push Not at hA
  have hden : 0 < -A + B := by linarith
  have ht0 : 0 < -A / (-A + B) := div_pos (by linarith) hden
  have ht1 : -A / (-A + B) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have h1 := h _ ht0 ht1
  have e : A + -A / (-A + B) * B = -(A ^ 2) / (-A + B) := by
    field_simp
    ring
  rw [e] at h1
  have h2 : -(A ^ 2) / (-A + B) < 0 := div_neg_of_neg_of_pos (by nlinarith) hden
  linarith

lemma gradient_gap {f : E → ℝ} {grad : E → E} {L : ℝ} (hL : 0 < L)
    (hlow : ∀ x y, f x + ⟪grad x, y - x⟫ ≤ f y)
    (hup : ∀ x y, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2) (x z : E) :
    f z + ⟪grad z, x - z⟫ + ‖grad x - grad z‖ ^ 2 / (2 * L) ≤ f x := by
  set d := grad x - grad z with hd
  have h1 := hlow z (x - (1 / L) • d)
  have h2 := hup x (x - (1 / L) • d)
  have e1 : ⟪grad z, x - (1 / L) • d - z⟫ = ⟪grad z, x - z⟫ - 1 / L * ⟪grad z, d⟫ := by
    rw [show x - (1 / L) • d - z = (x - z) - (1 / L) • d by abel, inner_sub_right,
      real_inner_smul_right]
  have e2 : ⟪grad x, x - (1 / L) • d - x⟫ = -(1 / L * ⟪grad x, d⟫) := by
    rw [show x - (1 / L) • d - x = -((1 / L) • d) by abel, inner_neg_right,
      real_inner_smul_right]
  have e3 : ‖x - (1 / L) • d - x‖ ^ 2 = (1 / L) ^ 2 * ‖d‖ ^ 2 := by
    rw [show x - (1 / L) • d - x = -((1 / L) • d) by abel, norm_neg, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
  have e4 : ⟪grad x, d⟫ - ⟪grad z, d⟫ = ‖d‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  rw [e1] at h1
  rw [e2, e3] at h2
  have e5 : L / 2 * ((1 / L) ^ 2 * ‖d‖ ^ 2) = ‖d‖ ^ 2 / (2 * L) := by
    field_simp
  have e6 : 1 / L * ⟪grad x, d⟫ - 1 / L * ⟪grad z, d⟫ = 2 * (‖d‖ ^ 2 / (2 * L)) := by
    rw [← mul_sub, e4]
    field_simp
  linarith

lemma proxF_eq {f : E → ℝ} {grad : E → E} {L γ : ℝ} (hL : 0 < L) (hγ : 0 < γ)
    (hup : ∀ x y, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2) {w x : E}
    (hx : IsMinOn (fun x => f x + ‖x - w‖ ^ 2 / (2 * γ)) univ x) : w - x = γ • grad x := by
  set r := γ • grad x + x - w with hr
  set t := 1 / (γ * L + 1) with ht
  have htpos : 0 < t := by positivity
  have htL : t * (γ * L + 1) = 1 := by
    rw [ht]
    field_simp
  have hmin : f x + ‖x - w‖ ^ 2 / (2 * γ) ≤ f (x - t • r) + ‖x - t • r - w‖ ^ 2 / (2 * γ) :=
    hx (mem_univ (x - t • r))
  have hu := hup x (x - t • r)
  have e2 : ⟪grad x, x - t • r - x⟫ = -(t * ⟪grad x, r⟫) := by
    rw [show x - t • r - x = -(t • r) by abel, inner_neg_right, real_inner_smul_right]
  have e3 : ‖x - t • r - x‖ ^ 2 = t ^ 2 * ‖r‖ ^ 2 := by
    rw [show x - t • r - x = -(t • r) by abel, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
  have e4 : ‖x - t • r - w‖ ^ 2 = ‖x - w‖ ^ 2 - 2 * t * ⟪x - w, r⟫ + t ^ 2 * ‖r‖ ^ 2 := by
    rw [show x - t • r - w = (x - w) - t • r by abel, norm_sub_sq_real, real_inner_smul_right,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have e5 : γ * ⟪grad x, r⟫ + ⟪x - w, r⟫ = ‖r‖ ^ 2 := by
    rw [← real_inner_smul_left, ← inner_add_left, ← real_inner_self_eq_norm_sq, hr]
    congr 1
    abel
  rw [e2, e3] at hu
  rw [e4] at hmin
  set P := (-2 * t * ⟪x - w, r⟫ + t ^ 2 * ‖r‖ ^ 2) / (2 * γ) with hP
  have hP' : P * (2 * γ) = -2 * t * ⟪x - w, r⟫ + t ^ 2 * ‖r‖ ^ 2 :=
    div_mul_cancel₀ _ (by positivity)
  have hsplit : (‖x - w‖ ^ 2 - 2 * t * ⟪x - w, r⟫ + t ^ 2 * ‖r‖ ^ 2) / (2 * γ) =
      ‖x - w‖ ^ 2 / (2 * γ) + P := by
    rw [hP]
    ring
  rw [hsplit] at hmin
  have h0 : 0 ≤ -(t * ⟪grad x, r⟫) + L / 2 * (t ^ 2 * ‖r‖ ^ 2) + P := by linarith
  have h1 : 0 ≤ (-(t * ⟪grad x, r⟫) + L / 2 * (t ^ 2 * ‖r‖ ^ 2) + P) * (2 * γ) :=
    mul_nonneg h0 (by positivity)
  have h2 : (-(t * ⟪grad x, r⟫) + L / 2 * (t ^ 2 * ‖r‖ ^ 2) + P) * (2 * γ) =
      -2 * t * (γ * ⟪grad x, r⟫ + ⟪x - w, r⟫) + t * (t * (γ * L + 1)) * ‖r‖ ^ 2 := by
    rw [add_mul, hP']
    ring
  rw [h2, e5, htL] at h1
  have h3 : ‖r‖ ^ 2 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    nlinarith [mul_pos htpos hpos]
  have h4 : r = 0 := by
    have : ‖r‖ = 0 := by
      have hn := norm_nonneg r
      nlinarith
    exact norm_eq_zero.mp this
  have h5 : γ • grad x + x = w := sub_eq_zero.mp h4
  rw [← h5, add_sub_cancel_right]

lemma proxG_sub {g : E → ℝ} {C : Set E} {γ : ℝ} (hγ : 0 < γ) (hC : Convex ℝ C)
    (hg : ConvexOn ℝ C g) {v y : E} (hyC : y ∈ C)
    (hy : IsMinOn (fun y => g y + ‖y - v‖ ^ 2 / (2 * γ)) C y) :
    ∀ z ∈ C, g y + ⟪(1 / γ) • (v - y), z - y⟫ ≤ g z := by
  intro z hz
  have ei : ⟪(1 / γ) • (v - y), z - y⟫ = -(⟪y - v, z - y⟫ / γ) := by
    rw [real_inner_smul_left, ← neg_sub y v, inner_neg_left]
    ring
  have key : 0 ≤ g z - g y + ⟪y - v, z - y⟫ / γ := by
    apply limit_nonneg (B := ‖z - y‖ ^ 2 / (2 * γ)) (by positivity)
    intro t ht0 ht1
    have hmem : (1 - t) • y + t • z ∈ C := hC hyC hz (by linarith) ht0.le (by ring)
    have hmin : g y + ‖y - v‖ ^ 2 / (2 * γ) ≤
        g ((1 - t) • y + t • z) + ‖(1 - t) • y + t • z - v‖ ^ 2 / (2 * γ) := hy hmem
    have hconv := hg.2 hyC hz (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    simp only [smul_eq_mul] at hconv
    have en : ‖(1 - t) • y + t • z - v‖ ^ 2 =
        ‖y - v‖ ^ 2 + 2 * t * ⟪y - v, z - y⟫ + t ^ 2 * ‖z - y‖ ^ 2 := by
      rw [show (1 - t) • y + t • z - v = (y - v) + t • (z - y) by module, norm_add_sq_real,
        real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have h1 : (‖y - v‖ ^ 2 + 2 * t * ⟪y - v, z - y⟫ + t ^ 2 * ‖z - y‖ ^ 2) / (2 * γ) =
        ‖y - v‖ ^ 2 / (2 * γ) + t * (⟪y - v, z - y⟫ / γ) +
          t * (t * (‖z - y‖ ^ 2 / (2 * γ))) := by
      field_simp
    rw [en, h1] at hmin
    have h2 : 0 ≤ t * (g z - g y + ⟪y - v, z - y⟫ / γ + t * (‖z - y‖ ^ 2 / (2 * γ))) := by
      nlinarith
    by_contra hneg
    push Not at hneg
    exact absurd h2 (not_le.mpr (mul_neg_of_pos_of_neg ht0 hneg))
  rw [ei]
  linarith

lemma star_sub {f g : E → ℝ} {grad : E → E} {C : Set E} {L : ℝ} (hL : 0 < L)
    (hC : Convex ℝ C) (hg : ConvexOn ℝ C g)
    (hup : ∀ x y, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2) {xs : E} (hxs : xs ∈ C)
    (hmin : IsMinOn (fun x => f x + g x) C xs) :
    ∀ z ∈ C, g xs + ⟪-grad xs, z - xs⟫ ≤ g z := by
  intro z hz
  have key : 0 ≤ g z - g xs + ⟪grad xs, z - xs⟫ := by
    apply limit_nonneg (B := L / 2 * ‖z - xs‖ ^ 2) (by positivity)
    intro t ht0 ht1
    have hmem : (1 - t) • xs + t • z ∈ C := hC hxs hz (by linarith) ht0.le (by ring)
    have hm : f xs + g xs ≤ f ((1 - t) • xs + t • z) + g ((1 - t) • xs + t • z) := hmin hmem
    have hconv := hg.2 hxs hz (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    simp only [smul_eq_mul] at hconv
    have hu := hup xs ((1 - t) • xs + t • z)
    have e : (1 - t) • xs + t • z - xs = t • (z - xs) := by module
    rw [e, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hu
    have h2 : 0 ≤ t * (g z - g xs + ⟪grad xs, z - xs⟫ + t * (L / 2 * ‖z - xs‖ ^ 2)) := by
      nlinarith
    by_contra hneg
    push Not at hneg
    exact absurd h2 (not_le.mpr (mul_neg_of_pos_of_neg ht0 hneg))
  rw [inner_neg_left]
  linarith

structure DRPoint (f g : E → ℝ) (grad : E → E) (C : Set E) (γ : ℝ) (w x y : E) : Prop where
  hx : w - x = γ • grad x
  hyC : y ∈ C
  hy : ∀ z ∈ C, g y + ⟪(1 / γ) • (x - y) - grad x, z - y⟫ ≤ g z

noncomputable def res (γ : ℝ) (x y : E) : E := (1 / γ) • (x - y)

noncomputable def env (f g : E → ℝ) (grad : E → E) (γ : ℝ) (x y : E) : ℝ :=
  f x + g y + ⟪grad x, y - x⟫ + ‖y - x‖ ^ 2 / (2 * γ)

lemma drPoint_of_prox {f g : E → ℝ} {grad : E → E} {C : Set E} {L γ : ℝ} (hL : 0 < L)
    (hγ : 0 < γ) (hup : ∀ x y, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hC : Convex ℝ C) (hg : ConvexOn ℝ C g) {w x y : E}
    (hx : IsMinOn (fun x => f x + ‖x - w‖ ^ 2 / (2 * γ)) univ x) (hyC : y ∈ C)
    (hy : IsMinOn (fun y => g y + ‖y - ((2 : ℝ) • x - w)‖ ^ 2 / (2 * γ)) C y) :
    DRPoint f g grad C γ w x y := by
  have h1 := proxF_eq hL hγ hup hx
  refine ⟨h1, hyC, ?_⟩
  have h2 := proxG_sub hγ hC hg hyC hy
  have e : (1 / γ) • ((2 : ℝ) • x - w - y) = (1 / γ) • (x - y) - grad x := by
    have e1 : (2 : ℝ) • x - w - y = (x - y) - (w - x) := by module
    rw [e1, h1, smul_sub, smul_smul, one_div, inv_mul_cancel₀ hγ.ne', one_smul]
  rwa [e] at h2

lemma drPoint_star {f g : E → ℝ} {grad : E → E} {C : Set E} {L γ : ℝ} (hL : 0 < L)
    (hC : Convex ℝ C) (hg : ConvexOn ℝ C g)
    (hup : ∀ x y, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2) {xs : E} (hxs : xs ∈ C)
    (hmin : IsMinOn (fun x => f x + g x) C xs) :
    DRPoint f g grad C γ (xs + γ • grad xs) xs xs := by
  refine ⟨by abel, hxs, ?_⟩
  have h := star_sub hL hC hg hup hxs hmin
  simpa using h

lemma env_identity (dx na nb Ga Gb : E) {γ L : ℝ} (_hγ : γ ≠ 0) (hL : L ≠ 0) :
    (⟪na, -(γ • Ga)⟫ + ‖-(γ • Ga)‖ ^ 2 / (2 * γ)) - (⟪nb, -(γ • Gb)⟫ + ‖-(γ • Gb)‖ ^ 2 / (2 * γ))
      - ⟪Gb, dx + γ • (na - nb)⟫ - γ / 2 * ‖Ga - Gb‖ ^ 2 + L * γ ^ 2 / 2 * ‖Ga + Gb‖ ^ 2
      + ⟪nb, dx⟫ + ‖na - nb‖ ^ 2 / (2 * L) + ⟪Gb - nb, dx - γ • (Ga - Gb)⟫
      = ‖(nb - na) + (L * γ) • (Ga + Gb)‖ ^ 2 / (2 * L) := by
  have c1 : ⟪Gb, na⟫ = ⟪na, Gb⟫ := real_inner_comm _ _
  have c2 : ⟪Gb, nb⟫ = ⟪nb, Gb⟫ := real_inner_comm _ _
  have c3 : ⟪Gb, Ga⟫ = ⟪Ga, Gb⟫ := real_inner_comm _ _
  have c4 : ⟪nb, na⟫ = ⟪na, nb⟫ := real_inner_comm _ _
  simp only [norm_add_sq_real, norm_sub_sq_real, norm_neg, norm_smul, inner_add_right,
    inner_sub_right, inner_sub_left, real_inner_smul_right, inner_neg_right, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_self_eq_norm_sq, c1, c2, c3, c4]
  field_simp
  ring

lemma env_ineq {f g : E → ℝ} {grad : E → E} {C : Set E} {L γ : ℝ} (hL : 0 < L) (hγ : 0 < γ)
    (hlow : ∀ x y, f x + ⟪grad x, y - x⟫ ≤ f y)
    (hup : ∀ x y, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    {wa xa ya wb xb yb : E} (Pa : DRPoint f g grad C γ wa xa ya)
    (Pb : DRPoint f g grad C γ wb xb yb) :
    env f g grad γ xb yb + ⟪res γ xb yb, wa - wb⟫ + γ / 2 * ‖res γ xa ya - res γ xb yb‖ ^ 2
      - L * γ ^ 2 / 2 * ‖res γ xa ya + res γ xb yb‖ ^ 2 ≤ env f g grad γ xa ya := by
  have h1 := gradient_gap hL hlow hup xa xb
  have h2 := Pb.hy ya Pa.hyC
  have hya : ya - xa = -(γ • res γ xa ya) := by
    rw [res, smul_smul, mul_one_div_cancel hγ.ne', one_smul]
    abel
  have hyb : yb - xb = -(γ • res γ xb yb) := by
    rw [res, smul_smul, mul_one_div_cancel hγ.ne', one_smul]
    abel
  have hw : wa - wb = (xa - xb) + γ • (grad xa - grad xb) := by
    have ha := Pa.hx
    have hb := Pb.hx
    rw [smul_sub, ← ha, ← hb]
    abel
  have hy : ya - yb = (xa - xb) - γ • (res γ xa ya - res γ xb yb) := by
    rw [smul_sub, res, res, smul_smul, smul_smul, mul_one_div_cancel hγ.ne', one_smul, one_smul]
    abel
  have hid := env_identity (xa - xb) (grad xa) (grad xb) (res γ xa ya) (res γ xb yb) hγ.ne' hL.ne'
  have hsq : 0 ≤ ‖(grad xb - grad xa) + (L * γ) • (res γ xa ya + res γ xb yb)‖ ^ 2 / (2 * L) := by
    positivity
  rw [hy] at h2
  change f xb + g yb + ⟪grad xb, yb - xb⟫ + ‖yb - xb‖ ^ 2 / (2 * γ) + ⟪res γ xb yb, wa - wb⟫
      + γ / 2 * ‖res γ xa ya - res γ xb yb‖ ^ 2
      - L * γ ^ 2 / 2 * ‖res γ xa ya + res γ xb yb‖ ^ 2
    ≤ f xa + g ya + ⟪grad xa, ya - xa⟫ + ‖ya - xa‖ ^ 2 / (2 * γ)
  rw [hya, hyb, hw]
  have h2' : g yb + ⟪res γ xb yb - grad xb,
      xa - xb - γ • (res γ xa ya - res γ xb yb)⟫ ≤ g ya := h2
  linarith

lemma env_upper {f g : E → ℝ} {grad : E → E} {L γ : ℝ} (hγ : 0 < γ)
    (hup : ∀ x y, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2) (x y : E) :
    f y + g y + γ / 2 * (1 - γ * L) * ‖res γ x y‖ ^ 2 ≤ env f g grad γ x y := by
  have h := hup x y
  have e : ‖res γ x y‖ ^ 2 = ‖y - x‖ ^ 2 / γ ^ 2 := by
    rw [res, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sub_rev]
    field_simp
  have e2 : γ / 2 * (1 - γ * L) * (‖y - x‖ ^ 2 / γ ^ 2) =
      ‖y - x‖ ^ 2 / (2 * γ) - L / 2 * ‖y - x‖ ^ 2 := by
    field_simp
  rw [e, e2, env]
  linarith

end OracleTemplate.DouglasRachford

import LongTails.Proofs.NearZeroSumProjection
import LongTails.Algorithms.NearZeroSumFoam

open scoped RealInnerProductSpace

namespace OracleTemplate.NearZeroSum

open LongTails.Setups.NearZeroSumGames

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def innerPotential (k : ℝ) (x r : E) : ℝ :=
  k * (k + 1) / 2 * ‖r‖ ^ 2 + k * ⟪r, x⟫

set_option maxHeartbeats 1600000 in
lemma projected_eag_identity (k : ℝ) (hk : k + 1 ≠ 0) (x v u a b c n : E) :
    let m := (k / (k + 1)) • x - b - u
    let r := c + m
    innerPotential k x (a + n) - innerPotential (k + 1) u r -
      k * (k + 1) * (⟪c - a, u - x⟫ +
        ⟪(k / (k + 1)) • x - a - v, v - u⟫ + ⟪m, u - x⟫ + ⟪n, x - v⟫) =
      k * (k + 1) / 2 * (‖v - (k / (k + 1)) • x + a + n‖ ^ 2 +
        ‖v - u‖ ^ 2 - ‖b - c‖ ^ 2) + (k + 1) * ⟪b - c, r⟫ := by
  dsimp [innerPotential]
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  field_simp
  ring

lemma projected_eag_recurrence {k V W : ℝ} {t d e r : E} (hk : 1 ≤ k)
    (hdescent : k * (k + 1) / 2 * (‖t‖ ^ 2 + ‖d‖ ^ 2 - ‖e‖ ^ 2) +
      (k + 1) * ⟪e, r⟫ ≤ V - W)
    (hlip : 16 * ‖e‖ ^ 2 ≤ ‖d‖ ^ 2) :
    W ≤ V + ‖r‖ ^ 2 / 8 := by
  have h₁ : 0 ≤ k * (k + 1) / 2 := by positivity
  have h₂ : 2 * (k + 1) ^ 2 ≤ 15 * k * (k + 1) / 2 := by nlinarith
  have h₃ := mul_le_mul_of_nonneg_right h₂ (sq_nonneg ‖e‖)
  have h₄ := mul_le_mul_of_nonneg_left hlip h₁
  have hsq : 0 ≤ ‖(k + 1) • e + (1 / 4 : ℝ) • r‖ ^ 2 := sq_nonneg _
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm r e] at hsq
  simp only [real_inner_self_eq_norm_sq] at hsq
  simp only [real_inner_comm] at hsq hdescent
  nlinarith [mul_nonneg h₁ (sq_nonneg ‖t‖)]

lemma inner_potential_lower {k : ℝ} (hk : 0 ≤ k) {x r s : E}
    (hmono : 0 ≤ ⟪r, x - s⟫) :
    k * (k + 1) / 4 * ‖r‖ ^ 2 ≤ innerPotential k x r + ‖s‖ ^ 2 := by
  have hsq : 0 ≤ ‖(k / 2) • r + s‖ ^ 2 := sq_nonneg _
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm s r] at hsq
  simp only [real_inner_self_eq_norm_sq] at hsq
  have h := mul_nonneg hk hmono
  rw [inner_sub_right] at h
  dsimp [innerPotential]
  simp only [real_inner_comm] at hsq h ⊢
  nlinarith [mul_nonneg hk (sq_nonneg ‖r‖)]

lemma inner_initial_potential (t e : E) :
    innerPotential 1 t (-t + e) = ‖e‖ ^ 2 - ⟪e, t⟫ := by
  simp only [innerPotential, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_neg_left, inner_neg_right, real_inner_comm t e]
  ring

lemma inner_initial_bound {t e : E} {d : ℝ} (hd : 0 ≤ d)
    (ht : ‖t‖ ≤ 5 * d / 4) (he : ‖e‖ ≤ d / 16) :
    innerPotential 1 t (-t + e) ≤ d ^ 2 / 8 := by
  rw [inner_initial_potential]
  have hcs := real_inner_le_norm (-e) t
  rw [inner_neg_left, norm_neg] at hcs
  have hs := mul_self_le_mul_self (norm_nonneg e) he
  have hp := mul_le_mul he ht (norm_nonneg _) (by positivity)
  nlinarith

lemma projected_eag_step {C : Set E} {P A : E → E}
    (hP : ConstrainedMonotone.Proj C P)
    (hmono : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ ⟪A u - A v, u - v⟫)
    (hlip : ∀ u ∈ C, ∀ v ∈ C, ‖A u - A v‖ ≤ ‖u - v‖ / 4)
    {x0 x n : E} (hx : x ∈ C) (hn : ConstrainedMonotone.Normal C x n)
    {k : ℝ} (hk : 1 ≤ k) :
    let b := x0 + (k / (k + 1)) • (x - x0)
    let v := P (b - A x)
    let u := P (b - A v)
    let m := b - A v - u
    innerPotential (k + 1) (u - x0) (A u + m) ≤
      innerPotential k (x - x0) (A x + n) + ‖A u + m‖ ^ 2 / 8 := by
  dsimp only
  let b := x0 + (k / (k + 1)) • (x - x0)
  let v := P (b - A x)
  let u := P (b - A v)
  let m := b - A v - u
  change innerPotential (k + 1) (u - x0) (A u + m) ≤
    innerPotential k (x - x0) (A x + n) + ‖A u + m‖ ^ 2 / 8
  have hv : v ∈ C := hP.mem _
  have hu : u ∈ C := hP.mem _
  have h₁ := hmono u hu x hx
  have h₂ := hP.var (b - A x) u hu
  have h₃ := hP.var (b - A v) x hx
  have h₄ := hn v hv
  change ⟪b - A x - v, u - v⟫ ≤ 0 at h₂
  change ⟪m, x - u⟫ ≤ 0 at h₃
  have hid := projected_eag_identity k (by linarith) (x - x0) (v - x0) (u - x0)
    (A x) (A v) (A u) n
  have hm : (k / (k + 1)) • (x - x0) - A v - (u - x0) = m := by dsimp [m, b]; module
  have hvb : (k / (k + 1)) • (x - x0) - A x - (v - x0) = b - A x - v := by
    dsimp [b]; module
  simp only [hm, hvb, sub_sub_sub_cancel_right] at hid
  have hneg : 0 ≤ ⟪A u - A x, u - x⟫ + ⟪b - A x - v, v - u⟫ +
      ⟪m, u - x⟫ + ⟪n, x - v⟫ := by
    have he₂ : ⟪b - A x - v, v - u⟫ = -⟪b - A x - v, u - v⟫ := by
      rw [← inner_neg_right, neg_sub]
    have he₃ : ⟪m, u - x⟫ = -⟪m, x - u⟫ := by rw [← inner_neg_right, neg_sub]
    have he₄ : ⟪n, x - v⟫ = -⟪n, v - x⟫ := by rw [← inner_neg_right, neg_sub]
    rw [he₂, he₃, he₄]
    linarith
  have hh := mul_nonneg (show 0 ≤ k * (k + 1) by positivity) hneg
  apply projected_eag_recurrence hk
    (t := v - x0 - (k / (k + 1)) • (x - x0) + A x + n)
    (d := v - u) (e := A v - A u) (r := A u + m)
  · linarith
  · have hl := hlip v hv u hu
    have hs := mul_self_le_mul_self (norm_nonneg _) hl
    nlinarith

lemma inner_scalar_step {k C V W R : ℝ} (hk : 1 ≤ k) (hC : 0 ≤ C)
    (hV : k * V ≤ (2 * k - 1) * C)
    (hlower : (k + 1) * (k + 2) * R ≤ 4 * W)
    (hstep : W ≤ V + R / 8) :
    (k + 1) * W ≤ (2 * k + 1) * C := by
  let d := 2 * (k + 1) * (k + 2)
  have hd : 0 < d - 1 := by dsimp [d]; nlinarith
  have h₁ : (d - 1) * W ≤ d * V := by
    have h := mul_le_mul_of_nonneg_left hstep (show 0 ≤ d by dsimp [d]; positivity)
    dsimp [d] at h ⊢
    nlinarith
  have h₂ := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ k * (k + 1) by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hV
    (show 0 ≤ d * (k + 1) by dsimp [d]; positivity)
  have h₄ : 0 ≤ (5 * k + 4) * C := mul_nonneg (by linarith) hC
  apply (mul_le_mul_iff_right₀ (show 0 < k * (d - 1) by positivity)).mp
  dsimp [d] at h₂ h₃ ⊢
  nlinarith

lemma inner_rate {V R : ℕ → ℝ} {B C : ℝ}
    (hC : 0 ≤ C) (hbase : V 1 + B ≤ C)
    (hR : ∀ k, 0 ≤ R k)
    (hlower : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * (k + 1) * R k ≤ 4 * (V k + B))
    (hstep : ∀ k, 1 ≤ k → V (k + 1) ≤ V k + R (k + 1) / 8)
    {k : ℕ} (hk : 1 ≤ k) : (k : ℝ) ^ 2 * R k ≤ 8 * C := by
  have hbound : ∀ j : ℕ, 1 ≤ j → (j : ℝ) * (V j + B) ≤ (2 * j - 1) * C := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => norm_num; exact hbase
    | succ j hj ih =>
      have h := inner_scalar_step (k := (j : ℝ)) (by exact_mod_cast hj) hC ih
        (by convert hlower (j + 1) (by omega) using 1; push_cast; ring)
        (show V (j + 1) + B ≤ (V j + B) + R (j + 1) / 8 by linarith [hstep j hj])
      convert h using 1 <;> push_cast <;> ring
  have hkb : (k : ℝ) * (V k + B) ≤ 2 * k * C := by
    have h := hbound k hk
    nlinarith
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hvb : V k + B ≤ 2 * C := by nlinarith
  have hl := hlower k hk
  nlinarith [mul_nonneg hkpos.le (hR k)]

lemma eag_iterate_mem {C : Set E} {P A : E → E} (hP : ConstrainedMonotone.Proj C P)
    {u0 : E} (h0 : u0 ∈ C) (k : ℕ) : eagIterate P A u0 k ∈ C := by
  cases k with
  | zero => exact h0
  | succ k => exact hP.mem _

lemma eag_normal_mem {C : Set E} {P A : E → E} (hP : ConstrainedMonotone.Proj C P)
    (u0 : E) (k : ℕ) :
    ConstrainedMonotone.Normal C (eagIterate P A u0 k) (eagNormal P A u0 k) := by
  cases k with
  | zero => intro v hv; simp [eagNormal]
  | succ k => exact hP.var _

lemma eag_initial_bound {C : Set E} {P A : E → E}
    (hP : ConstrainedMonotone.Proj C P)
    (hlip : ∀ u ∈ C, ∀ v ∈ C, ‖A u - A v‖ ≤ ‖u - v‖ / 4)
    {u0 s : E} (h0 : u0 ∈ C) (hs : s ∈ C)
    (hsol : ConstrainedMonotone.Normal C s (-A s)) :
    innerPotential 1 (eagIterate P A u0 1 - u0)
      (A (eagIterate P A u0 1) + eagNormal P A u0 1) + ‖u0 - s‖ ^ 2 ≤
      2 * ‖u0 - s‖ ^ 2 := by
  let v := P (u0 - A u0)
  let u := P (u0 - A v)
  have hv : v ∈ C := hP.mem _
  have hu : u ∈ C := hP.mem _
  have hu₁ : eagIterate P A u0 1 = u := by simp [eagIterate, eagAnchor, u, v]
  have hn₁ : eagNormal P A u0 1 = u0 - A v - u := by
    simp [eagNormal, eagIterate, eagAnchor, u, v]
  have hfix : P (s - A s) = s := by
    simpa [sub_eq_add_neg] using projection_fixed_of_normal hP hs hsol (show (0 : ℝ) ≤ 1 by norm_num)
  have huv : ‖u - v‖ ≤ ‖v - u0‖ / 4 := by
    have h := projection_nonexpansive hP (u0 - A v) (u0 - A u0)
    have he : (u0 - A v) - (u0 - A u0) = -(A v - A u0) := by module
    rw [he, norm_neg] at h
    exact h.trans (hlip v hv u0 h0)
  have ht : ‖u - u0‖ ≤ 5 * ‖v - u0‖ / 4 := by
    have h := dist_triangle u v u0
    simp only [dist_eq_norm] at h
    linarith
  have he : ‖A u - A v‖ ≤ ‖v - u0‖ / 16 := by
    have h := hlip u hu v hv
    linarith
  have hvs : ‖v - s‖ ≤ 5 * ‖u0 - s‖ / 4 := by
    have h := projection_nonexpansive hP (u0 - A u0) (s - A s)
    rw [hfix] at h
    have hh : (u0 - A u0) - (s - A s) = (u0 - s) - (A u0 - A s) := by module
    rw [hh] at h
    have hn := norm_sub_le (u0 - s) (A u0 - A s)
    have hl := hlip u0 h0 s hs
    dsimp [v]
    linarith
  have hd : ‖v - u0‖ ≤ 9 * ‖u0 - s‖ / 4 := by
    have h := dist_triangle v s u0
    simp only [dist_eq_norm] at h
    rw [norm_sub_rev s u0] at h
    linarith
  have hb := inner_initial_bound (norm_nonneg (v - u0)) ht he
  have hd₂ := mul_self_le_mul_self (norm_nonneg (v - u0)) hd
  rw [hu₁, hn₁]
  have hr : A u + (u0 - A v - u) = -(u - u0) + (A u - A v) := by module
  rw [hr]
  nlinarith [sq_nonneg ‖u0 - s‖]

lemma eag_residual_pairing {C : Set E} {P A : E → E}
    (hP : ConstrainedMonotone.Proj C P)
    (hmono : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ ⟪A u - A v, u - v⟫)
    {u0 s : E} (h0 : u0 ∈ C) (hs : s ∈ C)
    (hsol : ConstrainedMonotone.Normal C s (-A s)) (k : ℕ) :
    0 ≤ ⟪A (eagIterate P A u0 k) + eagNormal P A u0 k, eagIterate P A u0 k - s⟫ := by
  have hu := eag_iterate_mem (A := A) hP h0 k
  have hn := eag_normal_mem (A := A) hP u0 k
  have h₁ := hmono _ hu s hs
  have h₂ := ConstrainedMonotone.normal_monotone hu hs hn hsol
  simp only [inner_sub_left, inner_neg_left] at h₁ h₂
  rw [inner_add_left]
  linarith

lemma eag_potential_recurrence {C : Set E} {P A : E → E}
    (hP : ConstrainedMonotone.Proj C P)
    (hmono : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ ⟪A u - A v, u - v⟫)
    (hlip : ∀ u ∈ C, ∀ v ∈ C, ‖A u - A v‖ ≤ ‖u - v‖ / 4)
    {u0 : E} (h0 : u0 ∈ C) {k : ℕ} (hk : 1 ≤ k) :
    innerPotential (k + 1) (eagIterate P A u0 (k + 1) - u0)
        (A (eagIterate P A u0 (k + 1)) + eagNormal P A u0 (k + 1)) ≤
      innerPotential k (eagIterate P A u0 k - u0)
        (A (eagIterate P A u0 k) + eagNormal P A u0 k) +
      ‖A (eagIterate P A u0 (k + 1)) + eagNormal P A u0 (k + 1)‖ ^ 2 / 8 := by
  exact projected_eag_step hP hmono hlip (eag_iterate_mem hP h0 k)
    (eag_normal_mem hP u0 k) (by exact_mod_cast hk)

lemma eag_residual_rate {C : Set E} {P A : E → E}
    (hP : ConstrainedMonotone.Proj C P)
    (hmono : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ ⟪A u - A v, u - v⟫)
    (hlip : ∀ u ∈ C, ∀ v ∈ C, ‖A u - A v‖ ≤ ‖u - v‖ / 4)
    {u0 s : E} (h0 : u0 ∈ C) (hs : s ∈ C)
    (hsol : ConstrainedMonotone.Normal C s (-A s)) {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) ^ 2 * ‖A (eagIterate P A u0 k) + eagNormal P A u0 k‖ ^ 2 ≤
      16 * ‖u0 - s‖ ^ 2 := by
  let R := fun j => ‖A (eagIterate P A u0 j) + eagNormal P A u0 j‖ ^ 2
  let V := fun j : ℕ => innerPotential j (eagIterate P A u0 j - u0)
    (A (eagIterate P A u0 j) + eagNormal P A u0 j)
  have hlow : ∀ j : ℕ, 1 ≤ j → (j : ℝ) * (j + 1) * R j ≤ 4 * (V j + ‖u0 - s‖ ^ 2) := by
    intro j hj
    have hm := eag_residual_pairing hP hmono h0 hs hsol j
    have h := inner_potential_lower (k := (j : ℝ)) (by positivity)
      (x := eagIterate P A u0 j - u0) (s := s - u0)
      (by simpa only [sub_sub_sub_cancel_right] using hm)
    rw [norm_sub_rev s u0] at h
    dsimp [R, V]
    linarith
  have h := inner_rate (V := V) (R := R) (B := ‖u0 - s‖ ^ 2) (C := 2 * ‖u0 - s‖ ^ 2)
    (by positivity) (by simpa only [V, Nat.cast_one] using eag_initial_bound hP hlip h0 hs hsol)
    (fun j => sq_nonneg _) hlow
    (fun j hj => by simpa only [V, R, Nat.cast_add, Nat.cast_one] using
      eag_potential_recurrence hP hmono hlip h0 hj) hk
  dsimp [R] at h
  linarith

lemma strong_residual_distance {C : Set E} {A : E → E} {ρ : ℝ}
    (hstrong : ∀ u ∈ C, ∀ v ∈ C, ρ * ‖u - v‖ ^ 2 ≤ ⟪A u - A v, u - v⟫)
    {u s n : E} (hu : u ∈ C) (hs : s ∈ C)
    (hn : ConstrainedMonotone.Normal C u n)
    (hsol : ConstrainedMonotone.Normal C s (-A s)) :
    ρ * ‖u - s‖ ≤ ‖A u + n‖ := by
  have hm := hstrong u hu s hs
  have hh := ConstrainedMonotone.normal_monotone hu hs hn hsol
  have hc := real_inner_le_norm (A u + n) (u - s)
  simp only [inner_sub_left, inner_neg_left, inner_add_left] at hm hh hc
  by_cases hzero : ‖u - s‖ = 0
  · rw [hzero, mul_zero]; exact norm_nonneg _
  · have hpos : 0 < ‖u - s‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith

lemma eag_relative_certificate {C : Set E} {P A : E → E} {ρ : ℝ}
    (hP : ConstrainedMonotone.Proj C P) (hρ : 0 < ρ)
    (hstrong : ∀ u ∈ C, ∀ v ∈ C, ρ * ‖u - v‖ ^ 2 ≤ ⟪A u - A v, u - v⟫)
    (hlip : ∀ u ∈ C, ∀ v ∈ C, ‖A u - A v‖ ≤ ‖u - v‖ / 4)
    {anchor s : E} (hs : s ∈ C) (hsol : ConstrainedMonotone.Normal C s (-A s))
    {k : ℕ} (hk : 1 ≤ k) (hK : 16 ≤ ρ * k) :
    let u := eagIterate P A (P anchor) k
    let n := eagNormal P A (P anchor) k
    ‖A u + n‖ ≤ ρ * ‖u - anchor‖ := by
  dsimp only
  let u := eagIterate P A (P anchor) k
  let n := eagNormal P A (P anchor) k
  change ‖A u + n‖ ≤ ρ * ‖u - anchor‖
  have hmono : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ ⟪A u - A v, u - v⟫ := by
    intro u hu v hv
    exact (mul_nonneg hρ.le (sq_nonneg _)).trans (hstrong u hu v hv)
  have hr := eag_residual_rate hP hmono hlip (hP.mem anchor) hs hsol hk
  have hd := hP.dist_le anchor hs
  have hd₂ := mul_self_le_mul_self (norm_nonneg _) hd
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkr : (k : ℝ) * ‖A u + n‖ ≤ 4 * ‖anchor - s‖ := by
    dsimp [u, n]
    nlinarith [norm_nonneg (A (eagIterate P A (P anchor) k) + eagNormal P A (P anchor) k),
      norm_nonneg (anchor - s)]
  have hrD : 4 * ‖A u + n‖ ≤ ρ * ‖anchor - s‖ := by
    have h₁ := mul_le_mul_of_nonneg_left hkr hρ.le
    have h₂ := mul_le_mul_of_nonneg_right hK (norm_nonneg (A u + n))
    nlinarith
  have hu := eag_iterate_mem (A := A) hP (hP.mem anchor) k
  have hn := eag_normal_mem (A := A) hP (P anchor) k
  have hdist := strong_residual_distance hstrong hu hs hn hsol
  have htri := dist_triangle anchor u s
  simp only [dist_eq_norm, norm_sub_rev anchor u] at htri
  have hmul := mul_le_mul_of_nonneg_left htri hρ.le
  change ρ * ‖u - s‖ ≤ ‖A u + n‖ at hdist
  nlinarith [norm_nonneg (A u + n)]


lemma eag_unscaled_certificate {C : Set E} {P A : E → E} {ρ L η : ℝ}
    (hC : IsComplete C) (hne : C.Nonempty) (hP : ConstrainedMonotone.Proj C P)
    (hρ : 0 < ρ) (hL : ρ ≤ L) (hη : 0 < η) (hηL : η * L ≤ 1 / 4)
    (hstrong : ∀ u ∈ C, ∀ v ∈ C, ρ * ‖u - v‖ ^ 2 ≤ ⟪A u - A v, u - v⟫)
    (hlip : ∀ u ∈ C, ∀ v ∈ C, ‖A u - A v‖ ≤ L * ‖u - v‖)
    (anchor : E) {k : ℕ} (hk : 1 ≤ k) (hK : 16 ≤ η * ρ * k) :
    let u := eagIterate P (fun u => η • A u) (P anchor) k
    let n := (1 / η) • eagNormal P (fun u => η • A u) (P anchor) k
    u ∈ C ∧ ConstrainedMonotone.Normal C u n ∧ ‖A u + n‖ ≤ ρ * ‖u - anchor‖ := by
  obtain ⟨s, hs, hsol⟩ := strongly_monotone_vi_exists hC hne hP hρ hL hstrong hlip
  have hstrong' : ∀ u ∈ C, ∀ v ∈ C,
      (η * ρ) * ‖u - v‖ ^ 2 ≤ ⟪η • A u - η • A v, u - v⟫ := by
    intro u hu v hv
    rw [← smul_sub, real_inner_smul_left]
    have h := mul_le_mul_of_nonneg_left (hstrong u hu v hv) hη.le
    nlinarith only [h]
  have hlip' : ∀ u ∈ C, ∀ v ∈ C, ‖η • A u - η • A v‖ ≤ ‖u - v‖ / 4 := by
    intro u hu v hv
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    have h := mul_le_mul_of_nonneg_left (hlip u hu v hv) hη.le
    have hh := mul_le_mul_of_nonneg_right hηL (norm_nonneg (u - v))
    nlinarith only [h, hh]
  have hnsol : ConstrainedMonotone.Normal C s (-(η • A s)) := by
    intro v hv
    rw [← smul_neg, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos hη.le (hsol v hv)
  have hcert := eag_relative_certificate hP (mul_pos hη hρ) hstrong' hlip' hs hnsol hk hK
    (anchor := anchor)
  have hnormal := eag_normal_mem (A := fun u => η • A u) hP (P anchor) k
  dsimp only at hcert ⊢
  refine ⟨eag_iterate_mem hP (hP.mem anchor) k, ?_, ?_⟩
  · intro v hv
    rw [real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hnormal v hv)
  · have hid : η • (A (eagIterate P (fun u => η • A u) (P anchor) k) +
        (1 / η) • eagNormal P (fun u => η • A u) (P anchor) k) =
        η • A (eagIterate P (fun u => η • A u) (P anchor) k) +
          eagNormal P (fun u => η • A u) (P anchor) k := by
      rw [smul_add, smul_smul, mul_one_div_cancel hη.ne', one_smul]
    rw [← hid, norm_smul, Real.norm_eq_abs, abs_of_pos hη] at hcert
    nlinarith only [hcert, hη]

end OracleTemplate.NearZeroSum

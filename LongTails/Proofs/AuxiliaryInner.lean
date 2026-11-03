import LongTails.Proofs.GuardedAcceleratedGeometry
import LongTails.Proofs.AuxiliaryCertificates

namespace LongTails.Proofs.AuxiliaryInner

open scoped RealInnerProductSpace
open LongTails.Algorithms.GuardedMetricAcceleration LongTails.Proofs.GuardedAcceleratedGeometry
open LongTails.Proofs.AuxiliaryCertificates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_quad_lower {c : ℝ} (hc : 0 < c) (g d : E) :
    -(‖g‖ ^ 2 / (4 * c)) ≤ ⟪g, d⟫ + c * ‖d‖ ^ 2 := by
  have key : 0 ≤ 4 * c ^ 2 * ‖d‖ ^ 2 + 4 * c * ⟪g, d⟫ + ‖g‖ ^ 2 := by
    have h := sq_nonneg ‖(2 * c) • d + g‖
    rw [norm_add_sq_real, norm_smul, real_inner_smul_left, real_inner_comm, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * c)] at h
    nlinarith
  have he : ⟪g, d⟫ + c * ‖d‖ ^ 2 + ‖g‖ ^ 2 / (4 * c) =
      (4 * c ^ 2 * ‖d‖ ^ 2 + 4 * c * ⟪g, d⟫ + ‖g‖ ^ 2) / (4 * c) := by
    field_simp
    ring
  have := div_nonneg key (by positivity : (0 : ℝ) ≤ 4 * c)
  linarith

lemma norm_sub_sq_le (a b : E) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 := norm_add_sq_real a b
  have h2 := norm_sub_sq_real a b
  nlinarith [sq_nonneg ‖a + b‖]

lemma norm_add_sq_le (a b : E) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 := norm_add_sq_real a b
  have h2 := norm_sub_sq_real a b
  nlinarith [sq_nonneg ‖a - b‖]

section Cheap

variable [CompleteSpace E]

lemma cheap_descent {Ψ : E → ℝ} {dΨ : E → E} {M : ℝ} (hM : 0 < M)
    (hg : ∀ x, HasGradientAt Ψ (dΨ x) x) (hl : ∀ x y, ‖dΨ x - dΨ y‖ ≤ M * ‖x - y‖)
    (z : ℕ → E) (hz : ∀ i, z (i + 1) = z i - (1 / M) • dΨ (z i)) (i : ℕ) :
    Ψ (z (i + 1)) ≤ Ψ (z i) - ‖dΨ (z i)‖ ^ 2 / (2 * M) := by
  rw [hz i]
  exact OracleTemplate.Gradient.descent hM hg hl (z i)

lemma cheap_mono {Ψ : E → ℝ} {dΨ : E → E} {M : ℝ} (hM : 0 < M)
    (hg : ∀ x, HasGradientAt Ψ (dΨ x) x) (hl : ∀ x y, ‖dΨ x - dΨ y‖ ≤ M * ‖x - y‖)
    (z : ℕ → E) (hz : ∀ i, z (i + 1) = z i - (1 / M) • dΨ (z i)) (i k : ℕ) :
    Ψ (z (i + k)) ≤ Ψ (z i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h := cheap_descent hM hg hl z hz (i + k)
      have : 0 ≤ ‖dΨ (z (i + k))‖ ^ 2 / (2 * M) := by positivity
      rw [← add_assoc]
      linarith

lemma cheap_first {Ψ : E → ℝ} {dΨ : E → E} {M : ℝ} (hM : 0 < M)
    (hg : ∀ x, HasGradientAt Ψ (dΨ x) x) (hl : ∀ x y, ‖dΨ x - dΨ y‖ ≤ M * ‖x - y‖)
    (z : ℕ → E) (hz : ∀ i, z (i + 1) = z i - (1 / M) • dΨ (z i)) (k : ℕ) :
    Ψ (z (k + 1)) ≤ Ψ (z 0) - ‖dΨ (z 0)‖ ^ 2 / (2 * M) := by
  have h1 := cheap_descent hM hg hl z hz 0
  have h2 := cheap_mono hM hg hl z hz 1 k
  rw [add_comm k 1]
  linarith

lemma cheap_rate {Ψ : E → ℝ} {dΨ : E → E} {M c : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hcM : 2 * c ≤ M)
    (hg : ∀ x, HasGradientAt Ψ (dΨ x) x) (hl : ∀ x y, ‖dΨ x - dΨ y‖ ≤ M * ‖x - y‖)
    (z : ℕ → E) (hz : ∀ i, z (i + 1) = z i - (1 / M) • dΨ (z i)) (N : ℕ)
    (hguard : ∀ i < N, c * ‖z N - z i‖ ^ 2 ≤ breg Ψ dΨ (z N) (z i)) (i : ℕ) (hi : i + 1 ≤ N) :
    ‖dΨ (z i)‖ ^ 2 ≤ 2 * M * ((1 - 2 * c / M) ^ i * (‖dΨ (z 0)‖ ^ 2 / (4 * c))) := by
  set κ := 2 * c / M
  have hκ : κ ≤ 1 := by rw [div_le_one hM]; exact hcM
  have hκ0 : 0 ≤ 1 - κ := sub_nonneg.mpr hκ
  have he : ∀ j < N, Ψ (z j) - Ψ (z N) ≤ ‖dΨ (z j)‖ ^ 2 / (4 * c) := by
    intro j hj
    have h1 := hguard j hj
    have h2 := inner_quad_lower hc (dΨ (z j)) (z N - z j)
    simp only [breg] at h1
    linarith
  have hstep : ∀ j < N, Ψ (z (j + 1)) - Ψ (z N) ≤ (1 - κ) * (Ψ (z j) - Ψ (z N)) := by
    intro j hj
    have h1 := he j hj
    have h2 := cheap_descent hM hg hl z hz j
    have h3 : ‖dΨ (z j)‖ ^ 2 / (2 * M) = κ * (‖dΨ (z j)‖ ^ 2 / (4 * c)) := by
      simp only [κ]; field_simp; ring
    have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ κ)
    nlinarith
  have hpow : ∀ j, j + 1 ≤ N → Ψ (z j) - Ψ (z N) ≤ (1 - κ) ^ j * (Ψ (z 0) - Ψ (z N)) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
        intro hj
        have h1 := hstep j (by omega)
        have h2 := mul_le_mul_of_nonneg_left (ih (by omega)) hκ0
        rw [pow_succ]
        nlinarith
  have h0 := he 0 (by omega)
  have hfin := cheap_descent hM hg hl z hz i
  have hmono : Ψ (z N) ≤ Ψ (z (i + 1)) := by
    have := cheap_mono hM hg hl z hz (i + 1) (N - (i + 1))
    rwa [Nat.add_sub_cancel' hi] at this
  have hp := hpow i (by omega)
  have hq := mul_le_mul_of_nonneg_left h0 (pow_nonneg hκ0 i)
  have hdiv : ‖dΨ (z i)‖ ^ 2 / (2 * M) ≤ (1 - κ) ^ i * (‖dΨ (z 0)‖ ^ 2 / (4 * c)) := by linarith
  rwa [div_le_iff₀ (by positivity), mul_comm] at hdiv

end Cheap

lemma dane_identity {ψ : E → ℝ} {dT dψ : E → E} (xj xn w : E) :
    ⟪dT xj, xn - xj⟫ + breg ψ dψ xn xj =
      ⟪dT xj, w - xj⟫ + ⟪dT xj + dψ xn - dψ xj, xn - w⟫ + breg ψ dψ w xj - breg ψ dψ w xn := by
  simp only [breg, inner_add_left, inner_sub_left, inner_sub_right]
  ring

lemma dane_rate {T ψ : E → ℝ} {dT dψ : E → E} {M ζ Rd : ℝ} (hM : 0 < M) (hζ : 0 ≤ ζ)
    (x : ℕ → E) (J : ℕ) (hJ : 1 ≤ J)
    (hrel : ∀ u w, breg T dT u w ≤ breg ψ dψ u w)
    (hsm : breg ψ dψ (x (J + 1)) (x 0) ≤ M / 2 * Rd ^ 2)
    (hsub : ∀ j ≤ J, ⟪dT (x j), x (j + 1) - x j⟫ + breg ψ dψ (x (j + 1)) (x j) ≤
      -(‖dT (x j)‖ ^ 2 / (2 * M)))
    (herr : ∀ j ≤ J, ‖dT (x j) + dψ (x (j + 1)) - dψ (x j)‖ ≤ ζ)
    (hloc : ∀ j ≤ J, ‖x (j + 1) - x (J + 1)‖ ≤ Rd)
    (hguard : ∀ j ≤ J, 2 / 5 * breg ψ dψ (x (J + 1)) (x j) ≤ breg T dT (x (J + 1)) (x j)) :
    ‖dT (x J)‖ ^ 2 ≤ 2 * M * ((3 / 5) ^ J * (M / 2 * Rd ^ 2) + 5 / 2 * ζ * Rd) := by
  set w := x (J + 1)
  set P := fun j => breg ψ dψ w (x j)
  have hdesc : ∀ j ≤ J, T (x (j + 1)) ≤ T (x j) - ‖dT (x j)‖ ^ 2 / (2 * M) := by
    intro j hj
    have h1 := hrel (x (j + 1)) (x j)
    have h2 := hsub j hj
    simp only [breg] at h1 h2 ⊢
    linarith
  have hmono : ∀ j ≤ J + 1, T w ≤ T (x j) := by
    intro j hj
    obtain ⟨k, hk⟩ : ∃ k, J + 1 = j + k := ⟨J + 1 - j, by omega⟩
    have : ∀ k, j + k ≤ J + 1 → T (x (j + k)) ≤ T (x j) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
          intro hk'
          have h1 := hdesc (j + k) (by omega)
          have h2 := ih (by omega)
          have : 0 ≤ ‖dT (x (j + k))‖ ^ 2 / (2 * M) := by positivity
          rw [← add_assoc]
          linarith
    have := this k (by omega)
    simp only [w]
    rwa [hk]
  have hkey : ∀ j ≤ J, T (x (j + 1)) - T w ≤ 3 / 5 * P j - P (j + 1) + ζ * Rd := by
    intro j hj
    have hid := dane_identity (dT := dT) (ψ := ψ) (dψ := dψ) (x j) (x (j + 1)) w
    have h1 := hrel (x (j + 1)) (x j)
    have h2 := hguard j hj
    have h3 : ⟪dT (x j) + dψ (x (j + 1)) - dψ (x j), x (j + 1) - w⟫ ≤ ζ * Rd :=
      (real_inner_le_norm _ _).trans (mul_le_mul (herr j hj) (hloc j hj) (norm_nonneg _) hζ)
    simp only [P, breg] at h1 h2 hid ⊢
    linarith
  have hP : ∀ j ≤ J, P j ≤ (3 / 5) ^ j * P 0 + 5 / 2 * ζ * Rd := by
    intro j
    induction j with
    | zero =>
        intro _
        have : 0 ≤ ζ * Rd := by
          have := (norm_nonneg _).trans (hloc 0 (by omega))
          positivity
        simp only [pow_zero, one_mul]
        linarith
    | succ j ih =>
        intro hj
        have h1 := hkey j (by omega)
        have h2 := hmono (j + 1) (by omega)
        have h3 := ih (by omega)
        rw [pow_succ]
        nlinarith
  have hPJ : 0 ≤ P J := by
    have h1 := hguard J le_rfl
    have h2 := hrel w (x J)
    simp only [P]
    linarith
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
  have h1 := hkey j (by omega)
  have h2 := hP j (by omega)
  have h3 : T w ≤ T (x (j + 1)) - ‖dT (x (j + 1))‖ ^ 2 / (2 * M) := hdesc (j + 1) le_rfl
  have h4 : P 0 ≤ M / 2 * Rd ^ 2 := hsm
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ (3 / 5) ^ (j + 1))
  have hp1 : (3 / 5 : ℝ) ^ (j + 1) = (3 / 5) ^ j * (3 / 5) := pow_succ _ _
  have h6 : 3 / 5 * P j ≤ (3 / 5) ^ (j + 1) * P 0 + 3 / 2 * ζ * Rd := by
    rw [hp1]; nlinarith [h2]
  have hdiv : ‖dT (x (j + 1))‖ ^ 2 / (2 * M) ≤
      (3 / 5) ^ (j + 1) * (M / 2 * Rd ^ 2) + 5 / 2 * ζ * Rd := by
    linarith
  rwa [div_le_iff₀ (by positivity), mul_comm] at hdiv

lemma support_of_guard {g : E → ℝ} {dg : E → E} {α db ϑ : ℝ} (hα : 0 ≤ α) (hαdb : α ≤ 2 * db)
    (hdb : 0 < db) (u v x' G : E) (hx' : x' = v - (2 * db)⁻¹ • G) (hacc : ‖dg x' - G‖ ≤ ϑ)
    (hguard : α / 2 * ‖u - x'‖ ^ 2 ≤ breg g dg u x') :
    g x' + ‖G‖ ^ 2 / (2 * (2 * db)) + ⟪G, u - v⟫ + α / 2 / 2 * ‖u - v‖ ^ 2 ≤
      g u + ϑ * ‖u - x'‖ := by
  set s := (2 * db)⁻¹
  have hs : 0 < s := by positivity
  have h1 : -(ϑ * ‖u - x'‖) ≤ ⟪dg x' - G, u - x'⟫ := by
    have := neg_abs_le ⟪dg x' - G, u - x'⟫
    have h := (abs_real_inner_le_norm (dg x' - G) (u - x')).trans
      (mul_le_mul_of_nonneg_right hacc (norm_nonneg _))
    linarith
  have h2 : u - x' = (u - v) + s • G := by rw [hx']; abel
  have h3 : ⟪G, u - x'⟫ = ⟪G, u - v⟫ + s * ‖G‖ ^ 2 := by
    rw [h2, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have h4 : ‖u - v‖ ^ 2 ≤ 2 * ‖u - x'‖ ^ 2 + 2 * (s ^ 2 * ‖G‖ ^ 2) := by
    have hh : u - v = (u - x') - s • G := by rw [h2]; abel
    rw [hh]
    have := norm_sub_sq_le (u - x') (s • G)
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow] at this
  have h5 : ⟪dg x', u - x'⟫ = ⟪G, u - x'⟫ + ⟪dg x' - G, u - x'⟫ := by
    rw [inner_sub_left]; ring
  have h6 : α * s ≤ 1 := by
    simp only [s]
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    exact hαdb
  have h7 : α / 2 * (s ^ 2 * ‖G‖ ^ 2) ≤ s / 2 * ‖G‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right h6 (by positivity : 0 ≤ s * ‖G‖ ^ 2 / 2)
    nlinarith
  have h8 : ‖G‖ ^ 2 / (2 * (2 * db)) = s / 2 * ‖G‖ ^ 2 := by
    simp only [s]; field_simp
  have h9 := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ α / 2 / 2)
  simp only [breg] at hguard
  rw [h8]
  nlinarith

lemma appa_potential {g : E → ℝ} {a μ L e : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hμ : 0 < μ)
    (hL : 0 < L) (htune : a ^ 2 * L = μ) (he : 0 ≤ e)
    (x z G : ℕ → E) (y c : E) (hx0 : x 0 = y) (hz0 : z 0 = y)
    (hz : ∀ t, z (t + 1) = centerStep a μ (extrapolate a (x t) (z t)) (z t) (G t)) (n : ℕ)
    (hsx : ∀ t < n, g (x (t + 1)) + ‖G t‖ ^ 2 / (2 * L) + ⟪G t, x t - extrapolate a (x t) (z t)⟫ +
      μ / 2 * ‖x t - extrapolate a (x t) (z t)‖ ^ 2 ≤ g (x t) + e)
    (hsc : ∀ t < n, g (x (t + 1)) + ‖G t‖ ^ 2 / (2 * L) + ⟪G t, c - extrapolate a (x t) (z t)⟫ +
      μ / 2 * ‖c - extrapolate a (x t) (z t)‖ ^ 2 ≤ g c + e) :
    g (x n) + μ / 2 * ‖c - z n‖ ^ 2 ≤
      g c + (1 - a) ^ n * (g y - g c + μ / 2 * ‖c - y‖ ^ 2) + e / a := by
  set Q0 := g y - g c + μ / 2 * ‖c - y‖ ^ 2
  have inv : ∀ m ≤ n, ∃ φ, g (x m) ≤ φ ∧
      φ + μ / 2 * ‖c - z m‖ ^ 2 ≤ g c + ((1 - a) ^ m * Q0 + (1 - (1 - a) ^ m) * (e / a)) := by
    intro m
    induction m with
    | zero =>
        intro _
        refine ⟨g y, by rw [hx0], ?_⟩
        rw [hz0]
        have hQ : Q0 = g y - g c + μ / 2 * ‖c - y‖ ^ 2 := rfl
        simp only [pow_zero, one_mul, sub_self, zero_mul, add_zero]
        rw [hQ]
        linarith
    | succ m ih =>
        intro hm
        obtain ⟨φ, hφ1, hφ2⟩ := ih (by omega)
        set v := extrapolate a (x m) (z m)
        set Fv := g (x (m + 1)) + ‖G m‖ ^ 2 / (2 * L)
        refine ⟨minimumUpdate a μ (φ + e) Fv v (z m) (G m), ?_, ?_⟩
        · have hs := hsx m (by omega)
          exact minimum_step (Fx := g (x m) + e) ha.le ha1 hμ hL htune (by linarith)
            (by linarith) (by simp only [Fv]; linarith)
        · have hid := estimate_quadratic_identity (a := a) (φ := φ + e) (Fy := Fv) hμ.ne' c v (z m)
            (G m)
          have hs := hsc m (by omega)
          rw [← hz m] at hid
          have hq1 := mul_le_mul_of_nonneg_left
            (show φ + e + μ / 2 * ‖c - z m‖ ^ 2 ≤
              g c + ((1 - a) ^ m * Q0 + (1 - (1 - a) ^ m) * (e / a)) + e by linarith)
            (sub_nonneg.mpr ha1)
          have hq2 := mul_le_mul_of_nonneg_left
            (show Fv + ⟪G m, c - v⟫ + μ / 2 * ‖c - v‖ ^ 2 ≤ g c + e by simp only [Fv]; linarith)
            ha.le
          have hcalc : (1 - a) * (g c + ((1 - a) ^ m * Q0 + (1 - (1 - a) ^ m) * (e / a)) + e) +
              a * (g c + e) =
              g c + ((1 - a) ^ (m + 1) * Q0 + (1 - (1 - a) ^ (m + 1)) * (e / a)) := by
            field_simp
            ring
          simp only [minimumUpdate] at hid ⊢
          linarith
  obtain ⟨φ, hφ1, hφ2⟩ := inv n le_rfl
  have hp : 0 ≤ (1 - a) ^ n * (e / a) := by
    have := pow_nonneg (sub_nonneg.mpr ha1) n
    positivity
  nlinarith

lemma final_gradient {g : E → ℝ} {dg : E → E} {db ϑ D : ℝ} (hdb : 0 < db) (xT x' : E)
    (hacc : ‖dg x' + (2 * db) • (x' - xT)‖ ≤ ϑ)
    (hdec : g x' + db * ‖x' - xT‖ ^ 2 ≤ g xT) (hD : g xT - g x' ≤ D) :
    ‖dg x'‖ ^ 2 ≤ 2 * ϑ ^ 2 + 8 * db * D := by
  have he : dg x' = (dg x' + (2 * db) • (x' - xT)) - (2 * db) • (x' - xT) := by abel
  have h1 := norm_sub_sq_le (dg x' + (2 * db) • (x' - xT)) ((2 * db) • (x' - xT))
  rw [← he, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * db), mul_pow] at h1
  have h2 : ‖dg x' + (2 * db) • (x' - xT)‖ ^ 2 ≤ ϑ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hacc 2
  have h3 : db * ‖x' - xT‖ ^ 2 ≤ D := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 4 * db)
  nlinarith

end LongTails.Proofs.AuxiliaryInner

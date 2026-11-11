import Mathlib.Tactic

namespace LongTails.Proofs.StrongGrowthAgdLmi

lemma quadForm_nonpos {A B C : ℝ} (hA : A ≤ 0) (hC : C ≤ 0) (hD : B ^ 2 ≤ 4 * A * C) (z d : ℝ) :
    A * z ^ 2 + B * z * d + C * d ^ 2 ≤ 0 := by
  rcases lt_or_eq_of_le hA with hA' | hA'
  · have h1 : 0 ≤ (2 * A * z + B * d) ^ 2 + (4 * A * C - B ^ 2) * d ^ 2 := by
      have : 0 ≤ (4 * A * C - B ^ 2) * d ^ 2 := mul_nonneg (by linarith) (sq_nonneg d)
      nlinarith [sq_nonneg (2 * A * z + B * d)]
    have h2 : (2 * A * z + B * d) ^ 2 + (4 * A * C - B ^ 2) * d ^ 2 =
        (4 * A) * (A * z ^ 2 + B * z * d + C * d ^ 2) := by ring
    rw [h2] at h1
    by_contra h
    have hpos : 0 < A * z ^ 2 + B * z * d + C * d ^ 2 := lt_of_not_ge h
    have := mul_neg_of_neg_of_pos (by linarith : (4 * A : ℝ) < 0) hpos
    linarith
  · subst hA'
    have hB : B = 0 := by nlinarith [sq_nonneg B]
    subst hB
    nlinarith [sq_nonneg d]

lemma s2_A {a θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (ha : -1 / 8 ≤ a) (ha' : a ≤ -θ) :
    (10 * a ^ 2 + 2 * a + 5 * θ - 12) / 20 ≤ 0 := by
  nlinarith

lemma s1_A {a θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (ha : -θ ≤ a) (ha' : a ≤ 1 / 8) :
    (10 * a ^ 2 - 2 * a + 5 * θ - 8) / 20 ≤ 0 := by
  nlinarith
lemma s2_Add {a θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (ha : -1 / 8 ≤ a) (ha' : a ≤ -θ) :
    (10 * a ^ 4 * θ ^ 2 - 20 * a ^ 4 * θ + 10 * a ^ 4 + 2 * a ^ 3 * θ ^ 2 - 4 * a ^ 3 * θ + 2 * a ^ 3 +
      5 * a ^ 2 * θ ^ 3 - 34 * a ^ 2 * θ ^ 2 + 53 * a ^ 2 * θ - 24 * a ^ 2 - 10 * a * θ ^ 3 +
      22 * a * θ ^ 2 - 14 * a * θ + 2 * a + 5 * θ ^ 3 - 15 * θ) / 20 ≤ 0 := by
  have h1 : 0 ≤ -a := by linarith
  have h2 : 0 ≤ 1 / 8 + a := by linarith
  have h3 : 0 ≤ -a - θ := by linarith
  have h4 : 0 ≤ 1 / 8 - θ := by linarith
  nlinarith [mul_nonneg h1 hθ.le, mul_nonneg h1 h1, mul_nonneg (mul_nonneg h1 h1) hθ.le,
    mul_nonneg (mul_nonneg h1 h1) h1, mul_nonneg hθ.le hθ.le, mul_nonneg h2 h1, mul_nonneg h2 hθ.le,
    mul_nonneg h4 hθ.le, mul_nonneg (mul_nonneg h1 h1) (mul_nonneg h1 h1),
    mul_nonneg (mul_nonneg h1 hθ.le) hθ.le, mul_nonneg (mul_nonneg hθ.le hθ.le) hθ.le,
    mul_nonneg (mul_nonneg h1 h1) (mul_nonneg hθ.le hθ.le)]

lemma s2_disc {a θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (ha : -1 / 8 ≤ a) (ha' : a ≤ -θ) :
    0 ≤ -a ^ 3 * θ ^ 2 + 4 * a ^ 3 * θ / 5 + a ^ 3 / 5 + a ^ 2 * θ ^ 3 / 2 - 14 * a ^ 2 * θ ^ 2 / 25 -
      31 * a ^ 2 * θ / 50 - 8 * a ^ 2 / 25 - a * θ ^ 3 + 88 * a * θ ^ 2 / 25 - 62 * a * θ / 25 -
      6 * a / 25 + θ ^ 3 / 2 - 49 * θ ^ 2 / 25 + 9 * θ / 5 := by
  have h1 : 0 ≤ -a := by linarith
  have h2 : 0 ≤ 1 / 8 + a := by linarith
  have h3 : 0 ≤ -a - θ := by linarith
  have h4 : 0 ≤ 1 / 8 - θ := by linarith
  nlinarith [mul_nonneg h1 hθ.le, mul_nonneg h1 h1, mul_nonneg (mul_nonneg h1 h1) hθ.le,
    mul_nonneg (mul_nonneg h1 h1) h1, mul_nonneg hθ.le hθ.le, mul_nonneg h2 h1, mul_nonneg h2 hθ.le,
    mul_nonneg h4 hθ.le, mul_nonneg h4 h1, mul_nonneg (mul_nonneg h1 hθ.le) hθ.le,
    mul_nonneg (mul_nonneg hθ.le hθ.le) hθ.le, mul_nonneg (mul_nonneg h1 h1) (mul_nonneg hθ.le hθ.le),
    mul_nonneg (mul_nonneg h1 h1) (mul_nonneg h1 hθ.le), mul_nonneg h3 hθ.le, mul_nonneg h3 h1]
lemma s1_Add {a θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (ha : -θ ≤ a) (ha' : a ≤ 1 / 8) :
    (10 * a ^ 4 * θ ^ 2 - 20 * a ^ 4 * θ + 10 * a ^ 4 - 2 * a ^ 3 * θ ^ 2 + 4 * a ^ 3 * θ - 2 * a ^ 3 +
      5 * a ^ 2 * θ ^ 3 - 26 * a ^ 2 * θ ^ 2 + 37 * a ^ 2 * θ - 16 * a ^ 2 - 10 * a * θ ^ 3 +
      18 * a * θ ^ 2 - 6 * a * θ - 2 * a + 5 * θ ^ 3 - 15 * θ) / 20 ≤ 0 := by
  have h1 : 0 ≤ a + θ := by linarith
  have h2 : 0 ≤ 1 / 8 - a := by linarith
  have h4 : 0 ≤ 1 / 8 - θ := by linarith
  have ha2 : a ^ 2 ≤ 1 / 64 := by nlinarith
  nlinarith [mul_nonneg h1 hθ.le, mul_nonneg h1 h2, mul_nonneg h2 hθ.le, mul_nonneg hθ.le hθ.le,
    mul_nonneg h4 hθ.le, sq_nonneg a, mul_nonneg (sq_nonneg a) hθ.le, mul_nonneg (sq_nonneg a) h2,
    mul_nonneg (sq_nonneg a) h1, mul_nonneg (mul_nonneg hθ.le hθ.le) hθ.le,
    mul_nonneg (sq_nonneg a) (sq_nonneg a), mul_nonneg (sq_nonneg a) (mul_nonneg hθ.le hθ.le),
    mul_nonneg (mul_nonneg h1 hθ.le) hθ.le, mul_nonneg (mul_nonneg h2 hθ.le) hθ.le]

lemma s1_disc {a θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (ha : -θ ≤ a) (ha' : a ≤ 1 / 8) :
    0 ≤ -a ^ 3 * θ ^ 2 + 6 * a ^ 3 * θ / 5 - a ^ 3 / 5 + a ^ 2 * θ ^ 3 / 2 + a ^ 2 * θ ^ 2 / 25 -
      71 * a ^ 2 * θ / 50 - 3 * a ^ 2 / 25 - a * θ ^ 3 + 63 * a * θ ^ 2 / 25 - 37 * a * θ / 25 +
      4 * a / 25 + θ ^ 3 / 2 - 39 * θ ^ 2 / 25 + 6 * θ / 5 := by
  have h1 : 0 ≤ a + θ := by linarith
  have h2 : 0 ≤ 1 / 8 - a := by linarith
  have h4 : 0 ≤ 1 / 8 - θ := by linarith
  nlinarith [mul_nonneg h1 hθ.le, mul_nonneg h1 h2, mul_nonneg h2 hθ.le, mul_nonneg hθ.le hθ.le,
    mul_nonneg h4 hθ.le, sq_nonneg a, mul_nonneg (sq_nonneg a) hθ.le, mul_nonneg (sq_nonneg a) h2,
    mul_nonneg (sq_nonneg a) h1, mul_nonneg (mul_nonneg hθ.le hθ.le) hθ.le,
    mul_nonneg (mul_nonneg h1 hθ.le) hθ.le, mul_nonneg (mul_nonneg h2 hθ.le) hθ.le,
    mul_nonneg (mul_nonneg h1 h2) hθ.le, mul_nonneg (sq_nonneg a) (mul_nonneg hθ.le hθ.le),
    mul_nonneg (mul_nonneg h1 h2) h1]

lemma lyapunov_step_concave {η θ lam G d : ℝ} (hη : 0 < η) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8)
    (ha : -1 / 8 ≤ η * lam) (ha' : η * lam ≤ -θ) :
    let d' := (1 - θ) * (1 - η * lam) * d - η * G
    let G' := G + lam * d'
    (G * d' + lam / 2 * d' ^ 2) + 3 / 5 * (G' * d' - G * d) + (d' ^ 2 - d ^ 2) / (2 * η)
      ≤ -(θ / (4 * η)) * d' ^ 2 - η / 2 * G' ^ 2 := by
  intro d' G'
  have hηne : η ≠ 0 := hη.ne'
  have key : η * ((G * d' + lam / 2 * d' ^ 2) + 3 / 5 * (G' * d' - G * d) + (d' ^ 2 - d ^ 2) / (2 * η)
      + (θ / (4 * η)) * d' ^ 2 + η / 2 * G' ^ 2) =
      ((10 * (η * lam) ^ 2 + 2 * (η * lam) + 5 * θ - 12) / 20) * (η * G) ^ 2 +
      (-(10 * (η * lam) ^ 3 * θ - 10 * (η * lam) ^ 3 + 2 * (η * lam) ^ 2 * θ - 2 * (η * lam) ^ 2 +
        5 * (η * lam) * θ ^ 2 - 23 * (η * lam) * θ + 18 * (η * lam) - 5 * θ ^ 2 + 11 * θ) / 10) *
        (η * G) * d +
      ((10 * (η * lam) ^ 4 * θ ^ 2 - 20 * (η * lam) ^ 4 * θ + 10 * (η * lam) ^ 4 + 2 * (η * lam) ^ 3 * θ ^ 2 -
        4 * (η * lam) ^ 3 * θ + 2 * (η * lam) ^ 3 + 5 * (η * lam) ^ 2 * θ ^ 3 - 34 * (η * lam) ^ 2 * θ ^ 2 +
        53 * (η * lam) ^ 2 * θ - 24 * (η * lam) ^ 2 - 10 * (η * lam) * θ ^ 3 + 22 * (η * lam) * θ ^ 2 -
        14 * (η * lam) * θ + 2 * (η * lam) + 5 * θ ^ 3 - 15 * θ) / 20) * d ^ 2 := by
    simp only [d', G']
    field_simp
    ring
  have hdisc : (-(10 * (η * lam) ^ 3 * θ - 10 * (η * lam) ^ 3 + 2 * (η * lam) ^ 2 * θ - 2 * (η * lam) ^ 2 +
        5 * (η * lam) * θ ^ 2 - 23 * (η * lam) * θ + 18 * (η * lam) - 5 * θ ^ 2 + 11 * θ) / 10) ^ 2 ≤
      4 * ((10 * (η * lam) ^ 2 + 2 * (η * lam) + 5 * θ - 12) / 20) *
      ((10 * (η * lam) ^ 4 * θ ^ 2 - 20 * (η * lam) ^ 4 * θ + 10 * (η * lam) ^ 4 + 2 * (η * lam) ^ 3 * θ ^ 2 -
        4 * (η * lam) ^ 3 * θ + 2 * (η * lam) ^ 3 + 5 * (η * lam) ^ 2 * θ ^ 3 - 34 * (η * lam) ^ 2 * θ ^ 2 +
        53 * (η * lam) ^ 2 * θ - 24 * (η * lam) ^ 2 - 10 * (η * lam) * θ ^ 3 + 22 * (η * lam) * θ ^ 2 -
        14 * (η * lam) * θ + 2 * (η * lam) + 5 * θ ^ 3 - 15 * θ) / 20) := by
    have h := s2_disc hθ hθ1 ha ha'
    nlinarith [h]
  have hform := quadForm_nonpos (s2_A hθ hθ1 ha ha') (s2_Add hθ hθ1 ha ha') hdisc (η * G) d
  have hle : η * ((G * d' + lam / 2 * d' ^ 2) + 3 / 5 * (G' * d' - G * d) + (d' ^ 2 - d ^ 2) / (2 * η)
      + (θ / (4 * η)) * d' ^ 2 + η / 2 * G' ^ 2) ≤ 0 := by rw [key]; exact hform
  have h2 : (G * d' + lam / 2 * d' ^ 2) + 3 / 5 * (G' * d' - G * d) + (d' ^ 2 - d ^ 2) / (2 * η)
      + (θ / (4 * η)) * d' ^ 2 + η / 2 * G' ^ 2 ≤ 0 := by
    by_contra h
    have hpos := lt_of_not_ge h
    have := mul_pos hη hpos
    linarith
  linarith

lemma lyapunov_step_convex {η θ lam G d : ℝ} (hη : 0 < η) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8)
    (ha : -θ ≤ η * lam) (ha' : η * lam ≤ 1 / 8) :
    let d' := (1 - θ) * (1 - η * lam) * d - η * G
    let G' := G + lam * d'
    (G * d' + lam / 2 * d' ^ 2) + 2 / 5 * (G' * d' - G * d) + (d' ^ 2 - d ^ 2) / (2 * η)
      ≤ -(θ / (4 * η)) * d' ^ 2 - η / 2 * G' ^ 2 := by
  intro d' G'
  have hηne : η ≠ 0 := hη.ne'
  have key : η * ((G * d' + lam / 2 * d' ^ 2) + 2 / 5 * (G' * d' - G * d) + (d' ^ 2 - d ^ 2) / (2 * η)
      + (θ / (4 * η)) * d' ^ 2 + η / 2 * G' ^ 2) =
      ((10 * (η * lam) ^ 2 - 2 * (η * lam) + 5 * θ - 8) / 20) * (η * G) ^ 2 +
      (-(10 * (η * lam) ^ 3 * θ - 10 * (η * lam) ^ 3 - 2 * (η * lam) ^ 2 * θ + 2 * (η * lam) ^ 2 +
        5 * (η * lam) * θ ^ 2 - 17 * (η * lam) * θ + 12 * (η * lam) - 5 * θ ^ 2 + 9 * θ) / 10) *
        (η * G) * d +
      ((10 * (η * lam) ^ 4 * θ ^ 2 - 20 * (η * lam) ^ 4 * θ + 10 * (η * lam) ^ 4 - 2 * (η * lam) ^ 3 * θ ^ 2 +
        4 * (η * lam) ^ 3 * θ - 2 * (η * lam) ^ 3 + 5 * (η * lam) ^ 2 * θ ^ 3 - 26 * (η * lam) ^ 2 * θ ^ 2 +
        37 * (η * lam) ^ 2 * θ - 16 * (η * lam) ^ 2 - 10 * (η * lam) * θ ^ 3 + 18 * (η * lam) * θ ^ 2 -
        6 * (η * lam) * θ - 2 * (η * lam) + 5 * θ ^ 3 - 15 * θ) / 20) * d ^ 2 := by
    simp only [d', G']
    field_simp
    ring
  have hdisc : (-(10 * (η * lam) ^ 3 * θ - 10 * (η * lam) ^ 3 - 2 * (η * lam) ^ 2 * θ + 2 * (η * lam) ^ 2 +
        5 * (η * lam) * θ ^ 2 - 17 * (η * lam) * θ + 12 * (η * lam) - 5 * θ ^ 2 + 9 * θ) / 10) ^ 2 ≤
      4 * ((10 * (η * lam) ^ 2 - 2 * (η * lam) + 5 * θ - 8) / 20) *
      ((10 * (η * lam) ^ 4 * θ ^ 2 - 20 * (η * lam) ^ 4 * θ + 10 * (η * lam) ^ 4 - 2 * (η * lam) ^ 3 * θ ^ 2 +
        4 * (η * lam) ^ 3 * θ - 2 * (η * lam) ^ 3 + 5 * (η * lam) ^ 2 * θ ^ 3 - 26 * (η * lam) ^ 2 * θ ^ 2 +
        37 * (η * lam) ^ 2 * θ - 16 * (η * lam) ^ 2 - 10 * (η * lam) * θ ^ 3 + 18 * (η * lam) * θ ^ 2 -
        6 * (η * lam) * θ - 2 * (η * lam) + 5 * θ ^ 3 - 15 * θ) / 20) := by
    have h := s1_disc hθ hθ1 ha ha'
    nlinarith [h]
  have hform := quadForm_nonpos (s1_A hθ hθ1 ha ha') (s1_Add hθ hθ1 ha ha') hdisc (η * G) d
  have hle : η * ((G * d' + lam / 2 * d' ^ 2) + 2 / 5 * (G' * d' - G * d) + (d' ^ 2 - d ^ 2) / (2 * η)
      + (θ / (4 * η)) * d' ^ 2 + η / 2 * G' ^ 2) ≤ 0 := by rw [key]; exact hform
  have h2 : (G * d' + lam / 2 * d' ^ 2) + 2 / 5 * (G' * d' - G * d) + (d' ^ 2 - d ^ 2) / (2 * η)
      + (θ / (4 * η)) * d' ^ 2 + η / 2 * G' ^ 2 ≤ 0 := by
    by_contra h
    have hpos := lt_of_not_ge h
    have := mul_pos hη hpos
    linarith
  linarith

noncomputable def Q (η lam g0 c z d : ℝ) : ℝ :=
  g0 * z + lam * z ^ 2 / 2 + c * (g0 + lam * z) * d + d ^ 2 / (2 * η)

lemma Q_perturb (η lam g0 c z d ε : ℝ) (hη : η ≠ 0) :
    Q η lam g0 c (z - η * ε) (d - η * ε) =
      Q η lam g0 c z d - η * ε * ((1 + c) * (g0 + lam * z) + (1 + c * (η * lam)) * d / η) +
        η / 2 * (1 + (1 + 2 * c) * (η * lam)) * ε ^ 2 := by
  unfold Q
  field_simp
  ring

lemma young_coef {A B x y : ℝ} (hA : 0 < A) (hAB : 1 ≤ 4 * A * B) :
    x * y ≤ A * x ^ 2 + B * y ^ 2 := by
  have h : 0 ≤ (2 * A * x - y) ^ 2 + (4 * A * B - 1) * y ^ 2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
  have h2 : (2 * A * x - y) ^ 2 + (4 * A * B - 1) * y ^ 2 =
      4 * A * (A * x ^ 2 + B * y ^ 2 - x * y) := by ring
  rw [h2] at h
  have h3 : 0 ≤ A * x ^ 2 + B * y ^ 2 - x * y := by
    by_contra hneg
    have hneg' : A * x ^ 2 + B * y ^ 2 - x * y < 0 := lt_of_not_ge hneg
    have := mul_neg_of_pos_of_neg (by linarith : (0 : ℝ) < 4 * A) hneg'
    linarith
  linarith

lemma aux_one_add_sq {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 3 / 5) : (1 + c) ^ 2 ≤ 64 / 25 := by
  nlinarith

lemma aux_ca_bounds {a c : ℝ} (ha : -1 / 8 ≤ a) (ha' : a ≤ 1 / 8) (hc0 : 0 ≤ c) (hc : c ≤ 3 / 5) :
    -(3 / 40) ≤ c * a ∧ c * a ≤ 3 / 40 := by
  constructor <;> nlinarith

lemma aux_one_add_ca_sq {u : ℝ} (h1 : -(3 / 40) ≤ u) (h2 : u ≤ 3 / 40) : (1 + u) ^ 2 ≤ 29 / 25 := by
  nlinarith

lemma aux_second_order {a c : ℝ} (ha : -1 / 8 ≤ a) (ha' : a ≤ 1 / 8) (hc0 : 0 ≤ c) (hc : c ≤ 3 / 5) :
    0 ≤ 1 + (1 + 2 * c) * a ∧ 1 + (1 + 2 * c) * a ≤ 32 / 25 := by
  constructor <;> nlinarith

lemma aux_sum_sq (δ e : ℝ) : (δ + e) ^ 2 ≤ 2 * δ ^ 2 + 2 * e ^ 2 := by
  nlinarith [sq_nonneg (δ - e)]

lemma aux_disp {θ η ddet d' u : ℝ} (hη : 0 < η) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8)
    (h : ddet = d' + η * u) :
    -(θ / η / 8) * ddet ^ 2 ≤ -(θ / η / 16) * d' ^ 2 + η / 64 * u ^ 2 := by
  subst h
  have h1 : d' ^ 2 / 2 - (η * u) ^ 2 ≤ (d' + η * u) ^ 2 := by
    nlinarith [sq_nonneg (d' + 2 * (η * u))]
  have hr : 0 ≤ θ / η / 8 := by positivity
  have h2 := mul_le_mul_of_nonneg_left h1 hr
  have h3 : θ / η / 8 * (η * u) ^ 2 = θ * η * u ^ 2 / 8 := by field_simp; try ring
  have h4 : θ * η * u ^ 2 / 8 ≤ η / 64 * u ^ 2 := by
    have := mul_le_mul_of_nonneg_right hθ1 (mul_nonneg hη.le (sq_nonneg u))
    nlinarith
  have h5 : θ / η / 8 * (d' ^ 2 / 2) = θ / η / 16 * d' ^ 2 := by ring
  nlinarith [h2, h3, h4, h5]

lemma aux_grad {η a Gw Gdet ghat u : ℝ} (hη : 0 < η) (ha' : a ≤ 1 / 8)
    (hG : Gdet = (1 - a) * Gw) (hGw : Gw = ghat - u) :
    -(3 * η / 8) * Gdet ^ 2 ≤ -(9 / 50 * η * ghat ^ 2) - 1 / 25 * η * Gw ^ 2 + 18 / 25 * η * u ^ 2 := by
  have h78 : 7 / 8 ≤ 1 - a := by linarith
  have hsq : 49 / 64 ≤ (1 - a) ^ 2 := by nlinarith
  have h1 : 153 / 200 * Gw ^ 2 ≤ Gdet ^ 2 := by
    rw [hG]; nlinarith [sq_nonneg Gw]
  have h2 : 3 / 4 * ghat ^ 2 - 3 * u ^ 2 ≤ Gw ^ 2 := by
    rw [hGw]; nlinarith [sq_nonneg (ghat / 2 - 2 * u)]
  have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 3 * η / 8)
  have h5 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 6 / 25 * η)
  nlinarith [h4, h5, mul_nonneg hη.le (sq_nonneg Gw)]

set_option maxHeartbeats 1000000 in
lemma coord_step_of_lmi {η θ lam g0 c z d δ e : ℝ} (hη : 0 < η) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8)
    (ha : -1 / 8 ≤ η * lam) (ha' : η * lam ≤ 1 / 8) (hc0 : 0 ≤ c) (hc : c ≤ 3 / 5)
    (hlmi : let G := g0 + lam * z
      let d' := (1 - θ) * (1 - η * lam) * d - η * G
      let G' := G + lam * d'
      (G * d' + lam / 2 * d' ^ 2) + c * (G' * d' - G * d) + (d' ^ 2 - d ^ 2) / (2 * η)
        ≤ -(θ / (4 * η)) * d' ^ 2 - η / 2 * G' ^ 2) :
    let G := g0 + lam * z
    let Gw := G + lam * ((1 - θ) * d)
    let ghat := Gw + δ + e
    let d' := (1 - θ) * d - η * ghat
    let z' := z + d'
    let ddet := (1 - θ) * (1 - η * lam) * d - η * G
    let Gdet := G + lam * ddet
    Q η lam g0 c z' d' ≤ Q η lam g0 c z d - θ / η / 16 * d' ^ 2 - 9 / 50 * η * ghat ^ 2 -
      1 / 25 * η * Gw ^ 2 - e * (η * (1 + c) * Gdet + (1 + c * (η * lam)) * ddet) +
      (58 / 25 * (η / θ) + 791 / 100 * η) * δ ^ 2 + 279 / 100 * η * e ^ 2 := by
  intro G Gw ghat d' z' ddet Gdet
  have hηne : η ≠ 0 := hη.ne'
  have hθne : θ ≠ 0 := hθ.ne'
  have hd' : d' = ddet - η * (δ + e) := by simp only [d', ddet, ghat, Gw, G]; ring
  have hz' : z' = (z + ddet) - η * (δ + e) := by simp only [z']; rw [hd']; ring
  have hGdet : Gdet = (1 - η * lam) * Gw := by simp only [Gdet, ddet, Gw, G]; ring
  have hGw : Gw = ghat - (δ + e) := by simp only [ghat]; ring
  have hQdet : Q η lam g0 c (z + ddet) ddet - Q η lam g0 c z d ≤
      -(θ / η / 4) * ddet ^ 2 - η / 2 * Gdet ^ 2 := by
    have h := hlmi
    simp only at h
    have hid : Q η lam g0 c (z + ddet) ddet - Q η lam g0 c z d =
        (G * ddet + lam / 2 * ddet ^ 2) + c * (Gdet * ddet - G * d) + (ddet ^ 2 - d ^ 2) / (2 * η) := by
      simp only [Q, Gdet, G]; field_simp; try ring
    have e4 : θ / (4 * η) = θ / η / 4 := by field_simp
    rw [hid, ← e4]; exact h
  have hpert : Q η lam g0 c z' d' = Q η lam g0 c (z + ddet) ddet -
      η * (δ + e) * ((1 + c) * Gdet + (1 + c * (η * lam)) * ddet / η) +
      η / 2 * (1 + (1 + 2 * c) * (η * lam)) * (δ + e) ^ 2 := by
    rw [hz', hd', Q_perturb _ _ _ _ _ _ _ hηne]
    simp only [Gdet, G]; ring
  have hlin : -(η * (δ + e) * ((1 + c) * Gdet + (1 + c * (η * lam)) * ddet / η)) =
      Gdet * (-(η * (1 + c) * δ)) + ddet * (-((1 + c * (η * lam)) * δ)) -
      e * (η * (1 + c) * Gdet + (1 + c * (η * lam)) * ddet) := by
    field_simp; try ring
  have hY1 : Gdet * (-(η * (1 + c) * δ)) ≤ η / 8 * Gdet ^ 2 + 128 / 25 * η * δ ^ 2 := by
    have h := young_coef (A := η / 8) (B := 2 / η) (x := Gdet) (y := -(η * (1 + c) * δ))
      (by positivity) (by field_simp; norm_num)
    have hc2 := aux_one_add_sq hc0 hc
    have h2 : 2 / η * (-(η * (1 + c) * δ)) ^ 2 = 2 * η * ((1 + c) ^ 2 * δ ^ 2) := by
      field_simp; try ring
    have h3 : 2 * η * ((1 + c) ^ 2 * δ ^ 2) ≤ 2 * η * (64 / 25 * δ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc2 (sq_nonneg δ)) (by positivity)
    linarith only [h, h2, h3]
  have hY2 : ddet * (-((1 + c * (η * lam)) * δ)) ≤ θ / η / 8 * ddet ^ 2 + 58 / 25 * (η / θ) * δ ^ 2 := by
    have h := young_coef (A := θ / η / 8) (B := 2 * (η / θ)) (x := ddet)
      (y := -((1 + c * (η * lam)) * δ)) (by positivity) (by field_simp; try norm_num)
    obtain ⟨hu1, hu2⟩ := aux_ca_bounds ha ha' hc0 hc
    have hca := aux_one_add_ca_sq hu1 hu2
    have h2 : 2 * (η / θ) * (-((1 + c * (η * lam)) * δ)) ^ 2 =
        2 * (η / θ) * ((1 + c * (η * lam)) ^ 2 * δ ^ 2) := by ring
    have h3 : 2 * (η / θ) * ((1 + c * (η * lam)) ^ 2 * δ ^ 2) ≤ 2 * (η / θ) * (29 / 25 * δ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hca (sq_nonneg δ)) (by positivity)
    linarith only [h, h2, h3]
  have hsq : η / 2 * (1 + (1 + 2 * c) * (η * lam)) * (δ + e) ^ 2 ≤
      32 / 25 * η * δ ^ 2 + 32 / 25 * η * e ^ 2 := by
    obtain ⟨h3, h1⟩ := aux_second_order ha ha' hc0 hc
    have h2 := aux_sum_sq δ e
    have h4 : η / 2 * (1 + (1 + 2 * c) * (η * lam)) ≤ η / 2 * (32 / 25) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    calc η / 2 * (1 + (1 + 2 * c) * (η * lam)) * (δ + e) ^ 2
        ≤ η / 2 * (32 / 25) * (2 * δ ^ 2 + 2 * e ^ 2) := mul_le_mul h4 h2 (sq_nonneg _) (by positivity)
      _ = 32 / 25 * η * δ ^ 2 + 32 / 25 * η * e ^ 2 := by ring
  have hdd : -(θ / η / 8) * ddet ^ 2 ≤ -(θ / η / 16) * d' ^ 2 + η / 32 * δ ^ 2 + η / 32 * e ^ 2 := by
    have h1 : ddet = d' + η * (δ + e) := by rw [hd']; ring
    have h2 := aux_disp hη hθ hθ1 h1
    have h3 := aux_sum_sq δ e
    have h4 : η / 64 * (δ + e) ^ 2 ≤ η / 64 * (2 * δ ^ 2 + 2 * e ^ 2) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith only [h2, h4]
  have hGG : -(3 * η / 8) * Gdet ^ 2 ≤ -(9 / 50 * η * ghat ^ 2) - 1 / 25 * η * Gw ^ 2 +
      36 / 25 * η * δ ^ 2 + 36 / 25 * η * e ^ 2 := by
    have h2 := aux_grad hη ha' hGdet hGw
    have h3 := aux_sum_sq δ e
    have h4 : 18 / 25 * η * (δ + e) ^ 2 ≤ 18 / 25 * η * (2 * δ ^ 2 + 2 * e ^ 2) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith only [h2, h4]
  rw [hpert, sub_eq_add_neg, hlin]
  have hδ0 : 0 ≤ η * δ ^ 2 := mul_nonneg hη.le (sq_nonneg δ)
  have he0 : 0 ≤ η * e ^ 2 := mul_nonneg hη.le (sq_nonneg e)
  linarith only [hQdet, hY1, hY2, hsq, hdd, hGG, hδ0, he0]

end LongTails.Proofs.StrongGrowthAgdLmi

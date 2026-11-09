import LongTails.Algorithms.BlackBoxDiagonalAccelerated

open scoped BigOperators

namespace OracleTemplate.BlackBoxDiagonal

variable {d : ℕ}

noncomputable def wsq (m : Fin d → ℝ) (v : Vec d) : ℝ := ∑ i, m i * v i ^ 2

noncomputable def isq (m : Fin d → ℝ) (g : Vec d) : ℝ := ∑ i, g i ^ 2 / m i

lemma wsq_nonneg {m : Fin d → ℝ} (hm : ∀ i, 0 < m i) (v : Vec d) : 0 ≤ wsq m v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (sq_nonneg _)

lemma isq_nonneg {m : Fin d → ℝ} (hm : ∀ i, 0 < m i) (g : Vec d) : 0 ≤ isq m g :=
  Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hm i).le

lemma dot_young {m : Fin d → ℝ} (hm : ∀ i, 0 < m i) {t : ℝ} (ht : 0 < t) (g v : Vec d) :
    dot g v ≤ t / 2 * isq m g + 1 / (2 * t) * wsq m v := by
  unfold dot isq wsq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hmi := hm i
  have key : 0 ≤ (t * g i - m i * v i) ^ 2 / (2 * t * m i) := by positivity
  have e : (t * g i - m i * v i) ^ 2 / (2 * t * m i) =
      t / 2 * (g i ^ 2 / m i) + 1 / (2 * t) * (m i * v i ^ 2) - g i * v i := by
    field_simp
    ring
  linarith

lemma isq_le_wsq_of_cocoercive {m : Fin d → ℝ} (hm : ∀ i, 0 < m i) {g v : Vec d}
    (h : isq m g ≤ dot g v) : isq m g ≤ wsq m v := by
  have := dot_young hm one_pos g v
  norm_num at this
  linarith

lemma wsq_le_of_strong_monotone {m : Fin d → ℝ} (hm : ∀ i, 0 < m i) {μ : ℝ} (hμ : 0 < μ)
    {g v : Vec d} (h : μ * wsq m v ≤ dot g v) : wsq m v ≤ isq m g / μ ^ 2 := by
  have hy := dot_young hm (inv_pos.mpr hμ) g v
  have hw := wsq_nonneg hm v
  rw [le_div_iff₀ (by positivity)]
  have e : 1 / (2 * μ⁻¹) = μ / 2 := by field_simp
  rw [e] at hy
  have : μ * wsq m v ≤ μ⁻¹ / 2 * isq m g + μ / 2 * wsq m v := le_trans h hy
  have h2 : μ / 2 * wsq m v ≤ μ⁻¹ / 2 * isq m g := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * μ)
  have e2 : 2 * μ * (μ⁻¹ / 2 * isq m g) = isq m g := by field_simp
  nlinarith [h3, e2]

lemma isq_add3 {m : Fin d → ℝ} (hm : ∀ i, 0 < m i) (a b c : Vec d) :
    isq m (a + b + c) ≤ 3 * (isq m a + isq m b + isq m c) := by
  unfold isq
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hmi := hm i
  simp only [PiLp.add_apply]
  have h1 : (a i + b i + c i) ^ 2 ≤ 3 * (a i ^ 2 + b i ^ 2 + c i ^ 2) := by
    nlinarith [sq_nonneg (a i - b i), sq_nonneg (b i - c i), sq_nonneg (a i - c i)]
  have e : 3 * (a i ^ 2 / m i + b i ^ 2 / m i + c i ^ 2 / m i) =
      3 * (a i ^ 2 + b i ^ 2 + c i ^ 2) / m i := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right h1 hmi.le

section Phase

variable (F : Vec d → ℝ) (G : Vec d → Vec d) (m : Fin d → ℝ) (μ α : ℝ) (x v y : ℕ → Vec d)

noncomputable def lowerModel (k : ℕ) (w : Vec d) : ℝ :=
  F (y k) + dot (G (y k)) (w - y k) + μ / 2 * wsq m (w - y k)

noncomputable def psi : ℕ → Vec d → ℝ
  | 0, w => F (x 0) + μ / 2 * wsq m (w - x 0)
  | k + 1, w => (1 - α) * psi k w + α * lowerModel F G m μ y k w

noncomputable def cst : ℕ → ℝ
  | 0 => F (x 0)
  | k + 1 => (1 - α) * cst k + α * F (y k) - isq m (G (y k)) / 2 +
      α * (1 - α) * (μ / 2 * wsq m (y k - v k) + dot (G (y k)) (v k - y k))

structure PhaseRec (N : ℕ) : Prop where
  m_pos : ∀ i, 0 < m i
  α_pos : 0 < α
  α_le : α ≤ 1 / 2
  μ_eq : μ = α ^ 2
  v0 : v 0 = x 0
  y_eq : ∀ k, k < N → ∀ i, (1 + α) * y k i = α * v k i + x k i
  x_eq : ∀ k, k < N → ∀ i, x (k + 1) i = y k i - G (y k) i / m i
  v_eq : ∀ k, k < N → ∀ i,
    v (k + 1) i = (1 - α) * v k i + α * y k i - α / μ * (G (y k) i / m i)

variable {F G m μ α x v y} {N : ℕ}

lemma PhaseRec.μ_pos (h : PhaseRec G m μ α x v y N) : 0 < μ := by
  rw [h.μ_eq]; exact pow_pos h.α_pos 2

lemma PhaseRec.psi_canon (h : PhaseRec G m μ α x v y N) (k : ℕ) (hk : k ≤ N) (w : Vec d) :
    psi F G m μ α x y k w = cst F G m μ α x v y k + μ / 2 * wsq m (w - v k) := by
  induction k with
  | zero => simp [psi, cst, h.v0]
  | succ k ih' =>
    have ih := ih' (by omega)
    simp only [psi, cst, ih, lowerModel]
    have hμ := h.μ_pos
    unfold wsq dot isq
    have hsum : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        (1 - α) * (μ / 2 * (m i * (w - v k) i ^ 2)) +
            (α * (G (y k) i * (w - y k) i) + α * (μ / 2 * (m i * (w - y k) i ^ 2))) =
          (α * (1 - α) * (μ / 2 * (m i * (y k - v k) i ^ 2)) +
              α * (1 - α) * (G (y k) i * (v k - y k) i) - G (y k) i ^ 2 / m i / 2) +
            μ / 2 * (m i * (w - v (k + 1)) i ^ 2) := by
      intro i _
      have hm := (h.m_pos i).ne'
      simp only [PiLp.sub_apply]
      rw [h.v_eq k (by omega) i, h.μ_eq]
      have hα := h.α_pos.ne'
      field_simp
      ring
    have := Finset.sum_congr rfl hsum
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_div] at this ⊢
    linarith [this]

lemma descent_of_check {m : Fin d → ℝ} (hm : ∀ i, 0 < m i) {F : Vec d → ℝ} {G : Vec d → Vec d}
    {y xp : Vec d} (hxp : ∀ i, xp i = y i - G y i / m i)
    (hA : isq m (G xp - G y) / 2 ≤ F y - F xp - dot (G xp) (y - xp)) :
    F xp ≤ F y - isq m (G y) / 2 := by
  have hdot : dot (G xp) (y - xp) = ∑ i, G xp i * G y i / m i := by
    unfold dot
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.sub_apply, hxp i]
    ring
  have hid : isq m (G xp - G y) / 2 + ∑ i, G xp i * G y i / m i =
      isq m (G xp) / 2 + isq m (G y) / 2 := by
    unfold isq
    rw [Finset.sum_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.sub_apply]
    have := (hm i).ne'
    field_simp
    ring
  have := isq_nonneg hm (G xp)
  linarith

end Phase

theorem phase_certificate {F : Vec d → ℝ} {G : Vec d → Vec d} {m : Fin d → ℝ} {μ α : ℝ}
    {x v y : ℕ → Vec d} {N : ℕ} {z : Vec d}
    (h : PhaseRec G m μ α x v y N)
    (hconv : ∀ k, k < N → F (y k) + dot (G (y k)) (x k - y k) ≤ F (x k))
    (hA : ∀ k, k < N →
      isq m (G (x (k + 1)) - G (y k)) / 2 ≤
        F (y k) - F (x (k + 1)) - dot (G (x (k + 1))) (y k - x (k + 1)))
    (hz : ∀ i, z i = x N i - G (x N) i / m i)
    (hAN : isq m (G z - G (x N)) / 2 ≤ F (x N) - F z - dot (G z) (x N - z))
    (hB : ∀ k, k < N →
      μ / 2 * wsq m (z - y k) ≤ F z - F (y k) - dot (G (y k)) (z - y k))
    (hC : μ / 2 * wsq m (x N - x 0) ≤ F (x N) - F (x 0) - dot (G (x 0)) (x N - x 0))
    (hD : μ * wsq m (z - x 0) ≤ dot (G z - G (x 0)) (z - x 0))
    (hE : isq m (G z - G (x N)) ≤ dot (G z - G (x N)) (z - x N))
    (hlam : (1 - α) ^ N ≤ μ / 24) :
    isq m (G (x N)) ≤ 8 * (1 - α) ^ N / μ * isq m (G (x 0)) := by
  have hm := h.m_pos
  have hμ := h.μ_pos
  set lam := (1 - α) ^ N with hlamdef
  have hlam0 : 0 ≤ lam := pow_nonneg (by linarith [h.α_le]) N
  have hdescN : ∀ k, k < N → F (x (k + 1)) ≤ F (y k) - isq m (G (y k)) / 2 :=
    fun k hk => descent_of_check hm (fun i => h.x_eq k hk i) (hA k hk)
  have hcstN : ∀ k, k ≤ N → F (x k) ≤ cst F G m μ α x v y k := by
    intro k hk
    induction k with
    | zero => simp [cst]
    | succ k ih =>
      have ih' := ih (by omega)
      simp only [cst]
      have hzero : dot (G (y k)) (x k - y k) + α * dot (G (y k)) (v k - y k) = 0 := by
        unfold dot
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun i _ => ?_
        simp only [PiLp.sub_apply]
        have := h.y_eq k (by omega) i
        linear_combination (-(G (y k) i)) * this
      have hw := wsq_nonneg hm (y k - v k)
      have hα := h.α_pos
      have hα1 : 0 ≤ 1 - α := by linarith [h.α_le]
      have h1 := hconv k (by omega)
      have h2 := hdescN k (by omega)
      have : 0 ≤ α * (1 - α) * (μ / 2 * wsq m (y k - v k)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left (le_trans h1 ih') hα1]
  have hmixN : ∀ k, k ≤ N → psi F G m μ α x y k z ≤
      (1 - α) ^ k * psi F G m μ α x y 0 z + (1 - (1 - α) ^ k) * F z := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have ih' := ih (by omega)
      rw [show psi F G m μ α x y (k + 1) z =
        (1 - α) * psi F G m μ α x y k z + α * lowerModel F G m μ y k z from rfl]
      have hα := h.α_pos
      have h1 : 0 ≤ 1 - α := by linarith [h.α_le]
      have hBk : lowerModel F G m μ y k z ≤ F z := by
        have := hB k (by omega)
        unfold lowerModel; linarith
      have := mul_le_mul_of_nonneg_left ih' h1
      have := mul_le_mul_of_nonneg_left hBk hα.le
      rw [pow_succ]
      nlinarith
  have hxN : F (x N) ≤ psi F G m μ α x y N z := by
    rw [h.psi_canon N le_rfl z]
    have := wsq_nonneg hm (z - v N)
    have := hcstN N le_rfl
    nlinarith
  have hmix := hmixN N le_rfl
  have hdz : F z ≤ F (x N) - isq m (G (x N)) / 2 := descent_of_check hm hz hAN
  set A := isq m (G (x N))
  set B := isq m (G (x 0))
  have hA0 := isq_nonneg hm (G (x N))
  have hB0 := isq_nonneg hm (G (x 0))
  have hCb : F (x 0) - F (x N) ≤ B / (2 * μ) := by
    have hy := dot_young hm (inv_pos.mpr hμ) (G (x 0)) (x 0 - x N)
    have e : 1 / (2 * μ⁻¹) = μ / 2 := by field_simp
    rw [e] at hy
    have hneg : dot (G (x 0)) (x N - x 0) = -dot (G (x 0)) (x 0 - x N) := by
      unfold dot; rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [PiLp.sub_apply]; ring
    have hwsym : wsq m (x N - x 0) = wsq m (x 0 - x N) := by
      unfold wsq; exact Finset.sum_congr rfl fun i _ => by simp only [PiLp.sub_apply]; ring
    rw [hneg, hwsym] at hC
    have e2 : μ⁻¹ / 2 * B = B / (2 * μ) := by field_simp
    linarith
  have hEb : isq m (G z - G (x N)) ≤ A := by
    have := isq_le_wsq_of_cocoercive hm hE
    have hw : wsq m (z - x N) = A := by
      unfold wsq; simp only [A, isq]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [PiLp.sub_apply, hz i]
      have := (hm i).ne'
      field_simp
      ring
    linarith
  have hDb : wsq m (z - x 0) ≤ isq m (G z - G (x 0)) / μ ^ 2 :=
    wsq_le_of_strong_monotone hm hμ hD
  have hsplit : G z - G (x 0) = (G z - G (x N)) + G (x N) + (-G (x 0)) := by abel
  have hneg : isq m (-G (x 0)) = B := by
    unfold isq; exact Finset.sum_congr rfl fun i _ => by simp
  have h3 := isq_add3 hm (G z - G (x N)) (G (x N)) (-G (x 0))
  rw [← hsplit, hneg] at h3
  have hzx : μ / 2 * wsq m (z - x 0) ≤ (6 * A + 3 * B) / (2 * μ) := by
    have h4 : isq m (G z - G (x 0)) ≤ 6 * A + 3 * B := by linarith
    have h5 : wsq m (z - x 0) ≤ (6 * A + 3 * B) / μ ^ 2 :=
      le_trans hDb (div_le_div_of_nonneg_right h4 (by positivity))
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ μ / 2)
    have e : μ / 2 * ((6 * A + 3 * B) / μ ^ 2) = (6 * A + 3 * B) / (2 * μ) := by
      field_simp
    linarith
  have hpsi0 : psi F G m μ α x y 0 z = F (x 0) + μ / 2 * wsq m (z - x 0) := rfl
  have hμ4 : μ ≤ 1 / 4 := by rw [h.μ_eq]; nlinarith [h.α_pos, h.α_le]
  have hlam1 : lam ≤ 1 := by linarith
  have key : (1 - lam) / 2 * A ≤ lam * ((4 * B + 6 * A) / (2 * μ)) := by
    have h7 : F (x N) ≤ lam * psi F G m μ α x y 0 z + (1 - lam) * F z := le_trans hxN hmix
    rw [hpsi0] at h7
    have h8 : (1 - lam) * F z ≤ (1 - lam) * (F (x N) - A / 2) :=
      mul_le_mul_of_nonneg_left hdz (by linarith)
    have h9 : lam * (F (x 0) - F (x N) + μ / 2 * wsq m (z - x 0)) ≤
        lam * (B / (2 * μ) + (6 * A + 3 * B) / (2 * μ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hlam0
    have e : B / (2 * μ) + (6 * A + 3 * B) / (2 * μ) = (4 * B + 6 * A) / (2 * μ) := by
      field_simp; ring
    rw [e] at h9
    nlinarith
  have hlamμ : lam / μ ≤ 1 / 24 := by rw [div_le_iff₀ hμ]; linarith
  have hlam1' : lam ≤ 1 / 96 := by linarith
  have e1 : lam * ((4 * B + 6 * A) / (2 * μ)) = lam / μ * (2 * B + 3 * A) := by
    field_simp; ring
  rw [e1] at key
  have e2 : 8 * lam / μ * B = 8 * (lam / μ) * B := by ring
  rw [e2]
  have hq : 0 ≤ lam / μ := div_nonneg hlam0 hμ.le
  nlinarith [mul_le_mul_of_nonneg_right hlamμ (by positivity : (0 : ℝ) ≤ 3 * A),
    mul_le_mul_of_nonneg_left hlam1' hA0]

end OracleTemplate.BlackBoxDiagonal

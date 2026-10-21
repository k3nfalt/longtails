import LongTails.Proofs.ExecutionHistory
import LongTails.Setups.RelativeErrorSmoothConvex
import LongTails.Algorithms.DampedAccelerated
import LongTails.Proofs.SgdExecution
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.RelativeErrorConvex

open LongTails.Setups.RelativeErrorSmoothConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def potential (f : E → ℝ) (L q : ℝ) (xs : E) (s : ℕ × E × E) : ℝ :=
  q * (s.1 : ℝ) * ((s.1 : ℝ) + 1) / (4 * L) * (f s.2.1 - f xs) + 1 / 2 * ‖s.2.2 - xs‖ ^ 2

lemma young_slack {s m b X Y : ℝ} (hs : 0 < s) (hb : b ^ 2 ≤ 4 * s * m) :
    b * X * Y ≤ s * X ^ 2 + m * Y ^ 2 := by
  have h1 : 0 ≤ (2 * s * X - b * Y) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (4 * s * m - b ^ 2) * Y ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 4 * s * (s * X ^ 2 + m * Y ^ 2 - b * X * Y) =
      (2 * s * X - b * Y) ^ 2 + (4 * s * m - b ^ 2) * Y ^ 2 := by ring
  have h4 : 0 ≤ 4 * s * (s * X ^ 2 + m * Y ^ 2 - b * X * Y) := by linarith
  have h5 : 0 ≤ s * X ^ 2 + m * Y ^ 2 - b * X * Y := by
    by_contra h
    have := mul_neg_of_pos_of_neg (show 0 < 4 * s by linarith) (not_le.mp h)
    linarith
  linarith

lemma potential_arith {P' P fy fs fx' Gn en wn gg ip L q α A' a : ℝ}
    (hL : 0 < L) (hq : 0 < q) (hα0 : 0 ≤ α) (hα1 : α < 1) (hq8 : 8 * q ≤ 1 - α)
    (hA' : 0 < A') (ha : 0 ≤ a) (haA : a ^ 2 * L ≤ q * A')
    (hen : 0 ≤ en) (hwn : 0 ≤ wn)
    (h1 : fx' ≤ fy - (Gn ^ 2 - en ^ 2) / (2 * L))
    (hP' : P' = A' * (fx' - fs) + 1 / 2 * wn ^ 2 - a * ip + a ^ 2 / 2 * gg)
    (h2 : A' * (fy - fs) + 1 / 2 * wn ^ 2 - a * ip ≤ P + a * (en * wn))
    (h6 : en ≤ α * Gn) (h7 : gg ≤ 2 * Gn ^ 2 + 2 * en ^ 2) (hPw : wn ^ 2 ≤ 2 * P) :
    P' ≤ (1 + 2 * q * α ^ 2 / (1 - α)) * P := by
  have hβ : 0 < 1 - α := by linarith
  have hee : en ^ 2 ≤ α ^ 2 * Gn ^ 2 := by
    have := pow_le_pow_left₀ hen h6 2
    rwa [mul_pow] at this
  have hα2 : α ^ 2 ≤ α := by nlinarith
  have hG2 : 0 ≤ Gn ^ 2 := sq_nonneg _
  have hGA : 0 ≤ A' * Gn ^ 2 / L := by positivity
  have s1 : A' * (fx' - fs) ≤ A' * (fy - fs) - A' * (Gn ^ 2 - en ^ 2) / (2 * L) := by
    have := mul_le_mul_of_nonneg_left h1 hA'.le
    have e : A' * (fy - (Gn ^ 2 - en ^ 2) / (2 * L)) - A' * fs =
        A' * (fy - fs) - A' * (Gn ^ 2 - en ^ 2) / (2 * L) := by ring
    linarith
  have s2 : a ^ 2 / 2 * gg ≤ q * (1 + α ^ 2) * (A' * Gn ^ 2 / L) := by
    have t1 : a ^ 2 / 2 * gg ≤ a ^ 2 * (Gn ^ 2 + en ^ 2) := by
      have := mul_le_mul_of_nonneg_left h7 (show 0 ≤ a ^ 2 / 2 by positivity)
      linarith
    have t2 : a ^ 2 * (Gn ^ 2 + en ^ 2) ≤ a ^ 2 * ((1 + α ^ 2) * Gn ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg a)
    have t3 : a ^ 2 ≤ q * A' / L := by
      rw [le_div_iff₀ hL]
      exact haA
    have t4 : a ^ 2 * ((1 + α ^ 2) * Gn ^ 2) ≤ q * A' / L * ((1 + α ^ 2) * Gn ^ 2) :=
      mul_le_mul_of_nonneg_right t3 (by positivity)
    have e : q * A' / L * ((1 + α ^ 2) * Gn ^ 2) = q * (1 + α ^ 2) * (A' * Gn ^ 2 / L) := by
      ring
    linarith
  have s3 : A' * (Gn ^ 2 - en ^ 2) / (2 * L) ≥ (1 - α ^ 2) / 2 * (A' * Gn ^ 2 / L) := by
    have t : A' * (Gn ^ 2 - en ^ 2) / (2 * L) - (1 - α ^ 2) / 2 * (A' * Gn ^ 2 / L) =
        A' * (α ^ 2 * Gn ^ 2 - en ^ 2) / (2 * L) := by
      field_simp
      ring
    have : 0 ≤ A' * (α ^ 2 * Gn ^ 2 - en ^ 2) / (2 * L) := by
      apply div_nonneg (mul_nonneg hA'.le (by linarith)) (by positivity)
    linarith
  have s4 : q * (1 + α ^ 2) - (1 - α ^ 2) / 2 ≤ -((1 - α) / 4) := by nlinarith
  have s5 : (q * (1 + α ^ 2) - (1 - α ^ 2) / 2) * (A' * Gn ^ 2 / L) ≤
      -((1 - α) / 4) * (A' * Gn ^ 2 / L) := mul_le_mul_of_nonneg_right s4 hGA
  have s6 : a * (en * wn) ≤ (1 - α) / 4 * (A' * Gn ^ 2 / L) + q * α ^ 2 / (1 - α) * wn ^ 2 := by
    have t1 : a * (en * wn) ≤ a * α * Gn * wn := by
      have := mul_le_mul_of_nonneg_left h6 (mul_nonneg ha hwn)
      nlinarith
    have hb : (a * α) ^ 2 ≤ 4 * ((1 - α) * A' / (4 * L)) * (q * α ^ 2 / (1 - α)) := by
      have e : 4 * ((1 - α) * A' / (4 * L)) * (q * α ^ 2 / (1 - α)) = q * A' / L * α ^ 2 := by
        field_simp
      rw [e, mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg α)
      rw [le_div_iff₀ hL]
      exact haA
    have t2 := young_slack (X := Gn) (Y := wn) (show 0 < (1 - α) * A' / (4 * L) by positivity) hb
    have e2 : (1 - α) * A' / (4 * L) * Gn ^ 2 = (1 - α) / 4 * (A' * Gn ^ 2 / L) := by
      field_simp
    rw [e2] at t2
    linarith
  have s7 : q * α ^ 2 / (1 - α) * wn ^ 2 ≤ 2 * q * α ^ 2 / (1 - α) * P := by
    have := mul_le_mul_of_nonneg_left hPw (show 0 ≤ q * α ^ 2 / (1 - α) by positivity)
    have e : q * α ^ 2 / (1 - α) * (2 * P) = 2 * q * α ^ 2 / (1 - α) * P := by ring
    linarith
  rw [hP']
  linarith

lemma step_potential {f : E → ℝ} {grad : E → E} {L q α : ℝ} {xs : E}
    (hL : 0 < L) (hq : 0 < q) (hα0 : 0 ≤ α) (hα1 : α < 1) (hq8 : 8 * q ≤ 1 - α)
    (hcv : ∀ x y, f x + ⟪grad x, y - x⟫ ≤ f y)
    (hup : ∀ x y, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hmin : ∀ x, f xs ≤ f x) (s : ℕ × E × E) (g : E)
    (hg : ‖g - grad (query s)‖ ≤ α * ‖grad (query s)‖) :
    potential f L q xs (step L q s g) ≤
      (1 + 2 * q * α ^ 2 / (1 - α)) * potential f L q xs s := by
  obtain ⟨n, x, z⟩ := s
  set k : ℝ := (n : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg n
  set y : E := query (n, x, z) with hy
  set G : E := grad y with hG
  have hyq : (k + 2) • y = k • x + (2 : ℝ) • z := by
    rw [hy, query, smul_smul, mul_one_div_cancel (by positivity), one_smul]
  set A : ℝ := q * k * (k + 1) / (4 * L) with hA
  set A' : ℝ := q * (k + 1) * (k + 2) / (4 * L) with hA'
  set a : ℝ := q * (k + 1) / (2 * L) with ha
  have hA0 : 0 ≤ A := by positivity
  have hA'0 : 0 < A' := by positivity
  have ha0 : 0 ≤ a := by positivity
  have haA : a ^ 2 * L ≤ q * A' := by
    have e1 : a ^ 2 * L = q ^ 2 * (k + 1) ^ 2 / (4 * L) := by
      rw [ha]
      field_simp
      ring
    have e2 : q * A' = q ^ 2 * (k + 1) * (k + 2) / (4 * L) := by
      rw [hA']
      ring
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg q, mul_nonneg (sq_nonneg q) (by linarith : (0 : ℝ) ≤ k + 1)]
  have a1 := hup y (y - (1 / L) • g)
  have h1 : f (y - (1 / L) • g) ≤ f y - (‖G‖ ^ 2 - ‖g - G‖ ^ 2) / (2 * L) := by
    have e1 : y - (1 / L) • g - y = -((1 / L) • g) := by abel
    rw [e1, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs] at a1
    have hee : ‖g - G‖ ^ 2 = ‖g‖ ^ 2 - 2 * ⟪g, G⟫ + ‖G‖ ^ 2 := norm_sub_sq_real g G
    have hcomm : ⟪g, G⟫ = ⟪G, g⟫ := real_inner_comm G g
    have e2 : L / 2 * ((1 / L) ^ 2 * ‖g‖ ^ 2) = ‖g‖ ^ 2 / (2 * L) := by
      field_simp
    have e3 : (‖G‖ ^ 2 - ‖g - G‖ ^ 2) / (2 * L) = 1 / L * ⟪G, g⟫ - ‖g‖ ^ 2 / (2 * L) := by
      rw [hee, hcomm]
      field_simp
      ring
    rw [e3]
    linarith
  have b2 : f y - f xs ≤ ⟪G, y - xs⟫ := by
    have h := hcv y xs
    have : ⟪G, xs - y⟫ = -⟪G, y - xs⟫ := by rw [← neg_sub, inner_neg_right]
    rw [this] at h
    linarith
  have b3 : f y - f x ≤ ⟪G, y - x⟫ := by
    have h := hcv y x
    have : ⟪G, x - y⟫ = -⟪G, y - x⟫ := by rw [← neg_sub, inner_neg_right]
    rw [this] at h
    linarith
  have hvec : A • (y - x) + a • (y - xs) = a • (z - xs) := by
    have : A • (y - x) + a • (y - xs) - a • (z - xs) =
        (q * (k + 1) / (4 * L)) • ((k + 2) • y - (k • x + (2 : ℝ) • z)) := by
      rw [hA, ha]
      module
    rw [hyq, sub_self, smul_zero] at this
    exact sub_eq_zero.mp this
  have hAa : A' = A + a := by
    rw [hA', hA, ha]
    field_simp
    ring
  have h2' : A' * (f y - f xs) - A * (f x - f xs) ≤ a * ⟪G, z - xs⟫ := by
    have hi : a * ⟪G, z - xs⟫ = A * ⟪G, y - x⟫ + a * ⟪G, y - xs⟫ := by
      rw [← inner_smul_right, ← hvec, inner_add_right, inner_smul_right, inner_smul_right]
    have m1 := mul_le_mul_of_nonneg_left b3 hA0
    have m2 := mul_le_mul_of_nonneg_left b2 ha0
    rw [hi, hAa]
    linarith
  have hgw : ⟪g, z - xs⟫ = ⟪G, z - xs⟫ + ⟪g - G, z - xs⟫ := by
    rw [← inner_add_left, add_sub_cancel]
  have herr : -⟪g - G, z - xs⟫ ≤ ‖g - G‖ * ‖z - xs‖ := by
    have := abs_real_inner_le_norm (g - G) (z - xs)
    have := neg_abs_le ⟪g - G, z - xs⟫
    linarith
  have h7 : ‖g‖ ^ 2 ≤ 2 * ‖G‖ ^ 2 + 2 * ‖g - G‖ ^ 2 := by
    have hgG : ‖g‖ ^ 2 = ‖G‖ ^ 2 + 2 * ⟪G, g - G⟫ + ‖g - G‖ ^ 2 := by
      rw [← norm_add_sq_real, add_sub_cancel]
    have h := sq_nonneg ‖G - (g - G)‖
    rw [norm_sub_sq_real] at h
    linarith
  have hP' : potential f L q xs (step L q (n, x, z) g) =
      A' * (f (y - (1 / L) • g) - f xs) + 1 / 2 * ‖z - xs‖ ^ 2 - a * ⟪g, z - xs⟫ +
        a ^ 2 / 2 * ‖g‖ ^ 2 := by
    have hz : z - a • g - xs = (z - xs) - a • g := by abel
    simp only [potential, step]
    rw [← hy, ← ha, hz, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_comm g (z - xs)]
    have hc : q * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1) / (4 * L) = A' := by
      rw [hA', hk]
      push_cast
      ring
    rw [hc]
    ring
  have hP : potential f L q xs (n, x, z) = A * (f x - f xs) + 1 / 2 * ‖z - xs‖ ^ 2 := rfl
  have hfx : 0 ≤ f x - f xs := by linarith [hmin x]
  have hPw : ‖z - xs‖ ^ 2 ≤ 2 * potential f L q xs (n, x, z) := by
    rw [hP]
    have := mul_nonneg hA0 hfx
    linarith
  have h2 : A' * (f y - f xs) + 1 / 2 * ‖z - xs‖ ^ 2 - a * ⟪g, z - xs⟫ ≤
      potential f L q xs (n, x, z) + a * (‖g - G‖ * ‖z - xs‖) := by
    rw [hP, hgw]
    have := mul_le_mul_of_nonneg_left herr ha0
    linarith
  exact potential_arith hL hq hα0 hα1 hq8 hA'0 ha0 haA (norm_nonneg (g - G))
    (norm_nonneg (z - xs)) h1 hP' h2 hg h7 hPw

lemma advance_potential {f : E → ℝ} {grad : E → E} {L q α : ℝ} {xs : E}
    (hL : 0 < L) (hq : 0 < q) (hα0 : 0 ≤ α) (hα1 : α < 1) (hq8 : 8 * q ≤ 1 - α)
    (hcv : ∀ x y, f x + ⟪grad x, y - x⟫ ≤ f y)
    (hup : ∀ x y, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hmin : ∀ x, f xs ≤ f x) (answer : ℕ → E → E)
    (herr : ∀ k x, ‖answer k x - grad x‖ ≤ α * ‖grad x‖) (K call : ℕ) (s : ℕ × E × E) :
    potential f L q xs (StochasticGradient.advance
        (fun k s => step L q s (answer k (query s))) K call s) ≤
      (1 + 2 * q * α ^ 2 / (1 - α)) ^ K * potential f L q xs s ∧
    (StochasticGradient.advance
        (fun k s => step L q s (answer k (query s))) K call s).1 = s.1 + K := by
  induction K generalizing call s with
  | zero => simp [StochasticGradient.advance]
  | succ K ih =>
    rw [StochasticGradient.advance]
    obtain ⟨h1, h1c⟩ := ih (call + 1) (step L q s (answer call (query s)))
    have h2 := step_potential hL hq hα0 hα1 hq8 hcv hup hmin s (answer call (query s))
      (herr call (query s))
    have hc : 0 ≤ 1 + 2 * q * α ^ 2 / (1 - α) := by
      have : 0 < 1 - α := by linarith
      positivity
    refine ⟨h1.trans ?_, ?_⟩
    · have e : (1 + 2 * q * α ^ 2 / (1 - α)) ^ (K + 1) * potential f L q xs s =
          (1 + 2 * q * α ^ 2 / (1 - α)) ^ K *
            ((1 + 2 * q * α ^ 2 / (1 - α)) * potential f L q xs s) := by
        rw [pow_succ, mul_assoc]
      rw [e]
      exact mul_le_mul_of_nonneg_left h2 (pow_nonneg hc K)
    · rw [h1c]
      simp only [step]
      omega

lemma damping_bounds {α : ℝ} (hα1 : α < 1) (N : ℕ) :
    0 < damping α N ∧ 8 * damping α N ≤ 1 - α ∧
      2 * damping α N * α ^ 2 / (1 - α) * N ≤ 1 := by
  have hβ : 0 < 1 - α := by linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hD : 0 < 8 + 2 * α ^ 2 * (N : ℝ) := by positivity
  refine ⟨by unfold damping; positivity, ?_, ?_⟩
  · unfold damping
    rw [show 8 * ((1 - α) / (8 + 2 * α ^ 2 * (N : ℝ))) = 8 * (1 - α) / (8 + 2 * α ^ 2 * (N : ℝ))
      by ring, div_le_iff₀ hD]
    nlinarith [mul_nonneg (sq_nonneg α) hN]
  · unfold damping
    have e : 2 * ((1 - α) / (8 + 2 * α ^ 2 * (N : ℝ))) * α ^ 2 / (1 - α) * N =
        2 * α ^ 2 * N / (8 + 2 * α ^ 2 * (N : ℝ)) := by
      field_simp
    rw [e, div_le_one hD]
    linarith

lemma horizon_accuracy {L α R ε gap : ℝ} {N : ℕ} (hL : 0 < L) (hα1 : α < 1)
    (hε : 0 < ε) (hN0 : 0 < N)
    (hN : 7 * Real.sqrt (L * R ^ 2 / ((1 - α) * ε)) +
      11 * α ^ 2 * L * R ^ 2 / ((1 - α) * ε) ≤ N)
    (hpot : damping α N * (N : ℝ) * ((N : ℝ) + 1) / (4 * L) * gap ≤
      Real.exp 1 * (1 / 2 * R ^ 2)) : gap ≤ ε := by
  have hβ : 0 < 1 - α := by linarith
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN0
  set T : ℝ := L * R ^ 2 / ((1 - α) * ε) with hT
  have hT0 : 0 ≤ T := by positivity
  set r : ℝ := Real.sqrt T with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg T
  have hrr : r * r = T := Real.mul_self_sqrt hT0
  have hN' : 7 * r + 11 * α ^ 2 * T ≤ N := by
    have e : 11 * α ^ 2 * L * R ^ 2 / ((1 - α) * ε) = 11 * α ^ 2 * T := by
      rw [hT]
      ring
    rw [e] at hN
    exact hN
  have hαT : 0 ≤ α ^ 2 * T := by positivity
  have h7r : 7 * r ≤ N := by linarith
  have hNN : 49 * T + 11 * α ^ 2 * T * N ≤ (N : ℝ) * N := by
    have m1 := mul_le_mul_of_nonneg_left hN' hNr.le
    have m2 := mul_le_mul_of_nonneg_left h7r (show (0 : ℝ) ≤ 7 * r by positivity)
    nlinarith
  have he : Real.exp 1 ≤ 2.75 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hLR : L * R ^ 2 = T * ((1 - α) * ε) := by
    rw [hT, div_mul_cancel₀ _ (by positivity)]
  have hD : 0 < 8 + 2 * α ^ 2 * (N : ℝ) := by positivity
  have hpot' : (1 - α) * (N : ℝ) * ((N : ℝ) + 1) * gap ≤
      Real.exp 1 * 2 * L * R ^ 2 * (8 + 2 * α ^ 2 * (N : ℝ)) := by
    unfold damping at hpot
    have e : (1 - α) / (8 + 2 * α ^ 2 * (N : ℝ)) * (N : ℝ) * ((N : ℝ) + 1) / (4 * L) * gap =
        (1 - α) * (N : ℝ) * ((N : ℝ) + 1) * gap / ((8 + 2 * α ^ 2 * (N : ℝ)) * (4 * L)) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)] at hpot
    nlinarith
  have hR0 : 0 ≤ L * R ^ 2 * (8 + 2 * α ^ 2 * (N : ℝ)) := by positivity
  have hpot'' : (1 - α) * (N : ℝ) * ((N : ℝ) + 1) * gap ≤
      5.5 * (T * ((1 - α) * ε)) * (8 + 2 * α ^ 2 * (N : ℝ)) := by
    rw [← hLR]
    nlinarith
  have hkey : 5.5 * T * (8 + 2 * α ^ 2 * (N : ℝ)) ≤ (N : ℝ) * ((N : ℝ) + 1) := by
    nlinarith
  have hfin : (1 - α) * ((N : ℝ) * ((N : ℝ) + 1)) * gap ≤
      (1 - α) * ((N : ℝ) * ((N : ℝ) + 1)) * ε := by
    have m := mul_le_mul_of_nonneg_left hkey (show 0 ≤ (1 - α) * ε by positivity)
    nlinarith
  exact le_of_mul_le_mul_left hfin (by positivity)

lemma execute_accuracy [CompleteSpace E] {f : E → ℝ} {L α R ε : ℝ} {x0 xstar : E}
    (hL : 0 < L) (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε)
    (hcv : ∀ x y, f x + ⟪gradient f x, y - x⟫ ≤ f y)
    (hup : ∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hmin : IsMinOn f Set.univ xstar) (hdist : ‖x0 - xstar‖ ≤ R)
    (O : Oracle E E)
    (herr : ∀ k x seed, ‖O.answer k (0, x) seed - gradient f x‖ ≤ α * ‖gradient f x‖)
    (N : ℕ) (hN : 7 * Real.sqrt (L * R ^ 2 / ((1 - α) * ε)) +
      11 * α ^ 2 * L * R ^ 2 / ((1 - α) * ε) ≤ N)
    (seed : (dampedAccelerated L (damping α N) x0).Seed) (ξ : (k : ℕ) → O.Seed k) :
    f (execute O (dampedAccelerated L (damping α N) x0) (fun _ => N) seed ξ) - f xstar ≤ ε := by
  have hβ : 0 < 1 - α := by linarith
  have hminx : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  rw [execute_advance_history]
  obtain ⟨hq0, hq8, hqN⟩ := damping_bounds hα1 N
  obtain ⟨hadv, hcount⟩ := advance_potential hL hq0 hα0 hα1 hq8 hcv hup hminx
    (fun k x => executeAnswerAt O (dampedAccelerated L (damping α N) x0) seed ξ k (0, x)) (fun k x => herr _ x (ξ _)) N 0 (0, x0, x0)
  set sN := StochasticGradient.advance
    (fun k s => step L (damping α N) s (executeAnswerAt O (dampedAccelerated L (damping α N) x0) seed ξ k (0, query s))) N 0 (0, x0, x0) with hsN
  show f sN.2.1 - f xstar ≤ ε
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · have hs : sN = (0, x0, x0) := by
      rw [hsN, h0]
      rfl
    rw [hs]
    have hT0 : 0 ≤ L * R ^ 2 / ((1 - α) * ε) := by positivity
    have h2 : 0 ≤ 11 * α ^ 2 * L * R ^ 2 / ((1 - α) * ε) := by positivity
    have h1 : Real.sqrt (L * R ^ 2 / ((1 - α) * ε)) ≤ 0 := by
      rw [h0] at hN
      simp only [Nat.cast_zero] at hN
      linarith
    have hT : L * R ^ 2 / ((1 - α) * ε) ≤ 0 := Real.sqrt_eq_zero'.mp
      (le_antisymm h1 (Real.sqrt_nonneg _))
    have hLR : L * R ^ 2 ≤ 0 := by
      rw [div_le_iff₀ (by positivity)] at hT
      linarith
    have hR0 : R = 0 := by
      have : R ^ 2 ≤ 0 := by nlinarith
      exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg R))
    have hx : x0 = xstar := by
      rw [hR0] at hdist
      exact sub_eq_zero.mp (norm_le_zero_iff.mp hdist)
    show f x0 - f xstar ≤ ε
    rw [hx, sub_self]
    exact hε.le
  · have hP0 : potential f L (damping α N) xstar (0, x0, x0) = 1 / 2 * ‖x0 - xstar‖ ^ 2 := by
      simp [potential]
    have hstart : potential f L (damping α N) xstar (0, x0, x0) ≤ 1 / 2 * R ^ 2 := by
      have hsq : ‖x0 - xstar‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
      rw [hP0]
      linarith
    have hstart0 : 0 ≤ potential f L (damping α N) xstar (0, x0, x0) := by
      rw [hP0]
      positivity
    have hgrow : (1 + 2 * damping α N * α ^ 2 / (1 - α)) ^ N ≤ Real.exp 1 := by
      have h1 : 1 + 2 * damping α N * α ^ 2 / (1 - α) ≤
          Real.exp (2 * damping α N * α ^ 2 / (1 - α)) := by
        linarith [Real.add_one_le_exp (2 * damping α N * α ^ 2 / (1 - α))]
      have h0' : 0 ≤ 1 + 2 * damping α N * α ^ 2 / (1 - α) := by positivity
      calc (1 + 2 * damping α N * α ^ 2 / (1 - α)) ^ N
          ≤ Real.exp (2 * damping α N * α ^ 2 / (1 - α)) ^ N := pow_le_pow_left₀ h0' h1 N
        _ = Real.exp ((N : ℝ) * (2 * damping α N * α ^ 2 / (1 - α))) := by
            rw [Real.exp_nat_mul]
        _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    have hcnt : sN.1 = N := by
      rw [hcount]
      simp
    have hgap : 0 ≤ f sN.2.1 - f xstar := by linarith [hminx sN.2.1]
    have hz : 0 ≤ 1 / 2 * ‖sN.2.2 - xstar‖ ^ 2 := by positivity
    have hpot : damping α N * (N : ℝ) * ((N : ℝ) + 1) / (4 * L) * (f sN.2.1 - f xstar) ≤
        Real.exp 1 * (1 / 2 * R ^ 2) := by
      have hP : potential f L (damping α N) xstar sN =
          damping α N * (N : ℝ) * ((N : ℝ) + 1) / (4 * L) * (f sN.2.1 - f xstar) +
            1 / 2 * ‖sN.2.2 - xstar‖ ^ 2 := by
        simp only [potential, hcnt]
      have m1 : (1 + 2 * damping α N * α ^ 2 / (1 - α)) ^ N *
          potential f L (damping α N) xstar (0, x0, x0) ≤
          Real.exp 1 * (1 / 2 * R ^ 2) :=
        mul_le_mul hgrow hstart hstart0 (Real.exp_pos 1).le
      linarith
    exact horizon_accuracy hL hα1 hε hpos hN hpot

end OracleTemplate.RelativeErrorConvex

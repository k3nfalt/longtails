import LongTails.Proofs.NcConcaveRhoModel

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveModel

open LongTails.Proofs.SmoothConvexFiniteGeometry LongTails.Proofs.NcConcaveScalars
open LongTails.Proofs.NcConcaveTransitions LongTails.Proofs.NcConcaveTransitionBounds
open LongTails.Proofs.NcConcavePsi LongTails.Proofs.NcConcavePartTwo LongTails.Proofs.NcConcaveGadgets
open LongTails.Proofs.NcConcaveHuber LongTails.Proofs.NcConcaveBlock
open LongTails.Proofs.NcConcaveInstance LongTails.Proofs.NcConcaveC11 LongTails.Proofs.NcConcavePhi
open LongTails.Proofs.NcConcaveRhoModel

variable {n m : ℕ}

lemma sum_model_bound {ι : Type*} (s : Finset ι) (E w : ι → ℝ) (C : ℝ)
    (h : ∀ i, |E i| ≤ C * w i) : |∑ i ∈ s, E i| ≤ C * ∑ i ∈ s, w i := by
  rw [Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => h i)

lemma two_sqrt_mul_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * (Real.sqrt x * Real.sqrt y) ≤ x + y := by
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y)]

noncomputable def dP (θ : ℝ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ)
    (du : Fin (n + 1) → ℝ) (da db : Fin n → ℝ) : ℝ :=
  -cη * du 0 - cη * ∑ j : Fin n, dnu (zeta θ (u j.succ)) * dzeta θ (u j.succ) * du j.succ +
    cη / 2 * ∑ j, 2 * rr (zeta θ (u j)) * drr (zeta θ (u j)) * dzeta θ (u j) * du j +
    ∑ i, 2 * zeta θ (a i) * dzeta θ (a i) * da i -
    ∑ i, (da i * rho (zu θ u) i + a i * dRho θ u du i) +
    ∑ i, rho (zu θ u) i * dRho θ u du i +
    ∑ i, 2 * zeta θ (b i) * dzeta θ (b i) * db i -
    ∑ i, (betaRB θ (b i) (u i.succ) * db i + betaRX θ (b i) (u i.succ) * du i.succ) +
    (1 / 2) * ∑ i : Fin n, 2 * rr (zeta θ (u i.succ)) * drr (zeta θ (u i.succ)) *
      dzeta θ (u i.succ) * du i.succ

noncomputable def dB (θ τ : ℝ) (a b : ℝ) (y : Fin (m + 1) → ℝ) (da db : ℝ)
    (dy : Fin (m + 1) → ℝ) : ℝ :=
  -(alpha m ^ 2 / 2) * (2 * zeta θ (y 0) * dzeta θ (y 0) * dy 0) -
    ∑ k : Fin m, dhuber τ (zeta (2 * θ) (y k.castSucc - y k.succ)) *
      dzeta (2 * θ) (y k.castSucc - y k.succ) * (dy k.castSucc - dy k.succ) +
    alpha m * (betaS θ a (y 0) * da + betaT θ a (y 0) * dy 0) -
    alpha m / 2 * (betaS θ b (y (Fin.last m)) * db + betaT θ b (y (Fin.last m)) * dy (Fin.last m)) -
    alpha m ^ 2 * m / 8 * (2 * zeta θ b * dzeta θ b * db) -
    (2 * alpha m * θ * domega θ (y 0) * dy 0 +
      2 * alpha m * θ * domega θ (y (Fin.last m)) * dy (Fin.last m))

noncomputable def dF (θ τ : ℝ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (y : Fin n → Fin (m + 1) → ℝ)
    (du : Fin (n + 1) → ℝ) (da db : Fin n → ℝ) (dy : Fin n → Fin (m + 1) → ℝ) : ℝ :=
  dP θ u a b du da db + ∑ i, dB θ τ (a i) (b i) (y i) (da i) (db i) (dy i)

noncomputable def sqY (y : Fin n → Fin (m + 1) → ℝ) : ℝ := ∑ i, ∑ k, y i k ^ 2

noncomputable def nsq (du : Fin (n + 1) → ℝ) (da db : Fin n → ℝ) (dy : Fin n → Fin (m + 1) → ℝ) : ℝ :=
  sq1 du + sq2 da + sq2 db + sqY dy

lemma sqY_nonneg (y : Fin n → Fin (m + 1) → ℝ) : 0 ≤ sqY y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma nsq_nonneg (du : Fin (n + 1) → ℝ) (da db : Fin n → ℝ) (dy : Fin n → Fin (m + 1) → ℝ) :
    0 ≤ nsq du da db dy := by
  unfold nsq; linarith [sq1_nonneg du, sq2_nonneg da, sq2_nonneg db, sqY_nonneg dy]

lemma sum_diff_sq_le (w : Fin (m + 1) → ℝ) :
    ∑ k : Fin m, (w k.castSucc - w k.succ) ^ 2 ≤ 4 * ∑ k, w k ^ 2 := by
  have h1 := sum_castSucc_le w
  have h2 := sum_succ_le w
  have : ∑ k : Fin m, (w k.castSucc - w k.succ) ^ 2 ≤
      ∑ k : Fin m, (2 * w k.castSucc ^ 2 + 2 * w k.succ ^ 2) :=
    Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (w k.castSucc + w k.succ)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
  unfold sq1 at h1 h2
  linarith

lemma single_le_sumsq (w : Fin (m + 1) → ℝ) (k : Fin (m + 1)) : w k ^ 2 ≤ ∑ j, w j ^ 2 :=
  Finset.single_le_sum (f := fun j => w j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)

set_option maxHeartbeats 800000 in
theorem robB_model {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 < τ) (a b a' b' : ℝ) (y y' : Fin (m + 1) → ℝ) :
    |robB θ τ a' b' y' - robB θ τ a b y - dB θ τ a b y (a' - a) (b' - b) (fun k => y' k - y k)| ≤
      40 * ((a' - a) ^ 2 + (b' - b) ^ 2 + ∑ k, (y' k - y k) ^ 2) := by
  have hα := alpha_pos m
  have hα1 := alpha_le_one m
  have hα2 : alpha m ^ 2 * m ≤ 1 := by
    rw [alpha_sq, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hα3 : alpha m ^ 2 ≤ 1 := by nlinarith
  set l := Fin.last m
  set E1 := zeta θ (y' 0) ^ 2 - zeta θ (y 0) ^ 2 - 2 * zeta θ (y 0) * dzeta θ (y 0) * (y' 0 - y 0)
  set E2 := ∑ k : Fin m, (huber τ (zeta (2 * θ) (y' k.castSucc - y' k.succ)) -
      huber τ (zeta (2 * θ) (y k.castSucc - y k.succ)) -
      dhuber τ (zeta (2 * θ) (y k.castSucc - y k.succ)) * dzeta (2 * θ) (y k.castSucc - y k.succ) *
        (y' k.castSucc - y k.castSucc - (y' k.succ - y k.succ)))
  set E3 := beta θ a' (y' 0) - beta θ a (y 0) - betaS θ a (y 0) * (a' - a) -
      betaT θ a (y 0) * (y' 0 - y 0)
  set E4 := beta θ b' (y' l) - beta θ b (y l) - betaS θ b (y l) * (b' - b) -
      betaT θ b (y l) * (y' l - y l)
  set E5 := zeta θ b' ^ 2 - zeta θ b ^ 2 - 2 * zeta θ b * dzeta θ b * (b' - b)
  set E6 := 2 * alpha m * θ * omega θ (y' 0) - 2 * alpha m * θ * omega θ (y 0) -
      2 * alpha m * θ * domega θ (y 0) * (y' 0 - y 0)
  set E7 := 2 * alpha m * θ * omega θ (y' l) - 2 * alpha m * θ * omega θ (y l) -
      2 * alpha m * θ * domega θ (y l) * (y' l - y l)
  have e : robB θ τ a' b' y' - robB θ τ a b y - dB θ τ a b y (a' - a) (b' - b) (fun k => y' k - y k) =
      -(alpha m ^ 2 / 2) * E1 - E2 + alpha m * E3 - alpha m / 2 * E4 -
        alpha m ^ 2 * m / 8 * E5 - E6 - E7 := by
    simp only [robB, dB, E1, E2, E3, E4, E5, E6, E7, Finset.sum_sub_distrib]
    ring
  rw [e]
  have b1 : |E1| ≤ 7 * (y' 0 - y 0) ^ 2 := sqz_model hθ (y 0) (y' 0)
  have b2 : |E2| ≤ 7 * ∑ k : Fin m, ((y' k.castSucc - y k.castSucc) - (y' k.succ - y k.succ)) ^ 2 := by
    apply sum_model_bound
    intro k
    have h := huberz_model hτ (by linarith : (0 : ℝ) < 2 * θ) (y k.castSucc - y k.succ)
      (y' k.castSucc - y' k.succ)
    have e2 : (y' k.castSucc - y' k.succ - (y k.castSucc - y k.succ)) =
        y' k.castSucc - y k.castSucc - (y' k.succ - y k.succ) := by ring
    rw [e2] at h
    exact h
  have b3 : |E3| ≤ 3 * ((a' - a) ^ 2 + (y' 0 - y 0) ^ 2) := beta_model hθ a (y 0) a' (y' 0)
  have b4 : |E4| ≤ 3 * ((b' - b) ^ 2 + (y' l - y l) ^ 2) := beta_model hθ b (y l) b' (y' l)
  have b5 : |E5| ≤ 7 * (b' - b) ^ 2 := sqz_model hθ b b'
  have b6 : |E6| ≤ 2 * alpha m * (y' 0 - y 0) ^ 2 := by
    have := omega_scaled_model (c := 2 * alpha m) hθ (by positivity) (y 0) (y' 0)
    simpa only [E6] using this
  have b7 : |E7| ≤ 2 * alpha m * (y' l - y l) ^ 2 := by
    have := omega_scaled_model (c := 2 * alpha m) hθ (by positivity) (y l) (y' l)
    simpa only [E7] using this
  have hS0 := single_le_sumsq (fun k => y' k - y k) 0
  have hSl := single_le_sumsq (fun k => y' k - y k) l
  have hSd := sum_diff_sq_le (fun k => y' k - y k)
  set S := ∑ k, (y' k - y k) ^ 2 with hSdef
  clear_value S E1 E2 E3 E4 E5 E6 E7
  have c1 : |-(alpha m ^ 2 / 2) * E1| ≤ 7 / 2 * S := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity)]
    calc alpha m ^ 2 / 2 * |E1| ≤ 1 / 2 * (7 * (y' 0 - y 0) ^ 2) :=
          mul_le_mul (by linarith) b1 (abs_nonneg _) (by norm_num)
      _ ≤ _ := by linarith
  have c2 : |E2| ≤ 28 * S := by linarith
  have c3 : |alpha m * E3| ≤ 3 * (a' - a) ^ 2 + 3 * S := by
    rw [abs_mul, abs_of_pos hα]
    calc alpha m * |E3| ≤ 1 * (3 * ((a' - a) ^ 2 + (y' 0 - y 0) ^ 2)) :=
          mul_le_mul hα1 b3 (abs_nonneg _) (by norm_num)
      _ ≤ _ := by linarith
  have c4 : |alpha m / 2 * E4| ≤ 3 / 2 * (b' - b) ^ 2 + 3 / 2 * S := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc alpha m / 2 * |E4| ≤ 1 / 2 * (3 * ((b' - b) ^ 2 + (y' l - y l) ^ 2)) :=
          mul_le_mul (by linarith) b4 (abs_nonneg _) (by norm_num)
      _ ≤ _ := by linarith
  have c5 : |alpha m ^ 2 * m / 8 * E5| ≤ 7 / 8 * (b' - b) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc alpha m ^ 2 * m / 8 * |E5| ≤ 1 / 8 * (7 * (b' - b) ^ 2) :=
          mul_le_mul (by linarith) b5 (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have c6 : |E6| ≤ 2 * S := by nlinarith [sq_nonneg (y' 0 - y 0)]
  have c7 : |E7| ≤ 2 * S := by nlinarith [sq_nonneg (y' l - y l)]
  have q1 := abs_le.mp c1; have q2 := abs_le.mp c2; have q3 := abs_le.mp c3
  have q4 := abs_le.mp c4; have q5 := abs_le.mp c5; have q6 := abs_le.mp c6
  have q7 := abs_le.mp c7
  rw [abs_le]; constructor <;> linarith [sq_nonneg (a' - a), sq_nonneg (b' - b)]

lemma grp_nu {θ : ℝ} (hθ : 0 < θ) (u u' : Fin (n + 1) → ℝ) :
    |∑ j : Fin n, (nu (zeta θ (u' j.succ)) - nu (zeta θ (u j.succ)) -
      dnu (zeta θ (u j.succ)) * dzeta θ (u j.succ) * (u' j.succ - u j.succ))| ≤
      21 * sq1 (fun j => u' j - u j) := by
  have h := sum_model_bound Finset.univ _ (fun j : Fin n => (u' j.succ - u j.succ) ^ 2) 21
    (fun j => nuz_model hθ (u j.succ) (u' j.succ))
  exact h.trans (mul_le_mul_of_nonneg_left (sum_succ_le (fun j => u' j - u j)) (by norm_num))

lemma grp_rr {θ : ℝ} (hθ : 0 < θ) (u u' : Fin (n + 1) → ℝ) :
    |∑ j, (rr (zeta θ (u' j)) ^ 2 - rr (zeta θ (u j)) ^ 2 -
      2 * rr (zeta θ (u j)) * drr (zeta θ (u j)) * dzeta θ (u j) * (u' j - u j))| ≤
      35 * sq1 (fun j => u' j - u j) :=
  sum_model_bound Finset.univ _ (fun j => (u' j - u j) ^ 2) 35
    (fun j => rrsqz_model hθ (u j) (u' j))

lemma grp_rr_succ {θ : ℝ} (hθ : 0 < θ) (u u' : Fin (n + 1) → ℝ) :
    |∑ j : Fin n, (rr (zeta θ (u' j.succ)) ^ 2 - rr (zeta θ (u j.succ)) ^ 2 -
      2 * rr (zeta θ (u j.succ)) * drr (zeta θ (u j.succ)) * dzeta θ (u j.succ) *
        (u' j.succ - u j.succ))| ≤ 35 * sq1 (fun j => u' j - u j) := by
  have h := sum_model_bound Finset.univ _ (fun j : Fin n => (u' j.succ - u j.succ) ^ 2) 35
    (fun j => rrsqz_model hθ (u j.succ) (u' j.succ))
  exact h.trans (mul_le_mul_of_nonneg_left (sum_succ_le (fun j => u' j - u j)) (by norm_num))

lemma grp_sq {θ : ℝ} (hθ : 0 < θ) (a a' : Fin n → ℝ) :
    |∑ i, (zeta θ (a' i) ^ 2 - zeta θ (a i) ^ 2 - 2 * zeta θ (a i) * dzeta θ (a i) * (a' i - a i))| ≤
      7 * sq2 (fun i => a' i - a i) :=
  sum_model_bound Finset.univ _ (fun i => (a' i - a i) ^ 2) 7 (fun i => sqz_model hθ (a i) (a' i))

lemma grp_arho {θ : ℝ} (hθ : 0 < θ) (B : ℝ) (hB : 0 ≤ B) (u u' : Fin (n + 1) → ℝ)
    (a a' : Fin n → ℝ) (ha : sq2 a ≤ B ^ 2) :
    |∑ i, (a' i * rho (zu θ u') i - a i * rho (zu θ u) i -
      ((a' i - a i) * rho (zu θ u) i + a i * dRho θ u (fun j => u' j - u j) i))| ≤
      (104 * B + 3) * sq1 (fun j => u' j - u j) + 3 * sq2 (fun i => a' i - a i) := by
  set E : Fin n → ℝ := fun i => rho (zu θ u') i - rho (zu θ u) i - dRho θ u (fun j => u' j - u j) i
  set D : Fin n → ℝ := fun i => rho (zu θ u') i - rho (zu θ u) i
  have e : ∑ i, (a' i * rho (zu θ u') i - a i * rho (zu θ u) i -
      ((a' i - a i) * rho (zu θ u) i + a i * dRho θ u (fun j => u' j - u j) i)) =
      ∑ i, a i * E i + ∑ i, (a' i - a i) * D i := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by simp only [E, D]; ring
  rw [e]
  set S := sq1 (fun j => u' j - u j)
  have hS := sq1_nonneg (fun j => u' j - u j)
  have hE := rhoz_model hθ u u'
  have hD := rhoz_lip hθ u u'
  have h1 := cs_bound a E
  have h2 := cs_bound (fun i => a' i - a i) D
  have hsa : Real.sqrt (sq2 a) ≤ B := by rw [Real.sqrt_le_left hB]; exact ha
  have hsE : Real.sqrt (sq2 E) ≤ 104 * S := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hsD : Real.sqrt (sq2 D) ≤ 6 * Real.sqrt S := by
    rw [show 6 * Real.sqrt S = Real.sqrt (36 * S) by
      rw [Real.sqrt_mul (by norm_num), show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hD
  have t1 : |∑ i, a i * E i| ≤ B * (104 * S) :=
    h1.trans (mul_le_mul hsa hsE (Real.sqrt_nonneg _) hB)
  have t2 : |∑ i, (a' i - a i) * D i| ≤ 3 * (sq2 (fun i => a' i - a i) + S) := by
    refine h2.trans ?_
    have := two_sqrt_mul_le (sq2 (fun i => a' i - a i)) S (sq2_nonneg _) hS
    calc _ ≤ Real.sqrt (sq2 fun i => a' i - a i) * (6 * Real.sqrt S) :=
          mul_le_mul_of_nonneg_left hsD (Real.sqrt_nonneg _)
      _ = 3 * (2 * (Real.sqrt (sq2 fun i => a' i - a i) * Real.sqrt S)) := by ring
      _ ≤ _ := by linarith
  calc _ ≤ |∑ i, a i * E i| + |∑ i, (a' i - a i) * D i| := abs_add_le _ _
    _ ≤ _ := by nlinarith

lemma grp_rhosq {θ : ℝ} (hθ : 0 < θ) (u u' : Fin (n + 1) → ℝ) :
    |∑ i, ((1 / 2) * rho (zu θ u') i ^ 2 - (1 / 2) * rho (zu θ u) i ^ 2 -
      rho (zu θ u) i * dRho θ u (fun j => u' j - u j) i)| ≤ 122 * sq1 (fun j => u' j - u j) := by
  set E : Fin n → ℝ := fun i => rho (zu θ u') i - rho (zu θ u) i - dRho θ u (fun j => u' j - u j) i
  set D : Fin n → ℝ := fun i => rho (zu θ u') i - rho (zu θ u) i
  have e : ∑ i, ((1 / 2) * rho (zu θ u') i ^ 2 - (1 / 2) * rho (zu θ u) i ^ 2 -
      rho (zu θ u) i * dRho θ u (fun j => u' j - u j) i) =
      ∑ i, rho (zu θ u) i * E i + (1 / 2) * sq2 D := by
    simp only [sq2, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [E, D]; ring
  rw [e]
  set S := sq1 (fun j => u' j - u j)
  have hS := sq1_nonneg (fun j => u' j - u j)
  have hE := rhoz_model hθ u u'
  have hD := rhoz_lip hθ u u'
  have h1 := cs_bound (rho (zu θ u)) E
  have hr : Real.sqrt (sq2 (rho (zu θ u))) ≤ 1 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith [sq2_rho_le_one (zu θ u)]
  have hsE : Real.sqrt (sq2 E) ≤ 104 * S := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have t1 : |∑ i, rho (zu θ u) i * E i| ≤ 1 * (104 * S) :=
    h1.trans (mul_le_mul hr hsE (Real.sqrt_nonneg _) (by norm_num))
  have hD0 := sq2_nonneg D
  have hD' : sq2 D ≤ 36 * S := hD
  calc _ ≤ |∑ i, rho (zu θ u) i * E i| + |(1 / 2) * sq2 D| := abs_add_le _ _
    _ ≤ 1 * (104 * S) + (1 / 2) * (36 * S) := by
        rw [abs_of_nonneg (mul_nonneg (by norm_num) hD0)]; linarith
    _ = _ := by ring

lemma grp_betaR {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (B : ℝ) (hB : 0 ≤ B) (u u' : Fin (n + 1) → ℝ)
    (b b' : Fin n → ℝ) (hb : ∀ i, |b i| ≤ B) :
    |∑ i, (betaR θ (b' i) (u' i.succ) - betaR θ (b i) (u i.succ) -
      (betaRB θ (b i) (u i.succ) * (b' i - b i) + betaRX θ (b i) (u i.succ) * (u' i.succ - u i.succ)))| ≤
      3 * sq2 (fun i => b' i - b i) + (B + 5) * sq1 (fun j => u' j - u j) := by
  have h := sum_model_bound Finset.univ
    (fun i : Fin n => betaR θ (b' i) (u' i.succ) - betaR θ (b i) (u i.succ) -
      (betaRB θ (b i) (u i.succ) * (b' i - b i) + betaRX θ (b i) (u i.succ) * (u' i.succ - u i.succ)))
    (fun i : Fin n => 3 * (b' i - b i) ^ 2 + (B + 5) * (u' i.succ - u i.succ) ^ 2) 1
    (fun i => by
      have h := betaR_model hθ hθ1 B (b i) (u i.succ) (b' i) (u' i.succ) (hb i)
      have e : betaR θ (b' i) (u' i.succ) - betaR θ (b i) (u i.succ) -
          (betaRB θ (b i) (u i.succ) * (b' i - b i) + betaRX θ (b i) (u i.succ) * (u' i.succ - u i.succ)) =
          betaR θ (b' i) (u' i.succ) - betaR θ (b i) (u i.succ) -
            betaRB θ (b i) (u i.succ) * (b' i - b i) - betaRX θ (b i) (u i.succ) * (u' i.succ - u i.succ) := by
        ring
      rw [e, one_mul]; exact h)
  rw [one_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  refine h.trans ?_
  have := sum_succ_le (fun j => u' j - u j)
  have hB5 : 0 ≤ B + 5 := by linarith
  have := mul_le_mul_of_nonneg_left this hB5
  unfold sq2
  linarith

noncomputable def cP (B : ℝ) : ℝ := 400000 + 105 * B

theorem robP_model {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (B : ℝ) (hB : 0 ≤ B)
    (u u' : Fin (n + 1) → ℝ) (a a' b b' : Fin n → ℝ) (ha : sq2 a ≤ B ^ 2) (hb : ∀ i, |b i| ≤ B) :
    |robP θ u' a' b' - robP θ u a b -
      dP θ u a b (fun j => u' j - u j) (fun i => a' i - a i) (fun i => b' i - b i)| ≤
      cP B * (sq1 (fun j => u' j - u j) + sq2 (fun i => a' i - a i) + sq2 (fun i => b' i - b i)) := by
  set S := sq1 (fun j => u' j - u j)
  set Sa := sq2 (fun i => a' i - a i)
  set Sb := sq2 (fun i => b' i - b i)
  have hS : 0 ≤ S := sq1_nonneg (fun j => u' j - u j)
  have hSa : 0 ≤ Sa := sq2_nonneg (fun i => a' i - a i)
  have hSb : 0 ≤ Sb := sq2_nonneg (fun i => b' i - b i)
  set G1 := ∑ j : Fin n, (nu (zeta θ (u' j.succ)) - nu (zeta θ (u j.succ)) -
      dnu (zeta θ (u j.succ)) * dzeta θ (u j.succ) * (u' j.succ - u j.succ))
  set G2 := ∑ j, (rr (zeta θ (u' j)) ^ 2 - rr (zeta θ (u j)) ^ 2 -
      2 * rr (zeta θ (u j)) * drr (zeta θ (u j)) * dzeta θ (u j) * (u' j - u j))
  set G3 := ∑ i, (zeta θ (a' i) ^ 2 - zeta θ (a i) ^ 2 - 2 * zeta θ (a i) * dzeta θ (a i) * (a' i - a i))
  set G4 := ∑ i, (a' i * rho (zu θ u') i - a i * rho (zu θ u) i -
      ((a' i - a i) * rho (zu θ u) i + a i * dRho θ u (fun j => u' j - u j) i))
  set G5 := (1 / 2) * ∑ i, rho (zu θ u') i ^ 2 - (1 / 2) * ∑ i, rho (zu θ u) i ^ 2 -
      ∑ i, rho (zu θ u) i * dRho θ u (fun j => u' j - u j) i
  set G6 := ∑ i, (zeta θ (b' i) ^ 2 - zeta θ (b i) ^ 2 - 2 * zeta θ (b i) * dzeta θ (b i) * (b' i - b i))
  set G7 := ∑ i, (betaR θ (b' i) (u' i.succ) - betaR θ (b i) (u i.succ) -
      (betaRB θ (b i) (u i.succ) * (b' i - b i) + betaRX θ (b i) (u i.succ) * (u' i.succ - u i.succ)))
  set G8 := ∑ j : Fin n, (rr (zeta θ (u' j.succ)) ^ 2 - rr (zeta θ (u j.succ)) ^ 2 -
      2 * rr (zeta θ (u j.succ)) * drr (zeta θ (u j.succ)) * dzeta θ (u j.succ) * (u' j.succ - u j.succ))
  have e : robP θ u' a' b' - robP θ u a b -
      dP θ u a b (fun j => u' j - u j) (fun i => a' i - a i) (fun i => b' i - b i) =
      -cη * G1 + cη / 2 * G2 + G3 - G4 + G5 + G6 - G7 + (1 / 2) * G8 := by
    simp only [robP, dP, G1, G2, G3, G4, G5, G6, G7, G8, Finset.sum_sub_distrib]
    ring
  rw [e]
  have g1 : |G1| ≤ 21 * S := grp_nu hθ u u'
  have g2 : |G2| ≤ 35 * S := grp_rr hθ u u'
  have g3 : |G3| ≤ 7 * Sa := grp_sq hθ a a'
  have g4 : |G4| ≤ (104 * B + 3) * S + 3 * Sa := grp_arho hθ B hB u u' a a' ha
  have g5 : |G5| ≤ 122 * S := by
    have h := grp_rhosq hθ u u'
    rwa [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  have g6 : |G6| ≤ 7 * Sb := grp_sq hθ b b'
  have g7 : |G7| ≤ 3 * Sb + (B + 5) * S := grp_betaR hθ hθ1 B hB u u' b b' hb
  have g8 : |G8| ≤ 35 * S := grp_rr_succ hθ u u'
  clear_value G1 G2 G3 G4 G5 G6 G7 G8 S Sa Sb
  have hc : cη = 10000 := rfl
  rw [hc]
  have q1 := abs_le.mp g1; have q2 := abs_le.mp g2; have q3 := abs_le.mp g3
  have q4 := abs_le.mp g4; have q5 := abs_le.mp g5; have q6 := abs_le.mp g6
  have q7 := abs_le.mp g7; have q8 := abs_le.mp g8
  unfold cP
  have hBS := mul_nonneg hB hS
  have hBa := mul_nonneg hB hSa
  have hBb := mul_nonneg hB hSb
  rw [abs_le]; constructor <;> linarith

noncomputable def cF (B : ℝ) : ℝ := cP B + 40

theorem robF_model {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (B : ℝ) (hB : 0 ≤ B)
    (u u' : Fin (n + 1) → ℝ) (a a' b b' : Fin n → ℝ) (y y' : Fin n → Fin (m + 1) → ℝ)
    (ha : sq2 a ≤ B ^ 2) (hb : ∀ i, |b i| ≤ B) :
    |robF θ τ u' a' b' y' - robF θ τ u a b y -
      dF θ τ u a b y (fun j => u' j - u j) (fun i => a' i - a i) (fun i => b' i - b i)
        (fun i k => y' i k - y i k)| ≤
      cF B * nsq (fun j => u' j - u j) (fun i => a' i - a i) (fun i => b' i - b i)
        (fun i k => y' i k - y i k) := by
  have hP := robP_model hθ hθ1 B hB u u' a a' b b' ha hb
  have hBl := sum_model_bound Finset.univ
    (fun i => robB θ τ (a' i) (b' i) (y' i) - robB θ τ (a i) (b i) (y i) -
      dB θ τ (a i) (b i) (y i) (a' i - a i) (b' i - b i) (fun k => y' i k - y i k))
    (fun i => (a' i - a i) ^ 2 + (b' i - b i) ^ 2 + ∑ k, (y' i k - y i k) ^ 2) 40
    (fun i => robB_model hθ hτ (a i) (b i) (a' i) (b' i) (y i) (y' i))
  have e : robF θ τ u' a' b' y' - robF θ τ u a b y -
      dF θ τ u a b y (fun j => u' j - u j) (fun i => a' i - a i) (fun i => b' i - b i)
        (fun i k => y' i k - y i k) =
      (robP θ u' a' b' - robP θ u a b -
        dP θ u a b (fun j => u' j - u j) (fun i => a' i - a i) (fun i => b' i - b i)) +
      ∑ i, (robB θ τ (a' i) (b' i) (y' i) - robB θ τ (a i) (b i) (y i) -
        dB θ τ (a i) (b i) (y i) (a' i - a i) (b' i - b i) (fun k => y' i k - y i k)) := by
    simp only [robF, dF, Finset.sum_sub_distrib]; ring
  rw [e]
  have hs : ∑ i, ((a' i - a i) ^ 2 + (b' i - b i) ^ 2 + ∑ k, (y' i k - y i k) ^ 2) =
      sq2 (fun i => a' i - a i) + sq2 (fun i => b' i - b i) + sqY (fun i k => y' i k - y i k) := by
    simp only [sq2, sqY, Finset.sum_add_distrib]
  rw [hs] at hBl
  have hY := sqY_nonneg (fun i k => y' i k - y i k)
  have hS := sq1_nonneg (fun j => u' j - u j)
  have hSa := sq2_nonneg (fun i => a' i - a i)
  have hSb := sq2_nonneg (fun i => b' i - b i)
  have hcP : 40 ≤ cP B := by unfold cP; linarith
  calc _ ≤ |robP θ u' a' b' - robP θ u a b -
        dP θ u a b (fun j => u' j - u j) (fun i => a' i - a i) (fun i => b' i - b i)| +
      |∑ i, (robB θ τ (a' i) (b' i) (y' i) - robB θ τ (a i) (b i) (y i) -
        dB θ τ (a i) (b i) (y i) (a' i - a i) (b' i - b i) (fun k => y' i k - y i k))| :=
        abs_add_le _ _
    _ ≤ _ := by
      unfold cF nsq
      have hcY := mul_nonneg (by linarith : (0 : ℝ) ≤ cP B) hY
      linarith

lemma dP_add (θ : ℝ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (du du' : Fin (n + 1) → ℝ)
    (da da' db db' : Fin n → ℝ) :
    dP θ u a b (du + du') (da + da') (db + db') = dP θ u a b du da db + dP θ u a b du' da' db' := by
  simp only [dP, dRho_add, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

lemma dP_smul (θ : ℝ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (c : ℝ) (du : Fin (n + 1) → ℝ)
    (da db : Fin n → ℝ) :
    dP θ u a b (c • du) (c • da) (c • db) = c * dP θ u a b du da db := by
  simp only [dP, dRho_smul, Pi.smul_apply, smul_eq_mul, mul_add, mul_sub, Finset.mul_sum]
  ring_nf

lemma dB_add (θ τ a b : ℝ) (y : Fin (m + 1) → ℝ) (da da' db db' : ℝ) (dy dy' : Fin (m + 1) → ℝ) :
    dB θ τ a b y (da + da') (db + db') (dy + dy') = dB θ τ a b y da db dy + dB θ τ a b y da' db' dy' := by
  simp only [dB, Pi.add_apply]
  have : ∑ k : Fin m, dhuber τ (zeta (2 * θ) (y k.castSucc - y k.succ)) *
      dzeta (2 * θ) (y k.castSucc - y k.succ) * (dy k.castSucc + dy' k.castSucc - (dy k.succ + dy' k.succ)) =
      ∑ k : Fin m, dhuber τ (zeta (2 * θ) (y k.castSucc - y k.succ)) *
        dzeta (2 * θ) (y k.castSucc - y k.succ) * (dy k.castSucc - dy k.succ) +
      ∑ k : Fin m, dhuber τ (zeta (2 * θ) (y k.castSucc - y k.succ)) *
        dzeta (2 * θ) (y k.castSucc - y k.succ) * (dy' k.castSucc - dy' k.succ) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]; ring

lemma dB_smul (θ τ a b : ℝ) (y : Fin (m + 1) → ℝ) (c da db : ℝ) (dy : Fin (m + 1) → ℝ) :
    dB θ τ a b y (c * da) (c * db) (c • dy) = c * dB θ τ a b y da db dy := by
  simp only [dB, Pi.smul_apply, smul_eq_mul]
  have : ∑ k : Fin m, dhuber τ (zeta (2 * θ) (y k.castSucc - y k.succ)) *
      dzeta (2 * θ) (y k.castSucc - y k.succ) * (c * dy k.castSucc - c * dy k.succ) =
      c * ∑ k : Fin m, dhuber τ (zeta (2 * θ) (y k.castSucc - y k.succ)) *
        dzeta (2 * θ) (y k.castSucc - y k.succ) * (dy k.castSucc - dy k.succ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]; ring

lemma dF_add (θ τ : ℝ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (y : Fin n → Fin (m + 1) → ℝ)
    (du du' : Fin (n + 1) → ℝ) (da da' db db' : Fin n → ℝ) (dy dy' : Fin n → Fin (m + 1) → ℝ) :
    dF θ τ u a b y (du + du') (da + da') (db + db') (dy + dy') =
      dF θ τ u a b y du da db dy + dF θ τ u a b y du' da' db' dy' := by
  simp only [dF, dP_add, Pi.add_apply]
  have : ∀ i, dB θ τ (a i) (b i) (y i) (da i + da' i) (db i + db' i) (dy i + dy' i) =
      dB θ τ (a i) (b i) (y i) (da i) (db i) (dy i) + dB θ τ (a i) (b i) (y i) (da' i) (db' i) (dy' i) :=
    fun i => dB_add θ τ (a i) (b i) (y i) _ _ _ _ _ _
  simp only [this, Finset.sum_add_distrib]
  ring

lemma dF_smul (θ τ : ℝ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (y : Fin n → Fin (m + 1) → ℝ)
    (c : ℝ) (du : Fin (n + 1) → ℝ) (da db : Fin n → ℝ) (dy : Fin n → Fin (m + 1) → ℝ) :
    dF θ τ u a b y (c • du) (c • da) (c • db) (c • dy) = c * dF θ τ u a b y du da db dy := by
  simp only [dF, dP_smul, Pi.smul_apply, smul_eq_mul]
  have : ∀ i, dB θ τ (a i) (b i) (y i) (c * da i) (c * db i) (c • dy i) =
      c * dB θ τ (a i) (b i) (y i) (da i) (db i) (dy i) :=
    fun i => dB_smul θ τ (a i) (b i) (y i) c _ _ _
  simp only [this, ← Finset.mul_sum]
  ring

end LongTails.Proofs.NcConcaveModel

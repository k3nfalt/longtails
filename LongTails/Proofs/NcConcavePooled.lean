import LongTails.Proofs.NcConcavePartTwo

open scoped BigOperators

namespace LongTails.Proofs.NcConcavePooled

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds LongTails.Proofs.NcConcavePsi
open LongTails.Proofs.NcConcavePartTwo

variable {n : ℕ}

lemma phi_tail (t : ℝ) : t ^ 2 / 2 - 2 ≤ rr t * drr t * t - dnu t * t := by
  rw [rr_cases, drr_cases, dnu_cases]
  split_ifs with h1 h2 <;> nlinarith [sq_nonneg (t - 1), sq_nonneg t, sq_nonneg (t - 2)]

lemma phi_zero (t : ℝ) : t ^ 2 / 2 - 4 ≤ rr t * drr t * t - t := by
  rw [rr_cases, drr_cases]
  split_ifs with h1 h2 <;> nlinarith [sq_nonneg (t - 1), sq_nonneg t, sq_nonneg (t - 2)]

lemma phi_rr (t : ℝ) : -(1 / 10) ≤ rr t * drr t * t := by
  rw [rr_cases, drr_cases]
  split_ifs with h1 h2
  · nlinarith
  · nlinarith [sq_nonneg (t - 3 / 4), mul_nonneg (sq_nonneg t) (sq_nonneg (t - 3 / 4))]
  · nlinarith

lemma sq1_sqrt_le {v : Fin (n + 1) → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : sq1 v ≤ r ^ 2) :
    Real.sqrt (sq1 v) ≤ r := by rw [Real.sqrt_le_left hr]; exact h

lemma radial_bound (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (ha : sq2 a ≤ Rab ^ 2)
    (hb : sq2 b ≤ Rab ^ 2) (hu : 16 * (n + 1) ≤ sq1 u) :
    Real.sqrt (sq1 u) ≤ dpsiU u a b u := by
  have hsq : 0 ≤ sq1 u := sq1_nonneg u
  set U := Real.sqrt (sq1 u) with hU
  have hU2 : U ^ 2 = sq1 u := Real.sq_sqrt hsq
  have hU0 : 0 ≤ U := Real.sqrt_nonneg _
  have hU4 : 4 ≤ U := by
    rw [hU, Real.le_sqrt (by norm_num) hsq]
    have : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    nlinarith
  have hH : cη * (sq1 u / 2 - 2 * (n + 1) - 4) ≤ dhpart u u := by
    unfold dhpart
    rw [Fin.sum_univ_succ (fun j => rr (u j) * drr (u j) * u j)]
    have h0 := phi_zero (u 0)
    have ht := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => phi_tail (u j.succ))
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at ht
    have hs : sq1 u = u 0 ^ 2 + ∑ j : Fin n, u j.succ ^ 2 := by unfold sq1; rw [Fin.sum_univ_succ]
    have hc : (0 : ℝ) < cη := by norm_num [cη]
    have e : -cη * u 0 - cη * ∑ j : Fin n, dnu (u j.succ) * u j.succ +
        cη * (rr (u 0) * drr (u 0) * u 0 + ∑ i : Fin n, rr (u i.succ) * drr (u i.succ) * u i.succ) =
        cη * ((rr (u 0) * drr (u 0) * u 0 - u 0) +
          ∑ i : Fin n, (rr (u i.succ) * drr (u i.succ) * u i.succ - dnu (u i.succ) * u i.succ)) := by
      rw [Finset.sum_sub_distrib]; simp only [mul_comm (dnu _)]; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hc.le
    rw [Finset.sum_sub_distrib]
    have : ∑ j : Fin n, u j.succ ^ 2 / 2 = (∑ j : Fin n, u j.succ ^ 2) / 2 := by
      rw [Finset.sum_div]
    nlinarith
  have hrho : -(10 * U) ≤ -∑ i, (a i - rho u i) * drho u u i := by
    have h1 := cs_bound (fun i => a i - rho u i) (drho u u)
    have h2 : Real.sqrt (sq2 fun i => a i - rho u i) ≤ 10 / 3 :=
      (Real.sqrt_le_sqrt (sq2_a_sub_rho_le u a ha)).trans sqrt_ten_le
    have h3 : Real.sqrt (sq2 (drho u u)) ≤ 3 * U := by
      rw [Real.sqrt_le_left (by positivity)]
      have := sq2_drho_le_nine u u
      nlinarith
    have h4 := le_abs_self (∑ i, (a i - rho u i) * drho u u i)
    nlinarith [mul_le_mul h2 h3 (Real.sqrt_nonneg _) (by norm_num),
      Real.sqrt_nonneg (sq2 fun i => a i - rho u i), Real.sqrt_nonneg (sq2 (drho u u))]
  have hbp : -(2 * U) - n / 10 ≤ -∑ i, (b i - rb u i) * (drr (u i.succ) * u i.succ) := by
    have e : -∑ i, (b i - rb u i) * (drr (u i.succ) * u i.succ) =
        -∑ i : Fin n, b i * (drr (u i.succ) * u i.succ) +
          ∑ i : Fin n, rr (u i.succ) * drr (u i.succ) * u i.succ := by
      simp only [rb, sub_mul, Finset.sum_sub_distrib]; rw [neg_sub]
      rw [show (∑ i : Fin n, rr (u i.succ) * (drr (u i.succ) * u i.succ)) =
        ∑ i : Fin n, rr (u i.succ) * drr (u i.succ) * u i.succ from Finset.sum_congr rfl fun i _ => by ring]
      ring
    rw [e]
    have h1 := cs_bound b (fun i : Fin n => drr (u i.succ) * u i.succ)
    have h2 : Real.sqrt (sq2 b) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; have : Rab ^ 2 = 2 ^ 2 := by norm_num [Rab]
      linarith
    have h3 : Real.sqrt (sq2 fun i => drr (u i.succ) * u i.succ) ≤ U := by
      apply Real.sqrt_le_sqrt
      have : sq2 (fun i => drr (u i.succ) * u i.succ) ≤ ∑ i : Fin n, u i.succ ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        rw [mul_pow]
        have := drr_abs (u i.succ)
        have h' : drr (u i.succ) ^ 2 ≤ 1 := by
          rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) this
        nlinarith [sq_nonneg (u i.succ)]
      exact this.trans (sum_succ_le u)
    have h4 := le_abs_self (∑ i, b i * (drr (u i.succ) * u i.succ))
    have h5 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => phi_rr (u i.succ))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h5
    nlinarith [mul_le_mul h2 h3 (Real.sqrt_nonneg _) (by norm_num), Real.sqrt_nonneg (sq2 b)]
  have hdef : dpsiU u a b u = dhpart u u - ∑ i, (a i - rho u i) * drho u u i -
      ∑ i, (b i - rb u i) * (drr (u i.succ) * u i.succ) := rfl
  rw [hdef]
  have hn : (n : ℝ) + 1 ≤ sq1 u / 16 := by linarith
  have hc : cη = 10000 := rfl
  rw [hc] at hH
  nlinarith

lemma gab_inner (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) :
    2 * (sq2 (fun i => a i - astar u i) + sq2 (fun i => b i - bstar u i)) ≤
      ∑ i, ((gab u a b i).1 * (a i - astar u i) + (gab u a b i).2 * (b i - bstar u i)) := by
  unfold sq2
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  simp only [gab, astar, bstar]
  nlinarith [sq_nonneg ((a i - (9 / 26 * rho u i + 1 / 13 * rb u i)) -
    (b i - (1 / 13 * rho u i + 6 / 13 * rb u i)) / 2)]

lemma gab_norm (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) :
    ∑ i, ((gab u a b i).1 ^ 2 + (gab u a b i).2 ^ 2) ≤
      16 * (sq2 (fun i => a i - astar u i) + sq2 (fun i => b i - bstar u i)) := by
  unfold sq2
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  simp only [gab, astar, bstar]
  nlinarith [sq_nonneg ((a i - (9 / 26 * rho u i + 1 / 13 * rb u i)) +
    (b i - (1 / 13 * rho u i + 6 / 13 * rb u i))),
    sq_nonneg ((a i - (9 / 26 * rho u i + 1 / 13 * rb u i)) -
    (b i - (1 / 13 * rho u i + 6 / 13 * rb u i)))]

lemma sq_add_le_two (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

lemma sq_sub_le_two (x y : ℝ) : (x - y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x + y)]

lemma sq_add_le_32 (x y : ℝ) : (x + y) ^ 2 ≤ 3 / 2 * x ^ 2 + 3 * y ^ 2 := by
  nlinarith [sq_nonneg (x - 2 * y)]

noncomputable def resU (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (l : ℝ) : ℝ :=
  ∑ j, (gu u a b j + l * u j) ^ 2

noncomputable def resAB (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (m : ℝ) : ℝ :=
  ∑ i, (((gab u a b i).1 + m * a i) ^ 2 + ((gab u a b i).2 + m * b i) ^ 2)

lemma u_part (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (Su l R2 : ℝ) (hl : 0 ≤ l)
    (hR2 : 256 * (n + 1) ≤ R2) (hlslack : 0 < l → sq1 u + Su = R2)
    (ha : sq2 a ≤ Rab ^ 2) (hb : sq2 b ≤ Rab ^ 2)
    (hRU : resU u a b l < (cδ / 3) ^ 2) (hlSu : l ^ 2 * Su < (cδ / 3) ^ 2) :
    sq1 (gu u a b) < cδ ^ 2 := by
  have hc0 : 0 < cδ / 3 := by norm_num [cδ]
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases eq_or_lt_of_le hl with hl0 | hlpos
  · subst hl0
    have : sq1 (gu u a b) = resU u a b 0 := by simp [resU, sq1]
    rw [this]
    have : (cδ / 3) ^ 2 ≤ cδ ^ 2 := by norm_num [cδ]
    linarith
  · have hbd := hlslack hlpos
    by_cases hbig : R2 / 16 ≤ sq1 u
    · exfalso
      have hrad := radial_bound u a b ha hb (by linarith)
      have hinner : dpsiU u a b u + l * sq1 u = ∑ j, (gu u a b j + l * u j) * u j := by
        rw [dpsiU_eq_sum]; unfold sq1
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hcs := cs_bound1 (fun j => gu u a b j + l * u j) u
      have hRU' : Real.sqrt (sq1 fun j => gu u a b j + l * u j) < cδ / 3 := by
        rw [Real.sqrt_lt' hc0]; exact hRU
      have hpos : 0 < Real.sqrt (sq1 u) := by
        apply Real.sqrt_pos.mpr; nlinarith
      have h1 : Real.sqrt (sq1 u) ≤ |∑ j, (gu u a b j + l * u j) * u j| := by
        rw [← hinner]
        have := mul_nonneg hlpos.le (sq1_nonneg u)
        rw [abs_of_nonneg (by linarith)]; linarith
      have h2 := h1.trans hcs
      have h3 : Real.sqrt (sq1 u) < cδ / 3 * Real.sqrt (sq1 u) :=
        lt_of_le_of_lt h2 (mul_lt_mul_of_pos_right hRU' hpos)
      have hc1 : cδ / 3 < 1 := by norm_num [cδ]
      nlinarith
    · push Not at hbig
      have hSu' : 15 * (R2 / 16) ≤ Su := by linarith
      have hl2 : l ^ 2 * (15 * (R2 / 16)) < (cδ / 3) ^ 2 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left hSu' (sq_nonneg l)) hlSu
      have hlu : l ^ 2 * sq1 u ≤ l ^ 2 * (R2 / 16) :=
        mul_le_mul_of_nonneg_left hbig.le (sq_nonneg l)
      have hpt : ∀ j, gu u a b j ^ 2 ≤ 2 * (gu u a b j + l * u j) ^ 2 + 2 * (l ^ 2 * u j ^ 2) :=
        fun j => by
          have := sq_sub_le_two (gu u a b j + l * u j) (l * u j)
          have e : gu u a b j + l * u j - l * u j = gu u a b j := by ring
          rw [e, mul_pow] at this; linarith
      have htri : sq1 (gu u a b) ≤ 2 * resU u a b l + 2 * (l ^ 2 * sq1 u) := by
        calc sq1 (gu u a b) ≤ ∑ j, (2 * (gu u a b j + l * u j) ^ 2 + 2 * (l ^ 2 * u j ^ 2)) :=
              Finset.sum_le_sum fun j _ => hpt j
          _ = _ := by simp only [resU, sq1, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hR0 : 0 ≤ R2 := by linarith
      have e9 : cδ ^ 2 = 9 * (cδ / 3) ^ 2 := by ring
      nlinarith

lemma star_small (u : Fin (n + 1) → ℝ) (hrb : Real.sqrt (sq2 (rb u)) ≤ κ) :
    sq2 (astar u) + sq2 (bstar u) ≤ 1 / 4 := by
  have hk := κ_small
  have hk0 := κ_pos
  have h1 : sq2 (astar u) ≤ 3 / 2 * (9 / 26) ^ 2 * sq2 (rho u) + 3 * (1 / 13) ^ 2 * sq2 (rb u) := by
    unfold sq2 astar; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i _
    have := sq_add_le_32 (9 / 26 * rho u i) (1 / 13 * rb u i)
    rw [mul_pow, mul_pow] at this; linarith
  have h2 : sq2 (bstar u) ≤ 3 / 2 * (1 / 13) ^ 2 * sq2 (rho u) + 3 * (6 / 13) ^ 2 * sq2 (rb u) := by
    unfold sq2 bstar; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i _
    have := sq_add_le_32 (1 / 13 * rho u i) (6 / 13 * rb u i)
    rw [mul_pow, mul_pow] at this; linarith
  have h3 := sq2_rho_le_one u
  have h4 : sq2 (rb u) ≤ κ ^ 2 := by
    have := Real.sq_sqrt (sq2_nonneg (rb u))
    have h5 := Real.sqrt_nonneg (sq2 (rb u))
    nlinarith
  have h5 : κ ^ 2 ≤ 1 / 100 := by nlinarith
  norm_num at h1 h2 ⊢
  linarith

lemma ab_small_case (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (Sab m : ℝ) (hSab : 0 ≤ Sab) (hmpos : 0 < m)
    (hbd : sq2 a + sq2 b + Sab = Rab ^ 2) (hoff : ¬ Rab ^ 2 / 4 ≤ Sab)
    (hRA : resAB u a b m < (cδ / 3) ^ 2)
    (hstar : sq2 (astar u) + sq2 (bstar u) ≤ 1 / 4) : False := by
  push Not at hoff
  set da : Fin n → ℝ := fun i => a i - astar u i
  set db : Fin n → ℝ := fun i => b i - bstar u i
  have hmono := gab_inner u a b
  have hnorm := gab_norm u a b
  set Dd := sq2 da + sq2 db with hDd
  have hD0 : 0 ≤ Dd := add_nonneg (sq2_nonneg _) (sq2_nonneg _)
  set Gs := ∑ i, ((gab u a b i).1 ^ 2 + (gab u a b i).2 ^ 2)
  have hRab : Rab ^ 2 = 4 := by norm_num [Rab]
  have hz : 3 ≤ sq2 a + sq2 b := by linarith
  have hrad : ∑ i, ((gab u a b i).1 * a i + (gab u a b i).2 * b i) ≤
      ∑ i, (((gab u a b i).1 + m * a i) * a i + ((gab u a b i).2 + m * b i) * b i) := by
    apply Finset.sum_le_sum; intro i _
    have := mul_nonneg hmpos.le (add_nonneg (sq_nonneg (a i)) (sq_nonneg (b i)))
    nlinarith
  have hsplit : ∑ i, ((gab u a b i).1 * a i + (gab u a b i).2 * b i) =
      ∑ i, ((gab u a b i).1 * da i + (gab u a b i).2 * db i) +
        ∑ i, ((gab u a b i).1 * astar u i + (gab u a b i).2 * bstar u i) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by simp only [da, db]; ring
  have hcs2 : (∑ i, ((gab u a b i).1 * astar u i + (gab u a b i).2 * bstar u i)) ^ 2 ≤
      Gs * (sq2 (astar u) + sq2 (bstar u)) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k : Fin n ⊕ Fin n => Sum.elim (fun i => (gab u a b i).1) (fun i => (gab u a b i).2) k)
      (fun k => Sum.elim (astar u) (bstar u) k)
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at this
    simpa [Gs, sq2, Finset.sum_add_distrib] using this
  have hD : 5 / 4 ≤ Dd := by
    have h1 : sq2 a + sq2 b ≤ 2 * Dd + 2 * (sq2 (astar u) + sq2 (bstar u)) := by
      have e1 : sq2 a ≤ 2 * sq2 da + 2 * sq2 (astar u) := by
        unfold sq2; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum; intro i _
        have := sq_add_le_two (da i) (astar u i)
        have e : da i + astar u i = a i := by simp only [da]; ring
        rw [e] at this; exact this
      have e2 : sq2 b ≤ 2 * sq2 db + 2 * sq2 (bstar u) := by
        unfold sq2; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum; intro i _
        have := sq_add_le_two (db i) (bstar u i)
        have e : db i + bstar u i = b i := by simp only [db]; ring
        rw [e] at this; exact this
      linarith
    linarith
  have hGs : Gs ≤ 16 * Dd := hnorm
  set I1 := ∑ i, ((gab u a b i).1 * da i + (gab u a b i).2 * db i)
  set I2 := ∑ i, ((gab u a b i).1 * astar u i + (gab u a b i).2 * bstar u i)
  have hI2 : I2 ^ 2 ≤ 4 * Dd := by
    calc I2 ^ 2 ≤ Gs * (sq2 (astar u) + sq2 (bstar u)) := hcs2
      _ ≤ 16 * Dd * (1 / 4) := mul_le_mul hGs hstar (add_nonneg (sq2_nonneg _) (sq2_nonneg _))
          (by linarith)
      _ = 4 * Dd := by ring
  have hsq : Real.sqrt Dd ^ 2 = Dd := Real.sq_sqrt hD0
  have hsD0 := Real.sqrt_nonneg Dd
  have hI2' : -I2 ≤ 2 * Real.sqrt Dd := by
    by_contra hc; push Not at hc
    have : (2 * Real.sqrt Dd) ^ 2 < I2 ^ 2 := by nlinarith
    nlinarith
  have hsD : 11 / 10 ≤ Real.sqrt Dd := by
    rw [Real.le_sqrt (by norm_num) hD0]; linarith
  have hlow : 2 * Dd - 2 * Real.sqrt Dd ≤ ∑ i, (((gab u a b i).1 + m * a i) * a i +
      ((gab u a b i).2 + m * b i) * b i) := by linarith
  have hcs3 : (∑ i, (((gab u a b i).1 + m * a i) * a i + ((gab u a b i).2 + m * b i) * b i)) ^ 2 ≤
      resAB u a b m * (sq2 a + sq2 b) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k : Fin n ⊕ Fin n => Sum.elim (fun i => (gab u a b i).1 + m * a i)
        (fun i => (gab u a b i).2 + m * b i) k)
      (fun k => Sum.elim a b k)
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at this
    simpa [resAB, sq2, Finset.sum_add_distrib] using this
  have hRA0 : 0 ≤ resAB u a b m := Finset.sum_nonneg fun _ _ => by positivity
  have hab4 : sq2 a + sq2 b ≤ 4 := by linarith
  have hlow0 : 0 ≤ 2 * Dd - 2 * Real.sqrt Dd := by nlinarith
  have hlow2 : (2 * Dd - 2 * Real.sqrt Dd) ^ 2 ≤ resAB u a b m * 4 :=
    (pow_le_pow_left₀ hlow0 hlow 2).trans (hcs3.trans (mul_le_mul_of_nonneg_left hab4 hRA0))
  have hc1 : (cδ / 3) ^ 2 < 1 / 100 := by norm_num [cδ]
  have h11 : 11 / 10 * (2 * (11 / 10) - 2) ≤ Real.sqrt Dd * (2 * Real.sqrt Dd - 2) := by
    apply mul_le_mul hsD (by linarith) (by norm_num) hsD0
  have e : 2 * Dd - 2 * Real.sqrt Dd = Real.sqrt Dd * (2 * Real.sqrt Dd - 2) := by
    rw [show Real.sqrt Dd * (2 * Real.sqrt Dd - 2) = 2 * Real.sqrt Dd ^ 2 - 2 * Real.sqrt Dd by ring, hsq]
  rw [e] at hlow2
  have h22 : (11 / 10 * (2 * (11 / 10) - 2)) ^ 2 ≤ (Real.sqrt Dd * (2 * Real.sqrt Dd - 2)) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) h11 2
  nlinarith

lemma ab_part (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (Sab m : ℝ) (hSab : 0 ≤ Sab) (hm : 0 ≤ m)
    (hABfeas : sq2 a + sq2 b + Sab ≤ Rab ^ 2) (hmslack : 0 < m → sq2 a + sq2 b + Sab = Rab ^ 2)
    (hRA : resAB u a b m < (cδ / 3) ^ 2) (hmSab : m ^ 2 * Sab < (cδ / 3) ^ 2)
    (hstar : sq2 (astar u) + sq2 (bstar u) ≤ 1 / 4) :
    sq2 (fun i => a i - astar u i) + sq2 (fun i => b i - bstar u i) ≤ (cδ / 2) ^ 2 := by
  have hmono := gab_inner u a b
  have hnorm := gab_norm u a b
  set Dd := sq2 (fun i => a i - astar u i) + sq2 (fun i => b i - bstar u i) with hDd
  have hD0 : 0 ≤ Dd := add_nonneg (sq2_nonneg _) (sq2_nonneg _)
  set Gs := ∑ i, ((gab u a b i).1 ^ 2 + (gab u a b i).2 ^ 2) with hGs
  have hcsg : (∑ i, ((gab u a b i).1 * (a i - astar u i) + (gab u a b i).2 * (b i - bstar u i))) ^ 2 ≤
      Gs * Dd := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k : Fin n ⊕ Fin n => Sum.elim (fun i => (gab u a b i).1) (fun i => (gab u a b i).2) k)
      (fun k => Sum.elim (fun i => a i - astar u i) (fun i => b i - bstar u i) k)
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at this
    simpa [Gs, Dd, sq2, Finset.sum_add_distrib] using this
  have hsq : (2 * Dd) ^ 2 ≤ Gs * Dd := (pow_le_pow_left₀ (by positivity) hmono 2).trans hcsg
  have hG0 : 0 ≤ Gs := Finset.sum_nonneg fun _ _ => by positivity
  have key : ∀ G : ℝ, Gs ≤ G → G ≤ cδ ^ 2 → Dd ≤ (cδ / 2) ^ 2 := by
    intro G hG hGc
    rcases eq_or_lt_of_le hD0 with h0 | h0
    · rw [← h0]; positivity
    · have : 4 * Dd ≤ Gs := by nlinarith
      nlinarith
  rcases eq_or_lt_of_le hm with hm0 | hmpos
  · subst hm0
    have hG : Gs = resAB u a b 0 := by simp [Gs, resAB]
    apply key (resAB u a b 0) hG.le
    have : (cδ / 3) ^ 2 ≤ cδ ^ 2 := by norm_num [cδ]
    linarith
  · have hbd := hmslack hmpos
    by_cases hoff : Rab ^ 2 / 4 ≤ Sab
    · have hRab : Rab ^ 2 = 4 := by norm_num [Rab]
      have hm2 : m ^ 2 < (cδ / 3) ^ 2 := by
        have : m ^ 2 * 1 ≤ m ^ 2 * Sab := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg m)
        linarith
      have hz : sq2 a + sq2 b ≤ 4 := by linarith
      have hG : Gs ≤ 2 * resAB u a b m + 2 * m ^ 2 * (sq2 a + sq2 b) := by
        have hpt : ∀ i, (gab u a b i).1 ^ 2 + (gab u a b i).2 ^ 2 ≤
            2 * (((gab u a b i).1 + m * a i) ^ 2 + ((gab u a b i).2 + m * b i) ^ 2) +
              2 * m ^ 2 * (a i ^ 2 + b i ^ 2) := fun i => by
          have h1 := sq_sub_le_two ((gab u a b i).1 + m * a i) (m * a i)
          have h2 := sq_sub_le_two ((gab u a b i).2 + m * b i) (m * b i)
          simp only [add_sub_cancel_right, mul_pow] at h1 h2
          linarith
        calc Gs ≤ ∑ i, (2 * (((gab u a b i).1 + m * a i) ^ 2 + ((gab u a b i).2 + m * b i) ^ 2) +
              2 * m ^ 2 * (a i ^ 2 + b i ^ 2)) := Finset.sum_le_sum fun i _ => hpt i
          _ = _ := by
            simp only [resAB, sq2, Finset.sum_add_distrib, ← Finset.mul_sum]
      apply key (2 * resAB u a b m + 2 * m ^ 2 * (sq2 a + sq2 b)) hG
      have : m ^ 2 * (sq2 a + sq2 b) ≤ (cδ / 3) ^ 2 * 4 :=
        mul_le_mul hm2.le hz (add_nonneg (sq2_nonneg _) (sq2_nonneg _)) (by positivity)
      have e9 : cδ ^ 2 = 9 * (cδ / 3) ^ 2 := by ring
      nlinarith
    · exact (ab_small_case u a b Sab m hSab hmpos hbd hoff hRA hstar).elim

theorem pooled (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (Su Sab l m R2 : ℝ) (hSu : 0 ≤ Su)
    (hSab : 0 ≤ Sab) (hl : 0 ≤ l) (hm : 0 ≤ m) (hR2 : 256 * (n + 1) ≤ R2)
    (hABfeas : sq2 a + sq2 b + Sab ≤ Rab ^ 2)
    (hlslack : 0 < l → sq1 u + Su = R2)
    (hmslack : 0 < m → sq2 a + sq2 b + Sab = Rab ^ 2)
    (hT : u (Fin.last n) ≤ 1 / 4) :
    (cδ / 3) ^ 2 ≤ resU u a b l + l ^ 2 * Su + resAB u a b m + m ^ 2 * Sab := by
  by_contra hcon
  push Not at hcon
  have hRU0 : 0 ≤ resU u a b l := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hRA0 : 0 ≤ resAB u a b m := Finset.sum_nonneg fun _ _ => by positivity
  have h1 := mul_nonneg (sq_nonneg l) hSu
  have h2 := mul_nonneg (sq_nonneg m) hSab
  have hRU : resU u a b l < (cδ / 3) ^ 2 := by linarith
  have hRA : resAB u a b m < (cδ / 3) ^ 2 := by linarith
  have hlSu : l ^ 2 * Su < (cδ / 3) ^ 2 := by linarith
  have hmSab : m ^ 2 * Sab < (cδ / 3) ^ 2 := by linarith
  have ha : sq2 a ≤ Rab ^ 2 := by linarith [sq2_nonneg b]
  have hb : sq2 b ≤ Rab ^ 2 := by linarith [sq2_nonneg a]
  have hgu := u_part u a b Su l R2 hl hR2 hlslack ha hb hRU hlSu
  have hrb := rb_small u a b hgu ha hb
  have hstar := star_small u hrb
  have hdab := ab_part u a b Sab m hSab hm hABfeas hmslack hRA hmSab hstar
  exact part_two u a b hgu ha hb hdab hT

end LongTails.Proofs.NcConcavePooled

import LongTails.Proofs.FractalChebyshevSchedule
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.Factorization.Basic

namespace LongTails.Proofs.FractalChebyshevWeighted

open OracleTemplate.FractalChebyshev

def lowerDegrees (r : ℕ) (c : List (ℕ × ℝ)) : List (ℕ × ℝ) :=
  c.map fun p => (p.1 - r, p.2)

lemma chainBound_lowerDegrees (X : ℝ) (r : ℕ) (c : List (ℕ × ℝ))
    (hc : ∀ p ∈ c, r ≤ p.1) :
    chainBound X c = chainBound (dbl^[r] X) (lowerDegrees r c) := by
  induction c with
  | nil => simp [lowerDegrees, chainBound]
  | cons p c ih =>
    have hp := hc p (by simp)
    have ht : ∀ q ∈ c, r ≤ q.1 := fun q hq => hc q (by simp [hq])
    simp only [lowerDegrees, List.map_cons, chainBound_cons]
    have hi := ih ht
    dsimp [lowerDegrees] at hi
    rw [← hi]
    have he : dbl^[p.1 - r] (dbl^[r] X) = dbl^[p.1] X := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [he]

lemma isChain_lowerDegrees (r : ℕ) (c : List (ℕ × ℝ))
    (hc : ∀ p ∈ c, r ≤ p.1) (hchain : List.IsChain chainRel c) :
    List.IsChain chainRel (lowerDegrees r c) := by
  induction c with
  | nil => simp [lowerDegrees]
  | cons p c ih =>
    cases c with
    | nil => simp [lowerDegrees]
    | cons q c =>
      rw [isChain_cons_cons] at hchain
      have hp := hc p (by simp)
      have hq := hc q (by simp)
      have ht : ∀ z ∈ q :: c, r ≤ z.1 := fun z hz => hc z (by simp [hz])
      have hi := ih ht hchain.2
      change List.IsChain chainRel ((p.1 - r, p.2) :: (q.1 - r, q.2) :: lowerDegrees r c)
      rw [isChain_cons_cons]
      refine ⟨?_, hi⟩
      rcases hchain.1 with ⟨hlt, he⟩
      refine ⟨by dsimp; omega, ?_⟩
      dsimp
      have hd : q.1 - r - (p.1 - r) = q.1 - p.1 := by omega
      rw [hd]
      exact he

lemma chainBound_degree_bound {X : ℝ} (hX : 1 < X) (r : ℕ) (c : List (ℕ × ℝ))
    (hc : ∀ p ∈ c, r ≤ p.1) (hchain : List.IsChain chainRel c)
    (hangle : ∀ p ∈ c, 0 < p.2 ∧ p.2 < Real.pi / 2) :
    chainBound X c ≤ max 1 (2 / (dbl^[r] X - 1)) := by
  rw [chainBound_lowerDegrees X r c hc]
  apply chainBound_collapse (by linarith [le_dbl_iterate hX.le r]) _ _ rfl
    (isChain_lowerDegrees r c hc hchain)
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hangle q hq

lemma chain_even (k s : ℕ) : chain (k + 1) (2 * s) = liftChain (chain k s) := by
  rw [chain]
  have hm : (2 * s) % 2 = 0 := by omega
  have hd : (2 * s + 1) / 2 = s := by omega
  simp [hm, hd]

lemma chain_degree_multiple (r k t : ℕ) (hr : r ≤ k) :
    ∀ p ∈ chain k (2 ^ r * t), r ≤ p.1 := by
  induction r generalizing k with
  | zero => intro p _; exact Nat.zero_le _
  | succ r ih =>
    cases k with
    | zero => omega
    | succ k =>
      have he : 2 ^ (r + 1) * t = 2 * (2 ^ r * t) := by rw [pow_succ]; ring
      rw [he, chain_even]
      intro p hp
      obtain ⟨q, hq, rfl⟩ := mem_liftChain hp
      have := ih k (by omega) q hq
      dsimp
      omega

lemma window_degree_bound (k r t m : ℕ) (hr : r ≤ k) (ht : 2 ^ r * t ≤ 2 ^ k)
    {x X : ℝ} (hX : 1 < X) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |prodF x X (((angles k).drop (2 ^ r * t)).take m)| ≤
      max 1 (2 / (dbl^[r] X - 1)) := by
  obtain ⟨hangle, hchain, -⟩ := chain_props k (2 ^ r * t) ht
  exact (window_le_chain k (2 ^ r * t) m hX hx1 hx2).trans
    (chainBound_degree_bound hX r _ (chain_degree_multiple r k t hr) hchain hangle)

lemma angle_gap (r k j : ℕ) (hr : r < k) (hj : 2 ^ r * (2 * j + 1) ≤ 2 ^ k) :
    Real.pi / (2 : ℝ) ^ (r + 1) ≤
      Real.pi - (angles k).getD (2 ^ r * (2 * j + 1) - 1) 0 := by
  induction r generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k =>
      have hjk : j < (angles k).length := by
        rw [angles_length]
        simp only [pow_zero, one_mul, pow_succ] at hj
        omega
      simp only [pow_zero, one_mul, Nat.add_sub_cancel, angles]
      rw [getD_flatMap_even _ hjk]
      have hp := (getD_mem_angles (by simpa [angles_length] using hjk)).1
      linarith
  | succ r ih =>
    cases k with
    | zero => omega
    | succ k =>
      have hn : 0 < 2 ^ r * (2 * j + 1) := by positivity
      have hjk : 2 ^ r * (2 * j + 1) ≤ 2 ^ k := by
        rw [pow_succ, pow_succ] at hj
        nlinarith
      have hi := ih k (by omega) hjk
      have hindex : 2 ^ (r + 1) * (2 * j + 1) - 1 =
          2 * (2 ^ r * (2 * j + 1) - 1) + 1 := by
        rw [pow_succ]
        rw [show 2 ^ r * 2 * (2 * j + 1) = 2 * (2 ^ r * (2 * j + 1)) by ring]
        omega
      have hlt : 2 ^ r * (2 * j + 1) - 1 < (angles k).length := by
        rw [angles_length]
        omega
      rw [hindex, angles, getD_flatMap_odd _ hlt]
      rw [pow_succ, div_mul_eq_div_div]
      linarith

lemma root_lower_gap {L μ θ T : ℝ} (hμL : μ < L) (hT : 0 < T)
    (hθ : 0 ≤ θ ∧ θ ≤ Real.pi) (hgap : Real.pi / T ≤ Real.pi - θ) :
    μ + (L - μ) / T ^ 2 ≤ (L + μ) / 2 + (L - μ) / 2 * Real.cos θ := by
  have hg : 0 ≤ Real.pi - θ := sub_nonneg.mpr hθ.2
  have hc := Real.cos_le_one_sub_mul_cos_sq
    (show |Real.pi - θ| ≤ Real.pi by rw [abs_of_nonneg hg]; linarith [hθ.1])
  rw [Real.cos_pi_sub] at hc
  have hratio : 1 / T ^ 2 ≤ (Real.pi - θ) ^ 2 / Real.pi ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hT) (sq_pos_of_pos Real.pi_pos)]
    have hp := (div_le_iff₀ hT).mp hgap
    have hs := pow_le_pow_left₀ Real.pi_pos.le hp 2
    nlinarith
  have hcos : 2 / T ^ 2 ≤ 1 + Real.cos θ := by
    have hm := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ 2 by norm_num)
    simp only [div_eq_mul_inv] at hc hm ⊢
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hcos (show 0 ≤ (L - μ) / 2 by positivity)
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith

lemma schedule_window_degree_bound {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L)
    (k r j t : ℕ) (hr : r ≤ k) (hs : 2 ^ r * j ≤ t) (ht : t ≤ 2 ^ k)
    {lam : ℝ} (h0 : 0 ≤ lam) (hL : lam ≤ L) :
    |OracleTemplate.ScheduleBlock.win (etaOf L μ k) lam (2 ^ r * j) t| ≤
      max 1 ((L - μ) / (μ * (4 : ℝ) ^ r)) := by
  rw [win_schedule hμ hμL k lam hs ht]
  have hX := x0_gt_one hμ hμL
  obtain ⟨hx1, hx2⟩ := x_bounds hμL h0 hL
  have hd : 0 < L - μ := by linarith
  rcases le_or_gt lam μ with hlow | hhigh
  · have hx : 1 ≤ (L + μ - 2 * lam) / (L - μ) := by
      rw [le_div_iff₀ hd]; linarith
    obtain ⟨hp, hp'⟩ := prodF_mem_unit hx hx2
      (((angles k).drop (2 ^ r * j)).take (t - 2 ^ r * j))
      (fun θ h => angles_mem (List.mem_of_mem_drop (List.mem_of_mem_take h)))
    rw [abs_of_nonneg hp]
    exact hp'.trans (le_max_left _ _)
  · have hx : (L + μ - 2 * lam) / (L - μ) ≤ 1 := by
      rw [div_le_one hd]; linarith
    refine (window_degree_bound k r j (t - 2 ^ r * j) hr (by omega) hX hx1 hx).trans ?_
    apply max_le_max le_rfl
    have hg := dbl_iterate_ge hX.le r
    have hp : 0 < (4 : ℝ) ^ r := by positivity
    have hden : 0 < (4 : ℝ) ^ r * ((L + μ) / (L - μ) - 1) := by positivity
    calc
      2 / (dbl^[r] ((L + μ) / (L - μ)) - 1) ≤
          2 / ((4 : ℝ) ^ r * ((L + μ) / (L - μ) - 1)) :=
        div_le_div_of_nonneg_left (by norm_num) hden (by linarith)
      _ = (L - μ) / (μ * (4 : ℝ) ^ r) := by
        field_simp [ne_of_gt hμ, ne_of_gt hd]
        ring

lemma etaOf_degree_bound {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L)
    (k r j : ℕ) (hr : r < k) (hj : 2 ^ r * (2 * j + 1) ≤ 2 ^ k) :
    etaOf L μ k (2 ^ r * (2 * j + 1) - 1) ≤ (4 : ℝ) ^ (r + 1) / (L - μ) := by
  have hn : 0 < 2 ^ r * (2 * j + 1) := by positivity
  have hi : 2 ^ r * (2 * j + 1) - 1 < 2 ^ k := by omega
  have hθ := getD_mem_angles hi
  have hg := root_lower_gap hμL (show (0 : ℝ) < 2 ^ (r + 1) by positivity)
    ⟨hθ.1.le, hθ.2.le⟩ (angle_gap r k j hr hj)
  have hd : 0 < L - μ := by linarith
  have hp : ((2 : ℝ) ^ (r + 1)) ^ 2 = (4 : ℝ) ^ (r + 1) := by
    rw [← pow_mul, Nat.mul_comm (r + 1) 2, pow_mul]
    norm_num
  rw [hp] at hg
  rw [etaOf_eq hi]
  unfold stepOf
  calc
    _ ≤ 1 / ((L - μ) / (4 : ℝ) ^ (r + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    _ = (4 : ℝ) ^ (r + 1) / (L - μ) := by rw [one_div_div]

lemma weighted_window_of_index {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L)
    (k r j t : ℕ) (hr : r < k) (hs : 2 ^ r * (2 * j + 1) ≤ t) (ht : t ≤ 2 ^ k)
    {lam : ℝ} (h0 : 0 ≤ lam) (hL : lam ≤ L) :
    etaOf L μ k (2 ^ r * (2 * j + 1) - 1) *
      |OracleTemplate.ScheduleBlock.win (etaOf L μ k) lam (2 ^ r * (2 * j + 1)) t| ≤ 4 / μ := by
  have hn : 0 < 2 ^ r * (2 * j + 1) := by positivity
  have hi : 2 ^ r * (2 * j + 1) - 1 < 2 ^ k := by omega
  have he0 := etaOf_nonneg hμ hμL k (2 ^ r * (2 * j + 1) - 1)
  have hw := schedule_window_degree_bound hμ hμL k r (2 * j + 1) t hr.le hs ht h0 hL
  have hd : 0 < L - μ := by linarith
  rcases le_total ((L - μ) / (μ * (4 : ℝ) ^ r)) 1 with hb | hb
  · rw [max_eq_left hb] at hw
    calc
      _ ≤ etaOf L μ k (2 ^ r * (2 * j + 1) - 1) * 1 :=
        mul_le_mul_of_nonneg_left hw he0
      _ ≤ 1 / μ := by simpa using (etaOf_bounds hμ hμL hi).2
      _ ≤ 4 / μ := div_le_div_of_nonneg_right (by norm_num) hμ.le
  · rw [max_eq_right hb] at hw
    calc
      _ ≤ etaOf L μ k (2 ^ r * (2 * j + 1) - 1) * ((L - μ) / (μ * (4 : ℝ) ^ r)) :=
        mul_le_mul_of_nonneg_left hw he0
      _ ≤ ((4 : ℝ) ^ (r + 1) / (L - μ)) * ((L - μ) / (μ * (4 : ℝ) ^ r)) :=
        mul_le_mul_of_nonneg_right (etaOf_degree_bound hμ hμL k r j hr (by omega)) (by positivity)
      _ = 4 / μ := by rw [pow_succ]; field_simp [ne_of_gt hμ, ne_of_gt hd]

lemma weighted_window_bound {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L)
    (k : ℕ) {lam : ℝ} (h0 : 0 ≤ lam) (hL : lam ≤ L)
    {i t : ℕ} (hi : i < t) (ht : t ≤ 2 ^ k) :
    etaOf L μ k i * |OracleTemplate.ScheduleBlock.win (etaOf L μ k) lam (i + 1) t| ≤
      4 / μ := by
  by_cases he : i + 1 = 2 ^ k
  · have hit : t = i + 1 := by omega
    rw [hit]
    simp only [OracleTemplate.ScheduleBlock.win, Finset.Ico_self, Finset.prod_empty,
      abs_one, mul_one]
    exact (etaOf_bounds hμ hμL (by omega : i < 2 ^ k)).2.trans
      (div_le_div_of_nonneg_right (by norm_num) hμ.le)
  · have hs : i + 1 < 2 ^ k := by omega
    obtain ⟨r, q, hq, heq⟩ := Nat.exists_eq_two_pow_mul_odd (show i + 1 ≠ 0 by omega)
    obtain ⟨j, hj⟩ := hq
    have hq : q = 2 * j + 1 := by omega
    rw [hq] at heq
    have hp : 2 ^ r ≤ i + 1 := by
      rw [heq]
      nlinarith [show (1 : ℕ) ≤ 2 * j + 1 by omega]
    have hr : r < k := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hp.trans_lt hs)
    have h := weighted_window_of_index hμ hμL k r j t hr (by omega) ht h0 hL
    rw [← heq] at h
    simpa using h

lemma periodic_window_shift (a : ℕ → ℝ) (lam : ℝ) (n : ℕ)
    (ha : ∀ i, a (i + n) = a i) (s t : ℕ) :
    OracleTemplate.ScheduleBlock.win a lam (s + n) (t + n) =
      OracleTemplate.ScheduleBlock.win a lam s t := by
  unfold OracleTemplate.ScheduleBlock.win
  rw [← Finset.prod_Ico_add' (fun i => 1 - a i * lam) s t n]
  simp only [ha]

lemma periodic_window_split (a : ℕ → ℝ) (lam : ℝ) (n : ℕ)
    (ha : ∀ i, a (i + n) = a i) {s t : ℕ} (hs : s ≤ n) (ht : n ≤ t) :
    OracleTemplate.ScheduleBlock.win a lam s t =
      OracleTemplate.ScheduleBlock.win a lam s n * OracleTemplate.ScheduleBlock.pr a lam (t - n) := by
  have he : OracleTemplate.ScheduleBlock.win a lam n t =
      OracleTemplate.ScheduleBlock.pr a lam (t - n) := by
    simpa only [Nat.zero_add, Nat.sub_add_cancel ht, OracleTemplate.ScheduleBlock.pr]
      using periodic_window_shift a lam n ha 0 (t - n)
  rw [← he]
  exact (Finset.prod_Ico_consecutive (fun i => 1 - a i * lam) hs ht).symm

lemma periodic_prefix_bound (a : ℕ → ℝ) (lam : ℝ) (n : ℕ) (hn : 0 < n)
    (ha : ∀ i, a (i + n) = a i)
    (hp : ∀ t ≤ n, |OracleTemplate.ScheduleBlock.pr a lam t| ≤ 1) (t : ℕ) :
    |OracleTemplate.ScheduleBlock.pr a lam t| ≤ 1 := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t ≤ n
    · exact hp t ht
    have hnt : n ≤ t := by omega
    have he := periodic_window_split a lam n ha (Nat.zero_le n) hnt
    change OracleTemplate.ScheduleBlock.pr a lam t =
      OracleTemplate.ScheduleBlock.pr a lam n * OracleTemplate.ScheduleBlock.pr a lam (t - n) at he
    rw [he, abs_mul]
    have hr := ih (t - n) (by omega)
    nlinarith [hp n le_rfl, abs_nonneg (OracleTemplate.ScheduleBlock.pr a lam n),
      abs_nonneg (OracleTemplate.ScheduleBlock.pr a lam (t - n))]

lemma periodic_weighted_window_bound (a : ℕ → ℝ) (lam W : ℝ) (n : ℕ) (hn : 0 < n)
    (ha : ∀ i, a (i + n) = a i) (ha0 : ∀ i, 0 ≤ a i)
    (hp : ∀ t ≤ n, |OracleTemplate.ScheduleBlock.pr a lam t| ≤ 1)
    (hw : ∀ i t, i < t → t ≤ n →
      a i * |OracleTemplate.ScheduleBlock.win a lam (i + 1) t| ≤ W) :
    ∀ t i, i < t → a i * |OracleTemplate.ScheduleBlock.win a lam (i + 1) t| ≤ W := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro i hi
    by_cases ht : t ≤ n
    · exact hw i t hi ht
    by_cases hin : i < n
    · rw [periodic_window_split a lam n ha (by omega) (by omega), abs_mul, ← mul_assoc]
      have hp' := periodic_prefix_bound a lam n hn ha hp (t - n)
      calc
        _ ≤ a i * |OracleTemplate.ScheduleBlock.win a lam (i + 1) n| * 1 :=
          mul_le_mul_of_nonneg_left hp' (mul_nonneg (ha0 i) (abs_nonneg _))
        _ ≤ W := by simpa using hw i n hin le_rfl
    · have hni : n ≤ i := by omega
      have hnt : n ≤ t := by omega
      have he := periodic_window_shift a lam n ha (i - n + 1) (t - n)
      have hs : i - n + 1 + n = i + 1 := by omega
      rw [hs, Nat.sub_add_cancel hnt] at he
      have hai : a i = a (i - n) := by simpa only [Nat.sub_add_cancel hni] using ha (i - n)
      rw [hai, he]
      exact ih (t - n) (by omega) (i - n) (by omega)

end LongTails.Proofs.FractalChebyshevWeighted

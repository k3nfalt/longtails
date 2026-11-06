import LongTails.Proofs.HomotopyNewtonCost
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HomotopyNewtonBudget

open LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone
open LongTails.Algorithms.HomotopyNewtonAEP
open LongTails.Proofs.HomotopyNewtonSchedule
open LongTails.Proofs.MonotoneTensorBounds
open LongTails.Proofs.HomotopyNewtonInner
open LongTails.Proofs.HomotopyNewtonOuter
open LongTails.Proofs.HomotopyNewtonExecution
open LongTails.Proofs.HomotopyNewtonCost
open LongTails.Proofs.LazyAnchoredLyapunov

noncomputable section

variable {p : Params}

lemma recip_sum_le (N : ℕ) : ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 2) ≤ Real.log (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hlog : Real.log ((N : ℝ) + 1 + 1) - Real.log ((N : ℝ) + 1) ≥ 1 / ((N : ℝ) + 2) := by
      rw [← Real.log_div (by positivity) hpos.ne']
      have := Real.one_sub_inv_le_log_of_pos (x := ((N : ℝ) + 1 + 1) / ((N : ℝ) + 1))
        (by positivity)
      have e : 1 - (((N : ℝ) + 1 + 1) / ((N : ℝ) + 1))⁻¹ = 1 / ((N : ℝ) + 2) := by
        field_simp; ring
      linarith
    push_cast
    linarith

lemma step_le (hp : Valid p) {k : ℕ} (hk : k < outerCount p) : step p k ≤ 4 * p.D / p.ε := by
  have hN : (0 : ℝ) < outerCount p := by exact_mod_cast outerCount_pos
  have hk' : (k : ℝ) + 1 ≤ outerCount p := by exact_mod_cast hk
  have hD := hp.D; have hε := hp.ε
  have hsc := scale_pos hp
  have h1 : step p k ≤ scale p * outerCount p := by
    unfold step; exact mul_le_mul_of_nonneg_left hk' hsc.le
  have h2 : scale p * outerCount p = 4 * p.D / (p.ε * (outerCount p + 1)) := by
    unfold scale; field_simp
  have h3 : 4 * p.D / (p.ε * (outerCount p + 1)) ≤ 4 * p.D / p.ε :=
    div_le_div_of_nonneg_left (by positivity) hε (by nlinarith)
  linarith

lemma sqrt_sum_bound (hp : Valid p) (F : p.E → p.E) (S : ℝ)
    (hS : ∑ l ∈ Finset.range (outerCount p), ((l + 2) / 2 : ℝ) ^ 2 * gap F l ^ 2 ≤ S) :
    (∑ k ∈ Finset.range (outerCount p), Real.sqrt (step p k * p.L) * gap F k) ^ 2 ≤
      4 * scale p * p.L * Real.log (outerCount p + 1) * S := by
  set N := outerCount p
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun k => Real.sqrt (step p k * p.L) * (2 / ((k : ℝ) + 2)))
    (fun k => ((k : ℝ) + 2) / 2 * gap F k)
  have hprod : ∀ k ∈ Finset.range N, Real.sqrt (step p k * p.L) * (2 / ((k : ℝ) + 2)) *
      (((k : ℝ) + 2) / 2 * gap F k) = Real.sqrt (step p k * p.L) * gap F k := by
    intro k _; field_simp
  rw [Finset.sum_congr rfl hprod] at hcs
  have hA : ∑ k ∈ Finset.range N, (Real.sqrt (step p k * p.L) * (2 / ((k : ℝ) + 2))) ^ 2 ≤
      4 * scale p * p.L * Real.log (N + 1) := by
    have hterm : ∀ k ∈ Finset.range N,
        (Real.sqrt (step p k * p.L) * (2 / ((k : ℝ) + 2))) ^ 2 ≤
          4 * scale p * p.L * (1 / ((k : ℝ) + 2)) := by
      intro k _
      have hsc := scale_pos hp
      have hL := hp.L
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      rw [mul_pow, Real.sq_sqrt (by have := step_pos hp k; positivity)]
      have hfrac : ((k : ℝ) + 1) * (2 / ((k : ℝ) + 2)) ^ 2 ≤ 4 * (1 / ((k : ℝ) + 2)) := by
        have e : ((k : ℝ) + 1) * (2 / ((k : ℝ) + 2)) ^ 2 =
            4 * (1 / ((k : ℝ) + 2)) * (((k : ℝ) + 1) / ((k : ℝ) + 2)) := by
          field_simp
          norm_num
        rw [e]
        exact mul_le_of_le_one_right (by positivity) ((div_le_one hk2).mpr (by linarith))
      calc step p k * p.L * (2 / ((k : ℝ) + 2)) ^ 2
          = (scale p * p.L) * (((k : ℝ) + 1) * (2 / ((k : ℝ) + 2)) ^ 2) := by unfold step; ring
        _ ≤ (scale p * p.L) * (4 * (1 / ((k : ℝ) + 2))) :=
            mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = 4 * scale p * p.L * (1 / ((k : ℝ) + 2)) := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have := recip_sum_le N
    have hpos : 0 ≤ 4 * scale p * p.L := by have := scale_pos hp; have := hp.L; positivity
    exact mul_le_mul_of_nonneg_left this hpos
  have hB : ∑ k ∈ Finset.range N, (((k : ℝ) + 2) / 2 * gap F k) ^ 2 ≤ S := by
    refine le_trans (le_of_eq ?_) hS
    exact Finset.sum_congr rfl fun k _ => by rw [mul_pow]
  have hB0 : 0 ≤ ∑ k ∈ Finset.range N, (((k : ℝ) + 2) / 2 * gap F k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hA0 : 0 ≤ 4 * scale p * p.L * Real.log (N + 1) := by
    have := scale_pos hp; have := hp.L
    have : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    positivity
  calc _ ≤ _ := hcs
    _ ≤ 4 * scale p * p.L * Real.log (N + 1) * S := mul_le_mul hA hB hB0 hA0

def Γ (p : Params) : ℝ := 2 + p.H₀ * p.D / p.ε + p.L * p.D ^ 3 / p.ε

lemma Γ_ge (hp : Valid p) : 2 ≤ Γ p := by
  unfold Γ; have := hp.H; have := hp.D; have := hp.ε; have := hp.L
  have : 0 ≤ p.H₀ * p.D / p.ε := by positivity
  have : 0 ≤ p.L * p.D ^ 3 / p.ε := by positivity
  linarith

lemma log_two_gt : (0.69 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

lemma ℓ_ge (hp : Valid p) : 0.69 ≤ Real.log (Γ p) := by
  have := Real.log_le_log (by norm_num) (Γ_ge hp)
  linarith [log_two_gt]

lemma pow_eleven (hp : Valid p) : 1 + 1003 * Γ p ≤ Γ p ^ 11 := by
  have hG := Γ_ge hp
  have h10 : (2 : ℝ) ^ 10 ≤ Γ p ^ 10 := pow_le_pow_left₀ (by norm_num) hG 10
  have : Γ p ^ 11 = Γ p ^ 10 * Γ p := by ring
  rw [this]; norm_num at h10; nlinarith

lemma pow_nine (hp : Valid p) : 1 + 200 * Γ p ≤ Γ p ^ 9 := by
  have hG := Γ_ge hp
  have h8 : (2 : ℝ) ^ 8 ≤ Γ p ^ 8 := pow_le_pow_left₀ (by norm_num) hG 8
  have : Γ p ^ 9 = Γ p ^ 8 * Γ p := by ring
  rw [this]; norm_num at h8; nlinarith

lemma log_le_of_le_pow {x : ℝ} (hx : 0 < x) {n : ℕ} (h : x ≤ Γ p ^ n) :
    Real.log x ≤ n * Real.log (Γ p) := by
  rw [← Real.log_pow]
  exact Real.log_le_log hx h

lemma natlog2_le (hp : Valid p) (n : ℕ) (hn : (n : ℝ) ≤ Γ p ^ 11) :
    (Nat.log2 n : ℝ) ≤ 16 * Real.log (Γ p) := by
  have hℓ := ℓ_ge hp
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp; linarith
  · have hle : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le (by omega)
    have hle' : (2 : ℝ) ^ Nat.log2 n ≤ n := by exact_mod_cast hle
    have h1 : (Nat.log2 n : ℝ) * Real.log 2 ≤ 11 * Real.log (Γ p) := by
      rw [← Real.log_pow]
      exact (Real.log_le_log (by positivity) hle').trans
        (log_le_of_le_pow (p := p) (by exact_mod_cast h0) hn)
    have h2 := log_two_gt
    have hpos : (0 : ℝ) ≤ Nat.log2 n := Nat.cast_nonneg _
    nlinarith

lemma stiff_step (hp : Valid p) {k : ℕ} (hk : k < outerCount p) :
    step p k * stiff p ≤ 1000 * Γ p := by
  have ha := step_le hp hk
  have hs := stiff_nonneg hp
  have := hp.H; have := hp.D; have := hp.ε; have := hp.L
  have h1 : step p k * stiff p ≤ 4 * p.D / p.ε * stiff p := mul_le_mul_of_nonneg_right ha hs
  have h2 : 4 * p.D / p.ε * stiff p = 8 * (p.H₀ * p.D / p.ε) + 1000 * (p.L * p.D ^ 3 / p.ε) := by
    unfold stiff; field_simp; ring
  have h3 : 0 ≤ p.H₀ * p.D / p.ε := by positivity
  have h4 : 0 ≤ p.L * p.D ^ 3 / p.ε := by positivity
  unfold Γ; linarith

lemma sqrt_step (hp : Valid p) {k : ℕ} (hk : k < outerCount p) :
    Real.sqrt (step p k * p.L) * p.D ≤ 2 * Γ p := by
  have ha := step_le hp hk
  have hG := Γ_ge hp
  have := hp.D; have := hp.ε; have := hp.L
  have hpos := step_pos hp k
  have hsq : (Real.sqrt (step p k * p.L) * p.D) ^ 2 ≤ (2 * Γ p) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have h1 : step p k * p.L * p.D ^ 2 ≤ 4 * p.D / p.ε * p.L * p.D ^ 2 := by gcongr
    have h2 : 4 * p.D / p.ε * p.L * p.D ^ 2 = 4 * (p.L * p.D ^ 3 / p.ε) := by field_simp
    have h3 : p.L * p.D ^ 3 / p.ε ≤ Γ p := by
      unfold Γ; have : 0 ≤ p.H₀ * p.D / p.ε := by have := hp.H; positivity
      linarith
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq

lemma logTerm_le (hp : Valid p) {k : ℕ} (hk : k < outerCount p) :
    logTerm (p := p) k ≤ 20 * Real.log (Γ p) := by
  unfold logTerm
  have h1 := stiff_step hp hk
  have h2 := sqrt_step hp hk
  have hG := Γ_ge hp
  have hd := one_le_denom hp k
  have e1 : Real.log (1 + step p k * stiff p) ≤ 11 * Real.log (Γ p) := by
    have := log_le_of_le_pow (p := p) (by linarith) (n := 11)
      (show 1 + step p k * stiff p ≤ Γ p ^ 11 by linarith [pow_eleven hp])
    simpa using this
  have hq : 0 ≤ Real.sqrt (step p k * p.L) * p.D := by have := hp.D; positivity
  have e2 : Real.log (1 + 100 * Real.sqrt (step p k * p.L) * p.D) ≤ 9 * Real.log (Γ p) := by
    have := log_le_of_le_pow (p := p) (by nlinarith) (n := 9)
      (show 1 + 100 * Real.sqrt (step p k * p.L) * p.D ≤ Γ p ^ 9 by nlinarith [pow_nine hp])
    simpa using this
  linarith

lemma constTerm_le (hp : Valid p) {k : ℕ} (hk : k < outerCount p) :
    constTerm (p := p) k ≤ 5800 * Real.log (Γ p) ^ 2 := by
  have hℓ := ℓ_ge hp
  have hlt := logTerm_le hp hk
  have hs := stiff_step hp hk
  have hs0 := mul_nonneg (step_pos hp k).le (stiff_nonneg hp)
  have hc1 : ((⌈step p k * stiff p⌉₊ : ℕ) : ℝ) ≤ Γ p ^ 11 := by
    have := Nat.ceil_lt_add_one hs0
    linarith [pow_eleven hp]
  have hc2 : ((⌈step p k * stiff p⌉₊ + 2 : ℕ) : ℝ) ≤ Γ p ^ 11 := by
    have := Nat.ceil_lt_add_one hs0
    push_cast
    linarith [pow_eleven hp, Γ_ge hp]
  have hcap : (attemptCap (p := p) k : ℝ) ≤ 16 * Real.log (Γ p) + 1 := by
    unfold attemptCap; push_cast; linarith [natlog2_le hp _ hc1]
  have hKc : (extra p k : ℝ) ≤ 16 * Real.log (Γ p) + 5 := by
    unfold extra; push_cast; linarith [natlog2_le hp _ hc2]
  have hlt0 := logTerm_nonneg hp k
  have hcap0 : (0 : ℝ) ≤ attemptCap (p := p) k := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ extra p k := Nat.cast_nonneg _
  unfold constTerm
  have hA : 12 * logTerm (p := p) k + 13 + 2 * (extra p k : ℝ) ≤ 272 * Real.log (Γ p) + 23 := by
    linarith
  have hB : (attemptCap (p := p) k : ℝ) + 1 ≤ 16 * Real.log (Γ p) + 2 := by linarith
  have hprod := mul_le_mul hB hA (by positivity) (by positivity)
  nlinarith

lemma totalTicks_eq (F : p.E → p.E) (n : ℕ) :
    (totalTicks F n : ℝ) = ∑ k ∈ Finset.range n, (outerTicks F k (outerSeq F k).1 (outerSeq F k).2 : ℝ) := by
  induction n with
  | zero => simp [totalTicks]
  | succ n ih => rw [totalTicks, Finset.sum_range_succ, ← ih]; push_cast; ring

lemma outerCount_le (hp : Valid p) :
    (outerCount p : ℝ) ≤ (p.L * p.D ^ 3 / p.ε) ^ (1 / 4 : ℝ) + 2 := by
  unfold outerCount
  have hX : 0 ≤ (p.L * p.D ^ 3 / p.ε) ^ (1 / 4 : ℝ) := by
    apply Real.rpow_nonneg; have := hp.L; have := hp.D; have := hp.ε; positivity
  have := Nat.ceil_lt_add_one hX
  push_cast; linarith

lemma X_le_N4 (hp : Valid p) : p.L * p.D ^ 3 / p.ε ≤ (outerCount p : ℝ) ^ 4 := by
  have hX0 : 0 ≤ p.L * p.D ^ 3 / p.ε := by have := hp.L; have := hp.D; have := hp.ε; positivity
  have h1 : (p.L * p.D ^ 3 / p.ε) ^ (1 / 4 : ℝ) ≤ outerCount p := by
    unfold outerCount; push_cast
    have := Nat.le_ceil ((p.L * p.D ^ 3 / p.ε) ^ (1 / 4 : ℝ)); linarith
  have h2 : ((p.L * p.D ^ 3 / p.ε) ^ (1 / 4 : ℝ)) ^ 4 = p.L * p.D ^ 3 / p.ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]; norm_num
  rw [← h2]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hX0 _) h1 4

lemma logN_le (hp : Valid p) : Real.log ((outerCount p : ℝ) + 1) ≤ 3 * Real.log (Γ p) := by
  have hG := Γ_ge hp
  have hX0 : 0 ≤ p.L * p.D ^ 3 / p.ε := by have := hp.L; have := hp.D; have := hp.ε; positivity
  have hXG : p.L * p.D ^ 3 / p.ε ≤ Γ p := by
    unfold Γ; have : 0 ≤ p.H₀ * p.D / p.ε := by have := hp.H; have := hp.D; have := hp.ε; positivity
    linarith
  have hroot : (p.L * p.D ^ 3 / p.ε) ^ (1 / 4 : ℝ) ≤ Γ p := by
    rcases le_total (p.L * p.D ^ 3 / p.ε) 1 with h | h
    · have := Real.rpow_le_one hX0 h (by norm_num : (0 : ℝ) ≤ 1 / 4); linarith
    · calc (p.L * p.D ^ 3 / p.ε) ^ (1 / 4 : ℝ) ≤ (p.L * p.D ^ 3 / p.ε) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h (by norm_num)
        _ = p.L * p.D ^ 3 / p.ε := Real.rpow_one _
        _ ≤ Γ p := hXG
  have hN := outerCount_le hp
  have h3 : (outerCount p : ℝ) + 1 ≤ Γ p ^ 3 := by nlinarith [sq_nonneg (Γ p)]
  have := log_le_of_le_pow (p := p) (by positivity) h3
  simpa using this

lemma final_arith {N ℓ T S X : ℝ} (hN0 : 0 ≤ N) (hℓ : 0.69 ≤ ℓ)
    (hT : T ≤ N * (5800 * ℓ ^ 2) + 3600 * (20 * ℓ) * S) (hS : S ≤ 10 * N * ℓ)
    (hNX : N ≤ X + 2) (hX : 0 ≤ X) : T ≤ 2 ^ 21 * (1 + X) * ℓ ^ 2 := by
  have h1 : 3600 * (20 * ℓ) * S ≤ 3600 * (20 * ℓ) * (10 * N * ℓ) :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  have h2 : N * ℓ ^ 2 ≤ (X + 2) * ℓ ^ 2 := mul_le_mul_of_nonneg_right hNX (sq_nonneg ℓ)
  nlinarith [sq_nonneg ℓ]

lemma ticks_budget [FiniteDimensional ℝ p.E] (hp : Valid p) {F : p.E → p.E}
    (h : Regular F p.L) {xs : p.E} (hxs : F xs = 0) (hD : ‖p.x0 - xs‖ ≤ p.D)
    (hH : ∀ y ∈ Metric.closedBall p.x0 (5 * p.D), ‖fderiv ℝ F y‖ ≤ stiff p) :
    (totalTicks F (outerCount p) : ℝ) ≤
      2 ^ 21 * (1 + (p.L * p.D ^ 3 / p.ε) ^ (1 / 4 : ℝ)) * Real.log (Γ p) ^ 2 := by
  set N := outerCount p
  obtain ⟨hfacts, hV, -⟩ := aep_invariant h hp hxs hD hH N
  have hlow : -(p.D ^ 2 / 2) ≤ potential p.x0 (cumulative p N) (outerSeq F N).1 (F (outerSeq F N).1) := by
    apply potential_lower p.x0 xs _ _ _ p.D (cumulative_nonneg hp N) hD
    have := h.mono (outerSeq F N).1 xs; rwa [hxs, sub_zero] at this
  have hSb : ∑ l ∈ Finset.range N, ((l + 2) / 2 : ℝ) ^ 2 * gap F l ^ 2 ≤ 4 / 3 * p.D ^ 2 := by
    linarith
  set S := ∑ k ∈ Finset.range N, Real.sqrt (step p k * p.L) * gap F k
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => by unfold gap; positivity
  have hsq := sqrt_sum_bound hp F (4 / 3 * p.D ^ 2) hSb
  have hℓ := ℓ_ge hp
  have hlogN := logN_le hp
  have hX4 := X_le_N4 hp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast outerCount_pos
  have hSsq : S ^ 2 ≤ (10 * N * Real.log (Γ p)) ^ 2 := by
    refine hsq.trans ?_
    have hsc : scale p = 4 * p.D / (p.ε * N * (N + 1)) := rfl
    have hL := hp.L; have hDp := hp.D; have hε := hp.ε
    have hlog0 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
    have e : 4 * scale p * p.L * Real.log (N + 1) * (4 / 3 * p.D ^ 2) =
        64 / 3 * (p.L * p.D ^ 3 / p.ε) * Real.log (N + 1) / (N * (N + 1)) := by
      rw [hsc]; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have h1 : 64 / 3 * (p.L * p.D ^ 3 / p.ε) * Real.log (N + 1) ≤
        64 / 3 * (N : ℝ) ^ 4 * (3 * Real.log (Γ p)) := by
      apply mul_le_mul (by nlinarith) hlogN hlog0 (by positivity)
    have h2 : 64 / 3 * (N : ℝ) ^ 4 * (3 * Real.log (Γ p)) ≤
        (10 * N * Real.log (Γ p)) ^ 2 * (N * (N + 1)) := by
      have hℓℓ : 64 * Real.log (Γ p) ≤ 100 * Real.log (Γ p) ^ 2 := by nlinarith
      have : (N : ℝ) ^ 4 ≤ N ^ 3 * (N + 1) := by nlinarith [pow_pos hNpos 3]
      nlinarith [mul_le_mul_of_nonneg_left hℓℓ (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 4),
        mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 100 * Real.log (Γ p) ^ 2)]
    linarith
  have hS : S ≤ 10 * N * Real.log (Γ p) :=
    (pow_le_pow_iff_left₀ hS0 (by positivity) (by norm_num)).mp hSsq
  have hT : (totalTicks F N : ℝ) ≤ N * (5800 * Real.log (Γ p) ^ 2) +
      3600 * (20 * Real.log (Γ p)) * S := by
    rw [totalTicks_eq]
    have hterm : ∀ k ∈ Finset.range N, (outerTicks F k (outerSeq F k).1 (outerSeq F k).2 : ℝ) ≤
        5800 * Real.log (Γ p) ^ 2 + 3600 * (20 * Real.log (Γ p)) *
          (Real.sqrt (step p k * p.L) * gap F k) := by
      intro k hk
      have hkN := Finset.mem_range.mp hk
      have hf := hfacts k hkN
      have h1 := outerTicks_le hp F k _ _ hf
      have h2 := constTerm_le hp hkN
      have h3 := logTerm_le hp hkN
      have hq : 0 ≤ Real.sqrt (step p k * p.L) * gap F k := by unfold gap; positivity
      have hgap : gap F k = ‖nextPoint F k (outerSeq F k).1 (outerSeq F k).2 -
          center p k (outerSeq F k).1 (outerSeq F k).2‖ := rfl
      rw [← hgap] at h1
      have h4 : 3600 * logTerm (p := p) k * Real.sqrt (step p k * p.L) * gap F k ≤
          3600 * (20 * Real.log (Γ p)) * (Real.sqrt (step p k * p.L) * gap F k) := by
        rw [mul_assoc (3600 * logTerm (p := p) k)]
        exact mul_le_mul_of_nonneg_right (by linarith) hq
      linarith
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
  have hX0 : 0 ≤ (p.L * p.D ^ 3 / p.ε) ^ (1 / 4 : ℝ) := by
    apply Real.rpow_nonneg; have := hp.L; have := hp.D; have := hp.ε; positivity
  exact final_arith hNpos.le hℓ hT hS (outerCount_le hp) hX0

end

end LongTails.Proofs.HomotopyNewtonBudget

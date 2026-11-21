import LongTails.Algorithms.WarmHalvingBrox
import LongTails.Proofs.WarmHalvingBroxAnalysis
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set

namespace OracleTemplate.WarmHalvingBrox

open LongTails.Setups.BroxGeneralNormConstrainedPL

open private _run from LongTails.Template

lemma execute_of_invariant {Query Reply Output : Type*} {n : ℕ}
    (O : Oracle Query Reply n) (A : Algorithm Query Reply Output n)
    (budget : Fin n → ℕ) (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k)
    (Inv : A.State → (Fin n → ℕ) → Prop) (P : Output → Prop)
    (h0 : Inv (A.initial seed) budget)
    (hstep : ∀ history s rem, Inv s rem → 0 < rem (A.query s).1 →
      Inv (A.update s (O.answer history (A.query s) (ξ history.length)))
        (Function.update rem (A.query s).1 (rem (A.query s).1 - 1)))
    (hstop : ∀ s rem, Inv s rem → rem (A.query s).1 = 0 → P (A.output s)) :
    P (execute O A budget seed ξ) := by
  have key : ∀ fuel history rem s, ∑ i, rem i = fuel → Inv s rem →
      P (_run (fun history query => O.answer history query (ξ history.length)) A fuel
        history rem s).1 := by
    intro fuel
    induction fuel with
    | zero =>
      intro history rem s hsum hinv
      unfold _run
      apply hstop s rem hinv
      exact (Finset.sum_eq_zero_iff.1 hsum) _ (Finset.mem_univ _)
    | succ fuel ih =>
      intro history rem s hsum hinv
      unfold _run
      dsimp only
      split_ifs with hz
      · exact hstop s rem hinv hz
      · apply ih
        · have hsplit := Finset.add_sum_erase Finset.univ rem (Finset.mem_univ (A.query s).1)
          have hsplit' := Finset.add_sum_erase Finset.univ
            (Function.update rem (A.query s).1 (rem (A.query s).1 - 1))
            (Finset.mem_univ (A.query s).1)
          have hrest : ∑ i ∈ Finset.univ.erase (A.query s).1,
              Function.update rem (A.query s).1 (rem (A.query s).1 - 1) i =
              ∑ i ∈ Finset.univ.erase (A.query s).1, rem i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
          rw [← hsplit', hrest, Function.update_self]
          omega
        · exact hstep history s rem hinv (Nat.pos_of_ne_zero hz)
  exact key _ [] budget (A.initial seed) rfl h0

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure Hyp (f : E → ℝ) (C : Set E) (L μ : ℝ) : Prop where
  convex : Convex ℝ C
  diff : ∀ x ∈ C, DifferentiableAt ℝ f x
  lip : ∀ x ∈ C, ∀ y ∈ C, ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ L * ‖y - x‖
  bdd : BddBelow (f '' C)
  pl : ∀ x ∈ C, μ * (f x - optimalValue f C) ≤ stationarity f C x ^ 2 / 2
  L_pos : 0 < L
  μ_pos : 0 < μ

noncomputable def gap (f : E → ℝ) (C : Set E) (x : E) : ℝ := f x - optimalValue f C

structure IsOutput (f : E → ℝ) (C : Set E) (x v : E) (r : ℝ) : Prop where
  mem : v ∈ C
  dist : ‖v - x‖ ≤ r
  opt : ∀ z ∈ C, ‖z - x‖ ≤ r → fderiv ℝ f x v ≤ fderiv ℝ f x z

variable {f : E → ℝ} {C : Set E} {L μ : ℝ}

lemma gap_nonneg (H : Hyp f C L μ) {x : E} (hx : x ∈ C) : 0 ≤ gap f C x :=
  sub_nonneg.2 (csInf_le H.bdd ⟨x, hx, rfl⟩)

lemma descent (H : Hyp f C L μ) {x v : E} {r : ℝ} (hx : x ∈ C) (hv : IsOutput f C x v r) :
    gap f C v ≤ gap f C x - -fderiv ℝ f x (v - x) + L / 2 * r ^ 2 := by
  have hq := quadratic_bound H.convex H.diff H.lip hx hv.mem
  have hr : ‖v - x‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv.dist 2
  have hL := H.L_pos
  unfold gap
  have := (abs_le.1 hq).2
  nlinarith

lemma ascent (H : Hyp f C L μ) {x v : E} {r : ℝ} (hx : x ∈ C) (hv : IsOutput f C x v r) :
    gap f C x ≤ gap f C v + -fderiv ℝ f x (v - x) + L / 2 * r ^ 2 := by
  have hq := quadratic_bound H.convex H.diff H.lip hx hv.mem
  have hr : ‖v - x‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv.dist 2
  have hL := H.L_pos
  unfold gap
  have := (abs_le.1 hq).1
  nlinarith

lemma model_nonneg {x v : E} {r : ℝ} (hx : x ∈ C) (hr : 0 ≤ r) (hv : IsOutput f C x v r) :
    0 ≤ -fderiv ℝ f x (v - x) := by
  have := hv.opt x hx (by simpa using hr)
  rw [map_sub]
  linarith

lemma output_stationarity (H : Hyp f C L μ) {x v : E} {r : ℝ} (hx : x ∈ C) (hr : 0 < r)
    (hv : IsOutput f C x v r) :
    stationarity f C v ≤ L * r + -fderiv ℝ f x (v - x) / r :=
  certificate H.convex H.L_pos.le H.lip hx hv.mem hr hv.dist hv.opt

lemma reject_gap (H : Hyp f C L μ) {x v : E} {r : ℝ} (hx : x ∈ C) (hr : 0 < r)
    (hv : IsOutput f C x v r) (hd : -fderiv ℝ f x (v - x) < L * r ^ 2) :
    gap f C x < (2 * L ^ 2 / μ + 3 * L / 2) * r ^ 2 := by
  have hs := output_stationarity H hx hr hv
  have hs0 := stationarity_nonneg f C v
  have hdr : -fderiv ℝ f x (v - x) / r < L * r := by
    rw [div_lt_iff₀ hr]
    nlinarith
  have hs2 : stationarity f C v < 2 * L * r := by linarith
  have hsq : stationarity f C v ^ 2 < (2 * L * r) ^ 2 := pow_lt_pow_left₀ hs2 hs0 (by norm_num)
  have hpl := H.pl v hv.mem
  have hμ := H.μ_pos
  have hgv : gap f C v < 2 * L ^ 2 / μ * r ^ 2 := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hμ]
    unfold gap
    nlinarith
  have ha := ascent H hx hv
  nlinarith

lemma uncapped_gap (H : Hyp f C L μ) {x v : E} {r : ℝ} (hx : x ∈ C) (hr : 0 < r)
    (hv : IsOutput f C x v r) (hd : -fderiv ℝ f x (v - x) < 4 * L * r ^ 2) :
    gap f C v < 25 * L ^ 2 * r ^ 2 / (2 * μ) := by
  have hs := output_stationarity H hx hr hv
  have hs0 := stationarity_nonneg f C v
  have hdr : -fderiv ℝ f x (v - x) / r < 4 * L * r := by
    rw [div_lt_iff₀ hr]
    nlinarith
  have hs2 : stationarity f C v < 5 * L * r := by linarith
  have hsq : stationarity f C v ^ 2 < (5 * L * r) ^ 2 := pow_lt_pow_left₀ hs2 hs0 (by norm_num)
  have hpl := H.pl v hv.mem
  have hμ := H.μ_pos
  rw [lt_div_iff₀ (by positivity)]
  unfold gap
  nlinarith

lemma stop_gap (H : Hyp f C L μ) {x v : E} {r : ℝ} (hx : x ∈ C) (hr : 0 < r)
    (hv : IsOutput f C x v r) (h0 : fderiv ℝ f x (v - x) = 0) : gap f C x ≤ 0 := by
  have hs := stationary_of_zero H.convex hx hr hv.dist hv.opt h0
  have hs0 := stationarity_nonneg f C x
  have hpl := H.pl x hx
  have hμ := H.μ_pos
  have hseq : stationarity f C x = 0 := le_antisymm hs hs0
  rw [hseq] at hpl
  unfold gap
  nlinarith

lemma radius_pos {r : ℝ} (hr : 0 < r) (j : ℤ) : 0 < radius r j :=
  mul_pos hr (zpow_pos (by norm_num) j)

lemma radius_succ (r : ℝ) (j : ℤ) : radius r (j + 1) = 2 * radius r j := by
  unfold radius
  rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

lemma radius_pred (r : ℝ) (j : ℤ) : radius r (j - 1) = radius r j / 2 := by
  have := radius_succ r (j - 1)
  rw [sub_add_cancel] at this
  linarith

lemma radius_natCast_sq (r : ℝ) (m : ℕ) : radius r m ^ 2 = r ^ 2 * 4 ^ m := by
  unfold radius
  rw [zpow_natCast, mul_pow, ← pow_mul, mul_comm m 2, pow_mul]
  norm_num

lemma le_floor_logb {y : ℝ} {m : ℕ} (hm : (4 : ℝ) ^ m ≤ y) : m ≤ ⌊Real.logb 4 y⌋₊ := by
  have hy : 0 < y := lt_of_lt_of_le (by positivity) hm
  apply Nat.le_floor
  rw [Real.le_logb_iff_rpow_le (by norm_num) hy, Real.rpow_natCast]
  exact hm

lemma lt_ceil_log {a ρ : ℝ} {n : ℕ} (hρ : 1 < ρ) (h : ρ ^ n < a) :
    n < ⌈Real.log a / Real.log ρ⌉₊ := by
  have ha : 0 < a := lt_of_le_of_lt (by positivity) h
  apply Nat.lt_ceil.2
  rw [lt_div_iff₀ (Real.log_pos hρ), ← Real.log_pow]
  exact Real.log_lt_log (by positivity) h

lemma trial_bound {r L μ ε : ℝ} (hr : 0 < r) (hL : 0 < L) (hμ : 0 < μ) (hε : 0 < ε) {e : ℤ}
    (h : min r (Real.sqrt (ε / (2 * L ^ 2 / μ + 3 * L / 2)) / 2) ≤ radius r e) :
    -e ≤ ⌈Real.logb 4 (r ^ 2 * (8 * L ^ 2 / μ + 6 * L) / ε)⌉₊ := by
  rcases le_or_gt 0 e with he | he
  · have : (0 : ℤ) ≤ ⌈Real.logb 4 (r ^ 2 * (8 * L ^ 2 / μ + 6 * L) / ε)⌉₊ := by positivity
    omega
  obtain ⟨n, hn⟩ : ∃ n : ℕ, e = -(n : ℤ) := ⟨(-e).toNat, by omega⟩
  subst hn
  have h2n : radius r (-(n : ℤ)) = r / 2 ^ n := by
    unfold radius
    rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [h2n] at h
  set Cr := 2 * L ^ 2 / μ + 3 * L / 2
  have hC : 0 < Cr := by positivity
  have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hlt : r / 2 ^ n < r ∨ n = 0 := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact Or.inr h0
    · left
      rw [div_lt_iff₀ (by positivity)]
      have : (1 : ℝ) < 2 ^ n := one_lt_pow₀ (by norm_num) hpos.ne'
      nlinarith
  rcases hlt with hlt | h0
  · have hmin : Real.sqrt (ε / Cr) / 2 ≤ r / 2 ^ n := by
      rcases le_total r (Real.sqrt (ε / Cr) / 2) with hle | hle
      · rw [min_eq_left hle] at h
        linarith
      · rwa [min_eq_right hle] at h
    have hsq : ε / Cr / 4 ≤ r ^ 2 / 4 ^ n := by
      have h1 : (Real.sqrt (ε / Cr) / 2) ^ 2 ≤ (r / 2 ^ n) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hmin 2
      rw [div_pow, Real.sq_sqrt (by positivity), div_pow, ← pow_mul, mul_comm n 2, pow_mul]
        at h1
      norm_num at h1
      linarith
    have h4 : (4 : ℝ) ^ n ≤ r ^ 2 * (8 * L ^ 2 / μ + 6 * L) / ε := by
      have hCr : 8 * L ^ 2 / μ + 6 * L = 4 * Cr := by simp only [Cr]; ring
      rw [hCr, le_div_iff₀ hε]
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)] at hsq
      nlinarith
    have hy : 0 < r ^ 2 * (8 * L ^ 2 / μ + 6 * L) / ε := by positivity
    have hlog : (n : ℝ) ≤ Real.logb 4 (r ^ 2 * (8 * L ^ 2 / μ + 6 * L) / ε) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) hy, Real.rpow_natCast]
      exact h4
    have := (Nat.le_ceil _).trans' hlog
    have hn : n ≤ ⌈Real.logb 4 (r ^ 2 * (8 * L ^ 2 / μ + 6 * L) / ε)⌉₊ := by exact_mod_cast this
    omega
  · subst h0
    simp

end OracleTemplate.WarmHalvingBrox

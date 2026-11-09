import LongTails.Proofs.BlackBoxLevels
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped BigOperators

namespace OracleTemplate.BlackBoxDiagonal

variable {d : ℕ}

lemma log_two_gt : (1 : ℝ) / 2 < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

lemma cost_bound (j : ℕ) : (cost j : ℝ) ≤ 21 * Real.sqrt (2 ^ j) * Real.log (4 * 2 ^ j) := by
  have hs : 1 ≤ Real.sqrt (2 ^ j) := by
    rw [Real.one_le_sqrt]; exact one_le_pow₀ (by norm_num)
  have hl := log_two_gt
  have hx : 0 ≤ 2 * Real.sqrt (2 ^ j) * Real.log (512 * (2 ^ j) ^ 3) := by
    have : 0 ≤ Real.log (512 * (2 ^ j) ^ 3) :=
      Real.log_nonneg (by have : (1 : ℝ) ≤ (2 ^ j) ^ 3 := one_le_pow₀ (one_le_pow₀ (by norm_num))
                          nlinarith)
    positivity
  have hc : (len j : ℝ) < 2 * Real.sqrt (2 ^ j) * Real.log (512 * (2 ^ j) ^ 3) + 1 :=
    Nat.ceil_lt_add_one hx
  have e1 : Real.log (512 * (2 ^ j) ^ 3) = (9 + 3 * j) * Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow,
      show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
    push_cast; ring
  have e2 : Real.log (4 * 2 ^ j) = (2 + j) * Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [e1] at hc
  rw [e2]
  unfold cost
  push_cast
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ (6 + 9 * j) * Real.log 2)]

lemma cost_mono {i j : ℕ} (h : i ≤ j) : cost i ≤ cost j := by
  unfold cost len
  have : Real.sqrt (2 ^ i) * Real.log (512 * (2 ^ i) ^ 3) ≤
      Real.sqrt (2 ^ j) * Real.log (512 * (2 ^ j) ^ 3) := by
    have h1 : Real.sqrt (2 ^ i) ≤ Real.sqrt (2 ^ j) :=
      Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) h)
    have h2 : Real.log (512 * (2 ^ i) ^ 3) ≤ Real.log (512 * (2 ^ j) ^ 3) := by
      apply Real.log_le_log (by positivity)
      have : (2 : ℝ) ^ i ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) h
      have : ((2 : ℝ) ^ i) ^ 3 ≤ (2 ^ j) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
      linarith
    have h3 : 0 ≤ Real.log (512 * (2 ^ i) ^ 3) :=
      Real.log_nonneg (by have : (1 : ℝ) ≤ (2 ^ i) ^ 3 := one_le_pow₀ (one_le_pow₀ (by norm_num))
                          nlinarith)
    exact mul_le_mul h1 h2 h3 (Real.sqrt_nonneg _)
  have := Nat.ceil_le_ceil (by nlinarith : 2 * Real.sqrt (2 ^ i) * Real.log (512 * (2 ^ i) ^ 3) ≤
      2 * Real.sqrt (2 ^ j) * Real.log (512 * (2 ^ j) ^ 3))
  omega

section Inv

variable (f : Vec d → ℝ) (x0 : Vec d) (w : Fin d → ℝ) (μ : ℝ)

noncomputable def FCh (n : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (ms f x0 n).lvl, cap d j * cost j) + (ms f x0 n).fails * cost (ms f x0 n).lvl

noncomputable def Gam (x : Vec d) : ℝ := isq (sec f x0) (gradient f x)

noncomputable def rate : ℝ := 21 * Real.sqrt (2 ^ jstar μ)

structure Inv (n : ℕ) : Prop where
  lvl_le : (ms f x0 n).lvl ≤ jstar μ
  box : ∀ k, lo (sec f x0) k ≤ (ms f x0 n).θ k ∧ (ms f x0 n).θ k ≤ hi (sec f x0) (ms f x0 n).lvl k
  pot : 1 ≤ μ * 2 ^ (ms f x0 n).lvl →
    sqn (fun k => (ms f x0 n).θ k - θc w k) + (ms f x0 n).fails * Real.log 2 ^ 2 ≤
      d * ((ms f x0 n).lvl * Real.log 2) ^ 2 / 4
  fails_lt : (ms f x0 n).fails < cap d (ms f x0 n).lvl
  fch_le : FCh f x0 n ≤ bt f x0 n
  prog : Gam f x0 (ms f x0 n).base * Real.exp (((bt f x0 n : ℝ) - FCh f x0 n) / rate μ) ≤
    Gam f x0 x0

variable {f x0 w μ}

lemma inv_zero (Hy : BHyp f w μ) : Inv f x0 w μ 0 where
  lvl_le := Nat.zero_le _
  box := th0_box x0 0
  pot := fun h => by
    have := th0_pot Hy x0 h
    simp only [ms, startSt, probeSt, initial] at this ⊢
    simpa using this
  fails_lt := by simp [ms, startSt, probeSt, initial, cap]
  fch_le := by simp [FCh, ms, startSt, probeSt, initial, bt]
  prog := by simp [FCh, ms, startSt, probeSt, initial, bt, Gam]

end Inv

section Step

variable {f : Vec d → ℝ} {x0 : Vec d} {w : Fin d → ℝ} {μ : ℝ}

lemma phaseData_ms (n : ℕ) :
    PhaseData f (ms f x0 n).θ (ms f x0 n).lvl (ms f x0 n).base
      (Hrep f (ms f x0 n) (2 * (ms f x0 n).N + 1)) :=
  ⟨Hrep_cons f (ms f x0 n) (len_pos _)⟩

lemma cap_gt_of_pot {fails j : ℕ}
    (h : ((fails : ℝ) + 1) * Real.log 2 ^ 2 ≤ d * (j * Real.log 2) ^ 2 / 4) :
    fails + 1 < cap d j := by
  have hl : 0 < Real.log 2 ^ 2 := by have := log_two_gt; positivity
  have h1 : ((fails : ℝ) + 1) * 4 ≤ d * j ^ 2 := by
    have e : (d : ℝ) * (j * Real.log 2) ^ 2 / 4 = d * j ^ 2 / 4 * Real.log 2 ^ 2 := by ring
    rw [e] at h
    have := le_of_mul_le_mul_right h hl
    linarith
  have h2 : (fails + 1) * 4 ≤ d * j ^ 2 := by exact_mod_cast h1
  have h3 : fails + 1 ≤ d * j ^ 2 / 4 := (Nat.le_div_iff_mul_le (by norm_num)).mpr h2
  unfold cap; omega

lemma exp_cost_le {j : ℕ} (hj : j ≤ jstar μ) :
    Real.exp ((cost j : ℝ) / rate μ) ≤ 4 * 2 ^ j := by
  have hc := cost_bound j
  have hs : Real.sqrt (2 ^ j) ≤ Real.sqrt (2 ^ jstar μ) :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) hj)
  have hr : 0 < rate μ := by unfold rate; positivity
  have hl : 0 ≤ Real.log (4 * 2 ^ j) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num); linarith)
  have : (cost j : ℝ) / rate μ ≤ Real.log (4 * 2 ^ j) := by
    rw [div_le_iff₀ hr]
    unfold rate
    nlinarith [mul_le_mul_of_nonneg_right hs hl]
  calc Real.exp ((cost j : ℝ) / rate μ) ≤ Real.exp (Real.log (4 * 2 ^ j)) :=
        Real.exp_le_exp.mpr this
    _ = 4 * 2 ^ j := Real.exp_log (by positivity)

lemma endPhase_none (st : St d) (H : ℕ → ℝ × Vec d)
    (h : firstViolated st.θ (phaseCuts st.m (alph st.lvl) (muh st.lvl) st.N st.base H) = none) :
    endPhase st H =
      { st with base := (xv st.m (alph st.lvl) (muh st.lvl) st.base H st.N).1, s := 0, H := H } := by
  unfold endPhase; rw [h]

lemma endPhase_cap (st : St d) (H : ℕ → ℝ × Vec d) (C : Cut d)
    (h : firstViolated st.θ (phaseCuts st.m (alph st.lvl) (muh st.lvl) st.N st.base H) = some C)
    (hc : st.fails + 1 = cap d st.lvl) :
    endPhase st H =
      { st with lvl := st.lvl + 1, fails := 0, θ := th0 st.J (st.lvl + 1), s := 0, H := H } := by
  unfold endPhase; rw [h]; simp only [hc, ↓reduceIte]

lemma endPhase_cut (st : St d) (H : ℕ → ℝ × Vec d) (C : Cut d)
    (h : firstViolated st.θ (phaseCuts st.m (alph st.lvl) (muh st.lvl) st.N st.base H) = some C)
    (hc : ¬ st.fails + 1 = cap d st.lvl) :
    endPhase st H = { st with fails := st.fails + 1,
                              θ := cutStep (lo st.J) (hi st.J st.lvl) (Real.log 2) C st.θ,
                              s := 0, H := H } := by
  unfold endPhase; rw [h]; simp only [hc, ↓reduceIte]

theorem inv_succ (Hy : BHyp f w μ) (n : ℕ) (I : Inv f x0 w μ n) : Inv f x0 w μ (n + 1) := by
  set st := ms f x0 n with hst
  set H := Hrep f st (2 * st.N + 1) with hH
  have P : PhaseData f st.θ st.lvl st.base H := phaseData_ms n
  have hms : ms f x0 (n + 1) = endPhase st H := rfl
  have hbt : bt f x0 (n + 1) = bt f x0 n + cost st.lvl := rfl
  have hJ : st.J = sec f x0 := (ms_shape f x0 n).2.2
  have hbox := box_metric Hy x0 I.box
  rcases hfv : firstViolated st.θ (phaseCuts (metric st.θ) (alph st.lvl) (muh st.lvl)
      (len st.lvl) st.base H) with _ | C
  · have e : ms f x0 (n + 1) = { st with
        base := (xv (metric st.θ) (alph st.lvl) (muh st.lvl) st.base H (len st.lvl)).1,
        s := 0, H := H } := by
      rw [hms]; exact endPhase_none st H hfv
    have hsucc := phase_success Hy P (fun k => (hbox k).1) (fun k => (hbox k).2) hfv
    have hF : FCh f x0 (n + 1) = FCh f x0 n := by unfold FCh; rw [e]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e]; exact I.lvl_le
    · rw [e]; exact I.box
    · rw [e]; exact I.pot
    · rw [e]; exact I.fails_lt
    · rw [hF, hbt]; exact le_trans I.fch_le (Nat.le_add_right _ _)
    · rw [hF, hbt, e]
      have hexp := exp_cost_le I.lvl_le
      have hpos : 0 ≤ Gam f x0 st.base := isq_nonneg (sec_pos Hy x0) _
      have hgam : Gam f x0 (xv (metric st.θ) (alph st.lvl) (muh st.lvl) st.base H (len st.lvl)).1 ≤
          Gam f x0 st.base / (4 * 2 ^ st.lvl) := hsucc
      have hprog := I.prog
      have e2 : ((bt f x0 n + cost st.lvl : ℕ) : ℝ) - FCh f x0 n =
          ((bt f x0 n : ℝ) - FCh f x0 n) + cost st.lvl := by push_cast; ring
      rw [e2, add_div, Real.exp_add]
      have hE := Real.exp_pos (((bt f x0 n : ℝ) - FCh f x0 n) / rate μ)
      calc Gam f x0 (xv (metric st.θ) (alph st.lvl) (muh st.lvl) st.base H (len st.lvl)).1 *
            (Real.exp (((bt f x0 n : ℝ) - FCh f x0 n) / rate μ) *
              Real.exp ((cost st.lvl : ℝ) / rate μ))
          ≤ Gam f x0 st.base / (4 * 2 ^ st.lvl) *
            (Real.exp (((bt f x0 n : ℝ) - FCh f x0 n) / rate μ) * (4 * 2 ^ st.lvl)) := by
            apply mul_le_mul hgam (mul_le_mul_of_nonneg_left hexp hE.le) (by positivity)
              (by positivity)
        _ = Gam f x0 st.base * Real.exp (((bt f x0 n : ℝ) - FCh f x0 n) / rate μ) := by
            field_simp
        _ ≤ Gam f x0 x0 := hprog
  · obtain ⟨hCmem, hCpos⟩ := find_some hfv
    have hval := phase_cut_valid Hy P
    have hprogress : 1 ≤ μ * 2 ^ st.lvl →
        sqn (fun k => cutStep (lo (sec f x0)) (hi (sec f x0) st.lvl) (Real.log 2) C st.θ k -
          θc w k) ≤ sqn (fun k => st.θ k - θc w k) - Real.log 2 ^ 2 := by
      intro hv
      have hμj : 4 * muh st.lvl ≤ μ := by
        have e4 : 4 * muh st.lvl = 1 / 2 ^ st.lvl := by unfold muh; field_simp
        rw [e4, div_le_iff₀ (by positivity)]
        linarith
      obtain ⟨ha, hb, hv'⟩ := hval hμj hCmem
      exact cut_progress C ha hb (Real.log_pos (by norm_num))
        (fun θ' h => hv' θ' (ball_metric Hy.w_pos h))
        (θc_lo Hy x0) (θc_hi Hy x0 hv) hCpos
    by_cases hcap : st.fails + 1 = cap d st.lvl
    · have e : ms f x0 (n + 1) = { st with
          lvl := st.lvl + 1, fails := 0, θ := th0 (sec f x0) (st.lvl + 1), s := 0, H := H } := by
        rw [hms, endPhase_cap st H C hfv hcap, hJ]
      have hinv : μ * 2 ^ st.lvl < 1 := by
        by_contra hc
        push Not at hc
        have h1 := hprogress hc
        have h2 := I.pot hc
        have h3 := sqn_nonneg (fun k => cutStep (lo (sec f x0)) (hi (sec f x0) st.lvl)
          (Real.log 2) C st.θ k - θc w k)
        have h4 : ((st.fails : ℝ) + 1) * Real.log 2 ^ 2 ≤ d * (st.lvl * Real.log 2) ^ 2 / 4 := by
          nlinarith
        have := cap_gt_of_pot h4
        omega
      have hlt := lt_jstar_of_invalid Hy.μ_pos hinv
      have hF : FCh f x0 (n + 1) = FCh f x0 n + cost st.lvl := by
        unfold FCh; rw [e]
        simp only [Finset.sum_range_succ, zero_mul, add_zero]
        rw [← hcap]; ring
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e]; exact hlt
      · rw [e]; exact th0_box x0 _
      · rw [e]; intro hv
        simp only [Nat.cast_zero, zero_mul, add_zero]
        exact th0_pot Hy x0 hv
      · rw [e]; dsimp only; unfold cap; omega
      · rw [hF, hbt]; have := I.fch_le; omega
      · rw [hF, hbt, e]
        have e2 : ((bt f x0 n + cost st.lvl : ℕ) : ℝ) - ((FCh f x0 n + cost st.lvl : ℕ) : ℝ) =
            (bt f x0 n : ℝ) - FCh f x0 n := by push_cast; ring
        rw [e2]; exact I.prog
    · have e : ms f x0 (n + 1) = { st with
          fails := st.fails + 1,
          θ := cutStep (lo (sec f x0)) (hi (sec f x0) st.lvl) (Real.log 2) C st.θ,
          s := 0, H := H } := by
        rw [hms, endPhase_cut st H C hfv hcap, hJ]
      have hF : FCh f x0 (n + 1) = FCh f x0 n + cost st.lvl := by
        unfold FCh; rw [e]; ring
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e]; exact I.lvl_le
      · rw [e]; intro k
        have hlh : lo (sec f x0) k ≤ hi (sec f x0) st.lvl k := le_trans (I.box k).1 (I.box k).2
        unfold cutStep clampBox
        exact ⟨le_max_left _ _, max_le hlh (min_le_left _ _)⟩
      · rw [e]; intro hv
        have h1 := hprogress hv
        have h2 := I.pot hv
        push_cast
        linarith
      · rw [e]; dsimp only; have := I.fails_lt; rw [← hst] at this; omega
      · rw [hF, hbt]; have := I.fch_le; omega
      · rw [hF, hbt, e]
        have e2 : ((bt f x0 n + cost st.lvl : ℕ) : ℝ) - ((FCh f x0 n + cost st.lvl : ℕ) : ℝ) =
            (bt f x0 n : ℝ) - FCh f x0 n := by push_cast; ring
        rw [e2]; exact I.prog

theorem inv_all (Hy : BHyp f w μ) : ∀ n, Inv f x0 w μ n
  | 0 => inv_zero Hy
  | n + 1 => inv_succ Hy n (inv_all Hy n)

end Step

end OracleTemplate.BlackBoxDiagonal

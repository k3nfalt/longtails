import Mathlib.Tactic
import LongTails.Setups.RipmGeneral
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators
open LongTails.Setups.RipmGeneral

namespace LongTails.Proofs.RipmWeights

noncomputable section

lemma gautschi (x c : ℝ) (hx : 0 < x) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    x ^ (1 - c) ≤ Real.Gamma (x + 1) / Real.Gamma (x + c) ∧
      Real.Gamma (x + 1) / Real.Gamma (x + c) ≤ (x + 1) ^ (1 - c) := by
  have hx1 : 0 < x + 1 := by linarith
  have hxc : 0 < x + c := by linarith
  have hxc1 : 0 < x + c + 1 := by linarith
  have hGx := Real.Gamma_pos_of_pos hx
  have hG1 := Real.Gamma_pos_of_pos hx1
  have hGc := Real.Gamma_pos_of_pos hxc
  have hrec1 : Real.log (Real.Gamma (x + 1)) =
      Real.log x + Real.log (Real.Gamma x) := by
    rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' hGx.ne']
  have hrec2 : Real.log (Real.Gamma (x + c + 1)) =
      Real.log (x + c) + Real.log (Real.Gamma (x + c)) := by
    rw [Real.Gamma_add_one hxc.ne', Real.log_mul hxc.ne' hGc.ne']
  have hl := Real.convexOn_log_Gamma.2 hx hx1
    (sub_nonneg.mpr hc1) hc (show (1 - c) + c = 1 by ring)
  simp only [Function.comp_apply, smul_eq_mul] at hl
  have heql : (1 - c) * x + c * (x + 1) = x + c := by ring
  rw [heql, hrec1] at hl
  have hu := Real.convexOn_log_Gamma.2 hxc hxc1
    hc (sub_nonneg.mpr hc1) (show c + (1 - c) = 1 by ring)
  simp only [Function.comp_apply, smul_eq_mul] at hu
  have hequ : c * (x + c) + (1 - c) * (x + c + 1) = x + 1 := by ring
  rw [hequ, hrec2] at hu
  constructor
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hx (1 - c))
      (div_pos hG1 hGc)).mp
    rw [Real.log_rpow hx, Real.log_div hG1.ne' hGc.ne', hrec1]
    nlinarith [hl]
  · apply (Real.log_le_log_iff (div_pos hG1 hGc)
      (Real.rpow_pos_of_pos hx1 (1 - c))).mp
    rw [Real.log_div hG1.ne' hGc.ne', Real.log_rpow hx1]
    have hm := Real.log_le_log hxc (show x + c ≤ x + 1 by linarith)
    have hp := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hc1)
    nlinarith [hu, hp]

lemma weight_positive (T t : ℕ) (mu : ℝ) (hmu : 0 ≤ mu) (ht : t ≤ T) :
    0 < Core.weight T mu t := by
  have hw : ∀ n : ℕ, n ≤ T → 0 < Core.weight T mu n := by
    intro n
    induction n with
    | zero =>
        intro hn
        change 0 < (1 : ℝ)
        norm_num
    | succ n ih =>
        intro hn
        have hnT : n ≤ T := by omega
        have hsub : 0 < ((T - n : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < T - n by omega)
        have hrec : Core.weight T mu (n + 1) =
            Core.weight T mu n * ((T - n : ℕ) + 1) / ((T - n : ℕ) + mu) := rfl
        rw [hrec]
        exact div_pos (mul_pos (ih hnT) (by positivity))
          (add_pos_of_pos_of_nonneg hsub hmu)
  exact hw t ht

lemma weight_mixing (T t : ℕ) (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu < 1)
    (ht0 : 1 ≤ t) (ht : t ≤ T) :
    0 ≤ Core.mixing T mu t ∧ Core.mixing T mu t ≤ 1 ∧
      Core.weight T mu t * Core.mixing T mu t = Core.weight T mu (t - 1) ∧
      Core.weight T mu (t - 1) ≤ Core.weight T mu t := by
  cases t with
  | zero => omega
  | succ k =>
      let n : ℕ := T - (k + 1)
      have hsub : T - k = n + 1 := by dsimp [n]; omega
      have hp : Core.mixing T mu (k + 1) =
          ((n : ℝ) + 1 + mu) / ((n : ℝ) + 2) := by
        delta Core.mixing
        rw [ite_eq_right (show k + 1 ≠ 0 by omega)]
      have hnum : 0 < (n : ℝ) + 1 + mu := by positivity
      have hden : 0 < (n : ℝ) + 2 := by positivity
      have hp0 : 0 ≤ Core.mixing T mu (k + 1) := by
        rw [hp]
        exact (div_pos hnum hden).le
      have hp1 : Core.mixing T mu (k + 1) ≤ 1 := by
        rw [hp, div_le_iff₀ hden]
        linarith
      have hw : Core.weight T mu (k + 1) =
          Core.weight T mu k * ((n : ℝ) + 2) / ((n : ℝ) + 1 + mu) := by
        change Core.weight T mu k * ((T - k : ℕ) + 1) / ((T - k : ℕ) + mu) = _
        rw [hsub]
        push_cast
        ring
      have heq : Core.weight T mu (k + 1) * Core.mixing T mu (k + 1) =
          Core.weight T mu k := by
        rw [hw, hp]
        field_simp [hnum.ne', hden.ne']
      have ha := weight_positive T (k + 1) mu hmu ht
      have hinc : Core.weight T mu k ≤ Core.weight T mu (k + 1) := by
        calc
          Core.weight T mu k =
              Core.weight T mu (k + 1) * Core.mixing T mu (k + 1) := heq.symm
          _ ≤ Core.weight T mu (k + 1) * 1 :=
            mul_le_mul_of_nonneg_left hp1 ha.le
          _ = Core.weight T mu (k + 1) := mul_one _
      exact ⟨hp0, hp1, heq, hinc⟩

lemma weight_gamma (T t : ℕ) (mu : ℝ) (hT : 1 ≤ T) (hmu : 0 < mu)
    (hmu1 : mu < 1) (ht : t ≤ T) :
    Core.weight T mu t =
      Real.Gamma ((T : ℝ) + 2) * Real.Gamma (((T - t : ℕ) : ℝ) + 1 + mu) /
        (Real.Gamma ((T : ℝ) + 1 + mu) * Real.Gamma (((T - t : ℕ) : ℝ) + 2)) := by
  have hGA : 0 < Real.Gamma ((T : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
  have hGBne : Real.Gamma ((T : ℝ) + 1 + mu) ≠ 0 := by
    intro hzero
    have hx : 0 < (T : ℝ) + 1 := by positivity
    have hl := (gautschi ((T : ℝ) + 1) mu hx hmu.le hmu1.le).1
    have hp := Real.rpow_pos_of_pos hx (1 - mu)
    rw [hzero, div_zero] at hl
    exact (not_le_of_gt hp) hl
  have hall : ∀ k : ℕ, k ≤ T →
      Core.weight T mu k =
        Real.Gamma ((T : ℝ) + 2) * Real.Gamma (((T - k : ℕ) : ℝ) + 1 + mu) /
          (Real.Gamma ((T : ℝ) + 1 + mu) * Real.Gamma (((T - k : ℕ) : ℝ) + 2)) := by
    intro k
    induction k with
    | zero =>
        intro hk
        change (1 : ℝ) = _
        simp only [Nat.sub_zero]
        field_simp [hGA.ne', hGBne]
    | succ k ih =>
        intro hk
        have ihk := ih (show k ≤ T by omega)
        let n : ℕ := T - (k + 1)
        have hn : T - k = n + 1 := by dsimp [n]; omega
        have hp : 0 < (n : ℝ) + 1 + mu := by positivity
        have hq : 0 < (n : ℝ) + 2 := by positivity
        have hGq := Real.Gamma_pos_of_pos hq
        have hg1 : Real.Gamma ((n : ℝ) + 1 + 1 + mu) =
            ((n : ℝ) + 1 + mu) * Real.Gamma ((n : ℝ) + 1 + mu) := by
          rw [show (n : ℝ) + 1 + 1 + mu = ((n : ℝ) + 1 + mu) + 1 by ring,
            Real.Gamma_add_one hp.ne']
        have hg2 : Real.Gamma ((n : ℝ) + 1 + 2) =
            ((n : ℝ) + 2) * Real.Gamma ((n : ℝ) + 2) := by
          rw [show (n : ℝ) + 1 + 2 = ((n : ℝ) + 2) + 1 by ring,
            Real.Gamma_add_one hq.ne']
        rw [hn] at ihk
        push_cast at ihk
        rw [hg1, hg2] at ihk
        change Core.weight T mu k * ((T - k : ℕ) + 1) / ((T - k : ℕ) + mu) =
          Real.Gamma ((T : ℝ) + 2) * Real.Gamma ((n : ℝ) + 1 + mu) /
            (Real.Gamma ((T : ℝ) + 1 + mu) * Real.Gamma ((n : ℝ) + 2))
        rw [ihk, hn]
        push_cast
        field_simp [hGBne, hp.ne', hq.ne', hGq.ne']
        ring
  exact hall t ht

lemma weight_lower (T : ℕ) (mu : ℝ) (hT : 1 ≤ T) (hmu : 0 < mu) (hmu1 : mu < 1) :
    ((T : ℝ) + 1) ^ (1 - mu) / (2 : ℝ) ^ (1 - mu) ≤ Core.weight T mu T := by
  have hG2 : Real.Gamma (2 : ℝ) = 1 := by
    simp
  have hGA : 0 < Real.Gamma ((T : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
  have hGB : 0 < Real.Gamma ((T : ℝ) + 1 + mu) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hGm : 0 < Real.Gamma (1 + mu) := Real.Gamma_pos_of_pos (by positivity)
  have hp : 0 < (2 : ℝ) ^ (1 - mu) := Real.rpow_pos_of_pos (by norm_num) _
  have hlarge := (gautschi ((T : ℝ) + 1) mu (by positivity) hmu.le hmu1.le).1
  rw [show (T : ℝ) + 1 + 1 = (T : ℝ) + 2 by ring] at hlarge
  have hsmall := (gautschi 1 mu (by norm_num) hmu.le hmu1.le).2
  norm_num only [hG2] at hsmall
  have hinv : 1 / (2 : ℝ) ^ (1 - mu) ≤ Real.Gamma (1 + mu) := by
    apply (div_le_iff₀ hp).2
    have h := (div_le_iff₀ hGm).mp hsmall
    nlinarith
  calc
    ((T : ℝ) + 1) ^ (1 - mu) / (2 : ℝ) ^ (1 - mu) =
        ((T : ℝ) + 1) ^ (1 - mu) * (1 / (2 : ℝ) ^ (1 - mu)) := by ring
    _ ≤ (Real.Gamma ((T : ℝ) + 2) / Real.Gamma ((T : ℝ) + 1 + mu)) *
        Real.Gamma (1 + mu) :=
      mul_le_mul hlarge hinv (by positivity) (div_pos hGA hGB).le
    _ = Core.weight T mu T := by
      rw [weight_gamma T T mu hT hmu hmu1 (le_refl T)]
      simp only [Nat.sub_self, Nat.cast_zero, zero_add, hG2, mul_one]
      ring

lemma weight_sum (T : ℕ) (mu : ℝ) (hT : 1 ≤ T) (hmu : 0 < mu) (hmu1 : mu < 1) :
    (∑ t ∈ Finset.range T, Core.weight T mu (t + 1)) / Core.weight T mu T ≤
      8 * (T : ℝ) ^ mu * Real.log ((T : ℝ) + 1) := by
  have hG2 : Real.Gamma (2 : ℝ) = 1 := by
    simp
  have hGA : 0 < Real.Gamma ((T : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
  have hGB : 0 < Real.Gamma ((T : ℝ) + 1 + mu) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hGm : 0 < Real.Gamma (1 + mu) := Real.Gamma_pos_of_pos (by positivity)
  have hunit : 1 / Real.Gamma (1 + mu) ≤ 2 := by
    have h := (gautschi 1 mu (by norm_num) hmu.le hmu1.le).2
    norm_num only [hG2] at h
    have hp := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show 1 - mu ≤ 1 by linarith)
    rw [Real.rpow_one] at hp
    exact h.trans hp
  have hterm : ∀ t ∈ Finset.range T,
      Core.weight T mu (t + 1) / Core.weight T mu T ≤
        2 * (T : ℝ) ^ mu / ((T - t : ℕ) : ℝ) := by
    intro t htmem
    have htlt : t < T := Finset.mem_range.mp htmem
    have hts : t + 1 ≤ T := by omega
    let j : ℝ := ((T - t : ℕ) : ℝ)
    have hj : 0 < j := by
      dsimp [j]
      exact_mod_cast (show 0 < T - t by omega)
    have hjT : j ≤ (T : ℝ) := by
      dsimp [j]
      exact_mod_cast Nat.sub_le T t
    have hrem : ((T - (t + 1) : ℕ) : ℝ) + 1 = j := by
      dsimp [j]
      exact_mod_cast (show T - (t + 1) + 1 = T - t by omega)
    have hrem2 : ((T - (t + 1) : ℕ) : ℝ) + 2 = j + 1 := by linarith
    have hGjp : 0 < Real.Gamma (j + 1) := Real.Gamma_pos_of_pos (by positivity)
    have hGjm : 0 < Real.Gamma (j + mu) := Real.Gamma_pos_of_pos (by positivity)
    have hquot : Core.weight T mu (t + 1) / Core.weight T mu T =
        (Real.Gamma (j + mu) / Real.Gamma (j + 1)) *
          (1 / Real.Gamma (1 + mu)) := by
      rw [weight_gamma T (t + 1) mu hT hmu hmu1 hts,
        weight_gamma T T mu hT hmu hmu1 (le_refl T)]
      simp only [Nat.sub_self, Nat.cast_zero, zero_add, hG2, mul_one]
      rw [hrem, hrem2]
      field_simp [hGA.ne', hGB.ne', hGm.ne', hGjp.ne']
    have hpowj : 0 < j ^ (1 - mu) := Real.rpow_pos_of_pos hj _
    have hinv : Real.Gamma (j + mu) / Real.Gamma (j + 1) ≤ 1 / j ^ (1 - mu) := by
      have h := one_div_le_one_div_of_le hpowj (gautschi j mu hj hmu.le hmu1.le).1
      simpa only [one_div_div] using h
    calc
      Core.weight T mu (t + 1) / Core.weight T mu T =
          (Real.Gamma (j + mu) / Real.Gamma (j + 1)) *
            (1 / Real.Gamma (1 + mu)) := hquot
      _ ≤ (1 / j ^ (1 - mu)) * 2 := mul_le_mul hinv hunit (by positivity) (by positivity)
      _ = 2 * j ^ mu / j := by
        rw [Real.rpow_sub hj, Real.rpow_one, one_div_div]
        ring
      _ ≤ 2 * (T : ℝ) ^ mu / j :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hj.le hjT hmu.le) (by norm_num)) hj.le
      _ = 2 * (T : ℝ) ^ mu / ((T - t : ℕ) : ℝ) := rfl
  have hlogstep : ∀ k : ℕ, 1 ≤ k →
      (1 : ℝ) / (k : ℝ) ≤ 2 * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : 0 < (k : ℝ) := by linarith
    have hkp : 0 < (k : ℝ) + 1 := by positivity
    have hl := Real.log_le_sub_one_of_pos (div_pos hk0 hkp)
    rw [Real.log_div hk0.ne' hkp.ne'] at hl
    have heq : (k : ℝ) / ((k : ℝ) + 1) - 1 = -(1 / ((k : ℝ) + 1)) := by
      field_simp [hkp.ne']
      ring
    rw [heq] at hl
    have hrec : (1 : ℝ) / (k : ℝ) ≤ 2 / ((k : ℝ) + 1) := by
      apply (div_le_div_iff₀ hk0 hkp).2
      nlinarith
    have hlog : 1 / ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) := by
      linarith
    calc
      (1 : ℝ) / (k : ℝ) ≤ 2 / ((k : ℝ) + 1) := hrec
      _ = 2 * (1 / ((k : ℝ) + 1)) := by ring
      _ ≤ 2 * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
  let f : ℕ → ℝ := fun k => Real.log ((k : ℝ) + 1)
  have hH : (∑ k ∈ Finset.range T, (1 : ℝ) / ((k : ℝ) + 1)) ≤
      2 * Real.log ((T : ℝ) + 1) := by
    calc
      (∑ k ∈ Finset.range T, (1 : ℝ) / ((k : ℝ) + 1)) ≤
          ∑ k ∈ Finset.range T, 2 * (f (k + 1) - f k) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa only [f, Nat.cast_add, Nat.cast_one] using hlogstep (k + 1) (by omega)
      _ = 2 * (f T - f 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]
      _ = 2 * Real.log ((T : ℝ) + 1) := by
        simp only [f, Nat.cast_zero, zero_add, Real.log_one, sub_zero]
  have hreflect : (∑ t ∈ Finset.range T, (1 : ℝ) / ((T - t : ℕ) : ℝ)) =
      ∑ t ∈ Finset.range T, (1 : ℝ) / ((t : ℝ) + 1) := by
    calc
      (∑ t ∈ Finset.range T, (1 : ℝ) / ((T - t : ℕ) : ℝ)) =
          ∑ t ∈ Finset.range T, (1 : ℝ) / (((T - 1 - t : ℕ) : ℝ) + 1) := by
        apply Finset.sum_congr rfl
        intro t ht
        have htlt := Finset.mem_range.mp ht
        rw [show T - t = (T - 1 - t) + 1 by omega, Nat.cast_add, Nat.cast_one]
      _ = ∑ t ∈ Finset.range T, (1 : ℝ) / ((t : ℝ) + 1) :=
        Finset.sum_range_reflect (fun t : ℕ => (1 : ℝ) / ((t : ℝ) + 1)) T
  rw [Finset.sum_div]
  calc
    (∑ t ∈ Finset.range T, Core.weight T mu (t + 1) / Core.weight T mu T) ≤
        ∑ t ∈ Finset.range T, 2 * (T : ℝ) ^ mu / ((T - t : ℕ) : ℝ) :=
      Finset.sum_le_sum hterm
    _ = 2 * (T : ℝ) ^ mu * (∑ t ∈ Finset.range T, (1 : ℝ) / ((T - t : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = 2 * (T : ℝ) ^ mu * (∑ t ∈ Finset.range T, (1 : ℝ) / ((t : ℝ) + 1)) := by
      rw [hreflect]
    _ ≤ 2 * (T : ℝ) ^ mu * (2 * Real.log ((T : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ 8 * (T : ℝ) ^ mu * Real.log ((T : ℝ) + 1) := by
      have hl : 0 ≤ Real.log ((T : ℝ) + 1) := Real.log_nonneg (by
        have hT0 : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
        linarith)
      have hp := Real.rpow_nonneg (Nat.cast_nonneg T) mu
      nlinarith [mul_nonneg hp hl]

lemma power_bound (L C : ℝ) (T : ℕ) (hL : 0 < L) (hC : 2 < C) (hT : 1 ≤ T) :
    let tau := 1 / (C * L * Real.sqrt T)
    let gamma := (1 - 2 * tau * L) / (1 + 2 * tau * L)
    let mu := 2 * tau * L * (1 + gamma)
    0 < gamma ∧ 0 < mu ∧ mu < 1 ∧ tau * L = 1 / (C * Real.sqrt T) ∧
      tau * L ≤ 1 / C ∧ 1 / C < 1 / 2 ∧
      (T : ℝ) ^ mu ≤ Real.exp (8 / (Real.exp 1 * C)) := by
  let tau : ℝ := 1 / (C * L * Real.sqrt T)
  let gamma : ℝ := (1 - 2 * tau * L) / (1 + 2 * tau * L)
  let mu : ℝ := 2 * tau * L * (1 + gamma)
  change 0 < gamma ∧ 0 < mu ∧ mu < 1 ∧ tau * L = 1 / (C * Real.sqrt T) ∧
    tau * L ≤ 1 / C ∧ 1 / C < 1 / 2 ∧
    (T : ℝ) ^ mu ≤ Real.exp (8 / (Real.exp 1 * C))
  let s : ℝ := Real.sqrt T
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : 0 < (T : ℝ) := by linarith
  have hs1 : 1 ≤ s := by
    exact (Real.le_sqrt (by norm_num) (Nat.cast_nonneg T)).2 (by nlinarith)
  have hs : 0 < s := by linarith
  have hC0 : 0 < C := by linarith
  have hCsC : C ≤ C * s := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 hC0.le
  have htau : 0 < tau := by
    change 0 < 1 / (C * L * s)
    positivity
  have hz : tau * L = 1 / (C * s) := by
    change (1 / (C * L * s)) * L = 1 / (C * s)
    field_simp [hC0.ne', hL.ne', hs.ne']
  have hz2 : 2 * tau * L = 2 / (C * s) := by
    rw [mul_assoc, hz]
    ring
  have hc_half : 1 / C < (1 : ℝ) / 2 := by
    apply (div_lt_div_iff₀ hC0 (show (0 : ℝ) < 2 by norm_num)).2
    linarith
  have htle : tau * L ≤ 1 / C := by
    rw [hz]
    exact one_div_le_one_div_of_le hC0 hCsC
  have hz0 : 0 < tau * L := mul_pos htau hL
  have hzh : tau * L < (1 : ℝ) / 2 := htle.trans_lt hc_half
  have hn : 0 < 1 - 2 * tau * L := by nlinarith
  have hd : 0 < 1 + 2 * tau * L := by nlinarith
  have hg : 0 < gamma := div_pos hn hd
  have hm : 0 < mu := by
    change 0 < 2 * tau * L * (1 + gamma)
    positivity
  have hCs : 0 < C * s + 2 := by positivity
  have hmform : mu = 4 / (C * s + 2) := by
    change (2 * tau * L) * (1 + (1 - 2 * tau * L) / (1 + 2 * tau * L)) = _
    rw [hz2]
    have hplus : 0 < 1 + 2 / (C * s) := by positivity
    field_simp [hC0.ne', hs.ne', hCs.ne', hplus.ne']
    ring
  have hm1 : mu < 1 := by
    rw [hmform]
    apply (div_lt_iff₀ hCs).2
    linarith
  have he : 0 < Real.exp (1 : ℝ) := Real.exp_pos 1
  have heq : Real.exp (Real.log (T : ℝ) / 2) = s := by
    rw [Real.exp_half, Real.exp_log hTpos]
  have hraw := Real.add_one_le_exp (Real.log (T : ℝ) / 2 - 1)
  rw [Real.exp_sub, heq] at hraw
  have hlog : Real.exp 1 * Real.log (T : ℝ) ≤ 2 * s := by
    have hraw' : Real.log (T : ℝ) / 2 ≤ s / Real.exp 1 := by linarith
    have hprod := (le_div_iff₀ he).mp hraw'
    nlinarith
  have hexponent : Real.log (T : ℝ) * mu ≤ 8 / (Real.exp 1 * C) := by
    rw [hmform, ← mul_div_assoc]
    apply (div_le_div_iff₀ hCs (mul_pos he hC0)).2
    have hscaled := mul_le_mul_of_nonneg_right hlog (show 0 ≤ 4 * C by positivity)
    nlinarith
  have hpower : (T : ℝ) ^ mu ≤ Real.exp (8 / (Real.exp 1 * C)) := by
    rw [Real.rpow_def_of_pos hTpos]
    exact Real.exp_le_exp.mpr hexponent
  exact ⟨hg, hm, hm1, hz, htle, hc_half, hpower⟩

end

end LongTails.Proofs.RipmWeights

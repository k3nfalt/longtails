import LongTails.Template
import LongTails.Proofs.FreyaModel
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open scoped BigOperators ENNReal NNReal

namespace LongTails.Proofs.FreyaEquilibrium

open LongTails.Proofs.FreyaModel

theorem prefix_threshold {n : ℕ} (hn : 0 < n) (τ : Fin n → ℝ≥0∞)
    (hmono : Monotone τ) (hpos : ∀ i, 0 < τ i) (hfinite : ∃ i, τ i ≠ ⊤)
    (r : ℝ≥0∞) (hr : 0 < r) (hrfinite : r ≠ ⊤) :
    ∃ j : Fin n, τ j ≤ equilibriumTime τ r ∧
      equilibriumTime τ r = (r + (j.val + 1 : ℕ)) / ∑ i ∈ Finset.Iic j, (τ i)⁻¹ := by
  open scoped BigOperators ENNReal NNReal in
    classical
    have _ := hn
    have _ := hmono
    have _ := hr
    obtain ⟨i, hi⟩ := hfinite
    let : Nonempty (Fin n) := ⟨i⟩
    let t := equilibriumTime τ r
    let H (j : Fin n) : ℝ≥0∞ := ∑ k ∈ Finset.Iic j, (τ k)⁻¹
    have hnumfinite (j : Fin n) : r + (j.val + 1 : ℕ) ≠ (⊤ : ℝ≥0∞) := by
      simp [hrfinite]
    have hHfinite (j : Fin n) : H j ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun k _ => ENNReal.inv_ne_top.mpr (hpos k).ne'
    have hden : 0 < H i :=
      lt_of_lt_of_le (ENNReal.inv_pos.mpr hi)
        (Finset.single_le_sum (f := fun k : Fin n => (τ k)⁻¹) (a := i) (fun _ _ => zero_le) (by simp))
    have htfinite : t ≠ ⊤ := ne_top_of_le_ne_top
      (ENNReal.div_ne_top (hnumfinite i) hden.ne')
      (iInf_le (fun j : Fin n => (r + (j.val + 1 : ℕ)) / H j) i)
    obtain ⟨j, hj⟩ := Finite.ciInf_mem
      (fun j : Fin n => (r + (j.val + 1 : ℕ)) / H j)
    have hjt : t = (r + (j.val + 1 : ℕ)) / H j := hj.symm
    have hnumpos : 0 < r + (j.val + 1 : ℕ) := by positivity
    have htpos : 0 < t := by
      rw [hjt]
      exact ENNReal.div_pos hnumpos.ne' (hHfinite j)
    have hHne : H j ≠ 0 := by
      intro hz
      apply htfinite
      rw [hjt, hz]
      exact ENNReal.div_eq_top.mpr (Or.inl ⟨hnumpos.ne', rfl⟩)
    have hmul : t * H j = r + (j.val + 1 : ℕ) := by
      rw [hjt]
      exact ENNReal.div_mul_cancel hHne (hHfinite j)
    have hpre : t * (∑ k ∈ Finset.Iio j, (τ k)⁻¹) ≤ r + (j.val : ℝ≥0∞) := by
      by_cases hz : j.val = 0
      · have hempty : Finset.Iio j = ∅ := by
          ext k
          constructor
          · intro hk
            have hkFin : k < j := Finset.mem_Iio.mp hk
            have hk' : k.val < j.val := hkFin
            omega
          · intro hk
            simp at hk
        simp [hempty]
      · let q : Fin n := ⟨j.val - 1, by have hjn := j.isLt; omega⟩
        have hsets : Finset.Iio j = Finset.Iic q := by
          ext k
          simp only [Finset.mem_Iio, Finset.mem_Iic]
          change k.val < j.val ↔ k.val ≤ q.val
          dsimp [q]
          omega
        have hval : q.val + 1 = j.val := by dsimp [q]; omega
        have hnprev : r + (q.val + 1 : ℕ) ≠ (0 : ℝ≥0∞) := by positivity
        have htprev := (ENNReal.le_div_iff_mul_le
          (Or.inr hnprev) (Or.inr (hnumfinite q))).mp
          (show t ≤ (r + (q.val + 1 : ℕ)) / H q from iInf_le _ q)
        simpa only [hsets, H, hval] using htprev
    have hset : Finset.Iic j = insert j (Finset.Iio j) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Iio]
      exact le_iff_eq_or_lt
    have hsplit : H j = (∑ k ∈ Finset.Iio j, (τ k)⁻¹) + (τ j)⁻¹ := by
      dsimp [H]
      rw [hset, Finset.sum_insert (by simp)]
      exact add_comm _ _
    have hsum : (r + (j.val : ℝ≥0∞)) + 1 ≤
        (r + (j.val : ℝ≥0∞)) + t * (τ j)⁻¹ := by
      calc
        (r + (j.val : ℝ≥0∞)) + 1 = t * H j := by
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hmul.symm
        _ = t * (∑ k ∈ Finset.Iio j, (τ k)⁻¹) + t * (τ j)⁻¹ := by
          rw [hsplit, mul_add]
        _ ≤ (r + (j.val : ℝ≥0∞)) + t * (τ j)⁻¹ := add_le_add hpre le_rfl
    have hunit : (1 : ℝ≥0∞) ≤ t * (τ j)⁻¹ :=
      (ENNReal.add_le_add_iff_left (by simp [hrfinite])).mp hsum
    have htime : τ j ≤ t := by
      have h := (ENNReal.le_div_iff_mul_le
        (Or.inr htpos.ne') (Or.inr htfinite)).mp hunit
      simpa only [one_mul] using h
    exact ⟨j, htime, hjt⟩

theorem equilibrium_comparisons {n : ℕ} (τ : Fin n → ℝ≥0∞) :
    Monotone (equilibriumTime τ) ∧
      ∀ r s : ℝ≥0∞, 0 < r → r ≤ s → s ≠ ⊤ →
        equilibriumTime τ s / s ≤ equilibriumTime τ r / r := by
  open scoped BigOperators ENNReal NNReal in
    classical
    constructor
    · intro r s hrs
      apply iInf_mono
      intro j
      exact ENNReal.div_le_div_right (add_le_add hrs le_rfl) _
    · intro r s hr hrs hs
      have hr0 : r ≠ 0 := hr.ne'
      have hs0 : s ≠ 0 := (hr.trans_le hrs).ne'
      have hrf : r ≠ ⊤ := ne_top_of_le_ne_top hs hrs
      by_cases hn : n = 0
      · subst n
        change (⨅ j : Fin 0, (s + (j.val + 1 : ℕ)) / ∑ k ∈ Finset.Iic j, (τ k)⁻¹) / s ≤
          (⨅ j : Fin 0, (r + (j.val + 1 : ℕ)) / ∑ k ∈ Finset.Iic j, (τ k)⁻¹) / r
        simp [ENNReal.top_div, hs, hrf]
      · let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
        obtain ⟨j, hj⟩ := Finite.ciInf_mem
          (fun j : Fin n => (r + (j.val + 1 : ℕ)) / ∑ k ∈ Finset.Iic j, (τ k)⁻¹)
        let a : ℝ≥0∞ := (j.val + 1 : ℕ)
        let H : ℝ≥0∞ := ∑ k ∈ Finset.Iic j, (τ k)⁻¹
        have normalize (x : ℝ≥0∞) (hx0 : x ≠ 0) (hxt : x ≠ ⊤) :
            ((x + a) / H) / x = (1 + a / x) / H := by
          calc
            ((x + a) / H) / x = ((x + a) * x⁻¹) * H⁻¹ := by
              simp only [div_eq_mul_inv]
              ac_rfl
            _ = (1 + a * x⁻¹) * H⁻¹ := by
              rw [add_mul, ENNReal.mul_inv_cancel hx0 hxt]
            _ = (1 + a / x) / H := by simp only [div_eq_mul_inv]
        calc
          equilibriumTime τ s / s ≤ ((s + a) / H) / s :=
            ENNReal.div_le_div_right (iInf_le _ j) s
          _ = (1 + a / s) / H := normalize s hs0 hs
          _ ≤ (1 + a / r) / H := ENNReal.div_le_div_right
            (add_le_add le_rfl (ENNReal.div_le_div_left hrs a)) H
          _ = ((r + a) / H) / r := (normalize r hr0 hrf).symm
          _ = equilibriumTime τ r / r := congrArg (fun t => t / r) hj

theorem equilibrium_zero {n : ℕ} (τ : Fin n → ℝ≥0∞) (hzero : ∃ i, τ i = 0)
    (r : ℝ≥0∞) (hrfinite : r ≠ ⊤) : equilibriumTime τ r = 0 := by
  open scoped BigOperators ENNReal NNReal in
    classical
    have _ := hrfinite
    obtain ⟨i, hi⟩ := hzero
    apply le_antisymm ?_ bot_le
    delta equilibriumTime
    refine (iInf_le _ i).trans ?_
    have hs : (∑ k ∈ Finset.Iic i, (τ k)⁻¹) = ⊤ :=
      ENNReal.sum_eq_top.mpr ⟨i, by simp, by simp [hi]⟩
    simp [hs]

theorem equilibrium_top {n : ℕ} (τ : Fin n → ℝ≥0∞) (htop : ∀ i, τ i = ⊤)
    (r : ℝ≥0∞) : equilibriumTime τ r = ⊤ := by
  open scoped BigOperators ENNReal NNReal in
    classical
    apply top_unique
    delta equilibriumTime
    refine le_iInf fun j => ?_
    have hnum : r + (j.val + 1 : ℕ) ≠ (0 : ℝ≥0∞) := by positivity
    have hden : (∑ i ∈ Finset.Iic j, (τ i)⁻¹) = 0 := by simp [htop]
    rw [hden]
    exact le_of_eq (ENNReal.div_eq_top.mpr (Or.inl ⟨hnum, rfl⟩)).symm

theorem equilibrium_finite_positive {n : ℕ} (τ : Fin n → ℝ≥0∞)
    (hpos : ∀ i, 0 < τ i) (hfinite : ∃ i, τ i ≠ ⊤)
    (r : ℝ≥0∞) (hr : 0 < r) (hrfinite : r ≠ ⊤) :
    0 < equilibriumTime τ r ∧ equilibriumTime τ r ≠ ⊤ := by
  open scoped BigOperators ENNReal NNReal in
    classical
    have _ := hr
    obtain ⟨i, hi⟩ := hfinite
    let : Nonempty (Fin n) := ⟨i⟩
    have hs (j : Fin n) : (∑ k ∈ Finset.Iic j, (τ k)⁻¹) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun k _ => ENNReal.inv_ne_top.mpr (hpos k).ne'
    obtain ⟨j, hj⟩ := Finite.ciInf_mem
      (fun j : Fin n => (r + (j.val + 1 : ℕ)) / ∑ k ∈ Finset.Iic j, (τ k)⁻¹)
    have heq : equilibriumTime τ r =
        (r + (j.val + 1 : ℕ)) / ∑ k ∈ Finset.Iic j, (τ k)⁻¹ := hj.symm
    constructor
    · rw [heq]
      exact ENNReal.div_pos (by positivity) (hs j)
    · have hden : 0 < ∑ k ∈ Finset.Iic i, (τ k)⁻¹ :=
        lt_of_lt_of_le (ENNReal.inv_pos.mpr hi)
          (Finset.single_le_sum (f := fun k : Fin n => (τ k)⁻¹) (a := i) (fun _ _ => zero_le) (by simp))
      exact ne_top_of_le_ne_top
        (ENNReal.div_ne_top (by simp [hrfinite]) hden.ne')
        (iInf_le (fun j : Fin n =>
          (r + (j.val + 1 : ℕ)) / ∑ k ∈ Finset.Iic j, (τ k)⁻¹) i)

theorem equilibrium_ratio {n : ℕ} (τ : Fin n → ℝ≥0∞) (S m : ℝ≥0∞)
    (hS : 0 < S) (hSm : S ≤ m) (hmfinite : m ≠ ⊤)
    (htpos : 0 < equilibriumTime τ m) (htfinite : equilibriumTime τ m ≠ ⊤) :
    S / m ≤ equilibriumTime τ S / equilibriumTime τ m := by
  open scoped BigOperators ENNReal NNReal in
    have hSf : S ≠ ⊤ := ne_top_of_le_ne_top hmfinite hSm
    have hnorm := (equilibrium_comparisons τ).2 S m hS hSm hmfinite
    have hmul := (ENNReal.le_div_iff_mul_le (Or.inl hS.ne') (Or.inl hSf)).mp hnorm
    apply (ENNReal.le_div_iff_mul_le (Or.inl htpos.ne') (Or.inl htfinite)).mpr
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

theorem harmonic_bound {m : ℕ} (hm : 0 < m) :
    (harmonic m : ℝ) ≤ 1 + Real.log m := by
  have _ := hm
  exact harmonic_le_one_add_log m

theorem large_sample_harmonic {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hlarge : largeSample m n) :
    n ≤ m ∧ (n : ℝ) * (harmonic m : ℝ) ≤ 2 * m := by
  open scoped BigOperators ENNReal NNReal in
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlarge' : (n : ℝ) * Real.log n ≤ m := hlarge
    constructor
    · by_cases hn1 : n = 1
      · omega
      · have hnRne : (n : ℝ) ≠ 1 := by exact_mod_cast hn1
        have hinvne : 1 / (n : ℝ) ≠ 1 := by
          intro hh
          have hh' := (div_eq_iff hnR.ne').mp hh
          exact hnRne (by linarith)
        have hl := Real.log_lt_sub_one_of_pos (one_div_pos.mpr hnR) hinvne
        rw [Real.log_div (by norm_num) hnR.ne', Real.log_one, zero_sub] at hl
        have hmul := mul_lt_mul_of_pos_left hl hnR
        have hcancel : (n : ℝ) * (1 / n) = 1 := by field_simp
        simp only [mul_sub, hcancel, mul_one] at hmul
        have hh : (n : ℝ) < (m : ℝ) + 1 := by nlinarith
        have hh' : n < m + 1 := by exact_mod_cast hh
        omega
    · have hl := Real.log_le_sub_one_of_pos (div_pos hmR hnR)
      rw [Real.log_div hmR.ne' hnR.ne'] at hl
      have hmul := mul_le_mul_of_nonneg_left hl hnR.le
      have hcancel : (n : ℝ) * ((m : ℝ) / n) = m := by field_simp
      simp only [mul_sub, hcancel, mul_one] at hmul
      have hH := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log m) hnR.le
      nlinarith

end LongTails.Proofs.FreyaEquilibrium

import LongTails.Template
import LongTails.Algorithms.FreyaTuning
import LongTails.Proofs.FreyaEquilibrium

open scoped ENNReal NNReal

namespace LongTails.Proofs.FreyaParameterTuning

open LongTails.Proofs.FreyaModel LongTails.Proofs.FreyaEquilibrium
open LongTails.Algorithms.FreyaInputs LongTails.Algorithms.FreyaTuning

noncomputable def scalarCoefficient (L D a b : ℝ) (S : ℕ) (ρ : ℝ) : ℝ :=
  (L + D * Real.sqrt ((1 - ρ) / (ρ * S))) * (ρ * a + (1 - ρ) * b)

noncomputable def timeCoefficient (p : Optimized) (S : ℕ) (ρ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (familyCoefficient p.toWorkers.toBase S ρ) *
    (ENNReal.ofReal ρ * equilibriumTime p.τ p.m +
      ENNReal.ofReal (1 - ρ) * equilibriumTime p.τ S)

theorem probability_comparison (L D a b : ℝ) (S : ℕ)
    (hL : 0 ≤ L) (hD : 0 ≤ D) (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ a) (hS : 0 < S) :
    let B := min (L * a) (L * b + D * Real.sqrt (a * b / S))
    let ρstar := if L * a ≤ L * b + D * Real.sqrt (a * b / S) then 1 else b / a
    0 < ρstar ∧ ρstar ≤ 1 ∧ scalarCoefficient L D a b S ρstar ≤ 2 * B ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → B / 2 ≤ scalarCoefficient L D a b S ρ := by
  dsimp only
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
  have ha0 := ha.le
  have hb0 := hb.le
  have hab : 0 ≤ a * b / (S : ℝ) := by positivity
  have hsab : 0 ≤ Real.sqrt (a * b / (S : ℝ)) := Real.sqrt_nonneg _
  have hsab2 := Real.sq_sqrt hab
  have hlower : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      min (L * a) (L * b + D * Real.sqrt (a * b / S)) / 2 ≤
        scalarCoefficient L D a b S ρ := by
    intro ρ hρ hρ1
    let w := ρ * a + (1 - ρ) * b
    let q := (1 - ρ) / (ρ * (S : ℝ))
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hw : 0 < w := by dsimp [w]; positivity
    have hr : 0 ≤ 1 - ρ := by linarith
    have hsqrt := Real.sqrt_nonneg q
    have hsqrt2 := Real.sq_sqrt hq
    have hwa : ρ * a ≤ w := le_add_of_nonneg_right (mul_nonneg hr hb0)
    have hwb : (1 - ρ) * b ≤ w := le_add_of_nonneg_left (mul_nonneg hρ.le ha0)
    have hbase : L * w ≤ scalarCoefficient L D a b S ρ := by
      delta scalarCoefficient
      change L * w ≤ (L + D * Real.sqrt q) * w
      nlinarith only [mul_nonneg (mul_nonneg hD hsqrt) hw.le]
    by_cases hh : (1 / 2 : ℝ) ≤ ρ
    · have hmin := min_le_left (L * a) (L * b + D * Real.sqrt (a * b / S))
      have hwlower : a / 2 ≤ w := by nlinarith only [hwa, hh, ha]
      linarith only [hbase, hmin, mul_le_mul_of_nonneg_left hwlower hL]
    · have hhalf : (1 / 2 : ℝ) ≤ 1 - ρ := by linarith
      have hprod : ρ * (1 - ρ) * a * b ≤ w ^ 2 := by
        have h := mul_le_mul hwa hwb (mul_nonneg hr hb0) hw.le
        nlinarith only [h]
      have hscaled := mul_le_mul_of_nonneg_left hprod hq
      have hid : q * (ρ * (1 - ρ) * a * b) = (1 - ρ)^2 * (a * b / S) := by
        dsimp [q]
        field_simp [hρ.ne', hSreal.ne']
      rw [hid] at hscaled
      have hsq : ((1 - ρ) * Real.sqrt (a * b / S))^2 ≤ (Real.sqrt q * w)^2 := by
        simpa only [mul_pow, hsab2, hsqrt2] using hscaled
      have hnoise : (1 - ρ) * Real.sqrt (a * b / S) ≤ Real.sqrt q * w := by
        have hn1 : 0 ≤ (1 - ρ) * Real.sqrt (a * b / S) := mul_nonneg hr hsab
        have hn2 : 0 ≤ Real.sqrt q * w := mul_nonneg hsqrt hw.le
        exact (sq_le_sq₀ hn1 hn2).mp hsq
      have hbhalf : b / 2 ≤ w := by nlinarith only [hwb, hhalf, hb]
      have hhnoise : Real.sqrt (a * b / S) / 2 ≤ Real.sqrt q * w := by nlinarith only [hnoise, hhalf, hsab]
      have hLw := mul_le_mul_of_nonneg_left hbhalf hL
      have hDw := mul_le_mul_of_nonneg_left hhnoise hD
      have hmin := min_le_right (L * a) (L * b + D * Real.sqrt (a * b / S))
      delta scalarCoefficient
      change _ ≤ (L + D * Real.sqrt q) * w
      nlinarith only [hLw, hDw, hmin]
  by_cases hcase : L * a ≤ L * b + D * Real.sqrt (a * b / S)
  · simp only [hcase, ite_true, min_eq_left hcase]
    refine ⟨by norm_num, le_rfl, ?_, by simpa only [min_eq_left hcase] using hlower⟩
    delta scalarCoefficient
    simp only [sub_self, zero_div, Real.sqrt_zero, mul_zero,
      add_zero, one_mul]
    nlinarith only [mul_nonneg hL ha0]
  · have hρ : 0 < b / a := div_pos hb ha
    have hρ1 : b / a ≤ 1 := (div_le_one ha).mpr hba
    have hmin : min (L * a) (L * b + D * Real.sqrt (a * b / S)) =
        L * b + D * Real.sqrt (a * b / S) := min_eq_right (le_of_not_ge hcase)
    simp only [hcase, ite_false, hmin]
    refine ⟨hρ, hρ1, ?_, by simpa only [hmin] using hlower⟩
    let q := (1 - b / a) / (b / a * (S : ℝ))
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hqle : q * b^2 ≤ a * b / S := by
      have hid : q * b^2 = (a-b)*b/S := by
        dsimp [q]
        field_simp [ha.ne', hb.ne', hSreal.ne']
      rw [hid]
      exact div_le_div_of_nonneg_right (by nlinarith only [sq_nonneg b]) hSreal.le
    have hsqrt := Real.sqrt_nonneg q
    have hsqrt2 := Real.sq_sqrt hq
    have hnoise : Real.sqrt q * b ≤ Real.sqrt (a*b/S) := by
      have hsq : (Real.sqrt q * b)^2 ≤ (Real.sqrt (a*b/S))^2 := by
        simpa only [mul_pow, hsab2, hsqrt2] using hqle
      have hnonneg := mul_nonneg hsqrt hb0
      exact (sq_le_sq₀ hnonneg hsab).mp hsq
    have hw : b/a*a+(1-b/a)*b ≤ 2*b := by
      rw [div_mul_cancel₀ _ ha.ne']
      nlinarith only [mul_nonneg hρ.le hb0]
    have hcoeff : 0 ≤ L + D * Real.sqrt q := by positivity
    have hscale := mul_le_mul_of_nonneg_left hw hcoeff
    delta scalarCoefficient
    change (L+D*Real.sqrt q)*(b/a*a+(1-b/a)*b) ≤ _
    nlinarith only [hscale, mul_le_mul_of_nonneg_left hnoise hD]


theorem finite_batch_minimum (p : Optimized) (hm : 0 < p.m) :
    1 ≤ optimizedBatch p ∧ optimizedBatch p ≤ p.m ∧
      batchObjective p (optimizedBatch p) =
        ⨅ j : Fin p.m, batchObjective p (j.val + 1) := by
  classical
  let xs := List.range' 1 p.m
  have hone : 1 ∈ xs := List.mem_range'.mpr ⟨0, hm, by simp⟩
  have hxs : xs ≠ [] := List.ne_nil_of_mem hone
  have heq : optimizedBatch p = xs.minOn (batchObjective p) hxs := by
    change (xs.minOn? (batchObjective p)).getD 1 = _
    rw [List.minOn?_eq_some_minOn hxs]
    rfl
  have hmem : optimizedBatch p ∈ xs := heq ▸ List.minOn_mem
  have hb : 1 ≤ optimizedBatch p ∧ optimizedBatch p < 1 + p.m :=
    by
      obtain ⟨i, hi, he⟩ := List.mem_range'.mp hmem
      simp only [one_mul] at he
      omega
  refine ⟨hb.1, by omega, le_antisymm ?_ ?_⟩
  · apply le_iInf
    intro j
    rw [heq]
    exact List.apply_minOn_le_of_mem (List.mem_range'.mpr ⟨j.val, j.isLt, by omega⟩)
  · let j : Fin p.m := ⟨optimizedBatch p - 1, by omega⟩
    have hj : j.val + 1 = optimizedBatch p := by dsimp [j]; omega
    exact (iInf_le (fun j : Fin p.m => batchObjective p (j.val + 1)) j).trans_eq (by rw [hj])


theorem optimized_comparison (p : Optimized) (hm : 0 < p.m) (hn : 0 < p.n)
    (hL : 0 ≤ p.Lminus) (hD : 0 ≤ p.Lpm) (hmono : Monotone p.τ)
    (htpos : 0 < equilibriumTime p.τ p.m) (htfinite : equilibriumTime p.τ p.m ≠ ⊤) :
    timeCoefficient p (optimizedBatch p) (optimizedProbability p) ≤
      2 * (⨅ j : Fin p.m, batchObjective p (j.val + 1)) ∧
      ∀ S : ℕ, 0 < S → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        timeCoefficient p (optimizedBatch p) (optimizedProbability p) ≤
          4 * timeCoefficient p S ρ := by
  open scoped ENNReal NNReal BigOperators in
    classical
    have _ := hn
    have _ := hmono
    have hτpos : ∀ i, 0 < p.τ i := by
      intro i
      apply pos_iff_ne_zero.mpr
      intro hi
      have hz := equilibrium_zero p.τ ⟨i,hi⟩ p.m (by simp)
      rw [hz] at htpos
      exact (lt_irrefl 0) htpos
    have hτfinite : ∃ i, p.τ i ≠ ⊤ := by
      by_contra h
      push Not at h
      exact htfinite (equilibrium_top p.τ h p.m)
    have htime (S : ℕ) (hS : 0 < S) :
        0 < equilibriumTime p.τ S ∧ equilibriumTime p.τ S ≠ ⊤ :=
      equilibrium_finite_positive p.τ hτpos hτfinite S (by exact_mod_cast hS) (by simp)
    let a := (equilibriumTime p.τ p.m).toReal
    let b (S : ℕ) := (equilibriumTime p.τ S).toReal
    have ha : 0 < a := ENNReal.toReal_pos htpos.ne' htfinite
    have hb (S : ℕ) (hS : 0 < S) : 0 < b S :=
      ENNReal.toReal_pos (htime S hS).1.ne' (htime S hS).2
    have hcf (S : ℕ) (hS : 0 < S) (ρ : ℝ) : timeCoefficient p S ρ ≠ ⊤ := by
      delta timeCoefficient
      exact ENNReal.mul_ne_top (by simp)
        (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) htfinite,
          ENNReal.mul_ne_top (by simp) (htime S hS).2⟩)
    have hcr (S : ℕ) (hS : 0 < S) (ρ : ℝ) (hρ : 0 < ρ) (hρone : ρ ≤ 1) :
        (timeCoefficient p S ρ).toReal = scalarCoefficient p.Lminus p.Lpm a (b S) S ρ := by
      delta timeCoefficient
      rw [ENNReal.toReal_mul, ENNReal.toReal_add
        (ENNReal.mul_ne_top (by simp) htfinite)
        (ENNReal.mul_ne_top (by simp) (htime S hS).2)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hρ.le,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hρone)]
      rw [ENNReal.toReal_ofReal (show 0 ≤ familyCoefficient p.toWorkers.toBase S ρ from
        add_nonneg hL (mul_nonneg hD (Real.sqrt_nonneg _)))]
      rfl
    have hleft : ENNReal.ofReal p.Lminus * equilibriumTime p.τ p.m ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top htfinite
    have hright (S : ℕ) (hS : 0 < S) :
        ENNReal.ofReal p.Lminus * equilibriumTime p.τ S + ENNReal.ofReal p.Lpm *
          ((equilibriumTime p.τ p.m * equilibriumTime p.τ S / S) ^ (1 / (2 : ℝ))) ≠ ⊤ := by
      have hs : (S : ℝ≥0∞) ≠ 0 := by exact_mod_cast hS.ne'
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (htime S hS).2,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
          (ENNReal.div_ne_top (ENNReal.mul_ne_top htfinite (htime S hS).2) hs))⟩
    have hrightR (S : ℕ) (hS : 0 < S) :
        (ENNReal.ofReal p.Lminus * equilibriumTime p.τ S + ENNReal.ofReal p.Lpm *
          ((equilibriumTime p.τ p.m * equilibriumTime p.τ S / S) ^ (1 / (2 : ℝ)))).toReal =
            p.Lminus*b S+p.Lpm*Real.sqrt (a*b S/S) := by
      obtain ⟨h₁,h₂⟩ := ENNReal.add_ne_top.mp (hright S hS)
      rw [ENNReal.toReal_add h₁ h₂]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL, ENNReal.toReal_ofReal hD,
        ← ENNReal.toReal_rpow, ENNReal.toReal_div, ENNReal.toReal_natCast, Real.sqrt_eq_rpow]
      rfl
    have hbf (S : ℕ) : batchObjective p S ≠ ⊤ :=
      ne_top_of_le_ne_top hleft (show batchObjective p S ≤
        ENNReal.ofReal p.Lminus * equilibriumTime p.τ p.m from min_le_left _ _)
    have hbr (S : ℕ) (hS : 0 < S) :
        (batchObjective p S).toReal = min (p.Lminus*a)
          (p.Lminus*b S+p.Lpm*Real.sqrt (a*b S/S)) := by
      delta batchObjective
      rw [ENNReal.toReal_min hleft (hright S hS), hrightR S hS]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL]
      rfl
    have hcond (S : ℕ) (hS : 0 < S) :
        (ENNReal.ofReal p.Lminus * equilibriumTime p.τ p.m ≤
          ENNReal.ofReal p.Lminus * equilibriumTime p.τ S + ENNReal.ofReal p.Lpm *
            ((equilibriumTime p.τ p.m * equilibriumTime p.τ S / S) ^ (1 / (2 : ℝ)))) ↔
          p.Lminus*a ≤ p.Lminus*b S+p.Lpm*Real.sqrt (a*b S/S) := by
      rw [← ENNReal.toReal_le_toReal hleft (hright S hS), hrightR S hS]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL]
      rfl
    obtain ⟨hSstar,hSmstar,hmin⟩ := finite_batch_minimum p hm
    let Sstar := optimizedBatch p
    have hbstar : b Sstar ≤ a := ENNReal.toReal_mono htfinite
      ((equilibrium_comparisons p.τ).1 (by exact_mod_cast hSmstar))
    have hpstar : optimizedProbability p =
        if p.Lminus*a ≤ p.Lminus*b Sstar+p.Lpm*Real.sqrt (a*b Sstar/Sstar)
          then 1 else b Sstar/a := by
      delta optimizedProbability
      dsimp only
      rw [ite_eq_right (not_or.mpr ⟨htpos.ne',htfinite⟩)]
      split
      · rename_i he
        rw [ite_eq_left ((hcond Sstar hSstar).mp he)]
      · rename_i he
        rw [ite_eq_right (mt (hcond Sstar hSstar).mpr he)]
        exact ENNReal.toReal_div _ _
    have hcmp := probability_comparison p.Lminus p.Lpm a (b Sstar) Sstar
      hL hD ha (hb Sstar hSstar) hbstar hSstar
    dsimp only at hcmp
    rw [← hpstar] at hcmp
    have hchosen : timeCoefficient p Sstar (optimizedProbability p) ≤ 2*batchObjective p Sstar := by
      apply (ENNReal.toReal_le_toReal (hcf Sstar hSstar _) (ENNReal.mul_ne_top (by simp) (hbf Sstar))).mp
      rw [hcr Sstar hSstar _ hcmp.1 hcmp.2.1, ENNReal.toReal_mul, hbr Sstar hSstar]
      simpa only [ENNReal.toReal_ofNat] using hcmp.2.2.1
    refine ⟨?_, ?_⟩
    · simpa only [Sstar, hmin] using hchosen
    · intro S hS ρ hρ hρone
      have hbaseline : batchObjective p Sstar ≤ ENNReal.ofReal p.Lminus*equilibriumTime p.τ p.m :=
        min_le_left _ _
      by_cases hSm : S ≤ p.m
      · have hbale : b S ≤ a := ENNReal.toReal_mono htfinite
          ((equilibrium_comparisons p.τ).1 (by exact_mod_cast hSm))
        have hother := (probability_comparison p.Lminus p.Lpm a (b S) S
          hL hD ha (hb S hS) hbale hS).2.2.2 ρ hρ hρone
        have hbest : batchObjective p Sstar ≤ batchObjective p S := by
          rw [show batchObjective p Sstar = ⨅ j : Fin p.m, batchObjective p (j.val+1) from hmin]
          have hsindex : S-1 < p.m := by omega
          simpa only [Nat.sub_add_cancel (show 1 ≤ S from hS)] using
            (iInf_le (fun j : Fin p.m => batchObjective p (j.val+1)) ⟨S-1, hsindex⟩)
        have hbestR := ENNReal.toReal_mono (hbf S) hbest
        rw [hbr S hS] at hbestR
        have hchosenR := ENNReal.toReal_mono
          (ENNReal.mul_ne_top (by simp) (hbf Sstar)) hchosen
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hchosenR
        apply (ENNReal.toReal_le_toReal (hcf Sstar hSstar _) (ENNReal.mul_ne_top (by simp) (hcf S hS ρ))).mp
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, hcr S hS ρ hρ hρone]
        linarith only [hbestR,hchosenR,hother]
      · have hab : a ≤ b S := ENNReal.toReal_mono (htime S hS).2
          ((equilibrium_comparisons p.τ).1 (by exact_mod_cast (le_of_lt (lt_of_not_ge hSm))))
        have hweight : a ≤ ρ*a+(1-ρ)*b S := by
          have hh := mul_le_mul_of_nonneg_left hab (sub_nonneg.mpr hρone)
          nlinarith only [hh]
        have hA : p.Lminus ≤ p.Lminus+p.Lpm*Real.sqrt ((1-ρ)/(ρ*S)) :=
          le_add_of_nonneg_right (mul_nonneg hD (Real.sqrt_nonneg _))
        have hbaseR : p.Lminus*a ≤ scalarCoefficient p.Lminus p.Lpm a (b S) S ρ :=
          mul_le_mul hA hweight ha.le (le_trans hL hA)
        have hbestR := ENNReal.toReal_mono hleft hbaseline
        simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL] at hbestR
        have hchosenR := ENNReal.toReal_mono
          (ENNReal.mul_ne_top (by simp) (hbf Sstar)) hchosen
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hchosenR
        have hnonneg : 0 ≤ scalarCoefficient p.Lminus p.Lpm a (b S) S ρ :=
          (mul_nonneg hL ha.le).trans hbaseR
        apply (ENNReal.toReal_le_toReal (hcf Sstar hSstar _) (ENNReal.mul_ne_top (by simp) (hcf S hS ρ))).mp
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, hcr S hS ρ hρ hρone]
        change (batchObjective p Sstar).toReal ≤ p.Lminus*a at hbestR
        linarith only [hbestR,hchosenR,hbaseR,hnonneg]


theorem ratio_case_one (p : Optimized) (hm : 0 < p.m) (hn : 0 < p.n)
    (hL : 0 < p.Lminus) (hD : 0 < p.Lpm) (hmono : Monotone p.τ)
    (hlower : (p.n : ℝ) ≤ p.Lpm * Real.sqrt p.m / p.Lminus)
    (hupper : p.Lpm * Real.sqrt p.m / p.Lminus ≤ p.m) :
    let u := p.Lpm * Real.sqrt p.m / p.Lminus
    1 ≤ ⌈u⌉₊ ∧ ⌈u⌉₊ ≤ p.m ∧ 0 < u / p.m ∧ u / p.m ≤ 1 ∧
      ∀ S : ℕ, 0 < S → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        timeCoefficient p ⌈u⌉₊ (u / p.m) ≤ 20 * timeCoefficient p S ρ := by
  open scoped ENNReal NNReal BigOperators in
    have freyaDevelopmentRatioReal (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
        (L D H : ℝ) (hL : 0 < L) (hD : 0 < D) (hH : 0 < H)
        (t : ℕ → ℝ) (hmono : Monotone t)
        (ht : ∀ S : ℕ, 0 < S → (S : ℝ)/H ≤ t S ∧ t S ≤ ((S : ℝ)+n)/H)
        (hlower : (n : ℝ) ≤ D*Real.sqrt m/L) (hupper : D*Real.sqrt m/L ≤ m)
        (S : ℕ) (hS : 0 < S) (ρ : ℝ) (hρ : 0 < ρ) (hρone : ρ ≤ 1) :
        scalarCoefficient L D (t m) (t ⌈D*Real.sqrt m/L⌉₊) ⌈D*Real.sqrt m/L⌉₊
          ((D*Real.sqrt m/L)/m) ≤ 20*scalarCoefficient L D (t m) (t S) S ρ := by
      let u := D*Real.sqrt m/L
      let B := ⌈u⌉₊
      let p := u/(m : ℝ)
      have hmr : (0 : ℝ) < m := by exact_mod_cast hm
      have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have huone : 1 ≤ u := hnr.trans hlower
      have hu : 0 < u := lt_of_lt_of_le zero_lt_one huone
      have hB : 0 < B := Nat.ceil_pos.mpr hu
      have hBr : (0 : ℝ) < B := by exact_mod_cast hB
      have huB : u ≤ (B : ℝ) := Nat.le_ceil u
      have hBu : (B : ℝ) ≤ 2*u := by
        have hc := Nat.ceil_lt_add_one hu.le
        change (B : ℝ) < u+1 at hc
        linarith only [hc,huone]
      have hp : 0 < p := div_pos hu hmr
      have hpone : p ≤ 1 := (div_le_one hmr).mpr hupper
      have hpm : p*(m : ℝ) = u := div_mul_cancel₀ u hmr.ne'
      have huL : u*L = D*Real.sqrt m := div_mul_cancel₀ _ hL.ne'
      have hvar : (1-p)/(p*B) ≤ (m : ℝ)/u^2 := by
        apply (div_le_div_iff₀ (mul_pos hp hBr) (sq_pos_of_pos hu)).mpr
        have hUB : u^2 ≤ u*(B : ℝ) := by
          have hh := mul_le_mul_of_nonneg_left huB hu.le
          nlinarith only [hh]
        have he : (m : ℝ)*(p*B) = u*(B : ℝ) := by rw [mul_left_comm, ← mul_assoc, hpm]
        rw [he]
        nlinarith only [hUB, mul_nonneg hp.le (sq_nonneg u)]
      have hsqrt : Real.sqrt ((1-p)/(p*B)) ≤ Real.sqrt m/u := by
        calc
          _ ≤ Real.sqrt ((m : ℝ)/u^2) := Real.sqrt_le_sqrt hvar
          _ = _ := by rw [Real.sqrt_div hmr.le,Real.sqrt_sq hu.le]
      have hA : L+D*Real.sqrt ((1-p)/(p*B)) ≤ 2*L := by
        have hh := mul_le_mul_of_nonneg_left hsqrt hD.le
        have he : D*(Real.sqrt m/u) = L := by
          rw [← mul_div_assoc]
          exact (div_eq_iff hu.ne').mpr (by linarith only [huL])
        rw [he] at hh
        linarith only [hh]
      have htB : 0 ≤ t B := (div_pos hBr hH).le.trans (ht B hB).1
      have hweight : p*t m+(1-p)*t B ≤ 5*u/H := by
        have hmup := mul_le_mul_of_nonneg_left (ht m hm).2 hp.le
        have hBup := (mul_le_mul_of_nonneg_right (show 1-p ≤ 1 by linarith only [hp]) htB).trans
          (by simpa only [one_mul] using (ht B hB).2)
        have hpn : p*(n : ℝ) ≤ n := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hpone (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        have hnum : p*((m : ℝ)+n)+((B : ℝ)+n) ≤ 5*u := by
          rw [mul_add,hpm]
          nlinarith only [hpn,hBu,hlower]
        have hh := (div_le_div_iff_of_pos_right hH).mpr hnum
        rw [add_div,mul_div_assoc] at hh
        linarith only [hmup,hBup,hh]
      have hselected : scalarCoefficient L D (t m) (t B) B p ≤ 10*D*Real.sqrt m/H := by
        have hw : 0 ≤ p*t m+(1-p)*t B :=
          add_nonneg (mul_nonneg hp.le ((div_pos hmr hH).le.trans (ht m hm).1))
            (mul_nonneg (sub_nonneg.mpr hpone) htB)
        have hh := mul_le_mul hA hweight hw (by positivity : 0 ≤ 2*L)
        change scalarCoefficient L D (t m) (t B) B p ≤ _ at hh
        convert hh using 1
        rw [show (2*L)*(5*u/H) = 10*(u*L)/H by ring,huL]
        ring
      have hmlo : 0 < t m := (div_pos hmr hH).trans_le (ht m hm).1
      have hSr : (0 : ℝ) < S := by exact_mod_cast hS
      have hSlo : 0 < t S := (div_pos hSr hH).trans_le (ht S hS).1
      have hLm : D*Real.sqrt m/H ≤ L*t m := by
        have hum := mul_le_mul_of_nonneg_left hupper hL.le
        have hnum : D*Real.sqrt m ≤ L*(m : ℝ) := by nlinarith only [hum,huL]
        have hh := (div_le_div_iff_of_pos_right hH).mpr hnum
        exact hh.trans (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (ht m hm).1 hL.le)
      have hother : D*Real.sqrt m/(2*H) ≤ scalarCoefficient L D (t m) (t S) S ρ := by
        by_cases hSm : S ≤ m
        · have hprod := mul_le_mul (ht m hm).1 (ht S hS).1 (div_pos hSr hH).le hmlo.le
          have hrad : (m : ℝ)/H^2 ≤ t m*t S/(S : ℝ) := by
            apply (div_le_div_iff₀ (sq_pos_of_pos hH) hSr).mpr
            have he : ((m : ℝ)/H)*((S : ℝ)/H)*H^2 = (m : ℝ)*S := by field_simp [hH.ne']
            have hh := mul_le_mul_of_nonneg_right hprod (sq_nonneg H)
            rw [he] at hh
            exact hh
          have hroot : Real.sqrt m/H ≤ Real.sqrt (t m*t S/S) := by
            have hh := Real.sqrt_le_sqrt hrad
            rw [Real.sqrt_div hmr.le,Real.sqrt_sq hH.le] at hh
            exact hh
          have hDroot := mul_le_mul_of_nonneg_left hroot hD.le
          have hsecond : D*Real.sqrt m/H ≤ L*t S+D*Real.sqrt (t m*t S/S) := by
            have hnz : 0 ≤ L*t S := mul_nonneg hL.le hSlo.le
            rw [mul_div_assoc]
            linarith only [hDroot,hnz]
          have hb := le_min hLm hsecond
          have hc := (probability_comparison L D (t m) (t S) S hL.le hD.le hmlo hSlo
            (hmono hSm) hS).2.2.2 ρ hρ hρone
          have hh := div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 2)
          have he : (D*Real.sqrt m/H)/2 = D*Real.sqrt m/(2*H) := by ring
          rw [he] at hh
          exact hh.trans hc
        · have hab : t m ≤ t S := hmono (by omega)
          have hw : t m ≤ ρ*t m+(1-ρ)*t S := by
            have hh := mul_le_mul_of_nonneg_left hab (sub_nonneg.mpr hρone)
            nlinarith only [hh]
          have hA' : L ≤ L+D*Real.sqrt ((1-ρ)/(ρ*S)) :=
            le_add_of_nonneg_right (mul_nonneg hD.le (Real.sqrt_nonneg _))
          have hc : L*t m ≤ scalarCoefficient L D (t m) (t S) S ρ :=
            mul_le_mul hA' hw hmlo.le (hL.le.trans hA')
          have he : D*Real.sqrt m/(2*H) ≤ D*Real.sqrt m/H := by
            apply div_le_div_of_nonneg_left (by positivity) hH
            linarith only [hH]
          exact he.trans (hLm.trans hc)
      have hscaled := mul_le_mul_of_nonneg_left hother (by norm_num : (0 : ℝ) ≤ 20)
      have he : 20*(D*Real.sqrt m/(2*H)) = 10*D*Real.sqrt m/H := by ring
      rw [he] at hscaled
      exact hselected.trans hscaled
    classical
    have _ := hmono
    let u := p.Lpm*Real.sqrt p.m/p.Lminus
    have hmr : (0 : ℝ) < p.m := by exact_mod_cast hm
    have hu : 0 < u := lt_of_lt_of_le (by exact_mod_cast hn : (0 : ℝ) < p.n) hlower
    have hB : 0 < ⌈u⌉₊ := Nat.ceil_pos.mpr hu
    have hBm : ⌈u⌉₊ ≤ p.m := Nat.ceil_le.mpr hupper
    have hp : 0 < u/p.m := div_pos hu hmr
    have hpone : u/p.m ≤ 1 := (div_le_one hmr).mpr hupper
    refine ⟨hB,hBm,hp,hpone,?_⟩
    intro S hS ρ hρ hρone
    by_cases hzero : ∃ i, p.τ i = 0
    · have hz (r : ℕ) : equilibriumTime p.τ r = 0 := equilibrium_zero p.τ hzero r (by simp)
      delta timeCoefficient
      rw [hz p.m,hz ⌈u⌉₊,hz S]
      simp
    have hτpos : ∀ i, 0 < p.τ i := fun i => pos_iff_ne_zero.mpr (fun hi => hzero ⟨i,hi⟩)
    by_cases htop : ∀ i, p.τ i = ⊤
    · have hA : 0 < familyCoefficient p.toWorkers.toBase S ρ :=
        add_pos_of_pos_of_nonneg hL (mul_nonneg hD.le (Real.sqrt_nonneg _))
      have hr : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.mpr hρ).ne'
      have ha : ENNReal.ofReal (familyCoefficient p.toWorkers.toBase S ρ) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr hA).ne'
      have ht : timeCoefficient p S ρ = ⊤ := by
        delta timeCoefficient
        rw [equilibrium_top p.τ htop p.m,ENNReal.mul_top hr,top_add,ENNReal.mul_top ha]
      rw [ht]
      simp
    have hτfinite : ∃ i, p.τ i ≠ ⊤ := by simpa only [not_forall] using htop
    let R : ℝ≥0∞ := ∑ i : Fin p.n, (p.τ i)⁻¹
    have hRfinite : R ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.inv_ne_top.mpr (hτpos i).ne')
    have hRpos : 0 < R := by
      obtain ⟨i,hi⟩ := hτfinite
      exact (ENNReal.inv_pos.mpr hi).trans_le (Finset.single_le_sum (f := fun k => (p.τ k)⁻¹) (fun k _ => zero_le) (Finset.mem_univ i))
    have hbounds (r : ℕ) : (r : ℝ≥0∞)/R ≤ equilibriumTime p.τ r ∧
        equilibriumTime p.τ r ≤ ((r : ℝ≥0∞)+p.n)/R := by
      constructor
      · change _ ≤ ⨅ j : Fin p.n, ((r : ℝ≥0∞)+(j.val+1 : ℕ))/(∑ i ∈ Finset.Iic j, (p.τ i)⁻¹)
        apply le_iInf
        intro j
        have hden : (∑ i ∈ Finset.Iic j, (p.τ i)⁻¹) ≤ R :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        gcongr
        exact le_add_of_nonneg_right zero_le
      · let j : Fin p.n := ⟨p.n-1,by omega⟩
        have hI : Finset.Iic j = Finset.univ := by
          ext i
          simp only [Finset.mem_Iic,Finset.mem_univ,iff_true]
          change i.val ≤ p.n-1
          have hi := i.isLt
          omega
        have hnval : j.val+1 = p.n := by dsimp only [j]; omega
        have hh := iInf_le (fun j : Fin p.n => ((r : ℝ≥0∞)+(j.val+1 : ℕ))/
          (∑ i ∈ Finset.Iic j, (p.τ i)⁻¹)) j
        rw [hI,hnval] at hh
        exact hh
    have hfinite (r : ℕ) : equilibriumTime p.τ r ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.div_ne_top (by simp) hRpos.ne') (hbounds r).2
    let H := R.toReal
    have hH : 0 < H := ENNReal.toReal_pos hRpos.ne' hRfinite
    let t (r : ℕ) := (equilibriumTime p.τ r).toReal
    have htmono : Monotone t := fun r s hrs => ENNReal.toReal_mono (hfinite s)
      ((equilibrium_comparisons p.τ).1 (by exact_mod_cast hrs))
    have ht (r : ℕ) (_ : 0 < r) : (r : ℝ)/H ≤ t r ∧ t r ≤ ((r : ℝ)+p.n)/H := by
      constructor
      · have hh := ENNReal.toReal_mono (hfinite r) (hbounds r).1
        simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast] using hh
      · have hf : ((r : ℝ≥0∞)+p.n)/R ≠ ⊤ := ENNReal.div_ne_top (by simp) hRpos.ne'
        have hh := ENNReal.toReal_mono hf (hbounds r).2
        rw [ENNReal.toReal_div, ENNReal.toReal_add (by simp) (by simp)] at hh
        simpa only [ENNReal.toReal_natCast] using hh
    have hcf (r : ℕ) (θ : ℝ) : timeCoefficient p r θ ≠ ⊤ := by
      delta timeCoefficient
      exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by simp) (hfinite p.m),ENNReal.mul_ne_top (by simp) (hfinite r)⟩)
    have hcr (r : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
        (timeCoefficient p r θ).toReal = scalarCoefficient p.Lminus p.Lpm (t p.m) (t r) r θ := by
      delta timeCoefficient
      rw [ENNReal.toReal_mul, ENNReal.toReal_add
        (ENNReal.mul_ne_top (by simp) (hfinite p.m))
        (ENNReal.mul_ne_top (by simp) (hfinite r))]
      simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hθ.le,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hθone)]
      rw [ENNReal.toReal_ofReal (show 0 ≤ familyCoefficient p.toWorkers.toBase r θ from
        add_nonneg hL.le (mul_nonneg hD.le (Real.sqrt_nonneg _)))]
      rfl
    apply (ENNReal.toReal_le_toReal (hcf _ _) (ENNReal.mul_ne_top (by simp) (hcf S ρ))).mp
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofNat,hcr _ _ hp hpone,hcr S ρ hρ hρone]
    exact freyaDevelopmentRatioReal p.m p.n hm hn p.Lminus p.Lpm H hL hD hH t htmono ht
      hlower hupper S hS ρ hρ hρone


theorem simple_coefficient (p : Simple) (hm : 0 < p.m)
    (hL : 0 ≤ p.Lminus) (hD : 0 ≤ p.Lpm) :
    familyCoefficient p.toWorkers.toBase (simpleBatch p) (simpleProbability p) ≤
      2 * max p.Lminus p.Lpm := by
  have hm1 : (1 : ℝ) ≤ p.m := by exact_mod_cast hm
  have hu1 : 1 ≤ Real.sqrt (p.m : ℝ) := Real.le_sqrt_of_sq_le (by simpa using hm1)
  have hu : 0 < Real.sqrt (p.m : ℝ) := lt_of_lt_of_le zero_lt_one hu1
  have hS : Real.sqrt (p.m : ℝ) ≤ (simpleBatch p : ℝ) := Nat.le_ceil _
  have hden : 1 ≤ simpleProbability p * (simpleBatch p : ℝ) := by
    dsimp [simpleProbability]
    rw [one_div, inv_mul_eq_div]
    exact (le_div_iff₀ hu).mpr (by simpa using hS)
  have hprob : 0 ≤ simpleProbability p := by delta simpleProbability; positivity
  have hprob1 : simpleProbability p ≤ 1 := by
    delta simpleProbability
    exact (div_le_one hu).mpr hu1
  have hratio : (1 - simpleProbability p) / (simpleProbability p * (simpleBatch p : ℝ)) ≤ 1 :=
    (div_le_one (lt_of_lt_of_le zero_lt_one hden)).mpr (by linarith)
  have hsqrt : Real.sqrt ((1 - simpleProbability p) / (simpleProbability p * (simpleBatch p : ℝ))) ≤ 1 :=
    (Real.sqrt_le_one).mpr hratio
  have hcoeff : familyCoefficient p.toWorkers.toBase (simpleBatch p) (simpleProbability p) ≤ p.Lminus + p.Lpm := by
    delta familyCoefficient
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hD]
  have hmax1 := le_max_left p.Lminus p.Lpm
  have hmax2 := le_max_right p.Lminus p.Lpm
  have _ := hL
  have _ := hprob1
  linarith


theorem simple_time_comparisons (p : Simple) (hm : 0 < p.m)
    (τ : Fin p.n → ℝ≥0∞) :
    ENNReal.ofReal (simpleProbability p) * equilibriumTime τ p.m ≤
        equilibriumTime τ (ENNReal.ofReal (Real.sqrt p.m)) ∧
      ENNReal.ofReal (1 - simpleProbability p) * equilibriumTime τ (simpleBatch p) ≤
        equilibriumTime τ (ENNReal.ofReal (Real.sqrt p.m)) := by
  open scoped BigOperators ENNReal NNReal in
    classical
    have scaled (a b c : ℝ≥0∞) (hc : c ≤ 1) (hab : c * a ≤ b) :
        c * equilibriumTime τ a ≤ equilibriumTime τ b := by
      apply le_iInf
      intro j
      calc
        c * equilibriumTime τ a ≤ c * ((a + (j.val + 1 : ℕ)) /
            ∑ i ∈ Finset.Iic j, (τ i)⁻¹) := mul_le_mul' le_rfl (iInf_le _ j)
        _ = (c * (a + (j.val + 1 : ℕ))) / ∑ i ∈ Finset.Iic j, (τ i)⁻¹ := by
          simp only [div_eq_mul_inv, mul_assoc]
        _ ≤ (b + (j.val + 1 : ℕ)) / ∑ i ∈ Finset.Iic j, (τ i)⁻¹ := by
          apply ENNReal.div_le_div_right
          rw [mul_add]
          exact add_le_add hab (by simpa only [one_mul] using mul_le_mul_left hc ((j.val + 1 : ℕ) : ℝ≥0∞))
    let u : ℝ := Real.sqrt p.m
    have hmR : (0 : ℝ) < p.m := by exact_mod_cast hm
    have hm1 : (1 : ℝ) ≤ p.m := by exact_mod_cast hm
    have hu1 : 1 ≤ u := Real.le_sqrt_of_sq_le (by simpa using hm1)
    have hu : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    have hu2 : u^2 = p.m := Real.sq_sqrt hmR.le
    have hρ : 0 ≤ simpleProbability p := by change 0 ≤ 1 / u; positivity
    have hρ1 : simpleProbability p ≤ 1 := by change 1 / u ≤ 1; exact (div_le_one hu).mpr hu1
    have hρu : simpleProbability p * u = 1 := by change 1 / u * u = 1; exact div_mul_cancel₀ _ hu.ne'
    have hρm : simpleProbability p * (p.m : ℝ) = u := by
      change 1 / u * (p.m : ℝ) = u
      field_simp [hu.ne']
      nlinarith only [hu2]
    have hceil : (simpleBatch p : ℝ) ≤ u + 1 := (Nat.ceil_lt_add_one hu.le).le
    have hφ : 0 ≤ 1 - simpleProbability p := sub_nonneg.mpr hρ1
    have hφ1 : 1 - simpleProbability p ≤ 1 := by linarith
    have hφc : (1 - simpleProbability p) * (simpleBatch p : ℝ) ≤ u := by
      have h := mul_le_mul_of_nonneg_left hceil hφ
      nlinarith only [h, hρu, hρ]
    have hρe : ENNReal.ofReal (simpleProbability p) ≤ 1 := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hρ1
    have hφe : ENNReal.ofReal (1 - simpleProbability p) ≤ 1 := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hφ1
    constructor
    · apply scaled _ _ _ hρe
      have h := ENNReal.ofReal_le_ofReal hρm.le
      simpa only [ENNReal.ofReal_mul hρ, ENNReal.ofReal_natCast] using h
    · apply scaled _ _ _ hφe
      have h := ENNReal.ofReal_le_ofReal hφc
      simpa only [ENNReal.ofReal_mul hφ, ENNReal.ofReal_natCast] using h


theorem optimized_tuning_legal (p : Optimized) (hm : 0 < p.m) (hn : 0 < p.n)
    (hL : 0 < p.Lminus) (hD : 0 ≤ p.Lpm) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (hmono : Monotone p.τ) :
    1 ≤ optimizedBatch p ∧ optimizedBatch p ≤ p.m ∧
      0 < optimizedProbability p ∧ optimizedProbability p ≤ 1 ∧
      0 < optimizedStep p ∧ 1 ≤ optimizedHorizon p ∧
      familyCoefficient p.toWorkers.toBase (optimizedBatch p) (optimizedProbability p) ≤
        p.Lminus + p.Lpm * Real.sqrt p.m ∧
      2 * p.Δ / (optimizedStep p * optimizedHorizon p) ≤ p.ε := by
  open scoped ENNReal NNReal in
    have _ := hn
    have _ := hmono
    have _ := hΔ
    obtain ⟨hS, hSm, _⟩ := finite_batch_minimum p hm
    let S := optimizedBatch p
    let ρ := optimizedProbability p
    have hSr : (0 : ℝ) < S := by exact_mod_cast hS
    have hmr : (0 : ℝ) < p.m := by exact_mod_cast hm
    have hSmr : (S : ℝ) ≤ p.m := by exact_mod_cast hSm
    have hratio : 0 < ρ ∧ ρ ≤ 1 ∧ (S : ℝ) / p.m ≤ ρ := by
      change 0 < optimizedProbability p ∧ optimizedProbability p ≤ 1 ∧
        (S : ℝ) / p.m ≤ optimizedProbability p
      delta optimizedProbability
      dsimp only
      split
      · exact ⟨zero_lt_one, le_rfl, (div_le_one hmr).mpr hSmr⟩
      · rename_i hboundary
        have htm0 : equilibriumTime p.τ p.m ≠ 0 := fun h => hboundary (Or.inl h)
        have htmf : equilibriumTime p.τ p.m ≠ ⊤ := fun h => hboundary (Or.inr h)
        split
        · exact ⟨zero_lt_one, le_rfl, (div_le_one hmr).mpr hSmr⟩
        · have hSE : (0 : ℝ≥0∞) < S := by exact_mod_cast hS
          have hSmE : (S : ℝ≥0∞) ≤ p.m := by exact_mod_cast hSm
          have htsle := (equilibrium_comparisons p.τ).1 hSmE
          have htsf := ne_top_of_le_ne_top htmf htsle
          have hqf : equilibriumTime p.τ S / equilibriumTime p.τ p.m ≠ ⊤ :=
            ENNReal.div_ne_top htsf htm0
          have hqle : equilibriumTime p.τ S / equilibriumTime p.τ p.m ≤ 1 := by
            apply (ENNReal.div_le_iff htm0 htmf).mpr
            simpa only [one_mul] using htsle
          have hlower := equilibrium_ratio p.τ (S : ℝ≥0∞) p.m hSE hSmE
            (by simp) (pos_iff_ne_zero.mpr htm0) htmf
          have hlowerR : (S : ℝ) / p.m ≤
              (equilibriumTime p.τ S / equilibriumTime p.τ p.m).toReal := by
            simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast] using
              ENNReal.toReal_mono hqf hlower
          exact ⟨lt_of_lt_of_le (div_pos hSr hmr) hlowerR,
            by simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by simp) hqle,
            hlowerR⟩
    have hρS : 0 < ρ * S := mul_pos hratio.1 hSr
    have hvar : (1-ρ)/(ρ*S) ≤ (p.m : ℝ) := by
      have hproduct : (S : ℝ) ≤ ρ * p.m := (div_le_iff₀ hmr).mp hratio.2.2
      have hSone : (1 : ℝ) ≤ S := by exact_mod_cast hS
      have hmul := mul_le_mul_of_nonneg_right hproduct (le_of_lt hSr)
      have hsquare : (1 : ℝ) ≤ (S : ℝ)*(S : ℝ) := by nlinarith only [hSone]
      apply (div_le_iff₀ hρS).mpr
      nlinarith only [hmul, hsquare, hratio.1]
    have hAub : familyCoefficient p.toWorkers.toBase S ρ ≤
        p.Lminus+p.Lpm*Real.sqrt p.m := by
      change p.Lminus+p.Lpm*Real.sqrt ((1-ρ)/(ρ*S)) ≤ _
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar) hD)
    let A := familyCoefficient p.toWorkers.toBase S ρ
    have hA : 0 < A := by
      change 0 < p.Lminus+p.Lpm*Real.sqrt ((1-ρ)/(ρ*S))
      exact add_pos_of_pos_of_nonneg hL (mul_nonneg hD (Real.sqrt_nonneg _))
    have hη : 0 < optimizedStep p := by change 0 < 1/A; positivity
    have hK : 1 ≤ optimizedHorizon p := le_max_left _ _
    have hKr : (0 : ℝ) < optimizedHorizon p := by exact_mod_cast hK
    refine ⟨hS, hSm, hratio.1, hratio.2.1, hη, hK, hAub, ?_⟩
    have hceil : 2*p.Δ*A/p.ε ≤ (optimizedHorizon p : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈2*p.Δ*A/p.ε⌉₊))
    have hnum : 2*p.Δ*A ≤ (optimizedHorizon p : ℝ)*p.ε :=
      (div_le_iff₀ hε).mp hceil
    apply (div_le_iff₀ (mul_pos hη hKr)).mpr
    change 2*p.Δ ≤ p.ε*((1/A)*(optimizedHorizon p : ℝ))
    calc
      2*p.Δ = (2*p.Δ*A)*(1/A) := by field_simp [hA.ne']
      _ ≤ ((optimizedHorizon p : ℝ)*p.ε)*(1/A) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = p.ε*((1/A)*(optimizedHorizon p : ℝ)) := by ring


theorem simple_tuning_legal (p : Simple) (hm : 0 < p.m)
    (hL : 0 < p.Lminus) (hD : 0 ≤ p.Lpm) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    1 ≤ simpleBatch p ∧ simpleBatch p ≤ p.m ∧
      0 < simpleProbability p ∧ simpleProbability p ≤ 1 ∧
      0 < simpleStep p ∧ 1 ≤ simpleHorizon p ∧
      2 * p.Δ / (simpleStep p * simpleHorizon p) ≤ p.ε := by
  have _ := hΔ
  have hm1 : (1 : ℝ) ≤ p.m := by exact_mod_cast hm
  have hu1 : 1 ≤ Real.sqrt (p.m : ℝ) := Real.le_sqrt_of_sq_le (by simpa using hm1)
  have hu : 0 < Real.sqrt (p.m : ℝ) := lt_of_lt_of_le zero_lt_one hu1
  have hSpos : 1 ≤ simpleBatch p := by
    delta simpleBatch
    exact Nat.one_le_ceil_iff.mpr hu
  have hSle : simpleBatch p ≤ p.m := by
    delta simpleBatch
    apply Nat.ceil_le.mpr
    exact Real.sqrt_le_self_iff.mpr (Or.inr hm1)
  have hρ : 0 < simpleProbability p := by delta simpleProbability; positivity
  have hρ1 : simpleProbability p ≤ 1 := by
    delta simpleProbability
    exact (div_le_one hu).mpr hu1
  let A := familyCoefficient p.toWorkers.toBase (simpleBatch p) (simpleProbability p)
  have hA : 0 < A := by
    change 0 < p.Lminus + p.Lpm * Real.sqrt ((1 - simpleProbability p) / (simpleProbability p * (simpleBatch p : ℝ)))
    exact add_pos_of_pos_of_nonneg hL (mul_nonneg hD (Real.sqrt_nonneg _))
  have hη : 0 < simpleStep p := by change 0 < 1 / A; positivity
  have hK : 1 ≤ simpleHorizon p := le_max_left _ _
  have hKreal : (0 : ℝ) < simpleHorizon p := by exact_mod_cast hK
  refine ⟨hSpos, hSle, hρ, hρ1, hη, hK, ?_⟩
  have hceil : 2 * p.Δ * A / p.ε ≤ (simpleHorizon p : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈2 * p.Δ * A / p.ε⌉₊))
  have hnum : 2 * p.Δ * A ≤ (simpleHorizon p : ℝ) * p.ε :=
    (div_le_iff₀ hε).mp hceil
  apply (div_le_iff₀ (mul_pos hη hKreal)).mpr
  change 2 * p.Δ ≤ p.ε * ((1 / A) * (simpleHorizon p : ℝ))
  calc
    2 * p.Δ = (2 * p.Δ * A) * (1 / A) := by field_simp [hA.ne']
    _ ≤ ((simpleHorizon p : ℝ) * p.ε) * (1 / A) :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = p.ε * ((1 / A) * (simpleHorizon p : ℝ)) := by ring


end LongTails.Proofs.FreyaParameterTuning

import LongTails.Proofs.BlackBoxInvariant
import LongTails.Proofs.Execution

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.BlackBoxDiagonal

variable {d : ℕ}

section Accuracy

variable {f : Vec d → ℝ} {w : Fin d → ℝ} {μ : ℝ} (Hy : BHyp f w μ) (x0 : Vec d)
include Hy

lemma acc_of_gam (xstar x : Vec d) :
    f x - f xstar ≤ Gam f x0 x / (2 * μ) := by
  have hsc := Hy.sc x xstar
  rw [← dot_eq_inner] at hsc
  have hμ := Hy.μ_pos
  have hy := dot_young Hy.w_pos (inv_pos.mpr hμ) (gradient f x) (x - xstar)
  have e1 : 1 / (2 * μ⁻¹) = μ / 2 := by field_simp
  rw [e1] at hy
  have hneg : dot (gradient f x) (xstar - x) = -dot (gradient f x) (x - xstar) := by
    unfold dot; rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [PiLp.sub_apply]; ring
  have hw : wsq w (x - xstar) = ∑ i, w i * (xstar i - x i) ^ 2 := by
    unfold wsq; exact Finset.sum_congr rfl fun i _ => by simp only [PiLp.sub_apply]; ring
  have hJ : isq w (gradient f x) ≤ Gam f x0 x := by
    unfold Gam isq
    exact Finset.sum_le_sum fun i _ =>
      div_le_div_of_nonneg_left (sq_nonneg _) (sec_pos Hy x0 i) (sec_bounds Hy x0 i).2
  rw [hneg] at hsc
  have e2 : μ⁻¹ / 2 * isq w (gradient f x) = isq w (gradient f x) / (2 * μ) := by
    field_simp
  have : isq w (gradient f x) / (2 * μ) ≤ Gam f x0 x / (2 * μ) :=
    div_le_div_of_nonneg_right hJ (by positivity)
  have hwμ : μ / 2 * wsq w (x - xstar) = μ * (∑ i, w i * (xstar i - x i) ^ 2) / 2 := by
    rw [hw]; ring
  linarith

lemma gam0_le {xstar : Vec d} (hmin : IsMinOn f Set.univ xstar) :
    Gam f x0 x0 ≤ 2 * (f x0 - f xstar) / μ := by
  have hμ := Hy.μ_pos
  set g := gradient f x0
  set y : Vec d := WithLp.toLp 2 (fun i => x0 i - g i / w i)
  have hs := Hy.smooth x0 y
  rw [← dot_eq_inner] at hs
  have e1 : dot g (y - x0) = -isq w g := by
    unfold dot isq; rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [y, PiLp.sub_apply]
    have := (Hy.w_pos i).ne'
    field_simp
    ring
  have e2 : ∑ i, w i * (y i - x0 i) ^ 2 = isq w g := by
    unfold isq
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [y]
    have := (Hy.w_pos i).ne'
    field_simp
    ring
  rw [e1, e2] at hs
  have hm := hmin (Set.mem_univ y)
  simp only [Set.mem_ofPred_eq] at hm
  have h1 : isq w g ≤ 2 * (f x0 - f xstar) := by linarith
  have h2 : Gam f x0 x0 ≤ isq w g / μ := by
    unfold Gam isq
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    have hb := (sec_bounds Hy x0 i).1
    have hwp := Hy.w_pos i
    rw [div_div]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  calc Gam f x0 x0 ≤ isq w g / μ := h2
    _ ≤ 2 * (f x0 - f xstar) / μ := div_le_div_of_nonneg_right h1 hμ.le

end Accuracy

noncomputable def FCmax (d : ℕ) (μ : ℝ) : ℕ :=
  ∑ j ∈ Finset.range (jstar μ + 1), cap d j * cost j

section Count

variable {f : Vec d → ℝ} {x0 : Vec d} {w : Fin d → ℝ} {μ : ℝ}

lemma fch_le_max {n : ℕ} (I : Inv f x0 w μ n) : FCh f x0 n ≤ FCmax d μ := by
  unfold FCh FCmax
  have h1 : (ms f x0 n).fails * cost (ms f x0 n).lvl ≤ cap d (ms f x0 n).lvl * cost (ms f x0 n).lvl :=
    Nat.mul_le_mul_right _ I.fails_lt.le
  have h2 : ∑ j ∈ Finset.range ((ms f x0 n).lvl + 1), cap d j * cost j ≤
      ∑ j ∈ Finset.range (jstar μ + 1), cap d j * cost j :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (by have := I.lvl_le; omega))
  rw [Finset.sum_range_succ] at h2
  omega

end Count

lemma ell_bounds {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    (jstar μ : ℝ) + 2 ≤ 3 + Real.logb 2 (1 / μ) ∧ 1 ≤ 3 + Real.logb 2 (1 / μ) := by
  have h0 : 0 ≤ Real.logb 2 (1 / μ) :=
    Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hμ]; linarith)
  have h1 : (jstar μ : ℝ) < Real.logb 2 (1 / μ) + 1 := Nat.ceil_lt_add_one h0
  constructor <;> linarith

lemma budget_core {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) {L : ℝ} (hL : 0 ≤ L) :
    (FCmax d μ : ℝ) + rate μ * L + cost (jstar μ) ≤
      21 * Real.sqrt (2 / μ) * (L + (d + 1) * (3 + Real.logb 2 (1 / μ)) ^ 4) := by
  obtain ⟨hℓ, hℓ1⟩ := ell_bounds hμ hμ1
  set ℓ := 3 + Real.logb 2 (1 / μ)
  set js := jstar μ
  have hK : Real.sqrt (2 ^ js) ≤ Real.sqrt (2 / μ) :=
    Real.sqrt_le_sqrt (two_pow_jstar_le hμ hμ1)
  have hl2 := log_two_gt
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  set A := 21 * Real.sqrt (2 / μ) * (js + 2) * Real.log 2
  have hcost : ∀ j, j ≤ js → (cost j : ℝ) ≤ A := by
    intro j hj
    have hc := cost_bound j
    have e2 : Real.log (4 * 2 ^ j) = (2 + j) * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [e2] at hc
    have hs : Real.sqrt (2 ^ j) ≤ Real.sqrt (2 / μ) :=
      le_trans (Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) hj)) hK
    have hj' : (j : ℝ) ≤ js := by exact_mod_cast hj
    have hsq : 0 ≤ Real.sqrt (2 ^ j) := Real.sqrt_nonneg _
    have : Real.sqrt (2 ^ j) * ((2 + j) * Real.log 2) ≤ Real.sqrt (2 / μ) * ((js + 2) * Real.log 2) :=
      mul_le_mul hs (by nlinarith) (by positivity) (Real.sqrt_nonneg _)
    simp only [A]; nlinarith
  have hcap : ∀ j, j ≤ js → (cap d j : ℝ) ≤ d * js ^ 2 / 4 + 1 := by
    intro j hj
    unfold cap
    push_cast
    have h1 : ((d * j ^ 2 / 4 : ℕ) : ℝ) ≤ (d * j ^ 2 : ℕ) / 4 := Nat.cast_div_le
    have hj' : (j : ℝ) ≤ js := by exact_mod_cast hj
    push_cast at h1
    have : (d : ℝ) * j ^ 2 ≤ d * js ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      exact pow_le_pow_left₀ (Nat.cast_nonneg j) hj' 2
    linarith
  have hA : 0 ≤ A := by simp only [A]; positivity
  have hFC : (FCmax d μ : ℝ) ≤ (js + 1) * ((d * js ^ 2 / 4 + 1) * A) := by
    unfold FCmax
    push_cast
    calc ∑ j ∈ Finset.range (js + 1), (cap d j : ℝ) * cost j
        ≤ ∑ _j ∈ Finset.range (js + 1), (d * js ^ 2 / 4 + 1) * A := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' : j ≤ js := by have := Finset.mem_range.mp hj; omega
          exact mul_le_mul (hcap j hj') (hcost j hj') (Nat.cast_nonneg _) (by positivity)
      _ = (js + 1) * ((d * js ^ 2 / 4 + 1) * A) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hrate : rate μ ≤ 21 * Real.sqrt (2 / μ) := by unfold rate; linarith
  have hjs : (js : ℝ) + 2 ≤ ℓ := hℓ
  have hjs0 : (0 : ℝ) ≤ js := Nat.cast_nonneg _
  have hsq : 0 ≤ Real.sqrt (2 / μ) := Real.sqrt_nonneg _
  have hmain : (FCmax d μ : ℝ) + cost js ≤ 21 * Real.sqrt (2 / μ) * ((d + 1) * ℓ ^ 4) := by
    have h1 := hcost js le_rfl
    have h2 : (FCmax d μ : ℝ) + cost js ≤ (js + 2) * ((d * js ^ 2 / 4 + 1) * A) := by
      have : A ≤ (d * js ^ 2 / 4 + 1) * A := by
        have : (0 : ℝ) ≤ d * js ^ 2 / 4 := by positivity
        nlinarith
      nlinarith
    have h3 : (js + 2) * ((d * js ^ 2 / 4 + 1) * A) =
        21 * Real.sqrt (2 / μ) * ((js + 2) ^ 2 * ((d * js ^ 2 / 4 + 1) * Real.log 2)) := by
      simp only [A]; ring
    have h4 : (js + 2) ^ 2 * ((d * js ^ 2 / 4 + 1) * Real.log 2) ≤ (d + 1) * ℓ ^ 4 := by
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have e1 : (js + 2 : ℝ) ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ (by positivity) hjs 2
      have e2 : (js : ℝ) ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ hjs0 (by linarith) 2
      have e3 : (1 : ℝ) ≤ ℓ ^ 2 := by nlinarith
      have e4 : (d * js ^ 2 / 4 + 1) * Real.log 2 ≤ (d + 1) * ℓ ^ 2 := by
        have hp : (0 : ℝ) ≤ d * js ^ 2 / 4 + 1 := by positivity
        have f1 : (d * js ^ 2 / 4 + 1) * Real.log 2 ≤ d * js ^ 2 / 4 + 1 := by
          nlinarith [mul_le_mul_of_nonneg_left hl2'.le hp]
        have f2 : (d : ℝ) * js ^ 2 ≤ d * ℓ ^ 2 := mul_le_mul_of_nonneg_left e2 hd
        have f3 : (0 : ℝ) ≤ d * ℓ ^ 2 := by positivity
        nlinarith
      have e5 : 0 ≤ (d * js ^ 2 / 4 + 1) * Real.log 2 := by positivity
      calc (js + 2) ^ 2 * ((d * js ^ 2 / 4 + 1) * Real.log 2) ≤ ℓ ^ 2 * ((d + 1) * ℓ ^ 2) :=
            mul_le_mul e1 e4 e5 (by positivity)
        _ = (d + 1) * ℓ ^ 4 := by ring
    rw [h3] at h2
    calc (FCmax d μ : ℝ) + cost js ≤ _ := h2
      _ ≤ 21 * Real.sqrt (2 / μ) * ((d + 1) * ℓ ^ 4) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
  have hrl : rate μ * L ≤ 21 * Real.sqrt (2 / μ) * L := mul_le_mul_of_nonneg_right hrate hL
  nlinarith

section Main

variable {f : Vec d → ℝ} {w : Fin d → ℝ} {μ Δ ε : ℝ}

theorem accurate_after [NeZero d] (Hy : BHyp f w μ) (x0 : Vec d) {xstar : Vec d}
    (hmin : IsMinOn f Set.univ xstar) (hΔ : f x0 - f xstar ≤ Δ) (hε : 0 < ε)
    (T : ℕ) (hT : d + 1 + ⌈21 * Real.sqrt (2 / μ) * (Real.log (1 + Δ / (μ ^ 2 * ε)) +
      (d + 1) * (3 + Real.logb 2 (1 / μ)) ^ 4)⌉₊ ≤ T) :
    f ((stepOf f x0)^[T] (initial x0)).base - f xstar ≤ ε := by
  have hμ := Hy.μ_pos
  have hμ1 := Hy.μ_le
  obtain ⟨t, rfl⟩ : ∃ t, T = t + (d + 1) := ⟨T - (d + 1), by omega⟩
  rw [Function.iterate_add_apply, start_iterate]
  obtain ⟨n, hle, hlt, hbase⟩ := base_at f x0 t
  rw [hbase]
  have I := inv_all (x0 := x0) Hy n
  by_cases hacc : Gam f x0 (ms f x0 n).base ≤ 2 * μ * ε
  · have := acc_of_gam Hy x0 xstar (ms f x0 n).base
    have : Gam f x0 (ms f x0 n).base / (2 * μ) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  · exfalso
    push Not at hacc
    have hΔ0 : 0 ≤ Δ := by
      have := hmin (Set.mem_univ x0); simp only [Set.mem_ofPred_eq] at this; linarith
    have hg0 := gam0_le Hy x0 hmin
    have h2με : 0 < 2 * μ * ε := by positivity
    have hgpos : 0 < Gam f x0 (ms f x0 n).base := by linarith
    have hr : 0 < rate μ := by unfold rate; positivity
    set L := Real.log (1 + Δ / (μ ^ 2 * ε))
    have hΔq : 0 ≤ Δ / (μ ^ 2 * ε) := by positivity
    have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
    have hexp : Real.exp (((bt f x0 n : ℝ) - FCh f x0 n) / rate μ) < 1 + Δ / (μ ^ 2 * ε) := by
      have hp := I.prog
      have h1 : Real.exp (((bt f x0 n : ℝ) - FCh f x0 n) / rate μ) ≤
          Gam f x0 x0 / Gam f x0 (ms f x0 n).base := by
        rw [le_div_iff₀ hgpos]; linarith
      have h2 : Gam f x0 x0 / Gam f x0 (ms f x0 n).base < Gam f x0 x0 / (2 * μ * ε) + 1 := by
        rcases (show (0 : ℝ) ≤ Gam f x0 x0 from isq_nonneg (sec_pos Hy x0) _).lt_or_eq with
          hpos | hzero
        · have := div_lt_div_of_pos_left hpos (by positivity) hacc
          linarith [div_nonneg hpos.le (by positivity : (0:ℝ) ≤ 2 * μ * ε)]
        · have : Gam f x0 x0 = 0 := hzero.symm
          rw [this, zero_div, zero_div]; norm_num
      have h3 : Gam f x0 x0 / (2 * μ * ε) ≤ Δ / (μ ^ 2 * ε) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_right hg0 (by positivity : (0:ℝ) ≤ μ ^ 2 * ε)
        have e : 2 * (f x0 - f xstar) / μ * (μ ^ 2 * ε) = (f x0 - f xstar) * (2 * μ * ε) := by
          field_simp
        nlinarith [mul_le_mul_of_nonneg_right hΔ (by positivity : (0:ℝ) ≤ 2 * μ * ε)]
      linarith
    have hlog : ((bt f x0 n : ℝ) - FCh f x0 n) / rate μ < L := by
      rw [← Real.exp_lt_exp, Real.exp_log (by positivity)]; exact hexp
    have hbt : (bt f x0 n : ℝ) < FCh f x0 n + rate μ * L := by
      rw [div_lt_iff₀ hr] at hlog; linarith
    have hfch : (FCh f x0 n : ℝ) ≤ FCmax d μ := by exact_mod_cast fch_le_max I
    have hcostn : (cost (ms f x0 n).lvl : ℝ) ≤ cost (jstar μ) := by
      exact_mod_cast cost_mono I.lvl_le
    have hnext : (bt f x0 (n + 1) : ℝ) = bt f x0 n + cost (ms f x0 n).lvl := by
      simp only [bt]; push_cast; ring
    have hcore := budget_core (d := d) hμ hμ1 hL0
    have hceil : 21 * Real.sqrt (2 / μ) * (L + (d + 1) * (3 + Real.logb 2 (1 / μ)) ^ 4) ≤
        (t : ℝ) := by
      have := Nat.le_ceil (21 * Real.sqrt (2 / μ) * (L + (d + 1) * (3 + Real.logb 2 (1 / μ)) ^ 4))
      have h2 : (⌈21 * Real.sqrt (2 / μ) * (L + (d + 1) * (3 + Real.logb 2 (1 / μ)) ^ 4)⌉₊ : ℝ)
          ≤ t := by exact_mod_cast (by omega : ⌈21 * Real.sqrt (2 / μ) *
            (L + (d + 1) * (3 + Real.logb 2 (1 / μ)) ^ 4)⌉₊ ≤ t)
      linarith
    have htlt : (t : ℝ) < bt f x0 (n + 1) := by exact_mod_cast hlt
    linarith

end Main

end OracleTemplate.BlackBoxDiagonal

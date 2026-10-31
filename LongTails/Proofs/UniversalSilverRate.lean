import LongTails.Proofs.UniversalSilverConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.UniversalSilverRate

open OracleTemplate LongTails.Algorithms.SilverSchedule LongTails.Algorithms.UniversalSilver
open LongTails.Proofs.SilverCertificate LongTails.Proofs.SilverTrace
open LongTails.Proofs.SilverNonexpansive LongTails.Proofs.UniversalSilverSchedule
open LongTails.Proofs.UniversalSilverConvergence
open LongTails.Setups.SmoothConvexQuadraticGrowth

noncomputable def order (p : Params) : ℕ := ⌈Real.logb ratio (1 + 2 * p.L / p.μ)⌉₊

noncomputable def halvings (p : Params) : ℕ := ⌈Real.logb 2 (1 + p.L * p.R ^ 2 / p.ε)⌉₊

noncomputable def depth (p : Params) : ℕ := order p - 1 + Nat.clog 2 (halvings p)

lemma ratio_one_lt : 1 < ratio := by linarith [ratio_gt_two]

lemma order_pos (p : Params) (hp : spec.valid p) : 1 ≤ order p := by
  obtain ⟨hL, hμ, _, _⟩ := hp
  have hx : 1 < 1 + 2 * p.L / p.μ := by
    have : 0 < 2 * p.L / p.μ := by positivity
    linarith
  have hl : 0 < Real.logb ratio (1 + 2 * p.L / p.μ) := Real.logb_pos ratio_one_lt hx
  exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr hl))

lemma order_power (p : Params) (hp : spec.valid p) :
    1 + 2 * p.L / p.μ ≤ ratio ^ order p := by
  obtain ⟨hL, hμ, _, _⟩ := hp
  have hx : 0 < 1 + 2 * p.L / p.μ := by positivity
  have h1 : ratio ^ Real.logb ratio (1 + 2 * p.L / p.μ) = 1 + 2 * p.L / p.μ :=
    Real.rpow_logb ratio_pos (ne_of_gt ratio_one_lt) hx
  have h2 : ratio ^ Real.logb ratio (1 + 2 * p.L / p.μ) ≤ ratio ^ ((order p : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ratio_one_lt.le (Nat.le_ceil _)
  rw [Real.rpow_natCast] at h2
  linarith

lemma steps_condition (p : Params) (hp : spec.valid p) (o : ℕ) (ho : order p ≤ o) :
    1 ≤ (steps o).sum * (p.μ / (2 * p.L)) := by
  have hpow := order_power p hp
  obtain ⟨hL, hμ, _, _⟩ := hp
  have hmono : ratio ^ order p ≤ ratio ^ o := pow_le_pow_right₀ ratio_one_lt.le ho
  rw [steps_sum]
  have h : 2 * p.L / p.μ ≤ ratio ^ o - 1 := by linarith
  have h' := mul_le_mul_of_nonneg_right h (show 0 ≤ p.μ / (2 * p.L) by positivity)
  have he : 2 * p.L / p.μ * (p.μ / (2 * p.L)) = 1 := by field_simp
  linarith

lemma halvings_bound (p : Params) (hp : spec.valid p) :
    p.L / 2 * p.R ^ 2 * (1 / 2) ^ halvings p ≤ p.ε := by
  obtain ⟨hL, hμ, hR, hε⟩ := hp
  set X := 1 + p.L * p.R ^ 2 / p.ε
  have hX : 1 ≤ X := by
    have : 0 ≤ p.L * p.R ^ 2 / p.ε := by positivity
    simp only [X]; linarith
  have h1 : (2 : ℝ) ^ Real.logb 2 X = X := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ Real.logb 2 X ≤ (2 : ℝ) ^ ((halvings p : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  rw [Real.rpow_natCast, h1] at h2
  have hpos : (0 : ℝ) < 2 ^ halvings p := by positivity
  have hhalf : (1 / 2 : ℝ) ^ halvings p = 1 / 2 ^ halvings p := by rw [one_div_pow]
  rw [hhalf]
  have hLR : 0 ≤ p.L * p.R ^ 2 := by positivity
  have hXe : X * p.ε = p.ε + p.L * p.R ^ 2 := by simp only [X]; field_simp
  rw [mul_one_div, div_le_iff₀ hpos]
  nlinarith

lemma clog_pow_le (n : ℕ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (hn : (n : ℝ) ≤ ℓ + 1) :
    ((2 ^ Nat.clog 2 n : ℕ) : ℝ) ≤ 2 * (ℓ + 1) ∧
      (Nat.clog 2 n : ℝ) ≤ Real.logb 2 (ℓ + 1) + 1 := by
  have hlog0 : 0 ≤ Real.logb 2 (ℓ + 1) := Real.logb_nonneg (by norm_num) (by linarith)
  rcases le_or_gt n 1 with h | h
  · have hc : Nat.clog 2 n = 0 := Nat.clog_of_right_le_one h 2
    rw [hc]
    simp
    constructor <;> linarith
  · have hc1 : 1 ≤ Nat.clog 2 n := Nat.one_le_iff_ne_zero.mpr
      (ne_of_gt (Nat.clog_pos (by norm_num) h))
    have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have hlt' : ((2 ^ (Nat.clog 2 n - 1) : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hlt
    have hsplit : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n - 1) := by
      rw [← pow_succ']; congr 1; omega
    constructor
    · rw [hsplit]; push_cast at hlt' ⊢; linarith
    · have hpos : (0 : ℝ) < 2 ^ (Nat.clog 2 n - 1) := by positivity
      have hl : Real.logb 2 ((2 : ℝ) ^ (Nat.clog 2 n - 1)) < Real.logb 2 (ℓ + 1) := by
        apply Real.logb_lt_logb (by norm_num) hpos
        push_cast at hlt'; linarith
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hl
      have hcast : ((Nat.clog 2 n - 1 : ℕ) : ℝ) = (Nat.clog 2 n : ℝ) - 1 := by
        rw [Nat.cast_sub hc1]; simp
      rw [hcast] at hl
      linarith

lemma budget_ge (p : Params) (hp : spec.valid p) :
    (depth p + 1) * 2 ^ depth p ≤
      ⌈2 * (1 + 2 * p.L / p.μ) ^ (Real.log 2 / Real.log (1 + Real.sqrt 2)) *
        (Real.logb 2 (1 + p.L * p.R ^ 2 / p.ε) + 1) *
        (Real.logb 2 (1 + 2 * p.L / p.μ) + Real.logb 2 (Real.logb 2 (1 + p.L * p.R ^ 2 / p.ε) + 1) + 3)⌉₊ := by
  have hm1 := order_pos p hp
  obtain ⟨hL, hμ, hR, hε⟩ := hp
  set X := 1 + 2 * p.L / p.μ with hXdef
  set ℓ := Real.logb 2 (1 + p.L * p.R ^ 2 / p.ε) with hℓdef
  have hX : 1 < X := by have : 0 < 2 * p.L / p.μ := by positivity
                        simp only [hXdef]; linarith
  have hY : 1 ≤ 1 + p.L * p.R ^ 2 / p.ε := by
    have : 0 ≤ p.L * p.R ^ 2 / p.ε := by positivity
    linarith
  have hℓ : 0 ≤ ℓ := Real.logb_nonneg (by norm_num) hY
  have hrat : ratio = 1 + Real.sqrt 2 := rfl
  have hlogr : Real.log 2 ≤ Real.log ratio :=
    Real.log_le_log (by norm_num) ratio_gt_two.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX.le
  have hb : Real.logb ratio X ≤ Real.logb 2 X := by
    unfold Real.logb
    exact div_le_div_of_nonneg_left hlogX hlog2 hlogr
  have hb0 : 0 ≤ Real.logb ratio X := Real.logb_nonneg ratio_one_lt hX.le
  have hord : (order p : ℝ) < Real.logb ratio X + 1 := Nat.ceil_lt_add_one hb0
  have hK0 : (halvings p : ℝ) ≤ ℓ + 1 := (Nat.ceil_lt_add_one hℓ).le
  obtain ⟨hcp, hcl⟩ := clog_pow_le (halvings p) ℓ hℓ hK0
  have hpow : ((2 ^ (order p - 1) : ℕ) : ℝ) ≤ X ^ (Real.log 2 / Real.log (1 + Real.sqrt 2)) := by
    have he : ((order p - 1 : ℕ) : ℝ) ≤ Real.logb ratio X := by
      rw [Nat.cast_sub hm1]; simp; linarith
    have h2 : (2 : ℝ) ^ (((order p - 1 : ℕ)) : ℝ) ≤ (2 : ℝ) ^ Real.logb ratio X :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    rw [Real.rpow_natCast] at h2
    have h3 : (2 : ℝ) ^ Real.logb ratio X = X ^ (Real.log 2 / Real.log (1 + Real.sqrt 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by linarith), ← hrat]
      unfold Real.logb; congr 1; ring
    push_cast; linarith
  have hdepth : depth p + 1 = order p + Nat.clog 2 (halvings p) := by unfold depth; omega
  have hpow2 : 2 ^ depth p = 2 ^ (order p - 1) * 2 ^ Nat.clog 2 (halvings p) := by
    unfold depth; rw [pow_add]
  have hfac1 : ((depth p + 1 : ℕ) : ℝ) ≤ Real.logb 2 X + Real.logb 2 (ℓ + 1) + 3 := by
    rw [hdepth]; push_cast; linarith
  have hfac2 : ((2 ^ depth p : ℕ) : ℝ) ≤ X ^ (Real.log 2 / Real.log (1 + Real.sqrt 2)) * (2 * (ℓ + 1)) := by
    rw [hpow2]; push_cast
    push_cast at hpow hcp
    exact mul_le_mul hpow hcp (by positivity) (by positivity)
  have hprod : (((depth p + 1) * 2 ^ depth p : ℕ) : ℝ) ≤
      2 * X ^ (Real.log 2 / Real.log (1 + Real.sqrt 2)) * (ℓ + 1) *
        (Real.logb 2 X + Real.logb 2 (ℓ + 1) + 3) := by
    push_cast
    push_cast at hfac1 hfac2
    have h0 : (0 : ℝ) ≤ (depth p : ℝ) + 1 := by positivity
    calc ((depth p : ℝ) + 1) * 2 ^ depth p ≤ (Real.logb 2 X + Real.logb 2 (ℓ + 1) + 3) *
          (X ^ (Real.log 2 / Real.log (1 + Real.sqrt 2)) * (2 * (ℓ + 1))) :=
          mul_le_mul hfac1 hfac2 (by positivity) (by linarith)
      _ = _ := by ring
  exact Nat.cast_le.mp (hprod.trans (Nat.le_ceil _))

theorem accuracy (p : Params) (hp : spec.valid p) {f : p.E → ℝ} {G : p.E → p.E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ p.L * ‖x - y‖)
    {xstar : p.E} (hmin : IsMinOn f univ xstar) (hR : ‖p.x0 - xstar‖ ≤ p.R)
    (hqg : ∀ x, ∃ z, IsMinOn f univ z ∧ p.μ / 2 * ‖x - z‖ ^ 2 ≤ f x - f z)
    (K : ℕ) (hK : (depth p + 1) * 2 ^ depth p ≤ K) :
    f (run (fun x => (1 / p.L) • G x) ((blocks K).take K) p.x0) - f xstar ≤ p.ε := by
  have hv := hp
  obtain ⟨hL, hμ, hR0, hε⟩ := hv
  set g : p.E → p.E := fun x => (1 / p.L) • G x
  have hdef := scaled_defect hL hc hg hlip
  have hG0 : ∀ z, IsMinOn f univ z → G z = 0 :=
    fun z hz => OracleTemplate.CyclicInterpolation.gradient_min_zero hL hg hlip hz
  have hZ : ∀ z, IsMinOn f univ z → g z = 0 ∧ f z / p.L = f xstar / p.L := by
    intro z hz
    refine ⟨by simp [g, hG0 z hz], ?_⟩
    have h1 := hz (mem_univ xstar)
    have h2 := hmin (mem_univ z)
    simp only [Set.mem_ofPred_eq] at h1 h2
    rw [le_antisymm h1 h2]
  have hcpos : 0 < p.μ / (2 * p.L) := by positivity
  have hqg' : ∀ y, ∃ z, IsMinOn f univ z ∧
      p.μ / (2 * p.L) * ‖y - z‖ ^ 2 ≤ f y / p.L - f xstar / p.L := by
    intro y
    obtain ⟨z, hz, hq⟩ := hqg y
    refine ⟨z, hz, ?_⟩
    have hfz : f z = f xstar := by
      have h1 := hz (mem_univ xstar)
      have h2 := hmin (mem_univ z)
      simp only [Set.mem_ofPred_eq] at h1 h2
      exact le_antisymm h1 h2
    rw [hfz] at hq
    have he : p.μ / (2 * p.L) * ‖y - z‖ ^ 2 = (p.μ / 2 * ‖y - z‖ ^ 2) / p.L := by
      field_simp
    rw [he, ← sub_div]
    exact div_le_div_of_nonneg_right hq hL.le
  have hm1 := order_pos p hp
  have hA : depth p ≤ K := by
    have : depth p < 2 ^ depth p := Nat.lt_two_pow_self
    nlinarith
  obtain ⟨t, ht⟩ := ruler_prefix hA
  have hW : blocks K = blocks (depth p) ++ t.flatMap steps := by
    unfold blocks; rw [← ht, List.flatMap_append]
  have hlen : (blocks (depth p)).length ≤ K := by rw [blocks_length]; exact hK
  have htake : (blocks K).take K =
      blocks (depth p) ++ (t.flatMap steps).take (K - (blocks (depth p)).length) := by
    rw [hW, List.take_append, List.take_of_length_le hlen]
  rw [htake, run_append]
  set y := run g (blocks (depth p)) p.x0
  obtain ⟨z₁, hz₁, hdecay⟩ := blocks_decay (fun x => f x / p.L) g hdef
    (fun z => IsMinOn f univ z) (f xstar / p.L) (p.μ / (2 * p.L)) hcpos hZ hqg'
    (order p) (steps_condition p hp) (ruler (depth p)) p.x0 xstar hmin
  have hcount : halvings p ≤ (ruler (depth p)).countP (fun o => decide (order p ≤ o)) := by
    have hc := ruler_count (order p) (depth p) hm1 (by unfold depth; omega)
    have he : depth p + 1 - order p = Nat.clog 2 (halvings p) := by unfold depth; omega
    rw [he] at hc
    exact (Nat.le_pow_clog (by norm_num) _).trans hc
  set u := run g ((t.flatMap steps).take (K - (blocks (depth p)).length)) y
  have hu : ‖u - z₁‖ ≤ ‖y - z₁‖ :=
    blocks_nonexpansive (fun x => f x / p.L) g hdef z₁ (hZ z₁ hz₁).1 t y u
      (run_take_mem_nodes g _ y _)
  have hfz : f z₁ = f xstar := by
    have h1 := hz₁ (mem_univ xstar)
    have h2 := hmin (mem_univ z₁)
    simp only [Set.mem_ofPred_eq] at h1 h2
    exact le_antisymm h1 h2
  have hup := OracleTemplate.Gradient.smooth_upper_bound hg hlip z₁ u
  rw [hG0 z₁ hz₁, inner_zero_left, add_zero] at hup
  have hy2 : ‖y - z₁‖ ^ 2 ≤ p.R ^ 2 * (1 / 2) ^ halvings p := by
    have hRsq := pow_le_pow_left₀ (norm_nonneg _) hR 2
    have hp1 : (1 / 2 : ℝ) ^ ((ruler (depth p)).countP (fun o => decide (order p ≤ o))) ≤
        (1 / 2) ^ halvings p := pow_le_pow_of_le_one (by norm_num) (by norm_num) hcount
    calc ‖y - z₁‖ ^ 2 ≤ ‖p.x0 - xstar‖ ^ 2 * (1 / 2) ^
          ((ruler (depth p)).countP (fun o => decide (order p ≤ o))) := by
            simpa [y, blocks] using hdecay
      _ ≤ p.R ^ 2 * (1 / 2) ^ halvings p :=
          mul_le_mul hRsq hp1 (by positivity) (by positivity)
  have hu2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
  have hfin := halvings_bound p hp
  calc f u - f xstar = f u - f z₁ := by rw [hfz]
    _ ≤ p.L / 2 * ‖u - z₁‖ ^ 2 := by linarith
    _ ≤ p.L / 2 * (p.R ^ 2 * (1 / 2) ^ halvings p) := by
        apply mul_le_mul_of_nonneg_left (hu2.trans hy2) (by positivity)
    _ = p.L / 2 * p.R ^ 2 * (1 / 2) ^ halvings p := by ring
    _ ≤ p.ε := hfin

end LongTails.Proofs.UniversalSilverRate

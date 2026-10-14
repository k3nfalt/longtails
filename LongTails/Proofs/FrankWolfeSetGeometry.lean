import LongTails.Setups.UniformlyConvexHolder
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace OracleTemplate.FrankWolfe

open LongTails.Setups.UniformlyConvexHolder

lemma sum_power_upper {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    (a + b) ^ p ≤ (2 : ℝ) ^ (p - 1) * (a ^ p + b ^ p) := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow a b hp

lemma square_rpow (x p : ℝ) : (x ^ 2) ^ (p / 2) = |x| ^ p := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
  congr 1
  ring

lemma scalar_clarkson {q : ℝ} (hq : 2 ≤ q) (a b : ℝ) :
    |a + b| ^ q + |a - b| ^ q ≤ (2 : ℝ) ^ (q - 1) * (|a| ^ q + |b| ^ q) := by
  have hp : 1 ≤ q / 2 := by linarith
  have h₁ := Real.add_rpow_le_rpow_add (sq_nonneg (a + b)) (sq_nonneg (a - b)) hp
  have h₂ := sum_power_upper (sq_nonneg a) (sq_nonneg b) hp
  rw [square_rpow, square_rpow, show (a + b) ^ 2 + (a - b) ^ 2 =
    2 * (a ^ 2 + b ^ 2) by ring, Real.mul_rpow (by norm_num) (by positivity)] at h₁
  rw [square_rpow, square_rpow] at h₂
  have h := h₁.trans (mul_le_mul_of_nonneg_left h₂ (by positivity))
  rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    show q / 2 + (q / 2 - 1) = q - 1 by ring] at h
  exact h

lemma scalar_midpoint_deficit {q : ℝ} (hq : 2 ≤ q) (a b : ℝ) :
    |(a + b) / 2| ^ q + |(a - b) / 2| ^ q ≤ (|a| ^ q + |b| ^ q) / 2 := by
  have h := scalar_clarkson hq a b
  have htwo : 0 < (2 : ℝ) ^ q := by positivity
  rw [abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.div_rpow (abs_nonneg _) (by norm_num),
    Real.div_rpow (abs_nonneg _) (by norm_num), ← add_div]
  apply (div_le_iff₀ htwo).mpr
  have heq : (2 : ℝ) ^ (q - 1) = 2 ^ q / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
  rw [heq] at h
  nlinarith

noncomputable def twoGauge (q : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  ‖WithLp.toLp (ENNReal.ofReal q) x‖

lemma twoGauge_formula {q : ℝ} (hq : 0 < q) (x : Fin 2 → ℝ) :
    twoGauge q x = (|x 0| ^ q + |x 1| ^ q) ^ (1 / q) := by
  rw [twoGauge, PiLp.norm_eq_sum (by simpa [ENNReal.toReal_ofReal hq.le] using hq)]
  simp [Fin.sum_univ_two, ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs]

lemma twoGauge_power {q : ℝ} (hq : 0 < q) (x : Fin 2 → ℝ) :
    twoGauge q x ^ q = |x 0| ^ q + |x 1| ^ q := by
  rw [twoGauge_formula hq, ← Real.rpow_mul (by positivity),
    one_div_mul_cancel hq.ne', Real.rpow_one]

lemma twoGauge_nonneg {q : ℝ} (hq : 0 < q) (x : Fin 2 → ℝ) : 0 ≤ twoGauge q x := by
  rw [twoGauge_formula hq]
  positivity

lemma twoGauge_add {q : ℝ} (hq : 1 ≤ q) (x y : Fin 2 → ℝ) :
    twoGauge q (x + y) ≤ twoGauge q x + twoGauge q y := by
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq⟩
  exact norm_add_le (WithLp.toLp (ENNReal.ofReal q) x) (WithLp.toLp (ENNReal.ofReal q) y)

lemma twoGauge_smul {q : ℝ} (hq : 1 ≤ q) (t : ℝ) (x : Fin 2 → ℝ) :
    twoGauge q (t • x) = |t| * twoGauge q x := by
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq⟩
  exact norm_smul t (WithLp.toLp (ENNReal.ofReal q) x)

lemma twoGauge_continuous {q : ℝ} (hq : 1 ≤ q) : Continuous (twoGauge q) := by
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq⟩
  exact continuous_norm.comp (PiLp.continuous_toLp (ENNReal.ofReal q) (fun _ : Fin 2 => ℝ))

lemma twoGauge_clarkson {q : ℝ} (hq : 2 ≤ q) (x y : Fin 2 → ℝ) :
    twoGauge q ((1 / 2 : ℝ) • (x + y)) ^ q +
      twoGauge q ((1 / 2 : ℝ) • (x - y)) ^ q ≤
        (twoGauge q x ^ q + twoGauge q y ^ q) / 2 := by
  have hqpos : 0 < q := by linarith
  have h0 := scalar_midpoint_deficit hq (x 0) (y 0)
  have h1 := scalar_midpoint_deficit hq (x 1) (y 1)
  simp only [twoGauge_power hqpos, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  have heq : ∀ t : ℝ, 1 / 2 * t = t / 2 := by intro t; ring
  simp only [heq]
  linarith

lemma twoGauge_midpoint {q : ℝ} (hq : 2 ≤ q) {x y : Fin 2 → ℝ}
    (hx : twoGauge q x ≤ 1) (hy : twoGauge q y ≤ 1) :
    twoGauge q ((1 / 2 : ℝ) • (x + y)) ≤
      1 - twoGauge q (x - y) ^ q / (q * 2 ^ q) := by
  have hqpos : 0 < q := by linarith
  have hqone : 1 ≤ q := by linarith
  have htwo : 0 < (2 : ℝ) ^ q := by positivity
  have hxp : twoGauge q x ^ q ≤ 1 := by
    simpa using Real.rpow_le_rpow (twoGauge_nonneg hqpos x) hx hqpos.le
  have hyp : twoGauge q y ^ q ≤ 1 := by
    simpa using Real.rpow_le_rpow (twoGauge_nonneg hqpos y) hy hqpos.le
  have hc := twoGauge_clarkson hq x y
  have hs : twoGauge q ((1 / 2 : ℝ) • (x - y)) ^ q = twoGauge q (x - y) ^ q / 2 ^ q := by
    rw [twoGauge_smul hqone, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      Real.mul_rpow (by norm_num) (twoGauge_nonneg hqpos _),
      Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]
    ring
  rw [hs] at hc
  have hm := one_add_mul_self_le_rpow_one_add
    (s := twoGauge q ((1 / 2 : ℝ) • (x + y)) - 1)
    (by linarith [twoGauge_nonneg hqpos ((1 / 2 : ℝ) • (x + y))]) hqone
  simp only [add_sub_cancel] at hm
  have hh : q * (1 - twoGauge q ((1 / 2 : ℝ) • (x + y))) ≥
      twoGauge q (x - y) ^ q / 2 ^ q := by linarith
  apply (le_sub_iff_add_le).mpr
  have hd : twoGauge q (x - y) ^ q / (q * 2 ^ q) ≤
      1 - twoGauge q ((1 / 2 : ℝ) • (x + y)) := by
    rw [mul_comm q, ← div_div]
    exact (div_le_iff₀ hqpos).mpr (by nlinarith)
  linarith

lemma twoGauge_neg {q : ℝ} (hq : 1 ≤ q) (x : Fin 2 → ℝ) :
    twoGauge q (-x) = twoGauge q x := by
  have h := twoGauge_smul hq (-1) x
  simpa using h

lemma twoGauge_deficit_left {q t : ℝ} (hq : 2 ≤ q) {x y : Fin 2 → ℝ}
    (hx : twoGauge q x ≤ 1) (hy : twoGauge q y ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    twoGauge q (t • x + (1 - t) • y) ≤
      1 - 2 / (q * 2 ^ q) * t * (1 - t) * twoGauge q (x - y) ^ q := by
  have hqpos : 0 < q := by linarith
  have hqone : 1 ≤ q := by linarith
  have hm := twoGauge_midpoint hq hx hy
  have heq : t • x + (1 - t) • y =
      (2 * t) • ((1 / 2 : ℝ) • (x + y)) + (1 - 2 * t) • y := by module
  rw [heq]
  have hs := twoGauge_add hqone ((2 * t) • ((1 / 2 : ℝ) • (x + y))) ((1 - 2 * t) • y)
  rw [twoGauge_smul hqone (2 * t) ((1 / 2 : ℝ) • (x + y)),
    twoGauge_smul hqone (1 - 2 * t) y, abs_of_nonneg (by linarith : 0 ≤ 2 * t), abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * t)] at hs
  have h1 := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ 2 * t)
  have h2 := mul_le_mul_of_nonneg_left hy (by linarith : 0 ≤ 1 - 2 * t)
  have hnonneg : 0 ≤ twoGauge q (x - y) ^ q / (q * 2 ^ q) :=
    div_nonneg (Real.rpow_nonneg (twoGauge_nonneg hqpos _) _) (by positivity)
  have he : 2 / (q * 2 ^ q) * t * (1 - t) * twoGauge q (x - y) ^ q =
      2 * t * (1 - t) * (twoGauge q (x - y) ^ q / (q * 2 ^ q)) := by ring
  rw [he]
  nlinarith [mul_nonneg (sq_nonneg t) hnonneg]

lemma twoGauge_deficit {q t : ℝ} (hq : 2 ≤ q) {x y : Fin 2 → ℝ}
    (hx : twoGauge q x ≤ 1) (hy : twoGauge q y ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    twoGauge q (t • x + (1 - t) • y) ≤
      1 - 2 / (q * 2 ^ q) * t * (1 - t) * twoGauge q (x - y) ^ q := by
  by_cases hh : t ≤ 1 / 2
  · exact twoGauge_deficit_left hq hx hy ht hh
  have h := twoGauge_deficit_left hq hy hx (t := 1 - t) (by linarith) (by linarith)
  have he : (1 - t) • y + (1 - (1 - t)) • x = t • x + (1 - t) • y := by module
  rw [he, show y - x = -(x - y) by module, twoGauge_neg (by linarith : 1 ≤ q)] at h
  convert h using 1
  ring

lemma twoGauge_euclidean_bounds {q : ℝ} (hq : 2 ≤ q) (x : EuclideanSpace ℝ (Fin 2)) :
    twoGauge q x ≤ ‖x‖ ∧ ‖x‖ ^ q ≤ 2 ^ (q / 2 - 1) * twoGauge q x ^ q := by
  have hqpos : 0 < q := by linarith
  have hp : 1 ≤ q / 2 := by linarith
  have hn : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have hnorm : (x 0 ^ 2 + x 1 ^ 2) ^ (q / 2) = ‖x‖ ^ q := by
    rw [← hn, square_rpow, abs_of_nonneg (norm_nonneg x)]
  have hlo := Real.add_rpow_le_rpow_add (sq_nonneg (x 0)) (sq_nonneg (x 1)) hp
  have hhi := sum_power_upper (sq_nonneg (x 0)) (sq_nonneg (x 1)) hp
  rw [square_rpow, square_rpow, hnorm, ← twoGauge_power hqpos] at hlo hhi
  exact ⟨(Real.rpow_le_rpow_iff (twoGauge_nonneg hqpos x) (norm_nonneg x) hqpos).mp hlo, hhi⟩

noncomputable def twoBall (q : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | twoGauge q x ≤ 1}

noncomputable def twoBallModulus (q : ℝ) : ℝ := 2 / (q * 2 ^ q * 2 ^ (q / 2 - 1))

lemma twoBallModulus_pos {q : ℝ} (hq : 2 ≤ q) : 0 < twoBallModulus q := by
  have hqpos : 0 < q := by linarith
  unfold twoBallModulus
  positivity

lemma twoBall_uniformly_convex {q : ℝ} (hq : 2 ≤ q) :
    UniformlyConvexSet (twoBall q) (twoBallModulus q) q := by
  intro x hx y hy t ht w hw
  have hqpos : 0 < q := by linarith
  have hqone : 1 ≤ q := by linarith
  have hx' : twoGauge q x ≤ 1 := hx
  have hy' : twoGauge q y ≤ 1 := hy
  have hg := twoGauge_deficit hq hx' hy' ht.1 ht.2
  have hnorm := (twoGauge_euclidean_bounds hq (x - y)).2
  have hwg := (twoGauge_euclidean_bounds hq w).1.trans hw
  let a := twoBallModulus q
  let ρ := a * t * (1 - t) * ‖x - y‖ ^ q
  have ha : 0 < a := twoBallModulus_pos hq
  have hcoef : 0 ≤ a * t * (1 - t) :=
    mul_nonneg (mul_nonneg ha.le ht.1) (sub_nonneg.mpr ht.2)
  have hρ : 0 ≤ ρ := mul_nonneg hcoef (Real.rpow_nonneg (norm_nonneg _) _)
  have hρupper : ρ ≤ 2 / (q * 2 ^ q) * t * (1 - t) * twoGauge q (x - y) ^ q := by
    calc
      ρ ≤ (a * t * (1 - t)) * (2 ^ (q / 2 - 1) * twoGauge q (x - y) ^ q) :=
        mul_le_mul_of_nonneg_left hnorm hcoef
      _ = _ := by
        dsimp [a, twoBallModulus]
        field_simp
  have hsum := twoGauge_add hqone (t • (x : Fin 2 → ℝ) + (1 - t) • (y : Fin 2 → ℝ))
    (ρ • (w : Fin 2 → ℝ))
  rw [twoGauge_smul hqone ρ, abs_of_nonneg hρ] at hsum
  have hpert := mul_le_mul_of_nonneg_left hwg hρ
  change twoGauge q (t • (x : Fin 2 → ℝ) + (1 - t) • (y : Fin 2 → ℝ) +
    ρ • (w : Fin 2 → ℝ)) ≤ 1
  change ρ ≤ 2 / (q * 2 ^ q) * t * (1 - t) *
    twoGauge q ((x : Fin 2 → ℝ) - (y : Fin 2 → ℝ)) ^ q at hρupper
  linarith

lemma mem_twoBall_iff {q : ℝ} (hq : 0 < q) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ twoBall q ↔ |x 0| ^ q + |x 1| ^ q ≤ 1 := by
  change twoGauge q x ≤ 1 ↔ _
  rw [← twoGauge_power hq x]
  simpa only [Real.one_rpow] using
    (Real.rpow_le_rpow_iff (twoGauge_nonneg hq x) zero_le_one hq).symm

lemma twoBall_coordinates {q : ℝ} (hq : 0 < q) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ twoBall q) : |x 0| ≤ 1 ∧ |x 1| ≤ 1 := by
  have h := (mem_twoBall_iff hq x).mp hx
  have h0 := Real.rpow_nonneg (abs_nonneg (x 0)) q
  have h1 := Real.rpow_nonneg (abs_nonneg (x 1)) q
  constructor
  · apply (Real.rpow_le_rpow_iff (abs_nonneg (x 0)) zero_le_one hq).mp
    rw [Real.one_rpow]
    linarith
  · apply (Real.rpow_le_rpow_iff (abs_nonneg (x 1)) zero_le_one hq).mp
    rw [Real.one_rpow]
    linarith

lemma twoBall_norm_le_two {q : ℝ} (hq : 0 < q) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ twoBall q) : ‖x‖ ≤ 2 := by
  have hc := twoBall_coordinates hq hx
  have h0 : x 0 ^ 2 ≤ 1 := by
    simpa [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg (x 0)) hc.1
  have h1 : x 1 ^ 2 ≤ 1 := by
    simpa [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg (x 1)) hc.2
  have hn : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  nlinarith [norm_nonneg x]

lemma twoBall_compact {q : ℝ} (hq : 2 ≤ q) : IsCompact (twoBall q) := by
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin 2) => twoGauge q x) :=
    (twoGauge_continuous (by linarith : 1 ≤ q)).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))
  have hclosed : IsClosed (twoBall q) := isClosed_le hcont continuous_const
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2).of_isClosed_subset hclosed
  intro x hx
  simpa [Metric.mem_closedBall, dist_zero_right] using twoBall_norm_le_two (by linarith) hx

lemma twoBall_diameter {q : ℝ} (hq : 0 < q) {x y : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ twoBall q) (hy : y ∈ twoBall q) : ‖x - y‖ ≤ 4 := by
  have hn := norm_sub_le x y
  linarith [twoBall_norm_le_two hq hx, twoBall_norm_le_two hq hy]

end OracleTemplate.FrankWolfe

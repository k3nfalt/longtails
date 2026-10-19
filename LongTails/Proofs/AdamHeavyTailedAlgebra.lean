import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LongTails.Proofs.AdamHeavyTailedAlgebra

lemma abs_signal_le_twice_observation {μ e : ℝ} (he : |e| ≤ |μ| / 2) :
    |μ| ≤ 2 * |μ + e| := by
  have h := abs_add_le (μ + e) (-e)
  simp only [add_neg_cancel_right, abs_neg] at h
  linarith

lemma inverse_square_le {μ τ H d : ℝ} (hτ : 0 < τ) (hH : 0 < H)
    (hd : 0 < d) (hτd : τ ≤ d) (hHd : H ≤ 3 * d) :
    μ ^ 2 / d ^ 2 ≤ 3 * μ ^ 2 / (τ * H) := by
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) (mul_pos hτ hH)).2
  have hprod : τ * H ≤ 3 * d ^ 2 := by
    calc
      τ * H ≤ d * H := mul_le_mul_of_nonneg_right hτd hH.le
      _ ≤ d * (3 * d) := mul_le_mul_of_nonneg_left hHd hd.le
      _ = 3 * d ^ 2 := by ring
  nlinarith [mul_le_mul_of_nonneg_left hprod (sq_nonneg μ)]

lemma two_observation_ratio {μ e₀ e₁ A τ r d : ℝ}
    (hτ : 0 < τ) (hτA : τ ≤ A) (hAd : A ≤ d) (hr : 0 ≤ r)
    (h₀ : r * |μ + e₀| ≤ d) (h₁ : r * |μ + e₁| ≤ d) :
    μ ^ 2 / d ^ 2 ≤ 3 * μ ^ 2 / (τ * (A + r * |μ|)) +
      if A < r * |μ| ∧ |μ| / 2 < |e₀| ∧ |μ| / 2 < |e₁|
      then μ ^ 2 / A ^ 2 else 0 := by
  have hA : 0 < A := hτ.trans_le hτA
  have hd : 0 < d := hA.trans_le hAd
  have hH : 0 < A + r * |μ| := by positivity
  split_ifs with hbad
  · have hratio : μ ^ 2 / d ^ 2 ≤ μ ^ 2 / A ^ 2 := by
      apply div_le_div_of_nonneg_left (sq_nonneg μ) (sq_pos_of_pos hA)
      nlinarith
    have hnonneg : 0 ≤ 3 * μ ^ 2 / (τ * (A + r * |μ|)) := by positivity
    linarith
  · have hHd : A + r * |μ| ≤ 3 * d := by
      by_cases hsmall : r * |μ| ≤ A
      · linarith
      · have hobs : |e₀| ≤ |μ| / 2 ∨ |e₁| ≤ |μ| / 2 := by
          by_contra hn
          push Not at hn
          exact hbad ⟨lt_of_not_ge hsmall, hn.1, hn.2⟩
        rcases hobs with he | he
        · have hs := mul_le_mul_of_nonneg_left
            (abs_signal_le_twice_observation he) hr
          nlinarith
        · have hs := mul_le_mul_of_nonneg_left
            (abs_signal_le_twice_observation he) hr
          nlinarith
    simpa using inverse_square_le hτ hH hd (hτA.trans hAd) hHd

lemma ordinary_gradient_conversion {G S τ : ℝ} (_hG : 0 ≤ G) (hS : 0 ≤ S)
    (hτ : 0 ≤ τ) (h : G ^ 2 ≤ S * (4 * τ + G + Real.sqrt (τ * S))) :
    G ≤ 2 * S + 3 * Real.sqrt (τ * S) := by
  have hz := Real.sqrt_nonneg (τ * S)
  have hzsq := Real.sq_sqrt (mul_nonneg hτ hS)
  by_contra hn
  have hgt : 2 * S + 3 * Real.sqrt (τ * S) < G := lt_of_not_ge hn
  have hpos : 0 < G + S + 3 * Real.sqrt (τ * S) := by linarith
  have hmul := mul_pos (sub_pos.mpr hgt) hpos
  nlinarith [sq_nonneg S, mul_nonneg hS hz, sq_nonneg (Real.sqrt (τ * S))]

lemma ordinary_gradient_accuracy {G S τ ε : ℝ} (hG : 0 ≤ G) (hS : 0 ≤ S)
    (hε : 0 < ε) (hτε : ε ≤ τ) (hsmall : τ * S ≤ ε ^ 2 / 100)
    (h : G ^ 2 ≤ S * (4 * τ + G + Real.sqrt (τ * S))) : G ≤ ε := by
  have hτ : 0 < τ := hε.trans_le hτε
  have hconv := ordinary_gradient_conversion hG hS hτ.le h
  have hroot : Real.sqrt (τ * S) ≤ ε / 10 := by
    have hs := Real.sq_sqrt (mul_nonneg hτ.le hS)
    have hn := Real.sqrt_nonneg (τ * S)
    nlinarith
  have hSsmall : S ≤ ε / 100 := by
    have hmul := mul_le_mul_of_nonneg_right hτε hS
    nlinarith
  linarith

lemma weighted_square_le {a c u v : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    (a * u + c * v) ^ 2 ≤ a * u ^ 2 + c ^ 2 / (1 - a) * v ^ 2 := by
  have hgap : 0 < 1 - a := by linarith
  have hcancel : (c ^ 2 / (1 - a)) * (1 - a) = c ^ 2 := div_mul_cancel₀ _ hgap.ne'
  apply (mul_le_mul_iff_of_pos_right hgap).mp
  have hs := mul_nonneg ha (sq_nonneg ((1 - a) * u - c * v))
  have hcancelv := congrArg (fun z : ℝ => z * v ^ 2) hcancel
  nlinarith [hcancelv]

lemma geometric_uniform_bound {a c M : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (u v : ℕ → ℝ)
    (hzero : u 0 = 0) (hv : ∀ t, v t ≤ M)
    (hstep : ∀ t, u (t + 1) ≤ a * u t + c * v t) (t : ℕ) :
    u t ≤ c * M / (1 - a) := by
  have hgap : 0 < 1 - a := by linarith
  have hid : c * M / (1 - a) * (1 - a) = c * M := div_mul_cancel₀ _ hgap.ne'
  induction t with
  | zero => rw [hzero]; positivity
  | succ t ih =>
      have hb := (hstep t).trans
        (add_le_add (mul_le_mul_of_nonneg_left ih ha) (mul_le_mul_of_nonneg_left (hv t) hc))
      nlinarith

lemma geometric_energy {a c : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (u v : ℕ → ℝ) (hu : ∀ t, 0 ≤ u t)
    (hzero : u 0 = 0) (hstep : ∀ t, u (t + 1) ≤ a * u t + c * v t) (T : ℕ) :
    (∑ t ∈ Finset.range T, u (t + 1) ^ 2) ≤
      (c / (1 - a)) ^ 2 * ∑ t ∈ Finset.range T, v t ^ 2 := by
  have hgap : 0 < 1 - a := by linarith
  have hbound : ∀ t, u (t + 1) ^ 2 ≤ a * u t ^ 2 + c ^ 2 / (1 - a) * v t ^ 2 := by
    intro t
    exact (pow_le_pow_left₀ (hu _) (hstep t) 2).trans (weighted_square_le ha ha1)
  have hpotential : ∀ N : ℕ,
      (1 - a) * (∑ t ∈ Finset.range N, u (t + 1) ^ 2) + a * u N ^ 2 ≤
        c ^ 2 / (1 - a) * ∑ t ∈ Finset.range N, v t ^ 2 := by
    intro N
    induction N with
    | zero => simp [hzero]
    | succ N ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        nlinarith [hbound N]
  have hb := hpotential T
  have hlast : 0 ≤ a * u T ^ 2 := mul_nonneg ha (sq_nonneg _)
  have htarget : (1 - a) * (∑ t ∈ Finset.range T, u (t + 1) ^ 2) ≤
      c ^ 2 / (1 - a) * ∑ t ∈ Finset.range T, v t ^ 2 := by linarith
  have hdiv : (∑ t ∈ Finset.range T, u (t + 1) ^ 2) ≤
      (c ^ 2 / (1 - a) * ∑ t ∈ Finset.range T, v t ^ 2) / (1 - a) := by
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm]
    exact htarget
  convert hdiv using 1; ring

lemma linear_recurrence_expansion (a c : ℝ) (u v : ℕ → ℝ)
    (hzero : u 0 = 0) (hstep : ∀ t, u (t + 1) = a * u t + c * v t) (T : ℕ) :
    u T = c * ∑ k ∈ Finset.range T, a ^ (T - 1 - k) * v k := by
  induction T with
  | zero => simp [hzero]
  | succ T ih =>
    rw [hstep, ih, Finset.sum_range_succ]
    have he : a * (∑ k ∈ Finset.range T, a ^ (T - 1 - k) * v k) =
        ∑ k ∈ Finset.range T, a ^ (T + 1 - 1 - k) * v k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkT := Finset.mem_range.mp hk
      have hn : T + 1 - 1 - k = (T - 1 - k) + 1 := by omega
      rw [hn, pow_succ]
      ring
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    simp only [Nat.add_sub_cancel] at he
    rw [← he]
    ring

lemma linear_recurrence_from (a c : ℝ) (u v : ℕ → ℝ)
    (hstep : ∀ t, u (t + 1) = a * u t + c * v t) (T : ℕ) :
    u T = a ^ T * u 0 + c * ∑ k ∈ Finset.range T, a ^ (T - 1 - k) * v k := by
  have hz : u 0 - a ^ 0 * u 0 = 0 := by ring
  have hs (t : ℕ) : u (t + 1) - a ^ (t + 1) * u 0 =
      a * (u t - a ^ t * u 0) + c * v t := by
    rw [hstep, pow_succ]
    ring
  have hh := linear_recurrence_expansion a c (fun t => u t - a ^ t * u 0) v hz hs T
  linarith

lemma bias_absorption {τ a r x S : ℝ} (hτ : 0 < τ) (hτa : τ ≤ a)
    (hr : 0 ≤ r) (hx : 0 ≤ x) (hS : 0 ≤ S) (hs : x ^ 2 ≤ S * (a + r * x)) :
    100 * τ * r * x / a ≤ (1 / 40 + 200 * r ^ 2) * S + 200000 * τ * r ^ 2 := by
  have ha : 0 < a := hτ.trans_le hτa
  have hsmall : 100 * τ * r * x / a ≤ 100 * r * x := by
    apply (div_le_iff₀ ha).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hτa) (mul_nonneg hr hx)]
  by_cases hcase : r * x ≤ a
  · let y := x / a
    have hy : a * y = x := by dsimp [y]; field_simp
    have hs' : x ^ 2 ≤ 2 * a * S := by nlinarith [mul_le_mul_of_nonneg_left hcase hS]
    have hay : a * y ^ 2 ≤ 2 * S := by
      apply (mul_le_mul_iff_right₀ ha).mp
      nlinarith [congrArg (fun z : ℝ => z ^ 2) hy]
    have hty : τ * y ^ 2 ≤ 2 * S := (mul_le_mul_of_nonneg_right hτa (sq_nonneg y)).trans hay
    have hsq := mul_nonneg hτ.le (sq_nonneg (y - 4000 * r))
    have hrewrite : 100 * τ * r * x / a = 100 * τ * r * y := by dsimp [y]; ring
    rw [hrewrite]
    nlinarith [mul_nonneg (sq_nonneg r) hS]
  · have hlarge : x ≤ 2 * r * S := by
      have hrx : a < r * x := lt_of_not_ge hcase
      have hxp : 0 < x := by by_contra hn; have : x = 0 := le_antisymm (le_of_not_gt hn) hx; simp [this] at hrx; linarith
      nlinarith [mul_le_mul_of_nonneg_left hrx.le hS]
    have hbound := mul_le_mul_of_nonneg_left hlarge (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) hr)
    nlinarith [mul_nonneg hτ.le (sq_nonneg r)]

lemma bounded_square_interpolation {z u C p : ℝ} (hu : 0 ≤ u)
    (hp : 0 ≤ p) (hp2 : p ≤ 2) (hz : |z| ≤ C * u) (hcap : |z| ≤ C) :
    z ^ 2 ≤ C ^ 2 * u ^ p := by
  by_cases hu1 : u ≤ 1
  · have hpow : u ^ 2 ≤ u ^ p := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge' hu hu1 hp hp2
    calc
      z ^ 2 = |z| ^ 2 := (sq_abs z).symm
      _ ≤ (C * u) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hz _
      _ = C ^ 2 * u ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (sq_nonneg C)
  · have hpow : 1 ≤ u ^ p := Real.one_le_rpow (le_of_not_ge hu1) hp
    have hsq : z ^ 2 ≤ C ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hcap 2
    nlinarith [mul_le_mul_of_nonneg_left hpow (sq_nonneg C)]


lemma weighted_geometric_linear {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (T : ℕ) :
    (∑ j ∈ Finset.range T, ((j : ℝ) + 1) * r ^ j) ≤ 1 / (1 - r) ^ 2 := by
  have hn : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr] using hr1
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hn).add (hasSum_geometric_of_lt_one hr hr1)
  have hh := sum_le_hasSum (Finset.range T) (fun j _ => by positivity) hs
  have heq : r / (1 - r) ^ 2 + (1 - r)⁻¹ = 1 / (1 - r) ^ 2 := by
    field_simp
    ring
  rw [heq] at hh
  simpa only [add_mul, one_mul] using hh

lemma weighted_geometric_square {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (T : ℕ) :
    (∑ j ∈ Finset.range T, (j : ℝ) ^ 2 * r ^ j) ≤ r * (1 + r) / (1 - r) ^ 3 := by
  have hn : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr] using hr1
  exact sum_le_hasSum (Finset.range T) (fun j _ => by positivity) (hasSum_sq_mul_geometric_of_norm_lt_one hn)


lemma two_tail_scaling {x A r M α p : ℝ} (hx : 0 < x) (hA : 0 < A) (hr : 0 < r)
    (hα : 0 ≤ α) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hlarge : 1 ≤ r * x)
    (hM : M * r ^ p ≤ A ^ 2 * r ^ 2) :
    (x ^ 2 / A ^ 2) * (M * α / ((x / 2) ^ p) ^ 2) ≤ 16 * α * r ^ p := by
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr p
  have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx.le p
  have hh : 0 < (x / 2) ^ p := Real.rpow_pos_of_pos (by positivity) p
  have hpow : r * x ≤ r ^ p * x ^ p := by
    have ht := Real.rpow_le_rpow_of_exponent_le hlarge hp
    simpa only [Real.rpow_one, Real.mul_rpow hr.le hx.le] using ht
  have hsq : r ^ 2 * x ^ 2 ≤ (r ^ p) ^ 2 * (x ^ p) ^ 2 := by
    have ht := pow_le_pow_left₀ (mul_nonneg hr.le hx.le) hpow 2
    simpa only [mul_pow] using ht
  have hbase : M * x ^ 2 ≤ A ^ 2 * r ^ p * (x ^ p) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hrp).mp
    have h₁ := mul_le_mul_of_nonneg_right hM (sq_nonneg x)
    have h₂ := mul_le_mul_of_nonneg_left hsq (sq_nonneg A)
    nlinarith
  have htwo : (2 : ℝ) ^ p ≤ 4 := by
    have ht := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp2
    norm_num only [Real.rpow_two] at ht
    exact ht
  have hhalf : x ^ p ≤ 4 * (x / 2) ^ p := by
    calc
      x ^ p = (2 * (x / 2)) ^ p := by congr 1; ring
      _ = (2 : ℝ) ^ p * (x / 2) ^ p := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo hh.le
  have hhalfsq : (x ^ p) ^ 2 ≤ 16 * ((x / 2) ^ p) ^ 2 := by
    have ht := pow_le_pow_left₀ hxp hhalf 2
    nlinarith
  have hfinal : M * x ^ 2 ≤ 16 * A ^ 2 * r ^ p * ((x / 2) ^ p) ^ 2 :=
    hbase.trans (by nlinarith [mul_le_mul_of_nonneg_left hhalfsq (mul_nonneg (sq_nonneg A) hrp.le)])
  have he : (x ^ 2 / A ^ 2) * (M * α / ((x / 2) ^ p) ^ 2) =
      (M * x ^ 2 * α) / (A ^ 2 * ((x / 2) ^ p) ^ 2) := by ring
  rw [he]
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hA) (sq_pos_of_pos hh))).2
  nlinarith [mul_le_mul_of_nonneg_right hfinal hα]


lemma window_coefficient_absorption {x u B r c A τ M H p : ℝ}
    (hx : 0 ≤ x) (hu : 0 ≤ u) (hur : u ≤ r) (hr : 0 < r)
    (hc : 0 < c) (hc1 : c ≤ 1) (hτ : 0 < τ) (hτA : τ ≤ A)
    (hB : c * A ≤ B) (hM : 0 ≤ M) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hnoise : M * (r / τ) ^ p ≤ r ^ 2) (hH : 100 * τ * r * x / A ≤ H) :
    x * ((4 * (u / B) ^ p) / (r * c)) * M ≤ H / (25 * c ^ 4) := by
  have hA : 0 < A := hτ.trans_le hτA
  have hBp : 0 < B := (mul_pos hc hA).trans_le hB
  have ht0 : 0 ≤ τ / A := by positivity
  have ht1 : τ / A ≤ 1 := (div_le_one hA).2 hτA
  have hcp : 1 ≤ 1 / c := (le_div_iff₀ hc).2 (by simpa using hc1)
  have hpowc : (1 / c) ^ p ≤ (1 / c) ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hcp hp2
  have hpowt : (τ / A) ^ p ≤ τ / A := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' ht0 ht1 (by norm_num : (0 : ℝ) ≤ 1) hp
  have hbase : u / B ≤ (1 / c) * (r / τ) * (τ / A) := by
    calc
      _ ≤ r / (c * A) := div_le_div₀ hr.le hur (mul_pos hc hA) hB
      _ = _ := by field_simp
  have hpower := Real.rpow_le_rpow (div_nonneg hu hBp.le) hbase (by linarith : 0 ≤ p)
  rw [Real.mul_rpow (by positivity) ht0, Real.mul_rpow (by positivity) (by positivity)] at hpower
  have hupper : (u / B) ^ p ≤ (1 / c) ^ 2 * (r / τ) ^ p * (τ / A) := by
    apply hpower.trans
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpowc
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg ht0 _)).trans
        (mul_le_mul_of_nonneg_left hpowt (by positivity))
  have hH0 : 0 ≤ H := (by positivity : 0 ≤ 100 * τ * r * x / A).trans hH
  have hH' := (div_le_iff₀ hA).mp hH
  calc
    _ = (4 * x * M / (r * c)) * (u / B) ^ p := by ring
    _ ≤ (4 * x * M / (r * c)) * ((1 / c) ^ 2 * (r / τ) ^ p * (τ / A)) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = (4 * x / (r * c ^ 3)) * (M * (r / τ) ^ p) * (τ / A) := by field_simp
    _ ≤ (4 * x / (r * c ^ 3)) * r ^ 2 * (τ / A) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnoise (by positivity)) ht0
    _ = 4 * τ * r * x / (A * c ^ 3) := by field_simp
    _ ≤ H / (25 * c ^ 3) := by
      apply (div_le_div_iff₀ (mul_pos hA (pow_pos hc _)) (by positivity)).2
      nlinarith [mul_le_mul_of_nonneg_right hH' (pow_nonneg hc.le 3)]
    _ ≤ H / (25 * c ^ 4) := by
      apply div_le_div_of_nonneg_left hH0 (by positivity)
      have hh := mul_le_mul_of_nonneg_left hc1 (pow_nonneg hc.le 3)
      nlinarith [show c ^ 4 = c ^ 3 * c by ring]

lemma forgetting_geometric_ratio {ρ : ℝ} (hρsmall : ρ ≤ 1 / 1000000000000) :
    0 ≤ (9 / 10 : ℝ) / (1 - ρ) ^ 2 ∧ (9 / 10 : ℝ) / (1 - ρ) ^ 2 ≤ 91 / 100 := by
  have hb : 0 < 1 - ρ := by linarith
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ (sq_pos_of_pos hb)).2
  nlinarith [sq_nonneg ρ]

lemma geometric_bias_weight_sum {r : ℝ} (hr : 0 ≤ r) (hrsmall : r ≤ 91 / 100) (T : ℕ) :
    (1 / 250 : ℝ) * (∑ j ∈ Finset.range T, ((j : ℝ) + 1) * r ^ j) ≤ 1 := by
  have hr1 : r < 1 := by linarith
  have hh := weighted_geometric_linear hr hr1 T
  calc
    _ ≤ (1 / 250 : ℝ) * (1 / (1 - r) ^ 2) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ ≤ 1 := by
      rw [mul_one_div]
      apply (div_le_one (sq_pos_of_pos (sub_pos.mpr hr1))).2
      nlinarith [sq_nonneg (91 / 100 - r)]

lemma geometric_square_sum_bound {r : ℝ} (hr : 0 ≤ r) (hrsmall : r ≤ 91 / 100) (T : ℕ) :
    (∑ j ∈ Finset.range T, (j : ℝ) ^ 2 * r ^ j) ≤ 3000 := by
  have hr1 : r < 1 := by linarith
  apply (weighted_geometric_square hr hr1 T).trans
  apply (div_le_iff₀ (pow_pos (sub_pos.mpr hr1) 3)).2
  have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 100)
    (by linarith : 9 / 100 ≤ 1 - r) 3
  have hn : r * (1 + r) ≤ 2 := by nlinarith [sq_nonneg (1 - r)]
  nlinarith


lemma concave_power_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) : (∑ i ∈ s, a i) ^ p ≤ ∑ i ∈ s, (a i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hp.ne']
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (Real.rpow_add_le_add_rpow (ha i) (Finset.sum_nonneg fun k _ => ha k) hp.le hp1).trans
      (add_le_add le_rfl ih)

lemma weighted_rms_power {ι : Type*} (s : Finset ι) (a z : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    (Real.sqrt (∑ i ∈ s, a i * (z i) ^ 2)) ^ p ≤ ∑ i ∈ s, (a i) ^ (p / 2) * |z i| ^ p := by
  have hq : 0 < p / 2 := by positivity
  have he (i : ι) : ((z i) ^ 2) ^ (p / 2) = |z i| ^ p := by
    rw [← sq_abs (z i), ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  have hh := concave_power_sum s (fun i => a i * (z i) ^ 2)
    (fun i => mul_nonneg (ha i) (sq_nonneg _)) hq (by linarith)
  simp_rw [Real.mul_rpow (ha _) (sq_nonneg _), he] at hh
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (sq_nonneg _))]
  convert hh using 1
  congr 1
  ring

lemma forgetting_power_gap {ρ p : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ρ / 2 ≤ 1 - (1 - ρ) ^ (p / 2) := by
  have hh := rpow_one_add_le_one_add_mul_self (s := -ρ) (by linarith) (p := p / 2)
    (by linarith) (by linarith)
  simp only [← sub_eq_add_neg] at hh
  nlinarith


lemma shifted_square_sum_le (u : ℕ → ℝ) {N r T : ℕ} (h : N + r ≤ T) :
    (∑ s ∈ Finset.range N, (u (s + r)) ^ 2) ≤ ∑ t ∈ Finset.range T, (u t) ^ 2 := by
  have hshift : (∑ s ∈ Finset.range N, (u (s + r)) ^ 2) ≤ ∑ t ∈ Finset.range (r + N), (u t) ^ 2 := by
    rw [Finset.sum_range_add]
    simp_rw [Nat.add_comm r]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact hshift.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega)) (fun _ _ _ => sq_nonneg _))

lemma window_overlap_square_sum (u : ℕ → ℝ) (T j : ℕ) :
    (∑ s ∈ Finset.range (T - j), (∑ r ∈ Finset.range j, u (s + r)) ^ 2) ≤
      (j : ℝ) ^ 2 * ∑ t ∈ Finset.range T, (u t) ^ 2 := by
  have hrow (s : ℕ) : (∑ r ∈ Finset.range j, u (s + r)) ^ 2 ≤
      (j : ℝ) * ∑ r ∈ Finset.range j, (u (s + r)) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.range j) (fun _ => (1 : ℝ)) (fun r => u (s + r))
  by_cases hj : j ≤ T
  · calc
      _ ≤ ∑ s ∈ Finset.range (T - j), (j : ℝ) * ∑ r ∈ Finset.range j, (u (s + r)) ^ 2 :=
        Finset.sum_le_sum fun s _ => hrow s
      _ = (j : ℝ) * ∑ r ∈ Finset.range j, ∑ s ∈ Finset.range (T - j), (u (s + r)) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (j : ℝ) * ∑ _ ∈ Finset.range j, ∑ t ∈ Finset.range T, (u t) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro r hr
        exact shifted_square_sum_le u (by have := Finset.mem_range.mp hr; omega)
      _ = _ := by simp; ring
  · have he : T - j = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [he]
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity


lemma reciprocal_transport_cauchy {ι : Type*} [Fintype ι]
    (μ g D E : ι → ℝ) (hD : ∀ i, 0 < D i) (hE : ∀ i, 0 < E i)
    {r : ℝ} (hr : 0 < r) (hg : ∀ i, |g i| / D i ≤ 1 / r) :
    |(∑ i, μ i * g i / D i) - ∑ i, μ i * g i / E i| ≤
      (1 / r) * Real.sqrt (∑ i, (μ i) ^ 2 / (E i) ^ 2) *
        Real.sqrt (∑ i, (D i - E i) ^ 2) := by
  have hpoint (i : ι) : |μ i * g i / D i - μ i * g i / E i| ≤
      (1 / r) * (|μ i / E i| * |D i - E i|) := by
    have he : μ i * g i / D i - μ i * g i / E i = (μ i / E i) * (g i / D i) * (E i - D i) := by
      field_simp [(hD i).ne', (hE i).ne']
    rw [he, abs_mul, abs_mul, abs_div (g i), abs_of_pos (hD i), abs_sub_comm (E i)]
    have hh := mul_le_mul_of_nonneg_left (hg i) (abs_nonneg (μ i / E i))
    have hh' := mul_le_mul_of_nonneg_right hh (abs_nonneg (D i - E i))
    convert hh' using 1
    ring
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |μ i / E i|) (fun i => |D i - E i|)
  simp only [sq_abs, div_pow] at hcs
  calc
    _ ≤ ∑ i, |μ i * g i / D i - μ i * g i / E i| := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (1 / r) * (|μ i / E i| * |D i - E i|) := Finset.sum_le_sum fun i _ => hpoint i
    _ = (1 / r) * ∑ i, |μ i / E i| * |D i - E i| := (Finset.mul_sum ..).symm
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcs (by positivity : 0 ≤ 1 / r)


lemma triangle_sum_exchange (F : ℕ → ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∑ k ∈ Finset.range (t + 1), F (t - k) k) =
      ∑ k ∈ Finset.range T, ∑ s ∈ Finset.range (T - k), F s k := by
  have hrow (t : ℕ) (ht : t < T) :
      (∑ k ∈ Finset.range (t + 1), F (t - k) k) =
        ∑ k ∈ Finset.range T, if k ≤ t then F (t - k) k else 0 := by
    calc
      _ = ∑ k ∈ Finset.range (t + 1), if k ≤ t then F (t - k) k else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ite_eq_left (by have := Finset.mem_range.mp hk; omega)]
      _ = _ := Finset.sum_subset (Finset.range_mono (by omega)) (fun k hk hnot => by
        rw [ite_eq_right (by simp only [Finset.mem_range] at hnot; omega)])
  calc
    _ = ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range T, if k ≤ t then F (t - k) k else 0 :=
      Finset.sum_congr rfl fun t ht => hrow t (Finset.mem_range.mp ht)
    _ = ∑ k ∈ Finset.range T, ∑ t ∈ Finset.range T, if k ≤ t then F (t - k) k else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkT : k ≤ T := (Finset.mem_range.mp hk).le
      have hsplit : T = k + (T - k) := by omega
      rw [hsplit, Finset.sum_range_add]
      have hz : (∑ t ∈ Finset.range k, if k ≤ t then F (t - k) k else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        exact ite_eq_right (Nat.not_le.mpr (Finset.mem_range.mp ht))
      rw [hz, zero_add]
      apply Finset.sum_congr (by congr 1; omega)
      intro s _
      simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]


lemma forgetting_mass_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) :
    (∑ k ∈ Finset.range N, ρ * (1 - ρ) ^ k) ≤ 1 := by
  have hb : 0 ≤ 1 - ρ := sub_nonneg.mpr hρ1
  have hb1 : 1 - ρ < 1 := by linarith
  have hh := sum_le_hasSum (Finset.range N) (fun k _ => pow_nonneg hb k)
    (hasSum_geometric_of_lt_one hb hb1)
  rw [← Finset.mul_sum]
  calc
    _ ≤ ρ * (1 - (1 - ρ))⁻¹ := mul_le_mul_of_nonneg_left hh hρ.le
    _ = 1 := by rw [sub_sub_cancel]; exact mul_inv_cancel₀ hρ.ne'

lemma forgetting_lag_square_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) :
    (∑ k ∈ Finset.range N, ρ * (1 - ρ) ^ k * (k : ℝ) ^ 2) ≤ 2 / ρ ^ 2 := by
  have hb : 0 ≤ 1 - ρ := sub_nonneg.mpr hρ1
  have hb1 : 1 - ρ < 1 := by linarith
  have hn : ‖1 - ρ‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hb] using hb1
  have hh := sum_le_hasSum (Finset.range N) (fun k _ => by positivity)
    (hasSum_sq_mul_geometric_of_norm_lt_one hn)
  calc
    _ = ρ * (∑ k ∈ Finset.range N, (k : ℝ) ^ 2 * (1 - ρ) ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ ρ * ((1 - ρ) * (1 + (1 - ρ)) / (1 - (1 - ρ)) ^ 3) := mul_le_mul_of_nonneg_left hh hρ.le
    _ = (1 - ρ) * (1 + (1 - ρ)) / ρ ^ 2 := by rw [sub_sub_cancel]; field_simp
    _ ≤ 2 / ρ ^ 2 := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg ρ]) (sq_nonneg _)


lemma weighted_history_overlap (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (u : ℕ → ℝ) (E : ℕ → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ s k, E s k ≤ C * (∑ r ∈ Finset.range k, u (s + r)) ^ 2)
    (T : ℕ) :
    (∑ t ∈ Finset.range T, ∑ k ∈ Finset.range (t + 1), a k * E (t - k) k) ≤
      C * (∑ k ∈ Finset.range T, a k * (k : ℝ) ^ 2) * ∑ t ∈ Finset.range T, (u t) ^ 2 := by
  rw [triangle_sum_exchange (fun s k => a k * E s k) T]
  calc
    _ ≤ ∑ k ∈ Finset.range T, ∑ s ∈ Finset.range (T - k),
        a k * (C * (∑ r ∈ Finset.range k, u (s + r)) ^ 2) := by
      exact Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (hE s k) (ha k)
    _ = ∑ k ∈ Finset.range T, (a k * C) *
        ∑ s ∈ Finset.range (T - k), (∑ r ∈ Finset.range k, u (s + r)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ ∑ k ∈ Finset.range T, (a k * C) *
        ((k : ℝ) ^ 2 * ∑ t ∈ Finset.range T, (u t) ^ 2) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
        (window_overlap_square_sum u T k) (mul_nonneg (ha k) hC)
    _ = _ := by
      rw [Finset.mul_sum (Finset.range T) (fun k => a k * (k : ℝ) ^ 2) C, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma coordinate_inner_bound {ι : Type*} [Fintype ι]
    (u z E h : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) (hE : ∀ i, 0 < E i)
    (hz : ∀ i, |z i| / E i ≤ c * |h i|) :
    |∑ i, u i * z i / E i| ≤ c * Real.sqrt (∑ i, (u i) ^ 2) * Real.sqrt (∑ i, (h i) ^ 2) := by
  have hp (i : ι) : |u i * z i / E i| ≤ c * (|u i| * |h i|) := by
    rw [abs_div, abs_mul, abs_of_pos (hE i), mul_div_assoc]
    have hh := mul_le_mul_of_nonneg_left (hz i) (abs_nonneg (u i))
    nlinarith
  have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |u i|) (fun i => |h i|)
  simp only [sq_abs] at hh
  calc
    _ ≤ ∑ i, |u i * z i / E i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, c * (|u i| * |h i|) := Finset.sum_le_sum fun i _ => hp i
    _ = c * ∑ i, |u i| * |h i| := (Finset.mul_sum ..).symm
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hc

lemma triangle_convolution_exchange (q : ℝ) (H : ℕ → ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), q ^ (t - s) * H s t) =
      ∑ j ∈ Finset.range T, q ^ j * ∑ s ∈ Finset.range (T - j), H s (s + j) := by
  have hr (t : ℕ) : (∑ s ∈ Finset.range (t + 1), q ^ (t - s) * H s t) =
      ∑ j ∈ Finset.range (t + 1), q ^ j * H (t - j) t := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hjt : j ≤ t := by have := Finset.mem_range.mp hj; omega
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self hjt]
  simp_rw [hr]
  have he : (∑ t ∈ Finset.range T, ∑ j ∈ Finset.range (t + 1), q ^ j * H (t - j) t) =
      ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range (t + 1), q ^ j * H (t - j) (t - j + j) := by
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.sub_add_cancel (by have := Finset.mem_range.mp hj; omega)]
  rw [he, triangle_sum_exchange (fun s j => q ^ j * H s (s + j)) T]
  apply Finset.sum_congr rfl
  intro j _
  exact (Finset.mul_sum ..).symm

lemma geometric_linear_sum_bound {r : ℝ} (hr : 0 ≤ r) (hrsmall : r ≤ 91 / 100) (T : ℕ) :
    (∑ j ∈ Finset.range T, (j : ℝ) * r ^ j) ≤ 125 := by
  have hr1 : r < 1 := by linarith
  calc
    _ ≤ ∑ j ∈ Finset.range T, ((j : ℝ) + 1) * r ^ j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr j)
    _ ≤ 1 / (1 - r) ^ 2 := weighted_geometric_linear hr hr1 T
    _ ≤ 125 := by
      apply (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hr1))).2
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 100)
        (by linarith : 9 / 100 ≤ 1 - r) 2
      nlinarith

lemma triangular_weighted_sum_le (a H : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hH : ∀ s, 0 ≤ H s) (T : ℕ) :
    (∑ j ∈ Finset.range T, a j * ∑ s ∈ Finset.range (T - j), H s) ≤
      (∑ j ∈ Finset.range T, a j) * ∑ s ∈ Finset.range T, H s := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (ha j)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.sub_le T j)) (fun s _ _ => hH s)

lemma triangular_bias_sum_le {r : ℝ} (hr : 0 ≤ r) (hrsmall : r ≤ 91 / 100)
    (H : ℕ → ℝ) (hH : ∀ s, 0 ≤ H s) (T : ℕ) :
    (1 / 250 : ℝ) * (∑ j ∈ Finset.range T, ((j : ℝ) + 1) * r ^ j *
      ∑ s ∈ Finset.range (T - j), H s) ≤ ∑ s ∈ Finset.range T, H s := by
  have hh := triangular_weighted_sum_le (fun j => ((j : ℝ) + 1) * r ^ j) H
    (fun j => by positivity) hH T
  calc
    _ ≤ (1 / 250 : ℝ) * ((∑ j ∈ Finset.range T, ((j : ℝ) + 1) * r ^ j) *
        ∑ s ∈ Finset.range T, H s) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = ((1 / 250 : ℝ) * (∑ j ∈ Finset.range T, ((j : ℝ) + 1) * r ^ j)) *
        ∑ s ∈ Finset.range T, H s := by ring
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (geometric_bias_weight_sum hr hrsmall T) (Finset.sum_nonneg fun s _ => hH s)

lemma sqrt_product_le_common {X Y B : ℝ} (hX : 0 ≤ X) (_hY : 0 ≤ Y)
    (hXB : X ≤ B) (hYB : Y ≤ B) : Real.sqrt X * Real.sqrt Y ≤ B := by
  have hB : 0 ≤ B := hX.trans hXB
  calc
    _ ≤ Real.sqrt B * Real.sqrt B := mul_le_mul (Real.sqrt_le_sqrt hXB)
      (Real.sqrt_le_sqrt hYB) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = B := Real.mul_self_sqrt hB

lemma frozen_transport_energy_product {X U W c : ℝ} (hX : 0 ≤ X) (hU : 0 ≤ U)
    (hW : 0 ≤ W) (hc : 0 < c) (hc1 : c ≤ 1)
    (hXB : X ≤ 19 * W / c) (hUB : U ≤ 32 * W) :
    Real.sqrt X * Real.sqrt U ≤ 32 * W / c := by
  apply sqrt_product_le_common hX hU
  · exact hXB.trans (div_le_div_of_nonneg_right (by nlinarith) hc.le)
  · apply hUB.trans
    apply (le_div_iff₀ hc).2
    nlinarith

lemma lag_transport_scalar {a W c : ℝ} (ha : 0 ≤ a) (hW : 0 ≤ W)
    (hc : 0 < c) (hc1 : c ≤ 1) (j : ℕ) :
    a * (j : ℝ) * Real.sqrt j / c * (32 * W / c) ≤
      32 * a * (j : ℝ) ^ 2 / c ^ 4 * W := by
  have hj : (j : ℝ) * Real.sqrt j ≤ (j : ℝ) ^ 2 := by
    by_cases hz : j = 0
    · simp [hz]
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
    have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ j)
    have hn := Real.sqrt_nonneg (j : ℝ)
    have hroot : Real.sqrt j ≤ (j : ℝ) := by nlinarith
    nlinarith
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have hprod : (j : ℝ) * Real.sqrt j * c ^ 2 ≤ (j : ℝ) ^ 2 := by
    exact (mul_le_mul_of_nonneg_left hc2 (by positivity)).trans (by simpa using hj)
  have he : (a * (j : ℝ) * Real.sqrt j / c * (32 * W / c)) * c ^ 4 =
      32 * a * W * ((j : ℝ) * Real.sqrt j * c ^ 2) := by field_simp
  have he2 : (32 * a * (j : ℝ) ^ 2 / c ^ 4 * W) * c ^ 4 =
      32 * a * W * (j : ℝ) ^ 2 := by field_simp
  have hh := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 32 * a * W)
  rw [← he, ← he2] at hh
  nlinarith [pow_pos hc 4]

lemma mean_window_signal_sum {q : ℝ} (hq : 0 ≤ q) (M : ℕ → ℕ → ℝ)
    (S : ℕ → ℝ) (hM : ∀ s j, 0 ≤ M s j) (hzero : ∀ s, M s 0 = S s) (T : ℕ) :
    (∑ s ∈ Finset.range T, S s) ≤
      ∑ j ∈ Finset.range T, q ^ j * ∑ s ∈ Finset.range (T - j), M s j := by
  by_cases hT : T = 0
  · simp [hT]
  have hh := Finset.single_le_sum (f := fun j => q ^ j * ∑ s ∈ Finset.range (T - j), M s j)
    (fun j (_ : j ∈ Finset.range T) => mul_nonneg (pow_nonneg hq j)
      (Finset.sum_nonneg fun s _ => hM s j))
    (show 0 ∈ Finset.range T by simp; omega)
  simpa only [pow_zero, one_mul, Nat.sub_zero, hzero] using hh

lemma triangular_pairing_lower (A B F M : ℕ → ℕ → ℝ) (w : ℕ → ℝ)
    (hw : ∀ j, 0 ≤ w j) (T : ℕ) :
    (∑ j ∈ Finset.range T, w j * (∑ s ∈ Finset.range (T - j), M s j)) -
      (∑ j ∈ Finset.range T, w j * (∑ s ∈ Finset.range (T - j), (M s j - F s j))) -
      (∑ j ∈ Finset.range T, w j * (∑ s ∈ Finset.range (T - j), |A s j - B s j|)) -
      (∑ j ∈ Finset.range T, w j * (∑ s ∈ Finset.range (T - j), |B s j - F s j|)) ≤
      ∑ j ∈ Finset.range T, w j * (∑ s ∈ Finset.range (T - j), A s j) := by
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (hw j)
  apply Finset.sum_le_sum
  intro s _
  have ha := le_abs_self (B s j - A s j)
  have hb := le_abs_self (F s j - B s j)
  rw [abs_sub_comm (B s j), abs_sub_comm (F s j)] at *
  linarith

lemma sqrt_transport_identity {ρ c j x Z : ℝ} (hρ : 0 < ρ) (hc : 0 < c)
    (hj : 0 ≤ j) (hx : 0 ≤ x) :
    (1 / (Real.sqrt ρ * c)) * Real.sqrt Z * Real.sqrt (ρ * j * x ^ 2) =
      (Real.sqrt j / c) * (Real.sqrt Z * x) := by
  rw [Real.sqrt_mul (mul_nonneg hρ.le hj), Real.sqrt_mul hρ.le, Real.sqrt_sq hx]
  have hs : Real.sqrt ρ ≠ 0 := (Real.sqrt_pos.mpr hρ).ne'
  field_simp

lemma prefix_affine_sum_bound (E S : ℕ → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hS : ∀ s, 0 ≤ S s)
    (hE : ∀ s, E s ≤ a * S s + b) {N T : ℕ} (hNT : N ≤ T) :
    (∑ s ∈ Finset.range N, E s) ≤ a * (∑ s ∈ Finset.range T, S s) + b * T := by
  have hs := Finset.sum_le_sum (s := Finset.range N) (fun s _ => hE s)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hs
  have hp : (∑ s ∈ Finset.range N, S s) ≤ ∑ s ∈ Finset.range T, S s :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNT) (fun s _ _ => hS s)
  have hn : (N : ℝ) ≤ T := by exact_mod_cast hNT
  nlinarith [mul_le_mul_of_nonneg_left hp ha, mul_le_mul_of_nonneg_left hn hb]

lemma frozen_energy_simplify {S T τ ρ c : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hτ : 0 < τ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c) (hc1 : c ≤ 1) :
    (3 / (τ * c)) * S + 16 * ρ * T ≤ 19 * (S / τ + T) / c := by
  have hrc : ρ * c ≤ 1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hrc (mul_nonneg hτ.le hT)
  apply (le_div_iff₀ hc).2
  have he : ((3 / (τ * c)) * S + 16 * ρ * T) * c = 3 * S / τ + 16 * ρ * T * c := by
    field_simp
  rw [he]
  apply (mul_le_mul_iff_right₀ hτ).mp
  field_simp
  nlinarith

lemma current_transport_energy_product {R U W : ℝ} (hR : 0 ≤ R) (hU : 0 ≤ U)
    (hW : 0 ≤ W) (hR8 : R ≤ 8 * W) (hU32 : U ≤ 32 * W) :
    Real.sqrt R * Real.sqrt U ≤ 16 * W := by
  have hr := Real.sq_sqrt hR
  have hu := Real.sq_sqrt hU
  have hp := mul_le_mul hR8 hU32 hU (by positivity : 0 ≤ 8 * W)
  have he : (Real.sqrt R * Real.sqrt U) ^ 2 = R * U := by rw [mul_pow, hr, hu]
  have hn := mul_nonneg (Real.sqrt_nonneg R) (Real.sqrt_nonneg U)
  nlinarith

lemma geometric_linear_transport_cost {r a W : ℝ} (hr : 0 ≤ r) (hrsmall : r ≤ 91 / 100)
    (ha : 0 ≤ a) (hW : 0 ≤ W) (N : ℕ → ℝ)
    (hN : ∀ j, N j ≤ 16 * a * (j : ℝ) * r ^ j * W) (T : ℕ) :
    (1 / 10 : ℝ) * (∑ j ∈ Finset.range T, N j) ≤ 200 * a * W := by
  have hs := Finset.sum_le_sum (s := Finset.range T) (fun j _ => hN j)
  have he : (∑ j ∈ Finset.range T, 16 * a * (j : ℝ) * r ^ j * W) =
      16 * a * W * ∑ j ∈ Finset.range T, (j : ℝ) * r ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hs
  have hh := mul_le_mul_of_nonneg_left (geometric_linear_sum_bound hr hrsmall T)
    (by positivity : 0 ≤ 16 * a * W)
  linarith

lemma geometric_square_transport_cost {r a W : ℝ} (hr : 0 ≤ r) (hrsmall : r ≤ 91 / 100)
    (ha : 0 ≤ a) (hW : 0 ≤ W) (D : ℕ → ℝ)
    (hD : ∀ j, D j ≤ 32 * a * (j : ℝ) ^ 2 * r ^ j * W) (T : ℕ) :
    (1 / 10 : ℝ) * (∑ j ∈ Finset.range T, D j) ≤ 9600 * a * W := by
  have hs := Finset.sum_le_sum (s := Finset.range T) (fun j _ => hD j)
  have he : (∑ j ∈ Finset.range T, 32 * a * (j : ℝ) ^ 2 * r ^ j * W) =
      32 * a * W * ∑ j ∈ Finset.range T, (j : ℝ) ^ 2 * r ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hs
  have hh := mul_le_mul_of_nonneg_left (geometric_square_sum_bound hr hrsmall T)
    (by positivity : 0 ≤ 32 * a * W)
  linarith

lemma lag_numerator_scalar {a W c : ℝ} (ha : 0 ≤ a) (hW : 0 ≤ W)
    (hc : 0 < c) (hc1 : c ≤ 1) (j : ℕ) :
    (a / c) * (j : ℝ) * (16 * W) ≤ 16 * a * (j : ℝ) / c ^ 4 * W := by
  have hc3 : c ^ 3 ≤ 1 := pow_le_one₀ hc.le hc1
  have hpow : c ^ 4 ≤ c := by nlinarith
  have hh := div_le_div_of_nonneg_left (by positivity : 0 ≤ 16 * a * (j : ℝ) * W)
    (pow_pos hc 4) hpow
  convert hh using 1 <;> ring

lemma sqrt_power_four {b : ℝ} (hb : 0 ≤ b) (j : ℕ) :
    (Real.sqrt (b ^ j)) ^ 4 = (b ^ 2) ^ j := by
  calc
    _ = ((Real.sqrt (b ^ j)) ^ 2) ^ 2 := by ring
    _ = (b ^ j) ^ 2 := by rw [Real.sq_sqrt (pow_nonneg hb j)]
    _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm j 2]

lemma lag_denominator_cost {a W c X U D : ℝ} (ha : 0 ≤ a) (hW : 0 ≤ W)
    (hc : 0 < c) (hc1 : c ≤ 1) (hX : 0 ≤ X) (hU : 0 ≤ U)
    (hXB : X ≤ 19 * W / c) (hUB : U ≤ 32 * W) (j : ℕ)
    (hD : D ≤ (a * Real.sqrt j / c) * (j : ℝ) * (Real.sqrt X * Real.sqrt U)) :
    D ≤ 32 * a * (j : ℝ) ^ 2 / c ^ 4 * W := by
  have hp := frozen_transport_energy_product hX hU hW hc hc1 hXB hUB
  have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (a * Real.sqrt j / c) * (j : ℝ))
  have he : (a * Real.sqrt j / c) * (j : ℝ) * (32 * W / c) =
      a * (j : ℝ) * Real.sqrt j / c * (32 * W / c) := by ring
  rw [he] at hh
  exact (hD.trans hh).trans (lag_transport_scalar ha hW hc hc1 j)

lemma lag_numerator_cost {a W c R U N : ℝ} (ha : 0 ≤ a) (hW : 0 ≤ W)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 ≤ R) (hU : 0 ≤ U)
    (hR8 : R ≤ 8 * W) (hU32 : U ≤ 32 * W) (j : ℕ)
    (hN : N ≤ (a / c) * (j : ℝ) * (Real.sqrt R * Real.sqrt U)) :
    N ≤ 16 * a * (j : ℝ) / c ^ 4 * W := by
  have hp := current_transport_energy_product hR hU hW hR8 hU32
  have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (a / c) * (j : ℝ))
  exact (hN.trans hh).trans (lag_numerator_scalar ha hW hc hc1 j)

lemma geometric_bias_total {q b : ℝ} (hq : 0 ≤ q) (hb : 0 < b)
    (hrsmall : q / b ^ 2 ≤ 91 / 100) (H : ℕ → ℝ) (hH : ∀ s, 0 ≤ H s)
    (B : ℕ → ℕ → ℝ)
    (hB : ∀ s j, B s j ≤ ((j : ℝ) + 1) / (25 * (b ^ 2) ^ j) * H s) (T : ℕ) :
    (1 / 10 : ℝ) * (∑ j ∈ Finset.range T, q ^ j * (∑ s ∈ Finset.range (T - j), B s j)) ≤
      ∑ s ∈ Finset.range T, H s := by
  have hsum := Finset.sum_le_sum (s := Finset.range T) (fun j _ =>
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.range (T - j)) (fun s _ => hB s j))
      (pow_nonneg hq j))
  have hh := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have he : (1 / 10 : ℝ) * (∑ j ∈ Finset.range T, q ^ j *
      (∑ s ∈ Finset.range (T - j), ((j : ℝ) + 1) / (25 * (b ^ 2) ^ j) * H s)) =
      (1 / 250 : ℝ) * (∑ j ∈ Finset.range T, ((j : ℝ) + 1) * (q / b ^ 2) ^ j *
        (∑ s ∈ Finset.range (T - j), H s)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, div_pow]
    ring
  rw [he] at hh
  exact hh.trans (triangular_bias_sum_le (by positivity) hrsmall H hH T)

lemma triangular_linear_lower (A M B N D : ℕ → ℕ → ℝ) (w : ℕ → ℝ)
    (hw : ∀ j, 0 ≤ w j)
    (hpoint : ∀ s j, M s j - B s j - N s j - D s j ≤ A s j) (T : ℕ) :
    (∑ j ∈ Finset.range T, w j * (∑ s ∈ Finset.range (T - j), M s j)) -
      (∑ j ∈ Finset.range T, w j * (∑ s ∈ Finset.range (T - j), B s j)) -
      (∑ j ∈ Finset.range T, w j * (∑ s ∈ Finset.range (T - j), N s j)) -
      (∑ j ∈ Finset.range T, w j * (∑ s ∈ Finset.range (T - j), D s j)) ≤
      ∑ j ∈ Finset.range T, w j * (∑ s ∈ Finset.range (T - j), A s j) := by
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (hw j)
  exact Finset.sum_le_sum fun s _ => hpoint s j

lemma weighted_lag_linear_cost {q b a W : ℝ} (hq : 0 ≤ q) (hb : 0 < b)
    (hrsmall : q / b ^ 2 ≤ 91 / 100) (ha : 0 ≤ a) (hW : 0 ≤ W)
    (N : ℕ → ℝ) (hN : ∀ j, N j ≤ 16 * a * (j : ℝ) / (b ^ 2) ^ j * W) (T : ℕ) :
    (1 / 10 : ℝ) * (∑ j ∈ Finset.range T, q ^ j * N j) ≤ 200 * a * W := by
  apply geometric_linear_transport_cost (by positivity) hrsmall ha hW (fun j => q ^ j * N j) _ T
  intro j
  have hh := mul_le_mul_of_nonneg_left (hN j) (pow_nonneg hq j)
  convert hh using 1
  rw [div_pow]
  ring

lemma weighted_lag_square_cost {q b a W : ℝ} (hq : 0 ≤ q) (hb : 0 < b)
    (hrsmall : q / b ^ 2 ≤ 91 / 100) (ha : 0 ≤ a) (hW : 0 ≤ W)
    (D : ℕ → ℝ) (hD : ∀ j, D j ≤ 32 * a * (j : ℝ) ^ 2 / (b ^ 2) ^ j * W) (T : ℕ) :
    (1 / 10 : ℝ) * (∑ j ∈ Finset.range T, q ^ j * D j) ≤ 9600 * a * W := by
  apply geometric_square_transport_cost (by positivity) hrsmall ha hW (fun j => q ^ j * D j) _ T
  intro j
  have hh := mul_le_mul_of_nonneg_left (hD j) (pow_nonneg hq j)
  convert hh using 1
  rw [div_pow]
  ring

end LongTails.Proofs.AdamHeavyTailedAlgebra

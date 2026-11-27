import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory

namespace LongTails.Proofs.LogisticSpectralWork

private lemma hinge_integral (k : ℕ) {x R : ℝ} (hx : 0 ≤ x) (hR : x ≤ R) :
    (∫ t in 0..R, t^k*max (x-t) 0) =
      x^(k+2)/(((k:ℝ)+1)*((k:ℝ)+2)) := by
  have hi : Continuous (fun t : ℝ => t^k*max (x-t) 0) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable 0 x) (hi.intervalIntegrable x R)]
  have hzero : (∫ t in x..R, t^k*max (x-t) 0) = 0 := by
    calc
      _ = ∫ t in x..R, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hR] at ht
        simp [max_eq_right (sub_nonpos.mpr ht.1)]
      _ = _ := by simp
  rw [hzero,add_zero]
  calc
    _ = ∫ t in 0..x, x*t^k - t^(k+1) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      dsimp only
      rw [max_eq_left (sub_nonneg.mpr ht.2),pow_succ]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
        intervalIntegral.integral_const_mul,integral_pow,integral_pow]
      simp only [zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add, Nat.cast_one]
      field_simp
      ring

lemma signed_moment_floor {ι : Type*} [Fintype ι] (w μ : ι → ℝ)
    {a ρ R : ℝ} (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ R) (hρ : 0 ≤ ρ ∧ ρ ≤ R)
    (hprice : ∀ t ∈ Set.Icc 0 R,
      a*max (ρ-t) 0 ≤ ∑ i, w i*max (μ i-t) 0) (k : ℕ) :
    a*ρ^(k+2) ≤ ∑ i, w i*(μ i)^(k+2) := by
  have hR : 0 ≤ R := hρ.1.trans hρ.2
  have hcmp (t : ℝ) (ht : t ∈ Set.Icc 0 R) :
      a*(t^k*max (ρ-t) 0) ≤ ∑ i, w i*(t^k*max (μ i-t) 0) := by
    have hh := mul_le_mul_of_nonneg_left (hprice t ht) (pow_nonneg ht.1 k)
    rw [Finset.mul_sum] at hh
    convert hh using 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  have h := intervalIntegral.integral_mono_on (μ := volume) hR
    (f := fun t => a*(t^k*max (ρ-t) 0)) (g := fun t => ∑ i, w i*(t^k*max (μ i-t) 0))
    (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop) hcmp
  rw [intervalIntegral.integral_const_mul,hinge_integral k hρ.1 hρ.2,
    intervalIntegral.integral_finsetSum] at h
  · simp_rw [intervalIntegral.integral_const_mul] at h
    simp_rw [hinge_integral k (hμ _).1 (hμ _).2,← mul_div_assoc] at h
    rw [← Finset.sum_div] at h
    exact (div_le_div_iff_of_pos_right (by positivity)).mp h
  · intro i _
    apply Continuous.intervalIntegrable
    fun_prop

lemma paired_budget_work {d W : ℝ} (hd : 0 < d) (hW : 0 < W) (hu : W ≤ 4*d)
    (N : ℕ) (hN : 2*d ≤ N*W) :
    5*d/4 < (4*W/5) * ∑ j ∈ Finset.range N, (1-W/(4*d))^j := by
  let u := W/(4*d)
  have h0 : 0 ≤ 1-u := sub_nonneg.mpr ((div_le_one (by positivity)).mpr hu)
  have huW : u*(4*d) = W := by dsimp [u]; field_simp
  have hNu : 1/2 ≤ (N:ℝ)*u := by
    apply (le_of_mul_le_mul_right (a := 4*d) _ (by positivity))
    calc
      _ = 2*d := by ring
      _ ≤ N*W := hN
      _ = _ := by rw [mul_assoc, huW]
  have hpow : (1-u)^N ≤ Real.exp (-(1/2)) := by
    calc
      _ ≤ (Real.exp (-u))^N := pow_le_pow_left₀ h0 (by linarith [Real.add_one_le_exp (-u)]) N
      _ = Real.exp ((N:ℝ)*(-u)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hs : (64:ℝ)/39 < Real.exp (1/2) := by
    have ha := Real.exp_one_gt_d9
    have he : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    by_contra! h
    have hh := mul_self_le_mul_self (Real.exp_pos (1/2)).le h
    nlinarith
  have he : Real.exp (-(1/2)) < 39/64 := by
    rw [Real.exp_neg, inv_lt_comm₀ (by positivity) (by positivity)]
    norm_num
    exact hs
  have hg := geom_sum_mul_neg (1-u) N
  have hprod : (∑ j ∈ Finset.range N, (1-u)^j)*u = 1-(1-u)^N := by simpa using hg
  change 5*d/4 < (4*W/5) * ∑ j ∈ Finset.range N, (1-u)^j
  rw [← huW]
  calc
    _ < (16*d/5)*(1-(1-u)^N) := by nlinarith [mul_lt_mul_of_pos_left (hpow.trans_lt he) hd]
    _ = _ := by rw [← hprod]; ring

lemma signed_budget_floor {ι : Type*} [Fintype ι] (w μ : ι → ℝ)
    {d W R : ℝ} (hd : 0 < d) (hW : 0 < W) (hu : W ≤ 4*d)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ R) (hmax : 1-W/(4*d) ≤ R)
    (hm : 4*W/5 ≤ ∑ i, w i)
    (hp : ∀ t ∈ Set.Icc 0 R, (4*W/5)*max (1-W/(4*d)-t) 0 ≤
      ∑ i, w i*max (μ i-t) 0)
    (N : ℕ) (hN : 2*d ≤ N*W) :
    5*d/4 < ∑ j ∈ Finset.range N, ∑ i, w i*(μ i)^j := by
  let ρ := 1-W/(4*d)
  have hρ : 0 ≤ ρ := sub_nonneg.mpr ((div_le_one (by positivity)).mpr hu)
  refine (paired_budget_work hd hW hu N hN).trans_le ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  match j with
  | 0 => simpa using hm
  | 1 =>
    have hh := hp 0 ⟨le_rfl,hρ.trans hmax⟩
    simpa [ρ, sub_zero, max_eq_left hρ, fun i => max_eq_left (hμ i).1] using hh
  | j+2 => exact signed_moment_floor w μ hμ ⟨hρ,hmax⟩ hp j

end LongTails.Proofs.LogisticSpectralWork

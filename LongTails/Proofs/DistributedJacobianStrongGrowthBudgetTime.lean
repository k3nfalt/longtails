import LongTails.Proofs.DistributedJacobianStrongGrowthBudgetCommunication

namespace LongTails.Proofs.DistributedJacobianStrongGrowthBudgetTime

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
open DistributedJacobianStrongGrowthParameters
open DistributedJacobianStrongGrowthBudgetAlgebra
open DistributedJacobianStrongGrowthBudgetCommunication
open DistributedJacobianStrongGrowthTimeSchedule

lemma medianTime_real_bound (p : Params) :
    (medianTime p : ℝ) ≤ 2 * ((p.l : ℝ) + p.β *
      (64 + p.d * Real.log (2 * (p.n : ℝ)))) := by
  have hw := countWidth_real_bound p.n p.n.pos
  have hβ : 0 ≤ (p.β : ℝ) := p.β.coe_nonneg
  have hlatency : 0 ≤ (p.l : ℝ) := p.l.coe_nonneg
  have hd : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left hw (mul_nonneg hβ hd)
  change (p.l : ℝ) + (p.β : ℝ) * ((p.d * countWidth p.n + 64 : ℕ) : ℝ) ≤ _
  push_cast
  nlinarith

lemma refinementTime_real_bound (p : Params) (hp : valid p)
    (hn : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ))
    (hx : (1 : ℝ) / 2 < radius p (localDepth p) / p.ε) :
    (refinementTime p : ℝ) ≤ 64 * ((p.l : ℝ) + p.β *
      (64 + p.d * Real.log (2 + (p.n : ℝ) * p.d * (radius p (localDepth p) / p.ε)))) := by
  have ht := localDepth_properties p hp hn
  have hw := refinementWidth_real_bound p hp (localDepth p) ht.1 ht.2.1 ht.2.2 hx
  have hβ : 0 ≤ (p.β : ℝ) := p.β.coe_nonneg
  have hlatency : 0 ≤ (p.l : ℝ) := p.l.coe_nonneg
  have hd : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left hw (mul_nonneg hβ hd)
  change (p.l : ℝ) + (p.β : ℝ) *
    ((p.d * (refinementWidth p (localDepth p) + countWidth p.n) + 64 : ℕ) : ℝ) ≤ _
  push_cast at hh ⊢
  nlinarith

lemma refinementCount_positive_ratio (p : Params) (hp : valid p) (T : ℕ)
    (hT : 1 ≤ T) (hcount : 0 < refinementCount p T) :
    (1 : ℝ) / 2 < radius p T / p.ε := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hk : 0 < p.L / p.μ := div_pos (hμ.trans_le hp.2.2.2.2.2.2.2.1) hμ
  have ht : 0 < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have he : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hr := (radius_properties p hp T).1
  have hc : refinementCount p T = ⌈256 * ((p.L / p.μ) / (T : ℝ)) * Real.log (2 * radius p T / p.ε)⌉₊ := by
    simpa only [refinementCount, contraction, mul_assoc] using
      refinement_count_normalized (p.L / p.μ) (T : ℝ) (radius p T) p.ε
  rw [hc] at hcount
  have hprod : 0 < (256 * ((p.L / p.μ) / (T : ℝ))) * Real.log (2 * radius p T / p.ε) := Nat.ceil_pos.mp hcount
  have hl : 0 < Real.log (2 * radius p T / p.ε) := by
    by_contra h
    exact hprod.not_ge (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt h))
  have hx := (Real.log_pos_iff (by positivity : 0 ≤ 2 * radius p T / p.ε)).mp hl
  have hh : 2 * radius p T / p.ε = 2 * (radius p T / p.ε) := by ring
  rw [hh] at hx
  linarith

lemma refinementCount_continuous (p : Params) (hp : valid p) (T : ℕ) :
    refinementCount p T =
      ⌈256 * (((p.L / p.μ) / (T : ℝ)) * max (Real.log (2 * radius p T / p.ε)) 0)⌉₊ := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hk : 0 < p.L / p.μ := div_pos (hμ.trans_le hp.2.2.2.2.2.2.2.1) hμ
  have hc : refinementCount p T = ⌈256 * (((p.L / p.μ) / (T : ℝ)) * Real.log (2 * radius p T / p.ε))⌉₊ :=
    refinement_count_normalized (p.L / p.μ) (T : ℝ) (radius p T) p.ε
  rw [hc]
  by_cases hz : 0 ≤ Real.log (2 * radius p T / p.ε)
  · rw [max_eq_left hz]
  · rw [max_eq_right (le_of_not_ge hz)]
    have hn : 256 * (((p.L / p.μ) / (T : ℝ)) * Real.log (2 * radius p T / p.ε)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num)
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hz))
    rw [Nat.ceil_eq_zero.mpr hn]
    norm_num

lemma refinement_communication_bound (p : Params) (hp : valid p)
    (hn : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    (refinementCount p (localDepth p) : ℝ) * (refinementTime p : ℝ) ≤
      64 * (refinementCount p (localDepth p) : ℝ) * ((p.l : ℝ) + p.β *
        (64 + p.d * Real.log (2 + (p.n : ℝ) * p.d * (radius p (localDepth p) / p.ε)))) := by
  by_cases hz : refinementCount p (localDepth p) = 0
  · simp only [hz, Nat.cast_zero, zero_mul, mul_zero, le_refl]
  · have ht := (localDepth_properties p hp hn).1
    have hr := refinementCount_positive_ratio p hp (localDepth p) ht (Nat.pos_of_ne_zero hz)
    have hh := mul_le_mul_of_nonneg_left (refinementTime_real_bound p hp hn hr)
      (Nat.cast_nonneg (refinementCount p (localDepth p)) : (0 : ℝ) ≤ refinementCount p (localDepth p))
    nlinarith

lemma communication_envelope (p : Params) (hp : valid p)
    (hn : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    let A := 1 + Real.log ((p.d : ℝ) * (p.R / radius p (localDepth p)))
    let C := (p.l : ℝ) + p.β * (64 + p.d * Real.log (2 * (p.n : ℝ)))
    let D := (p.l : ℝ) + p.β * (64 + p.d * Real.log (2 + (p.n : ℝ) * p.d * (radius p (localDepth p) / p.ε)))
    let a := ((p.L / p.μ) / (localDepth p : ℝ)) * max (Real.log (2 * radius p (localDepth p) / p.ε)) 0
    (warmWidth p (localDepth p) : ℝ) * (medianTime p : ℝ) +
      (refinementCount p (localDepth p) : ℝ) * (refinementTime p : ℝ) ≤ 32768 * (A * C + a * D) := by
  intro A C D a
  have ht := localDepth_properties p hp hn
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hk : 0 < p.L / p.μ := div_pos (hμ.trans_le hp.2.2.2.2.2.2.2.1) hμ
  have hT : 0 < (localDepth p : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht.1)
  have he : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hr := radius_properties p hp (localDepth p)
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast hp.1
  have hnp : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n.pos
  have hq : 1 ≤ p.R / radius p (localDepth p) := (one_le_div hr.1).mpr hr.2.1
  have hratio : 1 ≤ (p.L / p.μ) / (localDepth p : ℝ) := (one_le_div hT).mpr ht.2.1
  have hx : 0 < radius p (localDepth p) / p.ε := div_pos hr.1 he
  have hA : 0 ≤ A := by
    have hh := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hd hq)
    dsimp [A]
    linarith
  have hC : 0 ≤ C := by
    have hh : 0 ≤ Real.log (2 * (p.n : ℝ)) := Real.log_nonneg (by linarith)
    dsimp [C]
    positivity
  have hD : 0 ≤ D := by
    have hh : 0 ≤ Real.log (2 + (p.n : ℝ) * p.d * (radius p (localDepth p) / p.ε)) :=
      Real.log_nonneg (by
        have hprod : 0 ≤ (p.n : ℝ) * p.d * (radius p (localDepth p) / p.ε) := by positivity
        linarith)
    dsimp [D]
    positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsmall : a < 1 → D ≤ 4 * (A * C) := by
    intro hsmall
    have hlog : 2 * radius p (localDepth p) / p.ε = 2 * (radius p (localDepth p) / p.ε) := by ring
    have hscale : ((p.L / p.μ) / (localDepth p : ℝ)) *
        max (Real.log (2 * (radius p (localDepth p) / p.ε))) 0 < 1 := by simpa only [a, hlog] using hsmall
    have hx2 := positive_log_small hratio hscale
    have hh := small_refinement_cost p.l.coe_nonneg p.β.coe_nonneg hnp hd hq hx hx2.le
    simpa only [A, C, D, mul_assoc] using hh
  have hceil := ceiling_overhead_absorption ha (mul_nonneg hA hC) hD (by norm_num : (0 : ℝ) ≤ 4) hsmall
  have hcount : refinementCount p (localDepth p) = ⌈256 * a⌉₊ := refinementCount_continuous p hp (localDepth p)
  rw [← hcount] at hceil
  have href := refinement_communication_bound p hp hn
  change (refinementCount p (localDepth p) : ℝ) * (refinementTime p : ℝ) ≤
    64 * (refinementCount p (localDepth p) : ℝ) * D at href
  have hw := warmWidth_real_bound p hp (localDepth p)
  change (warmWidth p (localDepth p) : ℝ) ≤ 128 * A at hw
  have hm := medianTime_real_bound p
  change (medianTime p : ℝ) ≤ 2 * C at hm
  have hwarm := mul_le_mul hw hm (medianTime p).coe_nonneg (by positivity : 0 ≤ 128 * A)
  nlinarith [mul_nonneg hA hC, mul_nonneg ha hD]

lemma elapsed_schedule_bound (p : Params) (hp : valid p)
    (hn : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) (hε : p.ε < p.R) :
    let A := 1 + Real.log ((p.d : ℝ) * (p.R / radius p (localDepth p)))
    let C := (p.l : ℝ) + p.β * (64 + p.d * Real.log (2 * (p.n : ℝ)))
    let D := (p.l : ℝ) + p.β * (64 + p.d * Real.log (2 + (p.n : ℝ) * p.d * (radius p (localDepth p) / p.ε)))
    let a := ((p.L / p.μ) / (localDepth p : ℝ)) * max (Real.log (2 * radius p (localDepth p) / p.ε)) 0
    (roundStart p (warmWidth p (localDepth p) + refinementCount p (localDepth p)) : ℝ) ≤
      65536 * ((((p.τ : ℝ) * p.ρ * (p.L / p.μ) ^ 2 + p.h * C) * A) +
        (p.τ : ℝ) * (p.L / p.μ) * Real.log (p.R / p.ε) + p.h * D * a) := by
  intro A C D a
  have ht := localDepth_properties p hp hn
  have hcomp := computation_count_upper p hp (localDepth p) ht.1 ht.2.1 hn hε
  change ((warmCount p (localDepth p) + 2 * localDepth p * refinementCount p (localDepth p) : ℕ) : ℝ) ≤
    1024 * (p.L / p.μ) * (p.ρ * (p.L / p.μ) * A + Real.log (p.R / p.ε)) at hcomp
  have hcomm := communication_envelope p hp hn
  change (warmWidth p (localDepth p) : ℝ) * (medianTime p : ℝ) +
    (refinementCount p (localDepth p) : ℝ) * (refinementTime p : ℝ) ≤ 32768 * (A * C + a * D) at hcomm
  have hsched : (roundStart p (warmWidth p (localDepth p) + refinementCount p (localDepth p)) : ℝ) =
      (p.τ : ℝ) * ((warmCount p (localDepth p) + 2 * localDepth p * refinementCount p (localDepth p) : ℕ) : ℝ) +
        2 * (p.h : ℝ) * ((warmWidth p (localDepth p) : ℝ) * (medianTime p : ℝ) +
          (refinementCount p (localDepth p) : ℝ) * (refinementTime p : ℝ)) := by
    simp only [roundStart, min_eq_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    push_cast
    ring
  rw [hsched]
  have hc := mul_le_mul_of_nonneg_left hcomp p.τ.coe_nonneg
  have hm := mul_le_mul_of_nonneg_left hcomm (by positivity : 0 ≤ 2 * (p.h : ℝ))
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hk : 0 < p.L / p.μ := div_pos (hμ.trans_le hp.2.2.2.2.2.2.2.1) hμ
  have hρ : 1 ≤ p.ρ := hp.2.2.2.2.2.2.2.2.1
  have he : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hr := radius_properties p hp (localDepth p)
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast hp.1
  have hq : 1 ≤ p.R / radius p (localDepth p) := (one_le_div hr.1).mpr hr.2.1
  have hA : 0 ≤ A := by
    have hh := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hd hq)
    dsimp [A]
    linarith
  have hJ : 0 ≤ Real.log (p.R / p.ε) := Real.log_nonneg ((one_le_div he).mpr hε.le)
  have hinit : 0 ≤ (p.τ : ℝ) * p.ρ * (p.L / p.μ) ^ 2 * A := by positivity
  have hacc : 0 ≤ (p.τ : ℝ) * (p.L / p.μ) * Real.log (p.R / p.ε) := by positivity
  nlinarith

end LongTails.Proofs.DistributedJacobianStrongGrowthBudgetTime

import LongTails.Proofs.DistributedJacobianStrongGrowthBudgetTime

namespace LongTails.Proofs.DistributedJacobianStrongGrowthBudgetCharacterization

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthParameters
open DistributedJacobianStrongGrowthBudgetAlgebra

lemma characterized_set_eq (p : Params) (hp : valid p)
    (hn : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) (f : ℕ → ℝ → Time) :
    {b : Time | ∃ T : ℕ, ∃ q : ℝ,
      1 ≤ T ∧ (T : ℝ) ≤ p.L / p.μ ∧
      64 * (p.L / p.μ) * growth p ^ T ≤ (p.n : ℝ) ∧
      ((p.L / p.μ) < (T + 1 : ℕ) ∨ (p.n : ℝ) < 64 * (p.L / p.μ) * growth p ^ (T + 1)) ∧
      q = 1 + 32 * p.ρ * p.M * p.R * growth p ^ T / p.μ ∧ b = f T q} =
        {f (localDepth p) (p.R / radius p (localDepth p))} := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hk : 1 ≤ p.L / p.μ := (one_le_div hμ).mpr hp.2.2.2.2.2.2.2.1
  ext b
  constructor
  · rintro ⟨T, q, _, hTk, hworkers, hnext, hq, hb⟩
    have hT : T = localDepth p := worker_depth_unique hk (growth_gt_one p hp) hn T hTk hworkers hnext
    subst T
    have hratio : q = p.R / radius p (localDepth p) := hq.trans (radius_ratio_explicit p hp (localDepth p)).symm
    rw [hratio] at hb
    exact Set.mem_singleton_iff.mpr hb
  · intro hb
    have hb' := Set.mem_singleton_iff.mp hb
    have ht := localDepth_properties p hp hn
    refine ⟨localDepth p, p.R / radius p (localDepth p), ht.1, ht.2.1, ht.2.2, ?_,
      radius_ratio_explicit p hp (localDepth p), hb'⟩
    exact worker_depth_next_infeasible hk (growth_gt_one p hp) hn

lemma characterized_inf_eq (p : Params) (hp : valid p)
    (hn : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) (f : ℕ → ℝ → Time) :
    sInf {b : Time | ∃ T : ℕ, ∃ q : ℝ,
      1 ≤ T ∧ (T : ℝ) ≤ p.L / p.μ ∧
      64 * (p.L / p.μ) * growth p ^ T ≤ (p.n : ℝ) ∧
      ((p.L / p.μ) < (T + 1 : ℕ) ∨ (p.n : ℝ) < 64 * (p.L / p.μ) * growth p ^ (T + 1)) ∧
      q = 1 + 32 * p.ρ * p.M * p.R * growth p ^ T / p.μ ∧ b = f T q} =
        f (localDepth p) (p.R / radius p (localDepth p)) := by
  rw [characterized_set_eq p hp hn f]
  exact csInf_singleton _

lemma displayed_time_nonneg (p : Params) (hp : valid p) (T : ℕ) (q : ℝ)
    (hq : 1 ≤ q) (hε : p.ε < p.R) :
    0 ≤ (((p.τ : ℝ) * p.ρ * (p.L / p.μ) ^ 2 + p.h *
      ((p.l : ℝ) + p.β * (64 + p.d * Real.log (2 * (p.n : ℝ))))) *
      (1 + Real.log (p.d * q)) + (p.τ : ℝ) * (p.L / p.μ) * Real.log (p.R / p.ε) +
      p.h * ((p.l : ℝ) + p.β *
        (64 + p.d * Real.log (2 + (p.n : ℝ) * p.d * p.R / (p.ε * q)))) *
        ((p.L / p.μ) / T * max (Real.log (2 * p.R / (p.ε * q))) 0)) := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hk : 0 < p.L / p.μ := div_pos (hμ.trans_le hp.2.2.2.2.2.2.2.1) hμ
  have hρ : 1 ≤ p.ρ := hp.2.2.2.2.2.2.2.2.1
  have he : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hR := he.trans hε
  have hqp : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast hp.1
  have hnp : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n.pos
  have hA := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hd hq)
  have hJ : 0 ≤ Real.log (p.R / p.ε) := Real.log_nonneg ((one_le_div he).mpr hε.le)
  have hC : 0 ≤ Real.log (2 * (p.n : ℝ)) := Real.log_nonneg (by linarith)
  have hD : 0 ≤ Real.log (2 + (p.n : ℝ) * p.d * p.R / (p.ε * q)) :=
    Real.log_nonneg (by
      have hh : 0 ≤ (p.n : ℝ) * p.d * p.R / (p.ε * q) := by positivity
      linarith)
  positivity

noncomputable def envelopeTime (p : Params) (T : ℕ) (q : ℝ) : Time :=
  (65536 * ((((p.τ : ℝ) * p.ρ * (p.L / p.μ) ^ 2 + p.h *
    ((p.l : ℝ) + p.β * (64 + p.d * Real.log (2 * (p.n : ℝ))))) *
    (1 + Real.log (p.d * q))) + (p.τ : ℝ) * (p.L / p.μ) * Real.log (p.R / p.ε) +
    p.h * ((p.l : ℝ) + p.β *
      (64 + p.d * Real.log (2 + (p.n : ℝ) * p.d * p.R / (p.ε * q)))) *
      ((p.L / p.μ) / T * max (Real.log (2 * p.R / (p.ε * q))) 0))).toNNReal

lemma envelopeTime_explicit_eq (p : Params) (hp : valid p) :
    envelopeTime p
      (min ⌊p.L / p.μ⌋₊
        ⌊Real.log ((p.n : ℝ) / (64 * (p.L / p.μ))) / Real.log (2 + p.ρ / 8 + p.ρ ^ 2 / 128)⌋₊)
      (1 + 32 * p.ρ * p.M * p.R * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^
        (min ⌊p.L / p.μ⌋₊
          ⌊Real.log ((p.n : ℝ) / (64 * (p.L / p.μ))) / Real.log (2 + p.ρ / 8 + p.ρ ^ 2 / 128)⌋₊) / p.μ) =
      envelopeTime p (localDepth p) (p.R / radius p (localDepth p)) := by
  change envelopeTime p (localDepth p)
    (1 + 32 * p.ρ * p.M * p.R * growth p ^ localDepth p / p.μ) = _
  rw [← radius_ratio_explicit p hp (localDepth p)]

lemma envelopeTime_suffices (p : Params) (hp : valid p)
    (hn : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) (hε : p.ε < p.R) :
    DistributedJacobianStrongGrowthTimeSchedule.roundStart p
      (warmWidth p (localDepth p) + refinementCount p (localDepth p)) ≤
        envelopeTime p (localDepth p) (p.R / radius p (localDepth p)) := by
  have hr := (radius_properties p hp (localDepth p)).1
  have hR : 0 < p.R := hp.2.2.2.2.2.2.2.2.2.2.1
  have he : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hratio : p.R / (p.ε * (p.R / radius p (localDepth p))) = radius p (localDepth p) / p.ε := by
    field_simp
  have hlog : 2 * p.R / (p.ε * (p.R / radius p (localDepth p))) = 2 * radius p (localDepth p) / p.ε := by
    field_simp
  have hbits : (p.n : ℝ) * p.d * p.R / (p.ε * (p.R / radius p (localDepth p))) =
      (p.n : ℝ) * p.d * (radius p (localDepth p) / p.ε) := by
    field_simp
  have hb := DistributedJacobianStrongGrowthBudgetTime.elapsed_schedule_bound p hp hn hε
  have hh := Real.toNNReal_le_toNNReal hb
  simpa only [envelopeTime, Real.toNNReal_coe, hlog, hbits] using hh

end LongTails.Proofs.DistributedJacobianStrongGrowthBudgetCharacterization

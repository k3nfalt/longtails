import LongTails.Setups.CohypomonotoneInclusion
import LongTails.Proofs.MultiStepAnchoredRun

namespace OracleTemplate.CohypomonotoneInclusion

open LongTails.Setups.CohypomonotoneInclusion

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 2 + (2 * ⌈2 / (1 - q.ρ * q.L) * Real.log (16 / (1 - q.ρ * q.L))⌉₊ + 3) * ⌈16 * q.L * q.R / ((1 - q.ρ * q.L) * q.ε)⌉₊

theorem result : Convergence LongTails.Setups.CohypomonotoneInclusion.spec budget := by
  refine ⟨fun p => multiStepAnchored ((1 + p.ρ * p.L) / (2 * p.L)) ((1 - p.ρ * p.L) / (2 * p.L))
    ⌈2 / (1 - p.ρ * p.L) * Real.log (16 / (1 - p.ρ * p.L))⌉₊ p.x0, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL, hρ, hr, hR, hε⟩
  let m := ⌈2 / (1 - q.ρ * q.L) * Real.log (16 / (1 - q.ρ * q.L))⌉₊
  let n := ⌈16 * q.L * q.R / ((1 - q.ρ * q.L) * q.ε)⌉₊
  let K := 2 + (2 * m + 3) * n
  have hn : ⌈16 * q.L * q.R / ((1 - q.ρ * q.L) * q.ε)⌉₊ ≤ n := le_rfl
  rintro ⟨F, H⟩ oracle ⟨J, hF, hJ, hres, hmono, hlip, hco, xs, hxs, hdist⟩
  have hyp : Hyp F H J q.L q.ρ := ⟨hres, hmono, hlip, hco⟩
  let η := (1 + q.ρ * q.L) / (2 * q.L)
  let s := (1 - q.ρ * q.L) / (2 * q.L)
  have hbudget : K = 2 + (2 * m + 3) * n := rfl
  obtain ⟨hη, hq, hP, hσ⟩ := parameter_bounds hL hρ hr m (Nat.le_ceil _)
  have hδ : 0 < 1 - q.ρ * q.L := by linarith
  have hrun := run_residual hyp hL.le hη hq hP hσ q.x0 hxs n
  have hacc : ‖gval F η (run F J η s m q.x0 n)‖ ≤ q.ε := by
    have hn : 16 * q.L * q.R / ((1 - q.ρ * q.L) * q.ε) ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
    rw [div_le_iff₀ (mul_pos hδ hε)] at hn
    have hG : 0 ≤ ‖gval F η (run F J η s m q.x0 n)‖ := norm_nonneg _
    have e : ((n : ℝ) + 1) * ((1 - q.ρ * q.L) / (2 * q.L) / 2) *
        ‖gval F η (run F J η s m q.x0 n)‖ * (4 * q.L) =
        ((n : ℝ) + 1) * (1 - q.ρ * q.L) * ‖gval F η (run F J η s m q.x0 n)‖ := by
      field_simp
      ring
    have h1 := mul_le_mul_of_nonneg_right hrun (show 0 ≤ 4 * q.L by positivity)
    rw [e] at h1
    have h2 : 4 * ‖q.x0 - xs‖ * (4 * q.L) ≤ 16 * q.L * q.R := by nlinarith
    have hpos : 0 < ((n : ℝ) + 1) * (1 - q.ρ * q.L) := by positivity
    have h3 : ((n : ℝ) + 1) * (1 - q.ρ * q.L) * ‖gval F η (run F J η s m q.x0 n)‖ ≤
        ((n : ℝ) + 1) * (1 - q.ρ * q.L) * q.ε := by nlinarith [mul_pos hδ hε]
    exact le_of_mul_le_mul_left h3 hpos
  have hexec : ∀ seed : Unit × ((k : ℕ) → oracle.Seed k),
      execute oracle (multiStepAnchored η s m q.x0) (fun _ => (K)) seed.1 seed.2 =
        (run F J η s m q.x0 n).2 := by
    rintro ⟨⟨⟩, ξ⟩
    erw [hbudget, execute_eq_of_answer_eq oracle (Sum.elim F (fun z : ℝ × q.E => J z.1 z.2))
      (by
        rintro k (x | ⟨γ, z⟩) seed
        · exact hF k seed x
        · exact hJ k seed γ z)]
    exact execute_multiStep F J η s m q.x0 n
  refine Filter.Eventually.of_forall (fun seed => ?_)
  · change ∃ ξ ∈ H (execute oracle (multiStepAnchored η s m q.x0) (fun _ => (K)) seed.1 seed.2),
      ‖F (execute oracle (multiStepAnchored η s m q.x0) (fun _ => (K)) seed.1 seed.2) + ξ‖ ≤ q.ε
    erw [hexec]
    exact ⟨η⁻¹ • ((run F J η s m q.x0 n).1 - (run F J η s m q.x0 n).2),
      hyp.mem hη (run_resolvent F J η s m q.x0 n), hacc⟩

end OracleTemplate.CohypomonotoneInclusion

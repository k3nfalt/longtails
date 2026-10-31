import LongTails.Setups.BatchedSpectralSmooth
import LongTails.Proofs.BatchedMuonRate

namespace LongTails.Theorems.MuonNoiseSeparation

open MeasureTheory OracleTemplate
open LongTails.Setups.BatchedSpectralSmooth LongTails.Algorithms.MatrixPolar
open LongTails.Algorithms.BatchedDirection LongTails.Proofs.BatchedDirectionExecution
open LongTails.Proofs.BatchedMuonRate

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (⌈64 * p.s ^ 2 / p.ε ^ 2⌉₊ + 1) * (⌈8 * p.L * p.Δ / p.ε ^ 2⌉₊ + 1)

theorem result : Convergence LongTails.Setups.BatchedSpectralSmooth.spec budget := by
  refine ⟨fun p => muon (p.ε / (2 * p.L)) (⌈64 * p.s ^ 2 / p.ε ^ 2⌉₊ + 1)
    ⌈8 * p.L * p.Δ / p.ε ^ 2⌉₊ p.x0, ?_, ?_⟩
  · intro p hp f O hadm
    obtain ⟨hL, hΔ, hs, hε⟩ := hp
    obtain ⟨hgrad, hlip, ⟨fmin, hmin, hgap⟩, model, P, hIID, rfl⟩ := hadm
    dsimp only
    set η := p.ε / (2 * p.L) with hηdef
    set B := ⌈64 * p.s ^ 2 / p.ε ^ 2⌉₊ + 1 with hBdef
    set T := ⌈8 * p.L * p.Δ / p.ε ^ 2⌉₊ with hTdef
    have hη : 0 < η := by positivity
    have hB : 0 < B := Nat.succ_pos _
    have hfol : FollowsBatched polar η B T p.x0 (muon η B T p.x0) := method_follows polar η hB T p.x0
    obtain ⟨draw, hdraw, hlaw, hA⟩ := hfol
    have hbound := average_gradient_bound hL.le hs hη hgrad hlip hmin p.x0 hgap model
      hIID hB T
    have hout := uniform_output P model.sample model.jointly_measurable (measurable_polar _ _)
      draw hdraw hlaw hA (fun X => nuclearNorm (gradient f X))
      ((LongTails.Proofs.MatrixCovariance.continuous_nuclearNorm _ _).measurable.comp
        (LongTails.Proofs.MuonProcess.measurable_gradient f)) hbound.1
    simp only at hout
    have hbudget : budget p = fun _ => B * (T + 1) := by
      funext i
      simp only [budget, hBdef, hTdef]
    rw [hbudget]
    refine ⟨hout.1, hout.2.1, (hout.2.2).trans_le ?_⟩
    · have hT1 : (0 : ℝ) < T + 1 := by positivity
      rw [div_le_iff₀ hT1]
      refine le_trans hbound.2 ?_
      have hTge : 8 * p.L * p.Δ / p.ε ^ 2 ≤ T := Nat.le_ceil _
      have hBge : 64 * p.s ^ 2 / p.ε ^ 2 ≤ (B : ℝ) := by
        have := Nat.le_ceil (64 * p.s ^ 2 / p.ε ^ 2)
        push_cast [hBdef]
        linarith
      have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
      have hnoise : 2 * (p.s / Real.sqrt B) ≤ p.ε / 4 := by
        have hsq : 8 * p.s / p.ε ≤ Real.sqrt B := by
          apply Real.le_sqrt_of_sq_le
          rw [div_pow]
          calc (8 * p.s) ^ 2 / p.ε ^ 2 = 64 * p.s ^ 2 / p.ε ^ 2 := by ring
            _ ≤ (B : ℝ) := hBge
        have hsqpos : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBpos
        rw [div_le_iff₀ (by positivity)] at hsq
        rw [mul_div_assoc', div_le_iff₀ hsqpos]
        nlinarith
      have hgapterm : p.Δ / η ≤ (T + 1) * (p.ε / 4) := by
        rw [hηdef, div_div_eq_mul_div, div_le_iff₀ hε]
        rw [div_le_iff₀ (by positivity)] at hTge
        nlinarith
      have hsmooth : p.L / 2 * η = p.ε / 4 := by
        rw [hηdef]; field_simp; ring
      rw [hsmooth]
      nlinarith
  · intro p hp
    obtain ⟨hL, _, _, hε⟩ := hp
    exact ⟨p.ε / (2 * p.L), _, _, by positivity, Nat.succ_pos _,
      method_follows polar (p.ε / (2 * p.L)) (Nat.succ_pos _) _ p.x0⟩

end LongTails.Theorems.MuonNoiseSeparation

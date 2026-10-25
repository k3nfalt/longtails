import LongTails.Proofs.AdamComparisonTuning
import LongTails.Proofs.BatchedMuonRate

namespace LongTails.Proofs.AdamComparisonUpper

open MeasureTheory OracleTemplate
open LongTails.Setups.SpectralSmoothAdamComparison
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.BatchedDirection
open LongTails.Proofs.BatchedDirectionExecution LongTails.Proofs.BatchedMuonRate

lemma muon_accuracy (p : Public) (hp : spec.valid p)
    (f : Space p.r p.r → ℝ) (O : Oracle (Space p.r p.r) (Space p.r p.r))
    (hadm : LongTails.Setups.BatchedSpectralSmooth.spec.admissible p.toBase f O) :
    let η := p.ε / (2 * p.L)
    let T := ⌈8 * p.L * p.Δ / p.ε ^ 2⌉₊
    let A := muon η 65 T p.x0
    LongTails.Setups.BatchedSpectralSmooth.spec.successful p.toBase f
      (fun z : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => 65 * (T + 1)) z.1 z.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨_, hL, _, hε, _⟩ := hp
  obtain ⟨hgrad, hlip, ⟨fmin, hmin, hgap⟩, model, P, hIID, rfl⟩ := hadm
  dsimp only [Public.toBase] at hgrad hlip hmin hgap model
  dsimp only
  set η := p.ε / (2 * p.L) with hηdef
  set T := ⌈8 * p.L * p.Δ / p.ε ^ 2⌉₊ with hTdef
  have hη : 0 < η := by positivity
  obtain ⟨draw, hdraw, hlaw, hA⟩ := method_follows polar η (by norm_num : 0 < 65) T p.x0
  have hbound := average_gradient_bound hL.le hε.le hη hgrad hlip hmin p.x0 hgap model hIID
    (by norm_num : 0 < 65) T
  have hout := uniform_output P model.sample model.jointly_measurable (measurable_polar _ _)
    draw hdraw hlaw hA (fun X => nuclearNorm (gradient f X))
    ((LongTails.Proofs.MatrixCovariance.continuous_nuclearNorm _ _).measurable.comp
      (LongTails.Proofs.MuonProcess.measurable_gradient f)) hbound.1
  refine ⟨hout.1, hout.2.1, hout.2.2.trans_le ?_⟩
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < T + 1)]
  refine hbound.2.trans ?_
  have hTge : 8 * p.L * p.Δ / p.ε ^ 2 ≤ T := Nat.le_ceil _
  have hsqrt : (8 : ℝ) ≤ Real.sqrt 65 := Real.le_sqrt_of_sq_le (by norm_num)
  have hsqrtpos : 0 < Real.sqrt (65 : ℝ) := by positivity
  have hnoise : 2 * (p.ε / Real.sqrt 65) ≤ p.ε / 4 := by
    rw [mul_div_assoc', div_le_iff₀ hsqrtpos]
    nlinarith
  have hgapterm : p.Δ / η ≤ (T + 1) * (p.ε / 4) := by
    rw [hηdef, div_div_eq_mul_div, div_le_iff₀ hε]
    rw [div_le_iff₀ (by positivity)] at hTge
    nlinarith
  have hsmooth : p.L / 2 * η = p.ε / 4 := by
    rw [hηdef]
    field_simp
    ring
  rw [hsmooth]
  norm_num only [Nat.cast_ofNat] at *
  dsimp only [Public.toBase]
  have hn := mul_le_mul_of_nonneg_left hnoise (show (0 : ℝ) ≤ T + 1 by positivity)
  nlinarith

end LongTails.Proofs.AdamComparisonUpper

import LongTails.Proofs.SeparationTrajectory
import LongTails.Proofs.BatchedMuonRate
import LongTails.Proofs.AdaptiveIID

namespace LongTails.Proofs.SeparationSuccess

open MeasureTheory ProbabilityTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.BatchedDirection
open LongTails.Setups.BatchedSpectralSmooth
open LongTails.Proofs.DiagonalSpectral LongTails.Proofs.SeparationInstance
open LongTails.Proofs.SeparationModel LongTails.Proofs.GaussianBlocks
open LongTails.Proofs.BatchedDirectionExecution LongTails.Proofs.BatchedMuonRate

noncomputable def gaussianOracle {m n : ℕ} (g : Space m n → ℝ → Space m n) :
    Oracle (Space m n) (Space m n) where
  Seed := fun _ => ℝ
  law := (⟨stdStream, inferInstance⟩ : ProbabilityMeasure (ℕ → ℝ))
  answer := fun _ q ω => g q.2 ω

lemma measurable_frobeniusNormalize (m n : ℕ) :
    Measurable (frobeniusNormalize (m := m) (n := n)) := by
  unfold frobeniusNormalize
  fun_prop

lemma success_sum {p : Public} {f : Space p.m p.n → ℝ} {g : Space p.m p.n → ℝ → Space p.m p.n}
    (hg : Measurable (Function.uncurry g)) {direction : Space p.m p.n → Space p.m p.n}
    (hdir : Measurable direction) {η : ℝ} {B T : ℕ}
    {A : Algorithm (Space p.m p.n) (Space p.m p.n) (Space p.m p.n)}
    (hA : FollowsBatched direction η B T p.x0 A)
    (hi : ∀ t, Integrable (fun ξ => nuclearNorm (gradient f
      (sampledIterate direction η B p.x0 g ξ t))) stdStream)
    (hsucc : spec.successful p f
      (fun z : A.Seed × (ℕ → ℝ) => execute (gaussianOracle g) A (fun _ => B * (T + 1)) z.1 z.2)
      (⟨(A.law : Measure _).prod stdStream, inferInstance⟩ :
        ProbabilityMeasure (A.Seed × (ℕ → ℝ)))) :
    (∑ t ∈ Finset.range (T + 1), ∫ ξ, nuclearNorm (gradient f
      (sampledIterate direction η B p.x0 g ξ t)) ∂stdStream) ≤ (T + 1) * p.ε := by
  obtain ⟨draw, hdraw, hlaw, hA'⟩ := hA
  have hF : Measurable (fun X : Space p.m p.n => nuclearNorm (gradient f X)) :=
    (MatrixCovariance.continuous_nuclearNorm _ _).measurable.comp
      (MuonProcess.measurable_gradient f)
  have hout := uniform_output (⟨stdStream, inferInstance⟩ : ProbabilityMeasure (ℕ → ℝ)) g hg hdir
    draw hdraw hlaw hA'
    (fun X => nuclearNorm (gradient f X)) hF hi
  obtain ⟨_, _, hle⟩ := hsucc
  simp only at hout
  have h2 : (∑ t ∈ Finset.range (T + 1), ∫ ξ, nuclearNorm (gradient f
      (sampledIterate direction η B p.x0 g ξ t)) ∂stdStream) / (T + 1) ≤ p.ε :=
    (hout.2.2).symm.trans_le hle
  rw [div_le_iff₀ (by positivity)] at h2
  linarith

lemma separation_admissible {p : Public} (hm : 0 < p.m) {ℓ c τ : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 ≤ c)
    (hτ : 0 ≤ τ) (hτs : τ ≤ p.s) (φ : FlatShape)
    (hL : ℓ + (min p.m p.n - 1 : ℕ) * (c * φ.lip) ≤ p.L) (hr : 0 < min p.m p.n)
    (fmin : ℝ) (hmin : ∀ X, fmin ≤ objective ℓ c φ p.x0 X)
    (hgap : objective ℓ c φ p.x0 p.x0 - fmin ≤ p.Δ) :
    spec.admissible p (objective ℓ c φ p.x0) (gaussianOracle (sample ℓ c τ φ p.x0)) := by
  refine ⟨fun X => by
      rw [gradient_objective]; exact hasGradientAt_objective ℓ c φ p.x0 X, ?_, ⟨fmin, hmin, hgap⟩,
    raise (model ℓ c τ φ p.x0 hτ hm) hτs,
    (⟨stdStream, inferInstance⟩ : ProbabilityMeasure (ℕ → ℝ)),
    OracleTemplate.StochasticGeneralized.infinitePi_iid _, rfl⟩
  intro X Y
  refine (lipschitz_objective hℓ hc φ p.x0 X Y).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  show (∑ i : Fin (min p.m p.n), if i.val = 0 then ℓ else c * φ.lip) ≤ p.L
  rw [LongTails.Proofs.SeparationTrajectory.sum_stiff_split hr]
  exact hL

end LongTails.Proofs.SeparationSuccess

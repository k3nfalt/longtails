import LongTails.Proofs.MultirateMoments

namespace LongTails.Proofs.MultirateVariance

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.MultirateSchedule
open MultirateCausality MultirateTrajectory MultiratePackets MultirateMoments

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {f : Functions p}

noncomputable def coeff (p : Params) (i : Fin p.n) : ℝ := (p.n * (batch p i : ℝ))⁻¹

lemma error_sum (s : Samples p) (k : ℕ) :
    average p (replies g s k) - MultirateStaleness.stale g s f k =
      ∑ a : Index p, coeff p a.1 • noiseAt g f k a s := by
  unfold MultiratePackets.average MultirateStaleness.stale
  rw [ ← smul_sub, ← Finset.sum_sub_distrib, Finset.smul_sum,
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  have hb : (batch p i : ℝ) ≠ 0 := by exact_mod_cast (batch p i).pos.ne'
  simp only [mean_eq,coeff,mul_inv_rev,noiseAt,basePoint,smul_sub,Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [← Finset.smul_sum, smul_smul, smul_smul]
  congr 1 <;> congr 1 <;> field_simp

lemma adaptive_variance {P : Measure (Samples p)} [IsProbabilityMeasure P]
    {μ : Fin p.n → ProbabilityMeasure p.Ω}
    (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hi : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) P)
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (hm : ∀ i, Measurable (gradient (f i)))
    (hh : ∀ i, 0 < p.h i) (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε) (k : ℕ) :
    let e := fun s => ‖average p (replies g s k) - MultirateStaleness.stale g s f k‖^2
    Integrable e P ∧ (∫ s, e s ∂P) ≤ δ p ^ 2 := by
  classical
  let X := fun (a : Index p) (s : Samples p) => coeff p a.1 • noiseAt g f k a s
  have hu (a b : Index p) : Integrable (fun s => ⟪X a s, X b s⟫) P := by
    simp only [X, real_inner_smul_left,real_inner_smul_right]
    exact ((inner_integrable hw hi hsg hm k a b).const_mul _).const_mul _
  have he (s : Samples p) : ‖average p (replies g s k) - MultirateStaleness.stale g s f k‖^2 =
      ∑ a, ∑ b, ⟪X a s, X b s⟫ := by
    rw [error_sum, ← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
    rfl
  dsimp only
  simp_rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hu i j)), ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hu i j))]
  have hb (a : Index p) : (∫ s, ∑ b, ⟪X a s, X b s⟫ ∂P) ≤ coeff p a.1 ^ 2 * p.σ a.1 ^ 2 := by
    rw [integral_finsetSum _ (fun b _ => hu a b), Finset.sum_eq_single a]
    · simp only [real_inner_self_eq_norm_sq,X,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,integral_const_mul]
      exact mul_le_mul_of_nonneg_left (diagonal hw hi hsg hm k a).2 (sq_nonneg _)
    · intro b _ hn
      simp only [X,real_inner_smul_left, real_inner_smul_right,integral_const_mul,
        inner_zero hw hi hsg hm k a b hn.symm, mul_zero]
    · simp
  apply (Finset.sum_le_sum (fun a _ => hb a)).trans
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply le_trans _ (MultirateService.variance hh hσ hε)
  apply Finset.sum_le_sum
  intro i _
  apply le_of_eq
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.pos.ne'
  have hm' : (batch p i : ℝ) ≠ 0 := by exact_mod_cast (batch p i).pos.ne'
  unfold coeff
  field_simp

end LongTails.Proofs.MultirateVariance

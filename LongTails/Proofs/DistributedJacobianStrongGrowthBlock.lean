import LongTails.Algorithms.DistributedLocalExtragradient
import LongTails.Proofs.LocalNonlinearExtragradientMean
import LongTails.Proofs.LocalNonlinearExtragradientAveraging

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.DistributedJacobianStrongGrowthBlock

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradient

lemma measurable_blockOutput (p : Params) (T N : ℕ) (H : ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) :
    Measurable (fun z : Point p × (ℕ → p.Ω) => blockOutput p T N H g z.1 z.2) := by
  have hm (i : Fin p.n) : Measurable (fun z : Point p × (ℕ → p.Ω) =>
      z.1 + OracleTemplate.clip H
        (LongTails.Algorithms.LocalNonlinearExtragradient.run (1 / (4 * p.L)) (g i) z.1
          (fun k => z.2 (N + (p.n * k + i.val))) T - z.1)) := by
    have hread : Measurable (fun z : Point p × (ℕ → p.Ω) =>
        fun k => z.2 (N + (p.n * k + i.val))) :=
      Measurable.of_eval fun k => (measurable_pi_apply _).comp measurable_snd
    have hrun := (LocalNonlinearExtragradientSampling.measurable_run_joint
      (1 / (4 * p.L)) (g i) (hg i) T).comp (measurable_fst.prodMk hread)
    exact measurable_fst.add ((OracleTemplate.measurable_clip H).comp (hrun.sub measurable_fst))
  exact (Finset.measurable_sum _ (fun i _ => hm i)).const_smul (1 / (p.n : ℝ))

lemma blockOutput_centered (p : Params) (T N : ℕ) (H : ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p) (x y : Point p) (samples : ℕ → p.Ω) :
    blockOutput p T N H g x samples - y =
      (1 / (p.n : ℝ)) • ∑ i : Fin p.n, ((x - y) + OracleTemplate.clip H
        (LongTails.Algorithms.LocalNonlinearExtragradient.run (1 / (4 * p.L)) (g i) x
          (fun k => samples (N + (p.n * k + i.val))) T - x)) := by
  have hn : (p.n : ℝ) ≠ 0 := by positivity
  have he (v : Point p) : (x - y) + v = (x + v) - y := by abel
  simp_rw [he]
  rw [Finset.sum_sub_distrib, smul_sub]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [hn, blockOutput]

lemma local_block_contraction (p : Params) (hp : valid p) (I : Problem p)
    (hI : problemAssumptions p I)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (hg : oracleAssumptions p I g S) (T N : ℕ) {r : ℝ} (hr : 0 < r)
    (hT : 1 ≤ T) (hTκ : (T : ℝ) ≤ p.L / p.μ)
    (hn : 64 * (p.L / p.μ) * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T ≤ (p.n : ℝ))
    (hguard : p.M * r ≤ p.L /
      (16 * (p.L / p.μ) * p.ρ * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T))
    (x : Point p) (hx : ‖x - I.solution‖ ≤ r) :
    let H := 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T
    Integrable (fun ω => ‖blockOutput p T N H g x (fun k => S.sample k ω) - I.solution‖ ^ 2)
      (S.law : Measure _) ∧
    (∫ ω, ‖blockOutput p T N H g x (fun k => S.sample k ω) - I.solution‖ ^ 2
      ∂(S.law : Measure _)) ≤ (1 - (T : ℝ) / (64 * (p.L / p.μ))) * ‖x - I.solution‖ ^ 2 := by
  classical
  rcases hp with ⟨_, _, _, _, _, _, hμ, hμL, hρ, hM, _, _, _⟩
  rcases hI with ⟨hd, hlip, hJ, hroot, _, hmono⟩
  rcases hg with ⟨hgm, hgi, hg2, hmean, hsgc⟩
  let κ : ℝ := p.L / p.μ
  let G : ℝ := 2 + p.ρ / 8 + p.ρ ^ 2 / 128
  let B : ℝ := G ^ T
  let d : ℝ := ‖x - I.solution‖
  let H : ℝ := 256 * κ * (B + 1) * r / T
  let X : Fin p.n → S.Seed → Point p := fun i ω =>
    LongTails.Algorithms.LocalNonlinearExtragradient.run (1 / (4 * p.L)) (g i) x
      (fun k => S.sample (N + (p.n * k + i.val)) ω) T - I.solution
  have hL : 0 < p.L := lt_of_lt_of_le hμ hμL
  have hρ0 : 0 ≤ p.ρ := by linarith
  have hκ : 1 ≤ κ := (one_le_div hμ).mpr hμL
  have hκ0 : 0 < κ := by linarith
  have hG : 1 ≤ G := by dsimp [G]; nlinarith [sq_nonneg p.ρ]
  have hB : 1 ≤ B := one_le_pow₀ hG
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : (0 : ℝ) < T := by linarith
  have hH : 0 < H := by dsimp [H]; positivity
  have hc : ‖x - I.solution‖ ≤ H := by
    apply hx.trans
    dsimp [H]
    apply (le_div_iff₀ ht0).mpr
    have hh : (T : ℝ) ≤ 256 * κ * (B + 1) := by
      have hh' : κ ≤ 256 * κ * (B + 1) := by nlinarith
      exact hTκ.trans hh'
    nlinarith [mul_le_mul_of_nonneg_right hh hr.le]
  have hm (y : Point p) : 0 ≤ ⟪y - I.solution, I.F y⟫ := by
    rw [real_inner_comm]
    exact (mul_nonneg hμ.le (sq_nonneg _)).trans (hmono y)
  have hl (y : Point p) : ‖I.F y‖ ^ 2 ≤ p.L ^ 2 * ‖y - I.solution‖ ^ 2 := by
    have hh := hlip y I.solution
    rw [hroot, sub_zero] at hh
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (I.F y)) hh 2
  have hIID (i : Fin p.n) := LocalNonlinearExtragradientSampling.interleaved_worker_iid
    (S.law : Measure _) (S.marginal : Measure _) S.sample S.iid p.n.pos N i
  have hXs (i : Fin p.n) := LocalNonlinearExtragradientIteration.run_second_moment
    (S.law : Measure _) (S.marginal : Measure _) I.solution x I.F (g i)
    (fun k => S.sample (N + (p.n * k + i.val))) hL hρ0 (hgm i) (hIID i)
    (hgi i) (hg2 i) (hmean i) (hsgc i) hm hl T
  have hXm (i : Fin p.n) : Measurable (X i) :=
    ((LocalNonlinearExtragradientSampling.measurable_run (1 / (4 * p.L)) (g i) x (hgm i) T).comp
      (Measurable.of_eval (hIID i).measurable)).sub_const I.solution
  have hXi (i : Fin p.n) : Integrable (X i) (S.law : Measure _) := by
    apply ((integrable_const (1 : ℝ)).add (hXs i).1).mono' (hXm i).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    change ‖X i ω‖ ≤ 1 + ‖X i ω‖ ^ 2
    nlinarith [sq_nonneg (‖X i ω‖ - 1 / 2)]
  have hXmean (i : Fin p.n) : ‖∫ ω, X i ω ∂(S.law : Measure _)‖ ≤
      (1 - 3 * (T : ℝ) / (64 * κ)) * d := by
    have hh := LocalNonlinearExtragradientMean.run_mean_bound
      (S.law : Measure _) (S.marginal : Measure _) I.solution x I.F I.J (g i)
      (fun k => S.sample (N + (p.n * k + i.val))) hL hμ.le hμL hρ hM hd hJ hroot hlip hmono
      (hgm i) (hIID i) (hgi i) (hg2 i) (hmean i) (hsgc i) T
    have he : p.μ / (8 * p.L) = 1 / (8 * κ) := by dsimp [κ]; field_simp
    rw [he] at hh
    apply LocalNonlinearExtragradientBlock.local_power_mean_margin T hκ (by linarith) hL
      (norm_nonneg _) hG hTκ _ hh
    exact (mul_le_mul_of_nonneg_left hx hM).trans hguard
  have hindX : iIndepFun X (S.law : Measure _) :=
    (LocalNonlinearExtragradientSampling.interleaved_runs_independent
      (S.law : Measure _) (S.marginal : Measure _) S.sample S.iid p.n.pos N T
      (1 / (4 * p.L)) g x hgm).comp
      (fun _ z => z - I.solution) (fun _ => measurable_id.sub_const I.solution)
  have ha : 0 ≤ (1 - 3 * (T : ℝ) / (64 * κ)) * d := by
    have hh : 3 * (T : ℝ) / (64 * κ) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    exact mul_nonneg (by linarith) (norm_nonneg _)
  have hb := LocalNonlinearExtragradientAveraging.clipped_independent_average_bound
    p.n.pos X (x - I.solution) hH hc hindX hXm hXi (fun i => (hXs i).1)
    ha hXmean (fun i => (hXs i).2)
  have he (ω : S.Seed) : blockOutput p T N H g x (fun k => S.sample k ω) - I.solution =
      (1 / (p.n : ℝ)) • ∑ i : Fin p.n,
        ((x - I.solution) + OracleTemplate.clip H (X i ω - (x - I.solution))) := by
    rw [blockOutput_centered]
    congr 2
    funext i
    congr 2
    dsimp [X]
    abel
  dsimp only
  change Integrable (fun ω => ‖blockOutput p T N H g x (fun k => S.sample k ω) - I.solution‖ ^ 2)
    (S.law : Measure _) ∧
    (∫ ω, ‖blockOutput p T N H g x (fun k => S.sample k ω) - I.solution‖ ^ 2
      ∂(S.law : Measure _)) ≤ (1 - (T : ℝ) / (64 * κ)) * d ^ 2
  simp_rw [he]
  refine ⟨hb.1, ?_⟩
  exact hb.2.trans (LocalNonlinearExtragradientBlock.clipped_parameter_contraction
    hκ ht hTκ hB (norm_nonneg _) hr hx hn)

end LongTails.Proofs.DistributedJacobianStrongGrowthBlock

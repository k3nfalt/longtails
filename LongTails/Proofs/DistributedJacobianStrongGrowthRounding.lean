import LongTails.Proofs.DistributedJacobianStrongGrowthHistory
import LongTails.Proofs.DistributedJacobianStrongGrowthProjection
import LongTails.Proofs.LocalExtragradientQuantization

open MeasureTheory

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRounding

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradient

lemma measurable_roundedBlockOutput (p : Params) (T N : ℕ) (H : ℝ)
    (width : ℕ) (spacing : ℝ) (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) :
    Measurable (fun z : Point p × (ℕ → p.Ω) => roundedBlockOutput p T N H width spacing g z.1 z.2) := by
  have hm : Measurable (fun z : Point p × (ℕ → p.Ω) => fun i : Fin p.n =>
      OracleTemplate.clip H
        (LongTails.Algorithms.LocalNonlinearExtragradient.run (1 / (4 * p.L)) (g i) z.1
          (fun k => z.2 (N + (p.n * k + i.val))) T - z.1)) := by
    apply Measurable.of_eval
    intro i
    have hread : Measurable (fun z : Point p × (ℕ → p.Ω) =>
        fun k => z.2 (N + (p.n * k + i.val))) :=
      Measurable.of_eval fun k => (measurable_pi_apply _).comp measurable_snd
    have hrun := (LocalNonlinearExtragradientSampling.measurable_run_joint
      (1 / (4 * p.L)) (g i) (hg i) T).comp (measurable_fst.prodMk hread)
    exact (OracleTemplate.measurable_clip H).comp (hrun.sub measurable_fst)
  exact measurable_fst.add ((LocalExtragradientQuantization.measurable_quantizedAverage
    p.n p.d width spacing).comp hm)

lemma roundedBlockOutput_error (p : Params) (T N : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (width : ℕ) (spacing : ℝ) (hs : 0 < spacing)
    (hrange : H ≤ spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2)
    (g : Fin p.n → Point p → p.Ω → Point p) (x : Point p) (samples : ℕ → p.Ω) :
    ‖roundedBlockOutput p T N H width spacing g x samples - blockOutput p T N H g x samples‖ ≤
      Real.sqrt p.d * spacing := by
  let v : Fin p.n → Point p := fun i => OracleTemplate.clip H
    (LongTails.Algorithms.LocalNonlinearExtragradient.run (1 / (4 * p.L)) (g i) x
      (fun k => samples (N + (p.n * k + i.val))) T - x)
  have hb := DistributedJacobianStrongGrowthBlock.blockOutput_centered p T N H g x x samples
  have he : blockOutput p T N H g x samples = x + (1 / (p.n : ℝ)) • ∑ i, v i := by
    simp only [sub_self, zero_add] at hb
    change blockOutput p T N H g x samples - x = (1 / (p.n : ℝ)) • ∑ i, v i at hb
    rw [sub_eq_iff_eq_add] at hb
    simpa only [add_comm] using hb
  rw [he]
  change ‖(x + LongTails.Algorithms.LocalExtragradientQuantization.quantizedAverage
    p.n p.d width spacing v) - (x + (1 / (p.n : ℝ)) • ∑ i, v i)‖ ≤ _
  rw [add_sub_add_left_eq_sub]
  exact LocalExtragradientQuantization.quantizedAverage_error_of_norm
    p.n p.d width p.n.pos spacing hs v H (fun _ => OracleTemplate.norm_clip_le hH _) hrange

end LongTails.Proofs.DistributedJacobianStrongGrowthRounding

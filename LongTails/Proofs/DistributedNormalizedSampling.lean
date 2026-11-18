import LongTails.Algorithms.DistributedNormalizedDownlink
import LongTails.Proofs.DistributedSparseCompression
import Mathlib.Probability.HasLaw

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.DistributedNormalizedSampling

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedDownlink

attribute [local irreducible] LongTails.Algorithms.DistributedNormalizedCompression.fullReceive
  LongTails.Algorithms.DistributedRandomRounding.message

lemma draw_block_law (p : Params) [Nonempty (Fin p.d)] (m offset : ℕ) :
    HasLaw (fun θ : ℕ → Fin p.d × ℝ => fun q : Fin m => θ (offset + q.val))
      (Measure.pi fun _ : Fin m => (drawLaw p : Measure (Fin p.d × ℝ)))
      (Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))) := by
  have hinj : Function.Injective (fun q : Fin m => offset + q.val) := by
    intro a b h
    exact Fin.ext (Nat.add_left_cancel h)
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ)))
    (X := fun _ => id) (fun _ => measurable_id)
  refine ⟨(Measurable.of_eval fun q => measurable_pi_apply (offset + q.val)).aemeasurable, ?_⟩
  have hm := (hind.precomp hinj).map_fun_eq_pi_map
    (fun q : Fin m => (measurable_pi_apply (offset + q.val)).aemeasurable)
  simpa only [id_eq, Measure.infinitePi_map_eval] using hm

lemma draw_dither_law (p : Params) [Nonempty (Fin p.d)] :
    (drawLaw p : Measure (Fin p.d × ℝ)).map Prod.snd =
      (LongTails.Algorithms.DistributedRandomRounding.uniform : Measure ℝ) := by
  simp only [drawLaw, ProbabilityMeasure.coe_mk, Measure.map_snd_prod, measure_univ, one_smul]

lemma dither_block_law (p : Params) [Nonempty (Fin p.d)] (m offset : ℕ) :
    HasLaw (fun θ : ℕ → Fin p.d × ℝ => fun q : Fin m => (θ (offset + q.val)).2)
      (Measure.pi fun _ : Fin m => (LongTails.Algorithms.DistributedRandomRounding.uniform : Measure ℝ))
      (Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))) := by
  let f := fun z : Fin m → Fin p.d × ℝ => fun q => (z q).2
  let b := fun θ : ℕ → Fin p.d × ℝ => fun q : Fin m => θ (offset + q.val)
  have hf : Measurable f := Measurable.of_eval fun q => measurable_snd.comp (measurable_pi_apply q)
  have hb : Measurable b := Measurable.of_eval fun q => measurable_pi_apply (offset + q.val)
  have hμ := draw_dither_law p
  have : IsProbabilityMeasure ((drawLaw p : Measure (Fin p.d × ℝ)).map Prod.snd) := hμ.symm ▸ inferInstance
  refine ⟨(hf.comp hb).aemeasurable, ?_⟩
  change (Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))).map (f ∘ b) = _
  rw [← Measure.map_map hf hb, (draw_block_law p m offset).map_eq]
  change (Measure.pi fun _ : Fin m => (drawLaw p : Measure (Fin p.d × ℝ))).map
    (fun z q => (z q).2) = _
  rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
  simp only [hμ]

lemma sparse_stream_moments (p : Params) [Nonempty (Fin p.d)]
    (width m offset : ℕ) (hm : 0 < m) {spacing : ℝ} (hs : 0 < spacing)
    (x : Point p)
    (hx : ∀ j, |(p.d : ℝ) * x j| ≤ spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1)) :
    let P := Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))
    let Y := fun θ : ℕ → Fin p.d × ℝ =>
      LongTails.Algorithms.DistributedNormalizedCompression.sparseReceive width m spacing
        (fun q => (θ (offset + q.val)).1)
        (LongTails.Algorithms.DistributedNormalizedCompression.sparseMessage width m spacing x
          (fun q => (θ (offset + q.val)).1) (fun q => (θ (offset + q.val)).2))
    Integrable Y P ∧ (∫ θ, Y θ ∂P) = x ∧
      Integrable (fun θ => ‖Y θ - x‖ ^ 2) P ∧
      (∫ θ, ‖Y θ - x‖ ^ 2 ∂P) ≤
        (((p.d : ℝ) - 1) * ‖x‖ ^ 2 + spacing ^ 2 / 4) / m := by
  intro P Y
  obtain ⟨hi, he, h2, hv⟩ := DistributedSparseCompression.sparse_message_moments width m hm hs x hx
  have hl := draw_block_law p m offset
  refine ⟨hl.integrable_comp hi, ?_, hl.integrable_comp h2, ?_⟩
  · exact (hl.integral_comp hi.aestronglyMeasurable).trans he
  · exact (hl.integral_comp h2.aestronglyMeasurable).trans_le hv

lemma stream_dither_preserving (p : Params) [Nonempty (Fin p.d)] (j : ℕ) :
    MeasurePreserving (fun θ : ℕ → Fin p.d × ℝ => (θ j).2)
      (Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ)))
      (LongTails.Algorithms.DistributedRandomRounding.uniform : Measure ℝ) := by
  refine ⟨measurable_snd.comp (measurable_pi_apply j), ?_⟩
  change (Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))).map
    (Prod.snd ∘ (fun θ => θ j)) = _
  rw [← Measure.map_map measurable_snd (measurable_pi_apply j),
    Measure.infinitePi_map_eval, draw_dither_law]

set_option maxHeartbeats 800000 in
lemma full_stream_moments (p : Params) [Nonempty (Fin p.d)]
    (width offset : ℕ) {spacing : ℝ} (hs : 0 < spacing) (x : Point p)
    (hx : ∀ j, |x j| ≤ spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1)) :
    let P := Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))
    let Y := fun θ : ℕ → Fin p.d × ℝ =>
      LongTails.Algorithms.DistributedNormalizedCompression.fullReceive p.d width spacing
        (LongTails.Algorithms.DistributedRandomRounding.message p.d width spacing x
          (fun j => (θ (offset + j.val)).2))
    Integrable Y P ∧ (∫ θ, Y θ ∂P) = x ∧
      Integrable (fun θ => ‖Y θ - x‖ ^ 2) P ∧
      (∫ θ, ‖Y θ - x‖ ^ 2 ∂P) ≤ p.d * spacing ^ 2 / 4 := by
  intro P Y
  have hdecode (θ : ℕ → Fin p.d × ℝ) :
      Y θ = LongTails.Algorithms.DistributedQuantization.reconstruct spacing
        (LongTails.Algorithms.DistributedRandomRounding.grid p.d width spacing x
          (fun j => (θ (offset + j.val)).2)) := by
    exact (congrArg (LongTails.Algorithms.DistributedNormalizedCompression.fullReceive p.d width spacing)
      (List.append_nil _)).symm.trans (DistributedNormalizedCompression.full_receive_message
        p.d width spacing x (fun j => (θ (offset + j.val)).2) [])
  change Integrable (fun θ => Y θ) P ∧ _
  simp_rw [hdecode]
  exact DistributedCompressionMoments.full_grid_moments p.d width hs x
    (fun (θ : ℕ → Fin p.d × ℝ) (j : Fin p.d) => (θ (offset + j.val)).2) (fun j => stream_dither_preserving p (offset + j.val)) hx

end LongTails.Proofs.DistributedNormalizedSampling

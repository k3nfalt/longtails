import LongTails.Proofs.ClusteredConvolutionalPerceptronExecution
import LongTails.Proofs.ClusteredConvolutionalPerceptronParameters

namespace LongTails.Proofs.ClusteredConvolutionalPerceptronConvergence

open LongTails.Setups.ClusteredConvolutionalPerceptron
open LongTails.Algorithms.ClusteredConvolutionalPerceptron
open ClusteredConvolutionalPerceptronParameters
open ClusteredConvolutionalPerceptronGeometry
open ClusteredConvolutionalPerceptronExecution

lemma upper_pos (p : Params) (hp : spec.valid p) : 0 < p.upper := hp.2.1.trans_le hp.2.2.1

lemma rho_pos (p : Params) (hp : spec.valid p) : 0 < p.lower / (4 * p.upper) := by
  have hg := hp.2.1
  have hR := upper_pos p hp
  positivity

lemma rho_le (p : Params) (hp : spec.valid p) : p.lower / (4 * p.upper) ≤ 1 := by
  have hR := upper_pos p hp
  apply (div_le_iff₀ (by positivity : 0 < 4 * p.upper)).mpr
  linarith [hp.2.2.1]

lemma delta_pos (p : Params) (hp : spec.valid p) : 0 < (p.contrast / (4 * p.upper)) ^ 2 := by
  have hR := upper_pos p hp
  have hμ := hp.2.2.2.1
  positivity

noncomputable def tuning (p : Params) (hp : spec.valid p) : ClusteredConvolutionalPerceptronDynamics.Control :=
  control p.derivativeMargin (p.lower / (4 * p.upper)) ((p.contrast / (4 * p.upper)) ^ 2)
    hp.2.2.2.2.1 hp.2.2.2.2.2.1 (rho_pos p hp) (rho_le p hp) (delta_pos p hp) hp.2.2.2.2.2.2

lemma budget_eq (p : Params) (hp : spec.valid p) :
    (p.samples + 1) * (⌈8 / (tuning p hp).ρ ^ 2 * Real.log (1 / (tuning p hp).δ)⌉₊ + 3) =
      (p.samples + 1) * (⌈128 * p.upper ^ 2 / p.lower ^ 2 *
        Real.log (16 * p.upper ^ 2 / p.contrast ^ 2)⌉₊ + 3) := by
  have hg : p.lower ≠ 0 := ne_of_gt hp.2.1
  have hR : p.upper ≠ 0 := ne_of_gt (upper_pos p hp)
  have hμ : p.contrast ≠ 0 := ne_of_gt hp.2.2.2.1
  have hr : 8 / (p.lower / (4 * p.upper)) ^ 2 = 128 * p.upper ^ 2 / p.lower ^ 2 := by
    field_simp
    ring
  have hd : 1 / (p.contrast / (4 * p.upper)) ^ 2 = 16 * p.upper ^ 2 / p.contrast ^ 2 := by
    field_simp
    ring
  change (p.samples + 1) * (⌈8 / (p.lower / (4 * p.upper)) ^ 2 *
    Real.log (1 / (p.contrast / (4 * p.upper)) ^ 2)⌉₊ + 3) = _
  rw [hr, hd]

lemma output_eq_iterate (p : Params) (D : Data p.dimension p.samples)
    (O : OracleTemplate.Oracle (Query p.dimension p.samples) (Reply p.dimension))
    (hlaw : ∀ history query seed, O.answer history query seed = answer D query.2)
    (K : ℕ) (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    output p O K seed ξ =
      (((step D (1 / (4 * p.upper)))^[K]
        ((algorithm p).initial seed)).point) := by
  unfold output
  rw [OracleTemplate.execute_eq_of_answer_eq O (answer D) (fun h q s => hlaw h (0, q) s),
    OracleTemplate.execute_iterate]
  rfl

lemma tuned_iterate (p : Params) (hp : spec.valid p) {D : Data p.dimension p.samples}
    (G : Geometry D p.lower p.upper p.contrast p.derivativeMargin) (seed : (algorithm p).Seed) :
    Separates D ((step D (1 / (4 * p.upper)))^[(p.samples + 1) *
      (⌈128 * p.upper ^ 2 / p.lower ^ 2 * Real.log (16 * p.upper ^ 2 / p.contrast ^ 2)⌉₊ + 3)]
      ((algorithm p).initial seed)).point := by
  have hR := upper_pos p hp
  have hη : 0 < 1 / (4 * p.upper) := by positivity
  have hδ : (tuning p hp).δ = (1 / (4 * p.upper) * p.contrast) ^ 2 := by
    simp only [tuning, ClusteredConvolutionalPerceptronParameters.control]
    ring
  have hgeom := abstract_geometry G hp.2.2.2.2.1 hp.2.2.2.2.2.1
    (tuning p hp) hη.le rfl rfl
    (show (tuning p hp).ρ ≤ (1 / (4 * p.upper)) * p.lower by
      simp only [tuning, ClusteredConvolutionalPerceptronParameters.control]; ring_nf; rfl)
    (show (1 / (4 * p.upper)) * p.upper ≤ 1 by
      have he : (1 / (4 * p.upper)) * p.upper = 1 / 4 := by field_simp
      rw [he]; norm_num)
  have hd1 := delta_le_one hp.2.2.2.2.1 hp.2.2.2.2.2.1 (rho_pos p hp)
    (rho_le p hp) hp.2.2.2.2.2.2
  have hi := control_initial hp.2.2.2.2.1 hp.2.2.2.2.2.1 (rho_pos p hp)
    (rho_le p hp) (delta_pos p hp) hp.2.2.2.2.2.2
  have hn := control_noise hp.2.2.2.2.1 hp.2.2.2.2.2.1 (rho_pos p hp)
    (rho_le p hp) (delta_pos p hp) hp.2.2.2.2.2.2
  have hs := iterate_separates G hp.1 hη hδ hgeom hd1 hi hn
  rw [budget_eq p hp] at hs
  have hstart : initial (tuning p hp) (1 / (4 * p.upper) * p.contrast) =
      (algorithm p).initial seed := by
    simp [initial, ManySampleConvolutionalPerceptronGeometry.decode, tuning, ClusteredConvolutionalPerceptronParameters.control, algorithm]
  rw [hstart] at hs
  exact hs

end LongTails.Proofs.ClusteredConvolutionalPerceptronConvergence

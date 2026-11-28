import LongTails.Proofs.BrightnessLogisticModes
import LongTails.Proofs.BrightnessLogisticEnergy

open scoped RealInnerProductSpace
open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Setups.BrightnessLogisticRaw (mean vote)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)

namespace LongTails.Proofs.BrightnessLogisticForces

open ManySampleConvolutionalPerceptronDynamics (State)
open BrightnessLogisticModes BrightnessLogisticRawDynamics

lemma mean_mono {n : ℕ+} {a b : Fin n → ℝ} (h : ∀ i, a i ≤ b i) : mean a ≤ mean b := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) (by positivity)

lemma mean_add {n : ℕ+} (f g : Fin n → ℝ) : mean (fun i => f i+g i)=mean f+mean g := by
  simp only [mean,Finset.sum_add_distrib,mul_add]

lemma mean_const {n : ℕ+} (z : ℝ) : mean (fun _ : Fin n => z)=z := by
  have hn : (n : ℝ) ≠ 0 := by positivity
  simp [mean,hn]

lemma votes_range (p : Params) (x : State (Features p.d)) :
    0 ≤ mean (weights p x) ∧ mean (weights p x) ≤ 1 := by
  unfold weights
  have hl := mean_mono (n := p.n) (a := fun _ => 0) (fun i => (confidence (scores p x i)).1)
  have hh := mean_mono (n := p.n) (fun i => (confidence (scores p x i)).2)
  simpa only [mean_const] using And.intro hl hh

lemma norm_force {d : ℕ} {n : ℕ+} (g : Fin n → ℝ) (Z : Fin n → Features d)
    (hg : ∀ i, 0 ≤ g i) : ‖force g Z‖ ≤ mean (fun i => g i*‖Z i‖) := by
  unfold force mean
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le ..).trans
  exact Finset.sum_le_sum fun i _ => by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hg i)]

lemma force_budget (p : Params) (hp : Valid p) (x : State (Features p.d)) :
    ‖force (weights p x) p.plus‖+‖force (weights p x) p.minus‖ ≤ p.J*mean (weights p x) := by
  let g := weights p x
  have hg (i) : 0 ≤ g i := (confidence _).1
  have h := add_le_add (norm_force g p.plus hg) (norm_force g p.minus hg)
  rw [← mean_add] at h
  apply h.trans
  rw [← mean_scale]
  apply mean_mono
  intro i
  have hh := mul_le_mul_of_nonneg_left (hp.radius i) (hg i)
  dsimp only [g] at hh ⊢
  linarith only [hh]

lemma work_identity (p : Params) (x : State (Features p.d)) :
    mean (fun i => scores p x i*weights p x i) =
    x.a*x.q*dcForce p x+x.a*⟪force (weights p x) p.plus,x.z⟫+
      x.t*⟪force (weights p x) p.minus,x.z⟫ := by
  rw [force_inner,force_inner,dcForce]
  rw [show x.a*x.q*(Real.sqrt 2*p.R*mean (fun i => p.dc i*weights p x i)) =
    (x.a*x.q*(Real.sqrt 2*p.R))*mean (fun i => p.dc i*weights p x i) by ring]
  simp_rw [← mean_scale,← mean_add]
  congr 1
  funext i
  unfold scores
  ring

lemma centered_work {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a q S : ℝ) (u v z : E) (ha : |a| ≤ S) (hq : |q| ≤ S) (hz : ‖z‖ ≤ S) :
    |a*⟪u,z⟫+q*⟪v,z⟫| ≤ (‖u‖+‖v‖)*S^2 := by
  have hS := (norm_nonneg _).trans hz
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_mul]
  have haux (y : E) : |⟪y,z⟫| ≤ ‖y‖*S :=
    (abs_real_inner_le_norm y z).trans (mul_le_mul_of_nonneg_left hz (norm_nonneg _))
  nlinarith only [mul_le_mul ha (haux u) (abs_nonneg _) hS,mul_le_mul hq (haux v) (abs_nonneg _) hS]

end LongTails.Proofs.BrightnessLogisticForces

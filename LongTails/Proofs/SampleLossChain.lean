import LongTails.Proofs.SampleLossRadial
import LongTails.Proofs.SampleLossCalculus

open scoped RealInnerProductSpace BigOperators
open LongTails.Proofs.SampleLossRadial LongTails.Proofs.SampleLossMixture LongTails.Proofs.SampleLossCalculus
open LongTails.Proofs.SoftRadialProjection

namespace LongTails.Proofs.SampleLossChain

variable {E B : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]

noncomputable def signal (P : ℕ → E →L[ℝ] B) (u : ℕ → B) (j : ℕ) (x : E) : ℝ :=
  alignment (u j) (P j x)

noncomputable def incoming (P : ℕ → E →L[ℝ] B) (u : ℕ → B) : ℕ → E → ℝ
  | 0 => fun _ => 1
  | j + 1 => fun x => gate (signal P u j x)

noncomputable def increment (P : ℕ → E →L[ℝ] B) (v : E) : ℕ → ℝ
  | 0 => 2048 * ‖P 0 v‖
  | j + 1 => 2048 * (‖P (j + 1) v‖ + ‖P j v‖)

noncomputable def link (P : ℕ → E →L[ℝ] B) (u : ℕ → B) (j : ℕ) (x : E) : ℝ :=
  incoming P u j x * (1 + signal P u j x)

noncomputable def base (P : ℕ → E →L[ℝ] B) (u : ℕ → B) (n : ℕ) (x : E) : ℝ :=
  ‖x‖ ^ 2 - ∑ j ∈ Finset.range n, link P u j x

noncomputable def perturbation (P : ℕ → E →L[ℝ] B) (u w : ℕ → B) (n : ℕ) (x : E) : ℝ :=
  mixture (fun j => incoming P u j x) (fun j => signal P w j x) n

noncomputable def sampleLoss (P : ℕ → E →L[ℝ] B) (u w : ℕ → B) (M : ℝ) (n : ℕ) (x : E) : ℝ :=
  2 * n + M + base P u n x + M * perturbation P u w n x

lemma signal_differentiable (P : ℕ → E →L[ℝ] B) (u : ℕ → B) (j : ℕ) :
    Differentiable ℝ (signal P u j) := fun x =>
  ((alignment_gradient (u j) (P j x)).differentiableAt.comp x (P j).differentiableAt)

lemma signal_fderiv (P : ℕ → E →L[ℝ] B) (u : ℕ → B) (j : ℕ) (x v : E) :
    fderiv ℝ (signal P u j) x v = ⟪derivative 1 (P j x) (u j), P j v⟫ := by
  have h := (alignment_gradient (u j) (P j x)).hasFDerivAt.comp x (P j).hasFDerivAt
  exact congrArg (fun l : E →L[ℝ] ℝ => l v) h.fderiv

lemma gate_hasDerivAt (z : ℝ) : HasDerivAt gate (gateSlope z) z := by
  apply AbcChainProfiles.model_hasDerivAt gate gateSlope 131072 gate_model

lemma incoming_differentiable (P : ℕ → E →L[ℝ] B) (u : ℕ → B) (j : ℕ) :
    Differentiable ℝ (incoming P u j) := by
  cases j with
  | zero => exact differentiable_const _
  | succ j => exact fun x => (gate_hasDerivAt _).differentiableAt.comp x (signal_differentiable P u j x)

lemma incoming_fderiv (P : ℕ → E →L[ℝ] B) (u : ℕ → B) (j : ℕ) (x v : E) :
    fderiv ℝ (incoming P u (j + 1)) x v =
      gateSlope (signal P u j x) * ⟪derivative 1 (P j x) (u j), P j v⟫ := by
  have h := (gate_hasDerivAt _).comp (0 : ℝ) (derivative_line x v (signal_differentiable P u j x))
  simp only [zero_smul, add_zero, signal_fderiv] at h
  exact (derivative_line x v (incoming_differentiable P u (j + 1) x)).unique h

omit [CompleteSpace B] in
lemma incoming_mem (P : ℕ → E →L[ℝ] B) (u : ℕ → B) (j : ℕ) (x : E) :
    0 ≤ incoming P u j x ∧ incoming P u j x ≤ 1 := by
  cases j with
  | zero => exact ⟨zero_le_one, le_rfl⟩
  | succ j => exact gate_mem _

lemma link_differentiable (P : ℕ → E →L[ℝ] B) (u : ℕ → B) (j : ℕ) :
    Differentiable ℝ (link P u j) :=
  (incoming_differentiable P u j).mul ((differentiable_const _).add (signal_differentiable P u j))

lemma base_differentiable (P : ℕ → E →L[ℝ] B) (u : ℕ → B) (n : ℕ) :
    Differentiable ℝ (base P u n) :=
  (show Differentiable ℝ (fun x : E => ‖x‖ ^ 2) from fun x => (hasStrictFDerivAt_norm_sq x).differentiableAt).sub
    (Differentiable.fun_sum fun j _ => link_differentiable P u j)

lemma perturbation_differentiable (P : ℕ → E →L[ℝ] B) (u w : ℕ → B) (n : ℕ) :
    Differentiable ℝ (perturbation P u w n) :=
  mixture_differentiable _ _ (incoming_differentiable P u) (signal_differentiable P w) n

lemma sampleLoss_differentiable (P : ℕ → E →L[ℝ] B) (u w : ℕ → B) (M : ℝ) (n : ℕ) :
    Differentiable ℝ (sampleLoss P u w M n) :=
  ((differentiable_const _).add (base_differentiable P u n)).add
    ((differentiable_const _).mul (perturbation_differentiable P u w n))

omit [CompleteSpace B] in
lemma sampleLoss_nonneg (P : ℕ → E →L[ℝ] B) {u w : ℕ → B} (hu : ∀ j, ‖u j‖ ≤ 1)
    (hw : ∀ j, ‖w j‖ ≤ 1) {M : ℝ} (hM : 0 ≤ M) (n : ℕ) (x : E) :
    0 ≤ sampleLoss P u w M n x := by
  have hb (j : ℕ) : link P u j x ≤ 2 := by
    have h := (le_abs_self _).trans ((alignment_abs (u j) (P j x)).trans (hu j))
    change signal P u j x ≤ 1 at h
    have h2 := mul_le_mul_of_nonneg_left (by linarith : 1 + signal P u j x ≤ 2) (incoming_mem P u j x).1
    unfold link
    linarith [(incoming_mem P u j x).2]
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun j _ => hb j)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have hm := abs_mixture_le (fun j => incoming P u j x) (fun j => signal P w j x)
    (fun j => incoming_mem P u j x) (fun j => (alignment_abs (w j) (P j x)).trans (hw j)) n
  change |perturbation P u w n x| ≤ 1 at hm
  unfold sampleLoss base
  nlinarith [sq_nonneg ‖x‖, mul_nonneg hM (show 0 ≤ 1 + perturbation P u w n x by linarith [(abs_le.mp hm).1])]

end LongTails.Proofs.SampleLossChain

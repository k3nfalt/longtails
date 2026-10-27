import LongTails.Proofs.GeneralizedFiniteSumStep
import LongTails.Proofs.GeneralizedFiniteSumParameters
import LongTails.Proofs.AcceleratedFiniteSum

namespace OracleTemplate.GeneralizedFiniteSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma query_radius {A a L1 R : ℝ} (hA : 0 < A) (ha : 0 ≤ a)
    (h1 : 0 ≤ L1) (hcap : a * L1 * R ≤ A / 1024)
    (s z : E) (hd : ‖z - s‖ ≤ 8 * R) :
    L1 * ‖mix A a s z - s‖ ≤ 1 / 128 := by
  have hB : 0 < A + a := by positivity
  rw [mix_sub_snapshot hB.ne', norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ha hB.le)]
  have hh := mul_le_mul_of_nonneg_left hd h1
  have he : L1 * (a / (A + a) * ‖z - s‖) =
      (a * (L1 * ‖z - s‖)) / (A + a) := by ring
  rw [he]
  apply (div_le_iff₀ hB).mpr
  have hh' := mul_le_mul_of_nonneg_left hh ha
  nlinarith only [hh', hcap, ha]

lemma primal_displacement {A a n M L1 : ℝ} (hA : 0 < A) (ha : 0 ≤ a)
    (hn : 0 < n) (_h1 : 0 ≤ L1)
    (hcontrol : a ^ 2 * M ≤ (207 / 1048576) * n * A)
    (v : E) (hv : L1 * ‖v‖ ≤ (33 / 32) * M) :
    L1 * ‖(a ^ 2 / (n * (A + a))) • v‖ ≤ 1 / 1024 := by
  have hB : 0 < A + a := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have he : L1 * (a ^ 2 / (n * (A + a)) * ‖v‖) =
      (a ^ 2 * (L1 * ‖v‖)) / (n * (A + a)) := by ring
  rw [he]
  apply (div_le_iff₀ (mul_pos hn hB)).mpr
  have hh := mul_le_mul_of_nonneg_left hv (sq_nonneg a)
  have hnA := mul_pos hn hA
  have hna := mul_nonneg hn.le ha
  nlinarith only [hh, hcontrol, hnA, hna]

lemma output_radius {A a n M L1 : ℝ} (hA : 0 < A) (ha : 0 ≤ a)
    (hn : 0 < n) (h1 : 0 ≤ L1)
    (hcontrol : a ^ 2 * M ≤ (207 / 1048576) * n * A)
    (s z v : E) (hy : L1 * ‖mix A a s z - s‖ ≤ 1 / 128)
    (hv : L1 * ‖v‖ ≤ (33 / 32) * M) :
    L1 * ‖mix A a s (z - (a / n) • v) - s‖ ≤ 1 / 64 := by
  have hB : 0 < A + a := by positivity
  rw [mix_dual_step hB.ne' hn.ne']
  have he : mix A a s z - (a ^ 2 / (n * (A + a))) • v - s =
      (mix A a s z - s) - (a ^ 2 / (n * (A + a))) • v := by abel
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (norm_sub_le (mix A a s z - s)
    ((a ^ 2 / (n * (A + a))) • v)) h1
  have hd := primal_displacement hA ha hn h1 hcontrol v hv
  nlinarith only [hh, hd, hy]

open Set
open scoped RealInnerProductSpace BigOperators
open LongTails.Setups.FiniteSumSmoothAndConvex (objective)

lemma localized_step [CompleteSpace E] {n : ℕ} [NeZero n]
    {f : Fin n → E → ℝ} {g : Fin n → E → E} {L0 L1 A a R : ℝ}
    (h0 : 0 < L0) (h1 : 0 ≤ L1) (hA : 0 < A) (ha : 0 < a)
    (hc : ∀ i, ConvexOn ℝ univ (f i)) (hf : ∀ i x, HasGradientAt (f i) (g i x) x)
    (hg : ∀ i, Continuous (g i))
    (hs : ∀ i, CompositeGeneralized.SymmetricSmooth (g i) L0 L1)
    (s z u : E) (hd : ‖z - s‖ ≤ 8 * R) (hcap : a * L1 * R ≤ A / 1024)
    (hcontrol : a ^ 2 * ((∑ i, snapshotWeights L0 L1 (fun j => g j s) i) / n) ≤
      (207 / 1048576) * n * A) :
    let w := snapshotWeights L0 L1 (fun i => g i s)
    let y := mix A a s z
    let v := fun (seed : Fin ((2 * n).factorial)) => direction w (fun i => g i s) (drawIndex w seed) (g (drawIndex w seed) y)
    (𝔼 seed : Fin ((2 * n).factorial),
      ((A + a) * (objective f (mix A a s (z - (a / n) • v seed)) - objective f u) +
        (n : ℝ) / 2 * ‖z - (a / n) • v seed - u‖ ^ 2)) ≤
      A * (objective f s - objective f u) + (n : ℝ) / 2 * ‖z - u‖ ^ 2 := by
  classical
  let : NeZero (2 * n).factorial := ⟨Nat.factorial_ne_zero _⟩
  let w := snapshotWeights L0 L1 (fun i => g i s)
  let M := (∑ i, w i) / n
  let y := mix A a s z
  let v := fun (seed : Fin ((2 * n).factorial)) => direction w (fun i => g i s) (drawIndex w seed) (g (drawIndex w seed) y)
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hB : 0 < A + a := by positivity
  have hw (i : Fin n) : 0 ≤ w i := by dsimp [w, snapshotWeights]; positivity
  have hM : 0 ≤ M := div_nonneg (Finset.sum_nonneg fun i _ => hw i) hn.le
  have hy : L1 * ‖y - s‖ ≤ 1 / 128 := query_radius hA ha.le h1 hcap s z hd
  have hdiff (i : Fin n) : ‖g i y - g i s‖ ≤ 2 * w i * ‖y - s‖ := by
    have hh := CompositeGeneralized.ball_lipschitz h0.le h1 (hg i) (hs i)
      (x := s) (u := y) (v := s) (r := ‖y - s‖) (by linarith) le_rfl (by simp)
    exact hh
  have hv (seed : Fin ((2 * n).factorial)) : L1 * ‖v seed‖ ≤ (33 / 32) * M := by
    have hh := mul_le_mul_of_nonneg_left
      (direction_norm w (fun i => g i s) (fun i => g i y) ‖y - s‖ hw (norm_nonneg _) hdiff
        (drawIndex w seed)) h1
    have hg0 := weighted_full_gradient_norm (fun i => g i s) h0.le h1
    have hm := mul_le_mul_of_nonneg_left hy (show 0 ≤ 4 * M by positivity)
    change L1 * ‖(n : ℝ)⁻¹ • ∑ i, g i s‖ ≤ M at hg0
    dsimp [v] at hh ⊢
    nlinarith only [hh, hg0, hm]
  have hout (seed : Fin ((2 * n).factorial)) :
      L1 * ‖mix A a s (z - (a / n) • v seed) - s‖ ≤ 1 / 64 :=
    output_radius hA ha.le hn h1 hcontrol s z (v seed) hy (hv seed)
  have hgrad (x : E) : HasGradientAt (objective f) ((n : ℝ)⁻¹ • ∑ i, g i x) x :=
    FiniteSum.objective_gradient (oracle := fun ix => g ix.1 ix.2) hf x
  have hgrad_eq (x : E) : gradient (objective f) x = (n : ℝ)⁻¹ • ∑ i, g i x := (hgrad x).gradient
  have hgrad' (x : E) : HasGradientAt (objective f) (gradient (objective f) x) x := by
    rw [hgrad_eq]; exact hgrad x
  have hunbiased : ((2 * n).factorial : ℝ)⁻¹ • ∑ seed, v seed = gradient (objective f) y := by
    rw [hgrad_eq]
    exact direction_unbiased w (fun i => g i s) (fun i => g i y)
  have hvar := local_direction_variance h0 h1 hc hf hg hs s y (by linarith)
  have hvar' : (𝔼 seed, ‖v seed - gradient (objective f) y‖ ^ 2) ≤
      (24 * M) * (objective f s - objective f y - ⟪gradient (objective f) y, s - y⟫) := by
    rw [hgrad_eq]
    simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, div_eq_inv_mul, v, M, w] using hvar
  have hstep : 2 * (2 * M) * a ^ 2 ≤ (n : ℝ) * A := by
    have hh : 0 < (n : ℝ) * A := mul_pos hn hA
    nlinarith only [hcontrol, hh]
  have hvariance : a ^ 2 * (24 * M) ≤ (n : ℝ) * A := by
    have hh : 0 < (n : ℝ) * A := mul_pos hn hA
    nlinarith only [hcontrol, hh]
  apply local_accelerated_step hA.le ha hn hstep hvariance (FiniteSum.objective_convex hc)
    hgrad' s z u v hunbiased hvar'
  intro seed
  have hu := aggregate_local_upper h0.le h1 hf hg hs s y
    (mix A a s (z - (a / n) • v seed)) (by linarith) (by linarith [hout seed])
  rw [mix_dual_step hB.ne' hn.ne'] at hu
  have he : 1 / ((n : ℝ) * (A + a) / a ^ 2) = a ^ 2 / ((n : ℝ) * (A + a)) := by field_simp
  dsimp only
  rw [he, hgrad_eq]
  convert hu using 1
  all_goals dsimp [M, w, snapshotWeights, y, mix]
  all_goals ring

end OracleTemplate.GeneralizedFiniteSum

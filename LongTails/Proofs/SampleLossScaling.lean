import LongTails.Proofs.SampleLossFrame
import LongTails.Proofs.SampleLossGradient

open scoped RealInnerProductSpace BigOperators
open LongTails.Setups.NonnegativeSmoothSampleLossEuclidean
open LongTails.Proofs.SampleLossFrame LongTails.Proofs.SampleLossRegularity
open LongTails.Proofs.SampleLossChain LongTails.Proofs.SampleLossGradient

namespace LongTails.Proofs.SampleLossScaling

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def stretch (a r : ℝ) (F : E → ℝ) (x : E) := a * F (r • x)

lemma stretch_gradient (a r : ℝ) {F : E → ℝ} (hF : Differentiable ℝ F) (x : E) :
    HasGradientAt (stretch a r F) ((a*r) • gradient F (r • x)) x := by
  let D := r • ContinuousLinearMap.id ℝ E
  have h := (hF (r • x)).hasGradientAt.hasFDerivAt.comp x D.hasFDerivAt
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert h.const_mul a using 1 <;> try rfl
  ext v
  simp [D, mul_assoc]

variable {n m d : ℕ}

noncomputable def mean (π : Table n m d) (M : ℝ) (x : Space n m d) :=
  2*(n:ℝ) + M + base proj (direction π) n x

lemma mean_differentiable (π : Table n m d) (M : ℝ) : Differentiable ℝ (mean π M) :=
  (differentiable_const _).add (base_differentiable _ _ _)

lemma mean_grad_eq (π : Table n m d) (M : ℝ) (x : Space n m d) :
    gradient (mean π M) x = gradient (base proj (direction π) n) x := by
  apply HasGradientAt.gradient
  exact ((base_differentiable proj (direction π) n x).hasGradientAt.hasFDerivAt.const_add (2*(n:ℝ)+M))

lemma mean_zero_le (π : Table n m d) (M : ℝ) : mean π M 0 ≤ 2*(n:ℝ)+M := by
  unfold mean base
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_sub, add_neg_le_iff_le_add]
  have h (j : ℕ) : 0 ≤ link proj (direction π) j (0 : Space n m d) := by
    simp [link,signal,SampleLossRadial.alignment,SoftRadialProjection.project,(incoming_mem proj (direction π) j (0 : Space n m d)).1]
  linarith [Finset.sum_nonneg (s:=Finset.range n) (fun j _ => h j)]

lemma mean_barrier (π : Table n m d) (hm : 0 < m) (M : ℝ) (x : Space n m d)
    (hs : ∃ j < n, signal proj (direction π) j x < 1/64) :
    1/8 < ‖gradient (mean π M) x‖ := by
  rw [mean_grad_eq]
  apply base_block_barrier _ _ n x (fun j hj => direction_norm π hj hm) hs
  intro k hk v
  let i : Fin n := ⟨k,hk⟩
  refine ⟨PiLp.single 2 i v, PiLp.norm_single _ _ _ _, ?_, ?_⟩
  · change (∑ t, ⟪x t, (PiLp.single 2 i v : Space n m d) t⟫) = ⟪proj k x,v⟫
    rw [Finset.sum_eq_single i]
    · simp [proj,hk,i]
    · intro b _ hb; simp [hb]
    · simp
  · intro j hj
    by_cases he : j=k
    · subst j; simp [proj,hk,i, PiLp.proj_apply]
    · have hne : (⟨j,hj⟩ : Fin n) ≠ i := fun h => he (congrArg Fin.val h)
      simp [proj,hj,i,PiLp.proj_apply,he,hne]

noncomputable def amplitude (q : Params) : ℝ := q.Δ / (2048 * (stages q : ℝ))

noncomputable def dilation (q : Params) : ℝ := 32*q.ε / amplitude q

lemma stages_pos {q : Params} (hq : spec.valid q) : 0 < stages q := by
  have hε := hq.2.2.1
  have hd : 0 < 4294967296*q.ε := by positivity
  exact Nat.floor_pos.mpr ((one_le_div hd).mpr hq.2.2.2)

lemma scaling {q : Params} (hq : spec.valid q) :
    0 < amplitude q ∧ 0 < dilation q ∧ amplitude q * dilation q = 32*q.ε ∧
    amplitude q * (2*(stages q:ℝ)+(1+Real.sqrt (rows (stages q)))) ≤ q.Δ ∧
    amplitude q * dilation q ^ 2 * (2147483648 * (1+(1+Real.sqrt (rows (stages q))))) ≤ q.L := by
  obtain ⟨hL,hΔ,hε,hR⟩ := hq
  let n := stages q
  have hn : 1 ≤ (n:ℝ) := by exact_mod_cast stages_pos (q:=q) ⟨hL,hΔ,hε,hR⟩
  have hn0 : 0 < (n:ℝ) := by linarith
  have hs : Real.sqrt (rows n) = 512 * ((n:ℝ)+1) := by
    simp [rows, Nat.cast_pow, Real.sqrt_sq (by positivity : 0 ≤ 512*((n:ℝ)+1))]
  have ha : 0 < amplitude q := by unfold amplitude; change 0 < q.Δ/(2048*(n:ℝ)); positivity
  have hr : 0 < dilation q := by unfold dilation; positivity
  have har : amplitude q * dilation q = 32*q.ε := by unfold dilation; field_simp
  have he : amplitude q * (2048*(n:ℝ)) = q.Δ := div_mul_cancel₀ _ (by positivity)
  have hnle : (n:ℝ) * (4294967296*q.ε) ≤ Real.sqrt (q.L*q.Δ) :=
    (le_div_iff₀ (by positivity)).mp (Nat.floor_le (by positivity))
  have hsq := pow_le_pow_left₀ (by positivity) hnle 2
  rw [Real.sq_sqrt (mul_nonneg hL.le hΔ.le)] at hsq
  refine ⟨ha,hr,har,?_,?_⟩
  · change amplitude q * (2*(n:ℝ)+(1+Real.sqrt (rows n))) ≤ q.Δ
    rw [hs,← he]
    exact mul_le_mul_of_nonneg_left (by linarith) ha.le
  · change amplitude q * dilation q ^ 2 * (2147483648 * (1+(1+Real.sqrt (rows n)))) ≤ q.L
    rw [hs]
    apply (mul_le_mul_iff_left₀ ha).mp
    calc
      _ = (32*q.ε)^2 * (2147483648 * (1+(1+512*((n:ℝ)+1)))) := by rw [← har]; ring
      _ ≤ (32*q.ε)^2 * (2147483648 * (1026*(n:ℝ))) := by gcongr; linarith
      _ ≤ _ := by
        apply (mul_le_mul_iff_left₀ (show 0 < 2048*(n:ℝ) by positivity)).mp
        rw [show q.L*amplitude q*(2048*(n:ℝ)) = q.L*q.Δ by rw [← he]; ring]
        nlinarith [sq_nonneg ((n:ℝ)*q.ε)]

end LongTails.Proofs.SampleLossScaling

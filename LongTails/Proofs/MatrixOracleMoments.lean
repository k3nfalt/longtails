import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Analysis.InnerProductSpace.Trace

namespace LongTails.Proofs.MatrixOracleMoments

open MeasureTheory
open scoped RealInnerProductSpace

lemma norm_toLp_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with ω hω
  simp [hω, pow_two]

lemma norm_toLp_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 P) {s : ℝ} (hs : 0 ≤ s)
    (hsecond : (∫ ω, f ω ^ 2 ∂P) ≤ s ^ 2) : ‖hf.toLp f‖ ≤ s := by
  rw [← norm_toLp_sq hf] at hsecond
  nlinarith [norm_nonneg (hf.toLp f)]

lemma second_moment_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hfa : (∫ ω, f ω ^ 2 ∂P) ≤ a ^ 2)
    (hgb : (∫ ω, g ω ^ 2 ∂P) ≤ b ^ 2) :
    (∫ ω, (f ω + g ω) ^ 2 ∂P) ≤ (a + b) ^ 2 := by
  have hh : ‖(hf.add hg).toLp (f + g)‖ ≤ a + b := by
    rw [MemLp.toLp_add hf hg]
    exact (norm_add_le _ _).trans (add_le_add (norm_toLp_le hf ha hfa)
      (norm_toLp_le hg hb hgb))
  have he := norm_toLp_sq (hf.add hg)
  simp only [Pi.add_apply] at he
  rw [← he]
  exact pow_le_pow_left₀ (norm_nonneg _) hh 2

lemma second_moment_sum {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset I) {f : I → Ω → ℝ} {σ : I → ℝ}
    (hf : ∀ i ∈ s, MemLp (f i) 2 P) (hσ : ∀ i ∈ s, 0 ≤ σ i)
    (hsecond : ∀ i ∈ s, (∫ ω, f i ω ^ 2 ∂P) ≤ σ i ^ 2) :
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂P) ≤ (∑ i ∈ s, σ i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs : MemLp (fun ω => ∑ j ∈ s, f j ω) 2 P :=
      memLp_finsetSum _ (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hsum := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hσ j (Finset.mem_insert_of_mem hj))
      (fun j hj => hsecond j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using second_moment_add
      (hf i (Finset.mem_insert_self _ _)) hs (hσ i (Finset.mem_insert_self _ _))
      (Finset.sum_nonneg (fun j hj => hσ j (Finset.mem_insert_of_mem hj)))
      (hsecond i (Finset.mem_insert_self _ _)) hsum

lemma second_moment_of_sum_bound {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset I) {f : I → Ω → ℝ} {σ : I → ℝ} {Y : Ω → ℝ}
    (hf : ∀ i ∈ s, MemLp (f i) 2 P) (hσ : ∀ i ∈ s, 0 ≤ σ i)
    (hsecond : ∀ i ∈ s, (∫ ω, f i ω ^ 2 ∂P) ≤ σ i ^ 2)
    (hY : AEStronglyMeasurable Y P) (hzero : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hbound : ∀ᵐ ω ∂P, Y ω ≤ ∑ i ∈ s, f i ω) :
    MemLp Y 2 P ∧ (∫ ω, Y ω ^ 2 ∂P) ≤ (∑ i ∈ s, σ i) ^ 2 := by
  have hs : MemLp (fun ω => ∑ i ∈ s, f i ω) 2 P := memLp_finsetSum _ hf
  have hYp : MemLp Y 2 P := hs.mono' hY (by
    filter_upwards [hzero, hbound] with ω hz hb
    simpa only [Real.norm_eq_abs, abs_of_nonneg hz] using hb)
  refine ⟨hYp, ?_⟩
  have hh : (∫ ω, Y ω ^ 2 ∂P) ≤ ∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂P := by
    apply integral_mono_ae hYp.integrable_sq hs.integrable_sq
    filter_upwards [hzero, hbound] with ω hz hb
    exact pow_le_pow_left₀ hz hb 2
  exact hh.trans (second_moment_sum s hf hσ hsecond)

lemma integral_mul_eq_zero_of_condExp {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] (hm : m ≤ m₀)
    {X Y : Ω → ℝ} (hX : StronglyMeasurable[m] X)
    (hiY : Integrable Y P) (hiXY : Integrable (X * Y) P)
    (hzero : ∀ᵐ ω ∂P, P[Y | m] ω = 0) :
    (∫ ω, X ω * Y ω ∂P) = 0 := by
  have hp := condExp_mul_of_stronglyMeasurable_left hX hiXY hiY
  have hz : P[X * Y | m] =ᵐ[P] 0 := by
    filter_upwards [hp, hzero] with ω hp hz
    simp only [Pi.mul_apply, Pi.zero_apply] at *
    rw [hp, hz, mul_zero]
  have he := integral_congr_ae hz
  rw [integral_condExp hm] at he
  simpa using he

lemma second_moment_add_of_orthogonal {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (hcross : (∫ ω, f ω * g ω ∂P) = 0) :
    (∫ ω, (f ω + g ω) ^ 2 ∂P) =
      (∫ ω, f ω ^ 2 ∂P) + ∫ ω, g ω ^ 2 ∂P := by
  have hfg : Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg
  have hi : Integrable (fun ω => f ω ^ 2 + g ω ^ 2) P := hf.integrable_sq.add hg.integrable_sq
  calc
    _ = ∫ ω, (f ω ^ 2 + g ω ^ 2) + 2 * (f ω * g ω) ∂P := by
      congr 1; funext ω; ring
    _ = _ := by
      rw [integral_add hi (hfg.const_mul 2),
        integral_add hf.integrable_sq hg.integrable_sq, integral_const_mul, hcross]
      ring

lemma martingale_sum_second_moment {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {m : ℕ → MeasurableSpace Ω}
    (hm : ∀ i, m i ≤ m₀) {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, MemLp (Y i) 2 P)
    (hpast : ∀ n, StronglyMeasurable[m n] (fun ω => ∑ i ∈ Finset.range n, Y i ω))
    (hzero : ∀ n, ∀ᵐ ω ∂P, P[Y n | m n] ω = 0) (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, ∫ ω, Y i ω ^ 2 ∂P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 P :=
      memLp_finsetSum _ (fun i _ => hY i)
    have hc := integral_mul_eq_zero_of_condExp (hm n) (hpast n)
      ((hY n).integrable (by norm_num)) (hs.integrable_mul (hY n)) (hzero n)
    simp only [Finset.sum_range_succ]
    rw [second_moment_add_of_orthogonal hs (hY n) hc, ih]

lemma localized_martingale_sum_second_moment {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {m : ℕ → MeasurableSpace Ω}
    (hm : ∀ i, m i ≤ m₀) {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, MemLp (Y i) 2 P)
    (hpast : ∀ n, StronglyMeasurable[m n] (fun ω => ∑ i ∈ Finset.range n, Y i ω))
    (hzero : ∀ n, ∀ᵐ ω ∂P, P[Y n | m n] ω = 0)
    {A : Set Ω} (hA : ∀ n, MeasurableSet[m n] A) (n : ℕ) :
    (∫ ω in A, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, ∫ ω in A, Y i ω ^ 2 ∂P := by
  apply martingale_sum_second_moment hm
    (fun i => (hY i).mono_measure Measure.restrict_le_self) hpast
  intro i
  exact (condExp_restrict_ae_eq_restrict (hm i) (hA i)
    ((hY i).integrable (by norm_num))).trans (ae_restrict_of_ae (hzero i))

lemma conditional_le_of_local_integrals {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] (hm : m ≤ m₀) {Y : Ω → ℝ}
    (hY : Integrable Y P) {c : ℝ}
    (hlocal : ∀ A, MeasurableSet[m] A → (∫ ω in A, Y ω ∂P) ≤ c * P.real A) :
    ∀ᵐ ω ∂P, P[Y | m] ω ≤ c := by
  apply ae_of_ae_trim hm
  apply ae_le_of_forall_setIntegral_le
    (Integrable.trim hm integrable_condExp stronglyMeasurable_condExp) (integrable_const c)
  intro A hA _
  rw [← setIntegral_trim hm stronglyMeasurable_condExp hA,
    ← setIntegral_trim hm stronglyMeasurable_const hA, setIntegral_condExp hm hY hA]
  simpa only [setIntegral_const, smul_eq_mul, mul_comm c] using hlocal A hA

lemma local_integral_le_of_conditional_bound {Ω : Type*}
    {m m₀ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    (hm : m ≤ m₀) {Y : Ω → ℝ} (hY : Integrable Y P) {c : ℝ}
    (hbound : ∀ᵐ ω ∂P, P[Y | m] ω ≤ c) {A : Set Ω} (hA : MeasurableSet[m] A) :
    (∫ ω in A, Y ω ∂P) ≤ c * P.real A := by
  rw [← setIntegral_condExp hm hY hA]
  calc
    _ ≤ ∫ ω in A, c ∂P := integral_mono_ae integrable_condExp.integrableOn
      (integrable_const _) (ae_restrict_of_ae hbound)
    _ = c * P.real A := by simp [mul_comm]

lemma weighted_martingale_sum_second_moment {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {m : ℕ → MeasurableSpace Ω}
    (hm : ∀ i, m i ≤ m₀) (hmono : Monotone m) {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, MemLp (Y i) 2 P)
    (hadapt : ∀ i, StronglyMeasurable[m (i + 1)] (Y i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, P[Y i | m i] ω = 0) (w : ℕ → ℝ) (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, w i * Y i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, w i ^ 2 * ∫ ω, Y i ω ^ 2 ∂P := by
  have hpast (j : ℕ) : StronglyMeasurable[m j]
      (fun ω => ∑ i ∈ Finset.range j, w i * Y i ω) := by
    have hh := Finset.stronglyMeasurable_sum (Finset.range j) (fun i hi =>
      ((hadapt i).mono (hmono (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))).const_mul (w i))
    convert hh using 1
    funext ω
    simp only [Finset.sum_apply]
  have hz (i : ℕ) : ∀ᵐ ω ∂P, P[fun ω => w i * Y i ω | m i] ω = 0 := by
    filter_upwards [condExp_smul (μ := P) (w i) (Y i) (m i), hzero i] with ω hc hz
    change P[fun ω => w i * Y i ω | m i] ω = w i * P[Y i | m i] ω at hc
    simpa only [hz, mul_zero] using hc
  have he := martingale_sum_second_moment hm
    (fun i => (hY i).const_mul (w i)) hpast hz n
  simpa only [mul_pow, integral_const_mul] using he

lemma conditional_mean_le_of_second_moment {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {P : Measure Ω} {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    {s : ℝ} (hs : 0 ≤ s)
    (hsecond : ∀ᵐ ω ∂P, P[fun u => Y u ^ 2 | m] ω ≤ s ^ 2) :
    ∀ᵐ ω ∂P, P[Y | m] ω ≤ s := by
  have hi : Integrable (fun ω => ‖Y ω‖ ^ (2 : ℝ)) P := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hY.integrable_sq
  have hj := Integrable.norm_condExp_rpow_le (m := m) (by norm_num : (1 : ℝ) ≤ 2) hi
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs] at hj
  filter_upwards [hj, hsecond] with ω hj hb
  nlinarith [sq_nonneg (P[Y | m] ω - s)]

lemma vector_martingale_sum_second_moment {Ω E I : Type*}
    {m₀ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype I]
    (b : OrthonormalBasis I ℝ E) {m : ℕ → MeasurableSpace Ω}
    (hm : ∀ i, m i ≤ m₀) (hmono : Monotone m) {Y : ℕ → Ω → E}
    (hY : ∀ i, MemLp (Y i) 2 P)
    (hadapt : ∀ i, StronglyMeasurable[m (i + 1)] (Y i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, P[Y i | m i] ω = 0) (w : ℕ → ℝ) (n : ℕ) :
    (∫ ω, ‖∑ i ∈ Finset.range n, w i • Y i ω‖ ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, w i ^ 2 * ∫ ω, ‖Y i ω‖ ^ 2 ∂P := by
  have hcoord (j : I) (i : ℕ) : MemLp (fun ω => inner ℝ (b j) (Y i ω)) 2 P :=
    (hY i).const_inner (b j)
  have hcoordzero (j : I) (i : ℕ) :
      ∀ᵐ ω ∂P, P[fun ω => inner ℝ (b j) (Y i ω) | m i] ω = 0 := by
    have hh := (innerSL ℝ (b j)).comp_condExp_comm (m := m i) ((hY i).integrable (by norm_num))
    filter_upwards [hh, hzero i] with ω hh hz
    change inner ℝ (b j) (P[Y i | m i] ω) =
      P[fun ω => inner ℝ (b j) (Y i ω) | m i] ω at hh
    simpa only [hz, inner_zero_right] using hh.symm
  have hsum (j : I) : MemLp
      (fun ω => ∑ i ∈ Finset.range n, w i * inner ℝ (b j) (Y i ω)) 2 P :=
    memLp_finsetSum _ (fun i _ => (hcoord j i).const_mul (w i))
  calc
    _ = ∫ ω, ∑ j : I, (∑ i ∈ Finset.range n, w i * inner ℝ (b j) (Y i ω)) ^ 2 ∂P := by
      congr 1
      funext ω
      rw [← b.sum_sq_inner_right]
      simp only [inner_sum, inner_smul_right]
    _ = ∑ j : I, ∫ ω, (∑ i ∈ Finset.range n, w i * inner ℝ (b j) (Y i ω)) ^ 2 ∂P :=
      integral_finsetSum _ (fun j _ => (hsum j).integrable_sq)
    _ = ∑ j : I, ∑ i ∈ Finset.range n, w i ^ 2 * ∫ ω, (inner ℝ (b j) (Y i ω)) ^ 2 ∂P := by
      apply Finset.sum_congr rfl
      intro j _
      exact weighted_martingale_sum_second_moment hm hmono (hcoord j)
        (fun i => (innerSL ℝ (b j)).continuous.comp_stronglyMeasurable (hadapt i))
        (hcoordzero j) w n
    _ = ∑ i ∈ Finset.range n, w i ^ 2 * ∫ ω, ‖Y i ω‖ ^ 2 ∂P := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, ← integral_finsetSum _ (fun j _ => (hcoord j i).integrable_sq)]
      simp only [b.sum_sq_inner_right]

lemma trace_pair_eq_rows {E F I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] [Fintype I]
    (b : OrthonormalBasis I ℝ F) (N X : E →L[ℝ] F) :
    (N.comp X.adjoint).toLinearMap.trace ℝ F =
      ∑ i, ⟪N.adjoint (b i), X.adjoint (b i)⟫ := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  exact (N.adjoint_inner_left _ _).symm

lemma trace_pair_bound {E F I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] [Fintype I]
    (b : OrthonormalBasis I ℝ F) (N X : E →L[ℝ] F) :
    |(N.comp X.adjoint).toLinearMap.trace ℝ F| ≤
      (∑ i, ‖N.adjoint (b i)‖) * ‖X‖ := by
  rw [trace_pair_eq_rows b N X, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hx : ‖X.adjoint (b i)‖ ≤ ‖X‖ := by
    simpa only [b.orthonormal.norm_eq_one i, mul_one,
      ContinuousLinearMap.adjoint.norm_map] using X.adjoint.le_opNorm (b i)
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left hx (norm_nonneg _))

end LongTails.Proofs.MatrixOracleMoments

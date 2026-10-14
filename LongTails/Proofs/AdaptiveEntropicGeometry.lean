import LongTails.Algorithms.AdaptiveEntropic
import LongTails.Proofs.SimplexEntropy

open scoped RealInnerProductSpace

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma oneNorm_nonneg {d : ℕ} (x : Vector d) : 0 ≤ oneNorm x :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma oneNorm_add {d : ℕ} (x y : Vector d) :
    oneNorm (x + y) ≤ oneNorm x + oneNorm y := by
  unfold oneNorm
  simp only [PiLp.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => abs_add_le (x i) (y i))

lemma oneNorm_smul {d : ℕ} (a : ℝ) (x : Vector d) :
    oneNorm (a • x) = |a| * oneNorm x := by
  simp [oneNorm, abs_mul, Finset.mul_sum]

lemma simplex_oneNorm {d : ℕ} (x : simplex d) : oneNorm x.val = 1 := by
  simpa only [oneNorm, abs_of_nonneg (x.property.1 _)] using x.property.2

lemma simplex_diameter {d : ℕ} (x y : simplex d) : oneNorm (x.val - y.val) ≤ 2 := by
  have hpoint (i : Fin d) : |x.val i - y.val i| ≤ x.val i + y.val i := by
    simpa only [abs_of_nonneg (x.property.1 i), abs_of_nonneg (y.property.1 i)]
      using abs_sub (x.val i) (y.val i)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  simpa only [oneNorm, PiLp.sub_apply, Finset.sum_add_distrib, x.property.2,
    y.property.2, show (1 : ℝ) + 1 = 2 by norm_num] using h

lemma abs_inner_le_dual_one {d : ℕ} (x y : Vector d) :
    |⟪x, y⟫| ≤ dualNorm x * oneNorm y := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  calc
    |∑ i, y i * x i| ≤ ∑ i, |y i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |y i| * dualNorm x := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact norm_le_pi_norm (fun j => x j) i
    _ = dualNorm x * oneNorm y := by rw [← Finset.sum_mul]; dsimp [oneNorm]; ring

noncomputable def entropy {d : ℕ} (x : simplex d) : ℝ :=
  (∑ i, x.val i * Real.log (x.val i)) + Real.log d

lemma entropy_upper {d : ℕ} (x : simplex d) : entropy x ≤ Real.log d := by
  suffices (∑ i, x.val i * Real.log (x.val i)) ≤ 0 by dsimp [entropy]; linarith
  apply Finset.sum_nonpos
  intro i _
  have hx : x.val i ≤ 1 := by
    rw [← x.property.2]
    exact Finset.single_le_sum (fun j _ => x.property.1 j) (Finset.mem_univ i)
  exact mul_nonpos_of_nonneg_of_nonpos (x.property.1 i)
    (Real.log_nonpos (x.property.1 i) hx)

lemma softmax_pos {d : ℕ} (hd : 0 < d) (v : Vector d) (i : Fin d) :
    0 < (softmax hd v).val i := by
  change 0 < Real.exp (v i) / ∑ j, Real.exp (v j)
  exact div_pos (Real.exp_pos _) (Finset.sum_pos (fun j _ => Real.exp_pos _)
    ⟨i, Finset.mem_univ _⟩)

lemma softmax_log {d : ℕ} (hd : 0 < d) (v : Vector d) (i : Fin d) :
    Real.log ((softmax hd v).val i) = v i - Real.log (∑ j, Real.exp (v j)) := by
  change Real.log (Real.exp (v i) / ∑ j, Real.exp (v j)) = _
  rw [Real.log_div (Real.exp_pos _).ne' (Finset.sum_pos (fun j _ => Real.exp_pos _)
    ⟨i, Finset.mem_univ _⟩).ne', Real.log_exp]

lemma entropy_nonneg {d : ℕ} (hd : 0 < d) (x : simplex d) : 0 ≤ entropy x := by
  let y := softmax hd (0 : Vector d)
  have hlog (i : Fin d) : Real.log (y.val i) = -Real.log d := by
    simpa [y] using softmax_log hd (0 : Vector d) i
  have h := SimplexEntropy.relative_entropy_lower x.property.1 (softmax_pos hd 0)
    x.property.2 y.property.2
  have hn : 0 ≤ ∑ i, (x.val i * Real.log (x.val i) - x.val i * Real.log (y.val i)) :=
    (by positivity : 0 ≤ (∑ i, |x.val i - y.val i|) ^ 2 / 4).trans h
  simp_rw [hlog] at hn
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, x.property.2] at hn
  simpa [entropy] using hn

lemma softmax_regularized_lower {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 0 < B)
    (s : Vector d) (x : simplex d) :
    let z := softmax hd (-(1 / B) • s)
    B / 4 * oneNorm (x.val - z.val) ^ 2 ≤
      (⟪s, x.val⟫ + B * entropy x) - (⟪s, z.val⟫ + B * entropy z) := by
  intro z
  have hlog (i : Fin d) : B * Real.log (z.val i) + s i =
      -B * Real.log (∑ j, Real.exp ((-(1 / B) • s) j)) := by
    rw [softmax_log]
    change B * ((-(1 / B)) * s i - _) + s i = _
    field_simp; ring
  have h := SimplexEntropy.regularized_linear_lower hB.le x.property.1
    (softmax_pos hd _) x.property.2 z.property.2 hlog
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  have he (v : Vector d) : ⟪s, v⟫ = ∑ i, s i * v i := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]
  dsimp [entropy, oneNorm]
  rw [he, he]
  change B / 4 * (∑ i, |x.val i - z.val i|) ^ 2 ≤ _
  linarith

lemma mix_distance_left {d : ℕ} (n : ℕ) (x z : simplex d) :
    oneNorm ((mix n x z).val - x.val) ≤ 4 / (n + 2) := by
  have he : (mix n x z).val - x.val = (2 / (n + 2) : ℝ) • (z.val - x.val) := by
    change (1 - (2 / (n + 2) : ℝ)) • x.val + (2 / (n + 2) : ℝ) • z.val - x.val = _
    module
  rw [he, oneNorm_smul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (n + 2))]
  have h := mul_le_mul_of_nonneg_left (simplex_diameter z x)
    (by positivity : (0 : ℝ) ≤ 2 / (n + 2))
  calc
    _ ≤ (2 / (n + 2) : ℝ) * 2 := h
    _ = _ := by ring

lemma mix_distance_same_left {d : ℕ} (n : ℕ) (x z w : simplex d) :
    oneNorm ((mix n x z).val - (mix n x w).val) ≤ 4 / (n + 2) := by
  have he : (mix n x z).val - (mix n x w).val =
      (2 / (n + 2) : ℝ) • (z.val - w.val) := by
    change (1 - (2 / (n + 2) : ℝ)) • x.val + (2 / (n + 2) : ℝ) • z.val -
      ((1 - (2 / (n + 2) : ℝ)) • x.val + (2 / (n + 2) : ℝ) • w.val) = _
    module
  rw [he, oneNorm_smul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (n + 2))]
  have h := mul_le_mul_of_nonneg_left (simplex_diameter z w)
    (by positivity : (0 : ℝ) ≤ 2 / (n + 2))
  calc
    _ ≤ (2 / (n + 2) : ℝ) * 2 := h
    _ = _ := by ring

lemma successive_query_distance {d : ℕ} (n : ℕ) (y pre post next : simplex d) :
    oneNorm ((mix (n + 1) (mix n y post) next).val - (mix n y pre).val) ≤
      8 / (n + 2) := by
  have h := oneNorm_add
    ((mix (n + 1) (mix n y post) next).val - (mix n y post).val)
    ((mix n y post).val - (mix n y pre).val)
  rw [sub_add_sub_cancel] at h
  have h1 := mix_distance_left (n + 1) (mix n y post) next
  have h2 := mix_distance_same_left n y post pre
  have hfrac : (4 : ℝ) / ((n + 1 : ℕ) + 2) ≤ 4 / (n + 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    push_cast
    linarith
  calc
    _ ≤ _ := h
    _ ≤ 4 / ((n + 1 : ℕ) + 2) + 4 / (n + 2) := add_le_add h1 h2
    _ ≤ 4 / (n + 2) + 4 / (n + 2) := add_le_add hfrac le_rfl
    _ = _ := by ring

end OracleTemplate.AdaptiveHeavyTailSimplex

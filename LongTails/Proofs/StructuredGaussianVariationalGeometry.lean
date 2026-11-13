import LongTails.Proofs.GaussianVariationalStep
import LongTails.Algorithms.StructuredReparameterizedSgd

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace OracleTemplate.StructuredGaussianVariational

open LongTails.Setups.GaussianVariationalInference
open LongTails.Setups.StructuredGaussianVariationalInference
open OracleTemplate.GaussianVariational

variable {d : ℕ}

def IsSupported (S : Fin d → Finset (Fin d)) (U : Scale d) : Prop := ∀ i j, j ∉ S i → U i j = 0

noncomputable def maskPair (S : Fin d → Finset (Fin d)) (z : Location d × Scale d) :
    Location d × Scale d := (z.1, maskScale S z.2)

noncomputable def rowSq (S : Fin d → Finset (Fin d)) (ξ : Fin d → ℝ) (i : Fin d) : ℝ :=
  ∑ j ∈ S i, ξ j ^ 2

noncomputable def rowMax (S : Fin d → Finset (Fin d)) (ξ : Fin d → ℝ) : ℝ := ⨆ i, rowSq S ξ i

section Basic

variable {S : Fin d → Finset (Fin d)}

lemma maskScale_of_supported {U : Scale d} (hU : IsSupported S U) : maskScale S U = U := by
  funext i j
  unfold maskScale
  split_ifs with h
  · rfl
  · exact (hU i j h).symm

lemma isSupported_sub {U W : Scale d} (hU : IsSupported S U) (hW : IsSupported S W) :
    IsSupported S (U - W) := by
  intro i j h
  simp [Pi.sub_apply, hU i j h, hW i j h]

lemma InFamily.supported {C : Scale d} (h : InFamily S C) : IsSupported S C := h.2

lemma pinner_maskScale (m : Location d) (C : Scale d) (u : Location d) (U : Scale d) :
    pinner m (maskScale S C) u U = pinner m C u (maskScale S U) := by
  unfold pinner maskScale
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

lemma pin_maskPair (a b : Location d × Scale d) : pin (maskPair S a) b = pin a (maskPair S b) :=
  pinner_maskScale _ _ _ _

lemma maskPair_of_supported {b : Location d × Scale d} (hb : IsSupported S b.2) :
    maskPair S b = b := by
  unfold maskPair
  rw [maskScale_of_supported hb]

lemma pin_maskPair_supported (a : Location d × Scale d) {b : Location d × Scale d}
    (hb : IsSupported S b.2) : pin (maskPair S a) b = pin a b := by
  rw [pin_maskPair, maskPair_of_supported hb]

lemma maskPair_sub (a b : Location d × Scale d) :
    maskPair S (a - b) = maskPair S a - maskPair S b := by
  refine Prod.ext rfl ?_
  funext i j
  simp only [maskPair, maskScale, Prod.snd_sub, Pi.sub_apply]
  split_ifs <;> ring

lemma maskPair_smul (c : ℝ) (a : Location d × Scale d) :
    maskPair S (c • a) = c • maskPair S a := by
  refine Prod.ext rfl ?_
  funext i j
  simp only [maskPair, maskScale, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

lemma isSupported_maskScale (U : Scale d) : IsSupported S (maskScale S U) := by
  intro i j h
  simp [maskScale, h]

lemma pin_maskPair_self_le (a : Location d × Scale d) :
    pin (maskPair S a) (maskPair S a) ≤ pin a a := by
  unfold pin pinner maskPair maskScale
  dsimp only
  refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
  split_ifs
  · exact le_rfl
  · simp only [mul_zero]
    exact mul_self_nonneg _

lemma rowSq_nonneg (ξ : Fin d → ℝ) (i : Fin d) : 0 ≤ rowSq S ξ i :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma rowSq_le_rowMax (ξ : Fin d → ℝ) (i : Fin d) : rowSq S ξ i ≤ rowMax S ξ :=
  le_ciSup (Set.finite_range _).bddAbove i

lemma rowMax_nonneg (ξ : Fin d → ℝ) : 0 ≤ rowMax S ξ :=
  Real.iSup_nonneg fun i => rowSq_nonneg ξ i

lemma rowSq_le_sqNorm (ξ : Fin d → ℝ) (i : Fin d) : rowSq S ξ i ≤ sqNorm ξ :=
  Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _

lemma rowMax_le_sqNorm (ξ : Fin d → ℝ) : rowMax S ξ ≤ sqNorm ξ :=
  Real.iSup_le (fun i => rowSq_le_sqNorm ξ i) (sqNorm_nonneg ξ)

lemma rowMax_attained {ξ : Fin d → ℝ} (h : 0 < rowMax S ξ) : ∃ i, rowMax S ξ = rowSq S ξ i := by
  rcases isEmpty_or_nonempty (Fin d) with he | hne
  · have : rowMax S ξ = 0 := Real.iSup_of_isEmpty _
    linarith
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => rowSq S ξ i)
    exact ⟨i, hi.symm⟩

lemma row_sq_le {U : Scale d} (hU : IsSupported S U) (ξ : Fin d → ℝ) (i : Fin d) :
    (∑ j, U i j * ξ j) ^ 2 ≤ (∑ j, U i j ^ 2) * rowMax S ξ := by
  have hsub : ∑ j, U i j * ξ j = ∑ j ∈ S i, U i j * ξ j := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
    rw [hU i j hj, zero_mul]
  rw [hsub]
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq (S i) (fun j => U i j) ξ
  have h2 : ∑ j ∈ S i, U i j ^ 2 ≤ ∑ j, U i j ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  have h3 := rowSq_le_rowMax (S := S) ξ i
  have h4 : 0 ≤ ∑ j ∈ S i, U i j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h5 : 0 ≤ rowSq S ξ i := rowSq_nonneg ξ i
  calc (∑ j ∈ S i, U i j * ξ j) ^ 2 ≤ (∑ j ∈ S i, U i j ^ 2) * rowSq S ξ i := h1
    _ ≤ (∑ j, U i j ^ 2) * rowMax S ξ := mul_le_mul h2 h3 h5 (le_trans h4 h2)

lemma norm_toLp_supported_le (u : Location d) {U : Scale d} (hU : IsSupported S U)
    (ξ : Fin d → ℝ) :
    ‖(WithLp.toLp 2 (u + Matrix.mulVec U ξ) : Point d)‖ ^ 2 ≤
      2 * (∑ i, u i ^ 2) + 2 * (∑ i, ∑ j, U i j ^ 2) * rowMax S ξ := by
  rw [norm_sq_eq_sum]
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
  have h : ∀ i, (u i + ∑ j, U i j * ξ j) ^ 2 ≤
      2 * u i ^ 2 + 2 * ((∑ j, U i j ^ 2) * rowMax S ξ) := by
    intro i
    nlinarith [row_sq_le hU ξ i, sq_nonneg (u i - ∑ j, U i j * ξ j)]
  calc ∑ i, (u i + ∑ j, U i j * ξ j) ^ 2
      ≤ ∑ i, (2 * u i ^ 2 + 2 * ((∑ j, U i j ^ 2) * rowMax S ξ)) :=
        Finset.sum_le_sum fun i _ => h i
    _ = 2 * (∑ i, u i ^ 2) + 2 * (∑ i, ∑ j, U i j ^ 2) * rowMax S ξ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
      ring

lemma norm_mulVec_supported_le {U : Scale d} (hU : IsSupported S U) (ξ : Fin d → ℝ) :
    ‖(WithLp.toLp 2 ((0 : Location d) + Matrix.mulVec U ξ) : Point d)‖ ^ 2 ≤
      (∑ i, ∑ j, U i j ^ 2) * rowMax S ξ := by
  rw [norm_sq_eq_sum]
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => row_sq_le hU ξ i

lemma norm_sample_sub_supported_le (m m' : Location d) {C C' : Scale d}
    (hC : IsSupported S (C - C')) (ξ : Fin d → ℝ) :
    ‖sample m C ξ - sample m' C' ξ‖ ^ 2 ≤ 2 * sqDist m m' C C' * (1 + rowMax S ξ) := by
  rw [sample_sub]
  have h := norm_toLp_supported_le (m - m') hC ξ
  have hS := rowMax_nonneg (S := S) ξ
  have h1 : 0 ≤ ∑ i, (m - m') i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∑ i, ∑ j, (C - C') i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← sqDist_split]
  nlinarith

lemma mask_gradScale {w : ℕ} (hS : IsPattern S w) (g : Point d) (ξ : Fin d → ℝ) (i j : Fin d) :
    maskScale S (gradScale g ξ) i j = if j ∈ S i then g i * ξ j else 0 := by
  unfold maskScale gradScale
  by_cases hj : j ∈ S i
  · simp [hj, (hS i).2.1 j hj]
  · simp [hj]

lemma pin_mask_grad_self_le {w : ℕ} (hS : IsPattern S w) (g : Point d) (ξ : Fin d → ℝ) :
    pin (maskPair S (gradPair g ξ)) (maskPair S (gradPair g ξ)) ≤ (1 + rowMax S ξ) * ‖g‖ ^ 2 := by
  rw [norm_sq_eq_sum]
  unfold pin pinner
  simp only [maskPair, gradPair, mask_gradScale hS]
  have hrow : ∀ i, ∑ j, (if j ∈ S i then g i * ξ j else 0) * (if j ∈ S i then g i * ξ j else 0) ≤
      g i ^ 2 * rowMax S ξ := by
    intro i
    have he : ∀ j, (if j ∈ S i then g i * ξ j else 0) * (if j ∈ S i then g i * ξ j else 0) =
        if j ∈ S i then g i ^ 2 * ξ j ^ 2 else 0 := by
      intro j
      split_ifs <;> ring
    simp_rw [he]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (rowSq_le_rowMax (S := S) ξ i) (sq_nonneg _)
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hrow i
  have he : (1 + rowMax S ξ) * ∑ i, g i ^ 2 =
      ∑ i, gradLoc g i * gradLoc g i + ∑ i, g i ^ 2 * rowMax S ξ := by
    rw [add_mul, one_mul, ← Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by simp [gradLoc]; ring
    · rw [mul_comm]
  rw [he]
  linarith

lemma maskedStep_eq (η : ℝ) (z : Location d × Scale d) (g : Point d) (ξ : Fin d → ℝ) :
    maskedStep S η z g ξ = proxPair η (z - η • maskPair S (gradPair g ξ)) := rfl

lemma maskedStep_family {w : ℕ} (hS : IsPattern S w) {η : ℝ} (hη : 0 < η)
    {z : Location d × Scale d} (hz : InFamily S z.2) (g : Point d) (ξ : Fin d → ℝ) :
    InFamily S (maskedStep S η z g ξ).2 := by
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hj => ?_⟩
  · have hne : i ≠ j := ne_of_lt hij
    simp only [maskedStep, proxScale, hne, ↓reduceIte, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      mask_gradScale hS]
    have hj : j ∉ S i := fun hj => absurd ((hS i).2.1 j hj) (not_le.mpr hij)
    simp [hj, hz.1.1 i j hij]
  · simp only [maskedStep, proxScale, ↓reduceIte]
    exact proxLog_pos hη _
  · have hne : i ≠ j := fun h => hj (h ▸ (hS i).1)
    simp only [maskedStep, proxScale, hne, ↓reduceIte, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      mask_gradScale hS, hj, hz.2 i j hj]
    ring

end Basic

section Optimality

variable {S : Fin d → Finset (Fin d)} {L μ : ℝ} {V : Point d → ℝ}

def IsPatternOptimal (V : Point d → ℝ) (S : Fin d → Finset (Fin d)) (ms : Location d)
    (Cs : Scale d) : Prop :=
  InFamily S Cs ∧ ∀ m C, InFamily S C → objective V ms Cs ≤ objective V m C

lemma pattern_opt_pinner (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (hopt : IsPatternOptimal V S ms Cs) (u : Location d) {U : Scale d} (hU : IsLower U)
    (hUS : IsSupported S U) :
    pinner (meanLoc V ms Cs) (meanScale V ms Cs) u U = ∑ i, U i i / Cs i i := by
  set A := pinner (meanLoc V ms Cs) (meanScale V ms Cs) u U
  set B := (∑ i, u i ^ 2) + ∑ i, ∑ j, U i j ^ 2
  set s : Fin d → ℝ := fun i => U i i / Cs i i
  set M := ∑ i, |s i|
  have hCs := hopt.1.1
  have hpos : ∀ i, 0 < Cs i i := hCs.2
  have ht0 : 0 < 1 / (2 * (M + 1)) := by
    have : 0 ≤ M := Finset.sum_nonneg fun i _ => abs_nonneg _
    positivity
  suffices hq : A - ∑ i, s i = 0 by
    have : A = ∑ i, s i := by linarith
    simpa [s] using this
  refine quad_zero (b := L / 2 * B + 2 * ∑ i, s i ^ 2) ht0 fun t ht => ?_
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hts : ∀ i, |t * s i| ≤ 1 / 2 := by
    intro i
    have hsi : |s i| ≤ M := Finset.single_le_sum (f := fun i => |s i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    rw [abs_mul]
    have h1 : |t| * |s i| ≤ 1 / (2 * (M + 1)) * M :=
      mul_le_mul ht hsi (abs_nonneg _) (le_of_lt ht0)
    have h2 : 1 / (2 * (M + 1)) * M ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hdiag : ∀ i, (Cs + t • U) i i = Cs i i * (1 + t * s i) := by
    intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, s]
    rw [mul_add, mul_one, mul_left_comm, mul_div_cancel₀ _ (hpos i).ne']
  have hfam : InFamily S (Cs + t • U) := by
    refine ⟨⟨isLower_add hCs.1 (isLower_smul hU t), fun i => ?_⟩, fun i j hj => ?_⟩
    · rw [hdiag i]
      have := neg_abs_le (t * s i)
      have := hts i
      have : 0 < 1 + t * s i := by linarith
      exact mul_pos (hpos i) this
    · simp [Pi.add_apply, Pi.smul_apply, hopt.1.2 i j hj, hUS i j hj]
  have hmin := hopt.2 (ms + t • u) (Cs + t • U) hfam
  have hlow : IsLower ((Cs + t • U) - Cs) := by
    rw [add_sub_cancel_left]
    exact isLower_smul hU t
  have heu := energy_upper h ms (ms + t • u) hlow
  rw [add_sub_cancel_left, add_sub_cancel_left, pinner_smul_right, sqDist_smul] at heu
  have hlog : ∀ i, -Real.log ((Cs + t • U) i i) ≤
      -Real.log (Cs i i) + (-(t * s i) + 2 * (t * s i) ^ 2) := by
    intro i
    rw [hdiag i, Real.log_mul (hpos i).ne' (by have := hts i; have := neg_abs_le (t * s i); linarith)]
    have := neg_log_one_add_le (show -1 / 2 ≤ t * s i by
      have := hts i; have := neg_abs_le (t * s i); linarith)
    linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hlog i
  rw [objective_eq, objective_eq] at hmin
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hsum
  have he1 : ∑ i, (t * s i) ^ 2 = t ^ 2 * ∑ i, s i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [he1] at hsum
  nlinarith

lemma isSupported_optScale {w : ℕ} (hS : IsPattern S w) (Cs : Scale d) :
    IsSupported S (optScale Cs) := by
  intro i j hj
  have hne : i ≠ j := fun h => hj (h ▸ (hS i).1)
  simp [optScale, hne]

lemma isLower_optScale (Cs : Scale d) : IsLower (optScale Cs) := by
  intro i j hij
  simp [optScale, ne_of_lt hij]

lemma pattern_opt_pin (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (hopt : IsPatternOptimal V S ms Cs) {b : Location d × Scale d} (hb : IsLower b.2)
    (hbS : IsSupported S b.2) :
    pin (meanPair V (ms, Cs)) b = pin (optPair Cs) b := by
  unfold pin meanPair optPair
  rw [pattern_opt_pinner h hopt b.1 hb hbS, pinner_optScale]

lemma bregmanMean_identity (h : Potential L μ V) (ms : Location d) (Cs : Scale d)
    (m : Location d) {C : Scale d} (hC : IsLower (C - Cs)) :
    bregmanMean V ms Cs m C = energy V m C - energy V ms Cs -
      pinner (meanLoc V ms Cs) (meanScale V ms Cs) (m - ms) (C - Cs) := by
  have hi := integral_inner_grad h ms Cs (m - ms) hC
  unfold bregmanMean bregman
  simp_rw [sample_sub]
  rw [integral_sub ((integrable_V_sample h m C).subL (integrable_V_sample h ms Cs)) hi.1,
    integral_sub (integrable_V_sample h m C) (integrable_V_sample h ms Cs), hi.2]
  rfl

lemma mean_monotone (h : Potential L μ V) (z w : Location d × Scale d)
    (hzw : IsLower (z.2 - w.2)) (hwz : IsLower (w.2 - z.2)) :
    bregmanMean V w.1 w.2 z.1 z.2 + μ / 2 * sqd z w ≤
      pin (meanPair V z - meanPair V w) (z - w) := by
  have hl := energy_lower h z.1 w.1 hwz
  have hb := bregmanMean_identity h w.1 w.2 z.1 hzw
  have e1 : pin (meanPair V z - meanPair V w) (z - w) =
      -pinner (meanLoc V z.1 z.2) (meanScale V z.1 z.2) (w.1 - z.1) (w.2 - z.2) -
        pinner (meanLoc V w.1 w.2) (meanScale V w.1 w.2) (z.1 - w.1) (z.2 - w.2) := by
    rw [pin_sub_left]
    unfold pin meanPair
    simp only [Prod.fst_sub, Prod.snd_sub, pinner_sub_right]
    ring
  have e2 : sqDist w.1 z.1 w.2 z.2 = sqd z w := sqDist_comm _ _ _ _
  rw [e1]
  rw [e2] at hl
  linarith

end Optimality

end OracleTemplate.StructuredGaussianVariational

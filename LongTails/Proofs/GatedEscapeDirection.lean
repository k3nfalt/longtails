import LongTails.Algorithms.GatedPerturbedEscape
import LongTails.Proofs.RelativeCurvatureSpectrum

namespace LongTails.Proofs.GatedEscapeDirection

open scoped RealInnerProductSpace
open LongTails.Algorithms.GatedPerturbedEscape

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

noncomputable def proj (b : OrthonormalBasis ι ℝ E) (J : Finset ι) (v : E) : E :=
  ∑ j ∈ J, ⟪b j, v⟫ • b j

noncomputable def pmass (b : OrthonormalBasis ι ℝ E) (J : Finset ι) (v : E) : ℝ := ‖proj b J v‖

lemma pmass_nonneg (b : OrthonormalBasis ι ℝ E) (J : Finset ι) (v : E) : 0 ≤ pmass b J v :=
  norm_nonneg _

open Classical in
lemma inner_proj (b : OrthonormalBasis ι ℝ E) (J : Finset ι) (v : E) (i : ι) :
    ⟪b i, proj b J v⟫ = if i ∈ J then ⟪b i, v⟫ else 0 := by
  classical
  unfold proj
  rw [inner_sum]
  simp_rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

lemma pmass_sq (b : OrthonormalBasis ι ℝ E) (J : Finset ι) (v : E) :
    pmass b J v ^ 2 = ∑ j ∈ J, ⟪b j, v⟫ ^ 2 := by
  classical
  unfold pmass
  rw [← b.sum_sq_inner_right (proj b J v)]
  simp_rw [inner_proj]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ J)]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h0 : ∑ x ∈ Finset.univ.filter (fun i => i ∉ J), (if x ∈ J then ⟪b x, v⟫ else 0) ^ 2 = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    rw [Finset.mem_filter] at hi; simp [hi.2]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl; intro i hi; simp [hi]

lemma pmass_le_norm (b : OrthonormalBasis ι ℝ E) (J : Finset ι) (v : E) : pmass b J v ≤ ‖v‖ := by
  have h1 := pmass_sq b J v
  have h2 : ∑ j ∈ J, ⟪b j, v⟫ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← b.sum_sq_inner_right v]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) (fun _ _ _ => sq_nonneg _)
  exact (sq_le_sq₀ (pmass_nonneg _ _ _) (norm_nonneg _)).mp (by linarith)

lemma proj_add (b : OrthonormalBasis ι ℝ E) (J : Finset ι) (u v : E) :
    proj b J (u + v) = proj b J u + proj b J v := by
  unfold proj; simp only [inner_add_right, add_smul, Finset.sum_add_distrib]

lemma proj_smul (b : OrthonormalBasis ι ℝ E) (J : Finset ι) (c : ℝ) (v : E) :
    proj b J (c • v) = c • proj b J v := by
  unfold proj; simp only [inner_smul_right, mul_smul, Finset.smul_sum]

lemma pmass_add_le (b : OrthonormalBasis ι ℝ E) (J : Finset ι) (u v : E) :
    pmass b J (u + v) ≤ pmass b J u + pmass b J v := by
  unfold pmass; rw [proj_add]; exact norm_add_le _ _

lemma pmass_neg (b : OrthonormalBasis ι ℝ E) (J : Finset ι) (v : E) : pmass b J (-v) = pmass b J v := by
  unfold pmass
  rw [show -v = (-1 : ℝ) • v by simp, proj_smul, norm_smul]; simp

lemma pmass_smul (b : OrthonormalBasis ι ℝ E) (J : Finset ι) (c : ℝ) (v : E) :
    pmass b J (c • v) = |c| * pmass b J v := by
  unfold pmass; rw [proj_smul, norm_smul, Real.norm_eq_abs]

lemma pmass_sub_le (b : OrthonormalBasis ι ℝ E) (J : Finset ι) (u v : E) :
    pmass b J (u - v) ≤ pmass b J u + ‖v‖ := by
  rw [sub_eq_add_neg]
  exact (pmass_add_le b J u (-v)).trans (by rw [pmass_neg]; linarith [pmass_le_norm b J v])

lemma pmass_lin_le (H : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, H v⟫ = eig i * ⟪b i, v⟫) (J : Finset ι) {η a : ℝ} (ha : 0 ≤ a)
    (hJ : ∀ j ∈ J, |1 - η * eig j| ≤ a) (v : E) :
    pmass b J (v - η • H v) ≤ a * pmass b J v := by
  have hterm : ∑ j ∈ J, ⟪b j, v - η • H v⟫ ^ 2 ≤ ∑ j ∈ J, a ^ 2 * ⟪b j, v⟫ ^ 2 := by
    apply Finset.sum_le_sum
    intro j hj
    have hco : ⟪b j, v - η • H v⟫ = (1 - η * eig j) * ⟪b j, v⟫ := by
      rw [inner_sub_right, inner_smul_right, hc]; ring
    rw [hco, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hJ j hj) 2
  have hsq : pmass b J (v - η • H v) ^ 2 ≤ (a * pmass b J v) ^ 2 := by
    rw [mul_pow, pmass_sq, pmass_sq, Finset.mul_sum]
    exact hterm
  exact (sq_le_sq₀ (pmass_nonneg _ _ _) (mul_nonneg ha (pmass_nonneg _ _ _))).mp hsq

lemma pmass_lin_ge (H : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, H v⟫ = eig i * ⟪b i, v⟫) (J : Finset ι) {η : ℝ}
    (hJ : ∀ j ∈ J, 1 ≤ |1 - η * eig j|) (v : E) :
    pmass b J v ≤ pmass b J (v - η • H v) := by
  refine (sq_le_sq₀ (pmass_nonneg _ _ _) (pmass_nonneg _ _ _)).mp ?_
  rw [pmass_sq, pmass_sq]
  apply Finset.sum_le_sum
  intro j hj
  have hco : ⟪b j, v - η • H v⟫ = (1 - η * eig j) * ⟪b j, v⟫ := by
    rw [inner_sub_right, inner_smul_right, hc]; ring
  rw [hco, mul_pow]
  have h1 : 1 ≤ (1 - η * eig j) ^ 2 := by
    rw [← sq_abs]; nlinarith [hJ j hj, abs_nonneg (1 - η * eig j)]
  nlinarith [sq_nonneg (⟪b j, v⟫)]

lemma clip_eq_smul (r : ℝ) (u : E) (hr : 0 ≤ r) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ clip r u = c • u ∧ (‖u‖ ≤ r ∨ ‖clip r u‖ = r) := by
  unfold clip
  split_ifs with h
  · exact ⟨1, zero_le_one, le_rfl, (one_smul _ _).symm, Or.inl h⟩
  · push Not at h
    have hu : 0 < ‖u‖ := lt_of_le_of_lt hr h
    refine ⟨r / ‖u‖, div_nonneg hr hu.le, (div_le_one hu).mpr h.le, rfl, Or.inr ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr hu.le), div_mul_cancel₀ _ hu.ne']

lemma clip_norm_le (r : ℝ) (u : E) (hr : 0 ≤ r) : ‖clip r u‖ ≤ r := by
  unfold clip
  split_ifs with h
  · exact h
  · push Not at h
    have hu : 0 < ‖u‖ := lt_of_le_of_lt hr h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr hu.le), div_mul_cancel₀ _ hu.ne']

section traj

variable (H : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
  (hc : ∀ i v, ⟪b i, H v⟫ = eig i * ⟪b i, v⟫)

include hc

theorem small_modes (J : Finset ι) {η a r : ℝ} (ha : 1 ≤ a) (hr : 0 ≤ r)
    (hJ : ∀ j ∈ J, |1 - η * eig j| ≤ a) (v : ℕ → E) (fo e : ℕ → E)
    (hv : ∀ t, v (t + 1) = clip r (v t - η • H (v t) - η • fo t - η • e t)) (hη : 0 ≤ η) :
    ∀ t, pmass b J (v t) ≤ a ^ t * (‖v 0‖ + ∑ s ∈ Finset.range t, η * (‖fo s‖ + ‖e s‖)) := by
  intro t
  induction t with
  | zero => simp [pmass_le_norm]
  | succ t ih =>
    obtain ⟨c, hc0, hc1, hcl, _⟩ := clip_eq_smul r (v t - η • H (v t) - η • fo t - η • e t) hr
    rw [hv, hcl, pmass_smul, abs_of_nonneg hc0]
    have h1 : pmass b J (v t - η • H (v t) - η • fo t - η • e t) ≤
        a * pmass b J (v t) + η * (‖fo t‖ + ‖e t‖) := by
      have s1 := pmass_sub_le b J (v t - η • H (v t) - η • fo t) (η • e t)
      have s2 := pmass_sub_le b J (v t - η • H (v t)) (η • fo t)
      have s3 := pmass_lin_le H b eig hc J (by linarith) hJ (v t)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at s1 s2
      nlinarith
    have hpos : 0 ≤ pmass b J (v t - η • H (v t) - η • fo t - η • e t) := pmass_nonneg _ _ _
    have h2 : c * pmass b J (v t - η • H (v t) - η • fo t - η • e t) ≤
        pmass b J (v t - η • H (v t) - η • fo t - η • e t) := by nlinarith
    have hat : 0 ≤ a ^ t := pow_nonneg (by linarith) t
    have hsum : 0 ≤ ∑ s ∈ Finset.range t, η * (‖fo s‖ + ‖e s‖) :=
      Finset.sum_nonneg fun s _ => mul_nonneg hη (by positivity)
    rw [Finset.sum_range_succ, pow_succ]
    have ha1 : 1 ≤ a ^ t := one_le_pow₀ ha
    calc c * pmass b J _ ≤ a * pmass b J (v t) + η * (‖fo t‖ + ‖e t‖) := h2.trans h1
      _ ≤ a * (a ^ t * (‖v 0‖ + ∑ s ∈ Finset.range t, η * (‖fo s‖ + ‖e s‖))) + η * (‖fo t‖ + ‖e t‖) := by
        have := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ a); linarith
      _ ≤ a ^ t * a * (‖v 0‖ + (∑ s ∈ Finset.range t, η * (‖fo s‖ + ‖e s‖) + η * (‖fo t‖ + ‖e t‖))) := by
        have hx : 0 ≤ η * (‖fo t‖ + ‖e t‖) := mul_nonneg hη (by positivity)
        have : η * (‖fo t‖ + ‖e t‖) ≤ a ^ t * a * (η * (‖fo t‖ + ‖e t‖)) := by
          have : 1 ≤ a ^ t * a := by nlinarith
          nlinarith
        nlinarith

theorem large_modes (N J : Finset ι) (hNJ : ∀ j, j ∈ N ∨ j ∈ J) {η r R : ℝ} (hr : 0 ≤ r)
    (hN : ∀ j ∈ N, 1 ≤ |1 - η * eig j|) (v : ℕ → E) (fo e : ℕ → E)
    (hv : ∀ t, v (t + 1) = clip r (v t - η • H (v t) - η • fo t - η • e t)) (hη : 0 ≤ η)
    (Tm : ℕ) (hJ : ∀ t ≤ Tm, pmass b J (v t) ≤ R) (τ : ℕ)
    (hclip : r < ‖v τ - η • H (v τ) - η • fo τ - η • e τ‖) :
    ∀ t, τ < t → t ≤ Tm →
      Real.sqrt (r ^ 2 - R ^ 2) - ∑ s ∈ Finset.Ico τ t, η * (‖fo s‖ + ‖e s‖) ≤ pmass b N (v t) := by
  classical
  have hfull : ∀ u : E, pmass b N u ^ 2 + pmass b J u ^ 2 ≥ ‖u‖ ^ 2 := by
    intro u
    rw [pmass_sq, pmass_sq, ← b.sum_sq_inner_right u]
    calc ∑ j, ⟪b j, u⟫ ^ 2 ≤ ∑ j, ((if j ∈ N then ⟪b j, u⟫ ^ 2 else 0) + (if j ∈ J then ⟪b j, u⟫ ^ 2 else 0)) := by
          apply Finset.sum_le_sum; intro j _
          rcases hNJ j with h | h
          · simp only [h, ↓reduceIte]; split_ifs <;> nlinarith [sq_nonneg ⟪b j, u⟫]
          · simp only [h, ↓reduceIte]; split_ifs <;> nlinarith [sq_nonneg ⟪b j, u⟫]
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem]; simp
  have hreset : ∀ t, t + 1 ≤ Tm → r < ‖v t - η • H (v t) - η • fo t - η • e t‖ →
      Real.sqrt (r ^ 2 - R ^ 2) ≤ pmass b N (v (t + 1)) := by
    intro t htm ht
    have hn : ‖v (t + 1)‖ = r := by
      obtain ⟨_, _, _, _, hor⟩ := clip_eq_smul r (v t - η • H (v t) - η • fo t - η • e t) hr
      rw [hv]; rcases hor with h | h
      · linarith
      · exact h
    have h1 := hfull (v (t + 1))
    rw [hn] at h1
    have h2 := hJ (t + 1) htm
    have h3 : pmass b J (v (t + 1)) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (pmass_nonneg _ _ _) h2 2
    calc Real.sqrt (r ^ 2 - R ^ 2) ≤ Real.sqrt (pmass b N (v (t + 1)) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = pmass b N (v (t + 1)) := Real.sqrt_sq (pmass_nonneg _ _ _)
  have hstep : ∀ t, t + 1 ≤ Tm → (pmass b N (v t) - η * (‖fo t‖ + ‖e t‖) ≤ pmass b N (v (t + 1)) ∨
      Real.sqrt (r ^ 2 - R ^ 2) ≤ pmass b N (v (t + 1))) := by
    intro t htm
    by_cases ht : r < ‖v t - η • H (v t) - η • fo t - η • e t‖
    · exact Or.inr (hreset t htm ht)
    · left
      push Not at ht
      have hcl : clip r (v t - η • H (v t) - η • fo t - η • e t) = v t - η • H (v t) - η • fo t - η • e t := by
        unfold clip; rw [ite_eq_left ht]
      rw [hv, hcl]
      have s3 := pmass_lin_ge H b eig hc N hN (v t)
      have hdec : v t - η • H (v t) = (v t - η • H (v t) - η • fo t - η • e t) + (η • fo t + η • e t) := by abel
      have s4 := pmass_add_le b N (v t - η • H (v t) - η • fo t - η • e t) (η • fo t + η • e t)
      rw [← hdec] at s4
      have s5 : pmass b N (η • fo t + η • e t) ≤ η * (‖fo t‖ + ‖e t‖) := by
        refine (pmass_le_norm _ _ _).trans ?_
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]; ring_nf; rfl
      linarith
  intro t ht htm
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases htt : τ = t
    · subst htt
      have := hreset τ htm hclip
      simp only [Finset.Ico_self, Finset.sum_empty, sub_zero, Nat.Ico_succ_singleton] at *
      have hnn : 0 ≤ η * (‖fo τ‖ + ‖e τ‖) := mul_nonneg hη (by positivity)
      rw [Finset.sum_singleton]; linarith
    · have ih' := ih (by omega) (by omega)
      rw [Finset.sum_Ico_succ_top (by omega)]
      have hnn : 0 ≤ η * (‖fo t‖ + ‖e t‖) := mul_nonneg hη (by positivity)
      have hsum_nn : 0 ≤ ∑ s ∈ Finset.Ico τ t, η * (‖fo s‖ + ‖e s‖) :=
        Finset.sum_nonneg fun s _ => mul_nonneg hη (by positivity)
      rcases hstep t htm with h | h
      · linarith
      · linarith

theorem rayleigh_split (N P : Finset ι) {μ : ℝ}
    (hN : ∀ j ∈ N, eig j ≤ -μ) (hNP : ∀ j, j ∉ N → j ∉ P → eig j ≤ 0) (hdisj : Disjoint N P)
    (v : E) :
    ⟪v, H v⟫ ≤ -μ * pmass b N v ^ 2 + ∑ j ∈ P, eig j * ⟪b j, v⟫ ^ 2 := by
  classical
  rw [LongTails.Proofs.RelativeCurvatureSpectrum.quadratic_decomposition H b eig hc v, pmass_sq,
    Finset.mul_sum]
  have hsplit : ∑ j, eig j * ⟪b j, v⟫ ^ 2 =
      ∑ j, ((if j ∈ N then eig j * ⟪b j, v⟫ ^ 2 else 0) + (if j ∈ P then eig j * ⟪b j, v⟫ ^ 2 else 0) +
        (if j ∉ N ∧ j ∉ P then eig j * ⟪b j, v⟫ ^ 2 else 0)) := by
    apply Finset.sum_congr rfl; intro j _
    by_cases h1 : j ∈ N
    · have h2 : j ∉ P := Finset.disjoint_left.mp hdisj h1
      simp [h1, h2]
    · by_cases h2 : j ∈ P <;> simp [h1, h2]
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem]
  simp only [Finset.univ_inter]
  have h3 : ∑ j, (if j ∉ N ∧ j ∉ P then eig j * ⟪b j, v⟫ ^ 2 else 0) ≤ 0 := by
    apply Finset.sum_nonpos; intro j _
    split_ifs with h
    · exact mul_nonpos_of_nonpos_of_nonneg (hNP j h.1 h.2) (sq_nonneg _)
    · exact le_rfl
  have h4 : ∑ j ∈ N, eig j * ⟪b j, v⟫ ^ 2 ≤ ∑ j ∈ N, -μ * ⟪b j, v⟫ ^ 2 := by
    apply Finset.sum_le_sum; intro j hj
    exact mul_le_mul_of_nonneg_right (hN j hj) (sq_nonneg _)
  linarith

end traj

end LongTails.Proofs.GatedEscapeDirection

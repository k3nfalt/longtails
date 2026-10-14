import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.IntermediateValue

open scoped RealInnerProductSpace

namespace OracleTemplate.StronglyMonotoneZero

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_eq_zero_of_mem_span {ι : Type*} (b : ι → E) (S : Finset ι) {g w : E}
    (hg : ∀ i ∈ S, ⟪g, b i⟫ = 0) (hw : w ∈ Submodule.span ℝ (b '' (S : Set ι))) : ⟪g, w⟫ = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨i, hi, rfl⟩
    exact hg i hi
  · simp
  · intro u v _ _ hu hv
    rw [inner_add_right, hu, hv, add_zero]
  · intro c u _ hu
    rw [inner_smul_right, hu, mul_zero]

lemma partial_zero {ι : Type*} [DecidableEq ι] (b : ι → E) (hb : Orthonormal ℝ b)
    {G : E → E} (hc : Continuous G) {μ : ℝ} (hμ : 0 < μ)
    (hmono : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫) (S : Finset ι) :
    ∀ a : E, ∃ p : E, p - a ∈ Submodule.span ℝ (b '' (S : Set ι)) ∧ ∀ i ∈ S, ⟪G p, b i⟫ = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro a
    exact ⟨a, by simp, by simp⟩
  | insert j S hj ih =>
    intro a
    choose p hp hperp using fun t : ℝ => ih (a + t • b j)
    have hsub : Submodule.span ℝ (b '' (S : Set ι)) ≤
        Submodule.span ℝ (b '' ((insert j S : Finset ι) : Set ι)) := by
      apply Submodule.span_mono
      apply Set.image_mono
      simp
    have hbj : b j ∈ Submodule.span ℝ (b '' ((insert j S : Finset ι) : Set ι)) :=
      Submodule.subset_span ⟨j, by simp, rfl⟩
    have hbjw : ∀ w ∈ Submodule.span ℝ (b '' (S : Set ι)), ⟪b j, w⟫ = 0 := by
      intro w hw
      refine inner_eq_zero_of_mem_span b S (fun i hi => ?_) hw
      exact hb.2 (fun h => hj (h ▸ hi))
    have hnorm : ‖b j‖ = 1 := hb.1 j
    have hclose : ∀ t t' : ℝ, μ * ‖p t - (p t' + (t - t') • b j)‖ ≤
        ‖G (p t' + (t - t') • b j) - G (p t')‖ := by
      intro t t'
      set q := p t' + (t - t') • b j with hq
      have hmem : p t - q ∈ Submodule.span ℝ (b '' (S : Set ι)) := by
        have e : p t - q = (p t - (a + t • b j)) - (p t' - (a + t' • b j)) := by
          rw [hq, sub_smul]; abel
        rw [e]
        exact Submodule.sub_mem _ (hp t) (hp t')
      have h1 : ⟪G (p t), p t - q⟫ = 0 := inner_eq_zero_of_mem_span b S (hperp t) hmem
      have h2 : ⟪G (p t'), p t - q⟫ = 0 := inner_eq_zero_of_mem_span b S (hperp t') hmem
      have h3 := hmono (p t) q
      have h4 : ⟪G (p t) - G q, p t - q⟫ = ⟪G (p t') - G q, p t - q⟫ := by
        rw [inner_sub_left, inner_sub_left, h1, h2]
      have h5 : ⟪G (p t') - G q, p t - q⟫ ≤ ‖G (p t') - G q‖ * ‖p t - q‖ := real_inner_le_norm _ _
      have h6 : ‖G (p t') - G q‖ = ‖G q - G (p t')‖ := norm_sub_rev _ _
      rcases eq_or_lt_of_le (norm_nonneg (p t - q)) with h0 | h0
      · rw [← h0, mul_zero]; exact norm_nonneg _
      · rw [← h6]
        have : μ * ‖p t - q‖ * ‖p t - q‖ ≤ ‖G (p t') - G q‖ * ‖p t - q‖ := by nlinarith
        exact le_of_mul_le_mul_right this h0
    have hpc : Continuous p := by
      rw [continuous_iff_continuousAt]
      intro t'
      have hq : Filter.Tendsto (fun t : ℝ => p t' + (t - t') • b j) (nhds t') (nhds (p t')) := by
        have : Continuous fun t : ℝ => p t' + (t - t') • b j := by fun_prop
        have h := this.tendsto t'
        simpa using h
      have hG : Filter.Tendsto (fun t : ℝ => ‖G (p t' + (t - t') • b j) - G (p t')‖ / μ)
          (nhds t') (nhds 0) := by
        have h := ((hc.tendsto (p t')).comp hq).sub_const (G (p t'))
        have h' := (h.norm).div_const μ
        simpa using h'
      have hd : Filter.Tendsto (fun t : ℝ => ‖p t - (p t' + (t - t') • b j)‖) (nhds t') (nhds 0) := by
        refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) hG
        rw [le_div_iff₀ hμ, mul_comm]
        exact hclose t t'
      have hd' : Filter.Tendsto (fun t : ℝ => p t - (p t' + (t - t') • b j)) (nhds t') (nhds 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mpr hd
      have := hd'.add hq
      simpa [ContinuousAt] using this
    let φ : ℝ → ℝ := fun t => ⟪G (p t), b j⟫
    have hφc : Continuous φ := (hc.comp hpc).inner continuous_const
    have hinc : ∀ t t' : ℝ, μ * (t - t') ^ 2 ≤ (φ t - φ t') * (t - t') := by
      intro t t'
      have hmem : p t - p t' - (t - t') • b j ∈ Submodule.span ℝ (b '' (S : Set ι)) := by
        have e : p t - p t' - (t - t') • b j = (p t - (a + t • b j)) - (p t' - (a + t' • b j)) := by
          rw [sub_smul]; abel
        rw [e]
        exact Submodule.sub_mem _ (hp t) (hp t')
      set w := p t - p t' - (t - t') • b j with hw
      have e : p t - p t' = (t - t') • b j + w := by rw [hw]; abel
      have h1 : ⟪G (p t), w⟫ = 0 := inner_eq_zero_of_mem_span b S (hperp t) hmem
      have h2 : ⟪G (p t'), w⟫ = 0 := inner_eq_zero_of_mem_span b S (hperp t') hmem
      have h3 := hmono (p t) (p t')
      have h4 : ⟪G (p t) - G (p t'), p t - p t'⟫ = (φ t - φ t') * (t - t') := by
        have e1 : ⟪G (p t) - G (p t'), w⟫ = 0 := by rw [inner_sub_left, h1, h2, sub_zero]
        have e2 : ⟪G (p t) - G (p t'), (t - t') • b j⟫ = (t - t') * (φ t - φ t') := by
          rw [inner_smul_right, inner_sub_left]
        rw [e, inner_add_right, e1, e2]
        ring
      have h5 : (t - t') ^ 2 ≤ ‖p t - p t'‖ ^ 2 := by
        have e3 : ⟪(t - t') • b j, w⟫ = 0 := by rw [inner_smul_left, hbjw w hmem, mul_zero]
        have e4 : ‖(t - t') • b j‖ ^ 2 = (t - t') ^ 2 := by
          rw [norm_smul, hnorm, mul_one, Real.norm_eq_abs, sq_abs]
        rw [e, norm_add_sq_real, e3, e4]
        nlinarith [sq_nonneg ‖w‖]
      nlinarith
    have hzero : (0 : ℝ) ∈ Set.range φ := by
      refine mem_range_of_exists_le_of_exists_ge hφc ⟨-(|φ 0| / μ), ?_⟩ ⟨|φ 0| / μ, ?_⟩
      · have h := hinc (-(|φ 0| / μ)) 0
        have hpos : 0 ≤ |φ 0| / μ := by positivity
        have e : μ * (|φ 0| / μ) = |φ 0| := by field_simp
        rcases eq_or_lt_of_le hpos with h0 | h0
        · have : |φ 0| = 0 := by rw [← e, ← h0, mul_zero]
          rw [← h0, neg_zero]
          exact le_of_eq (abs_eq_zero.mp this)
        · have : φ (-(|φ 0| / μ)) ≤ φ 0 - |φ 0| := by nlinarith
          linarith [le_abs_self (φ 0)]
      · have h := hinc (|φ 0| / μ) 0
        have hpos : 0 ≤ |φ 0| / μ := by positivity
        have e : μ * (|φ 0| / μ) = |φ 0| := by field_simp
        rcases eq_or_lt_of_le hpos with h0 | h0
        · have : |φ 0| = 0 := by rw [← e, ← h0, mul_zero]
          rw [← h0]
          exact le_of_eq (abs_eq_zero.mp this).symm
        · have : φ 0 + |φ 0| ≤ φ (|φ 0| / μ) := by nlinarith
          linarith [neg_abs_le (φ 0)]
    obtain ⟨t, ht⟩ := hzero
    refine ⟨p t, ?_, ?_⟩
    · have e : p t - a = (p t - (a + t • b j)) + t • b j := by abel
      rw [e]
      exact Submodule.add_mem _ (hsub (hp t)) (Submodule.smul_mem _ _ hbj)
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ht
      · exact hperp t i hi

theorem exists_zero [FiniteDimensional ℝ E] {G : E → E} (hc : Continuous G) {μ : ℝ} (hμ : 0 < μ)
    (hmono : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫) : ∃ x, G x = 0 := by
  classical
  let b := stdOrthonormalBasis ℝ E
  obtain ⟨p, -, hp⟩ := partial_zero b b.orthonormal hc hμ hmono Finset.univ 0
  refine ⟨p, ?_⟩
  apply b.repr.injective
  ext i
  rw [OrthonormalBasis.repr_apply_apply, map_zero, real_inner_comm]
  simpa using hp i (Finset.mem_univ i)

end OracleTemplate.StronglyMonotoneZero

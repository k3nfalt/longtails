import LongTailsOnline.Setups.StationaryTaskAllocation

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LongTailsOnline.Proofs.TaskAllocation

lemma clipped_mean_bias {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {μ H t : ℝ} {c : ℝ≥0}
    (hX : Integrable X P) (hmean : (∫ ω, X ω ∂P) = μ)
    (hsg : HasSubgaussianMGF (fun ω => X ω - μ) c P) (ht : 0 < t) :
    0 ≤ μ - (∫ ω, min (X ω) H ∂P) ∧
      μ - (∫ ω, min (X ω) H ∂P) ≤
        Real.exp (-t * (H - μ) + c * t ^ 2 / 2) / t := by
  have hclip : Integrable (fun ω => min (X ω) H) P := hX.inf (integrable_const H)
  have heq : (fun ω => Real.exp (t * (X ω - H))) =
      fun ω => Real.exp (t * (μ - H)) * Real.exp (t * (X ω - μ)) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp : Integrable (fun ω => Real.exp (t * (X ω - H))) P := by
    rw [heq]
    exact (hsg.integrable_exp_mul t).const_mul _
  have hpoint (ω : Ω) : X ω - min (X ω) H ≤ Real.exp (t * (X ω - H)) / t := by
    by_cases hle : X ω ≤ H
    · rw [min_eq_left hle, sub_self]
      positivity
    · rw [min_eq_right (le_of_not_ge hle)]
      simpa only [div_eq_mul_inv, mul_comm] using Real.le_inv_mul_exp (X ω - H) ht
  have hnonneg : 0 ≤ ∫ ω, X ω - min (X ω) H ∂P :=
    integral_nonneg (fun ω => sub_nonneg.mpr (min_le_left _ _))
  have hupper : (∫ ω, X ω - min (X ω) H ∂P) ≤
      ∫ ω, Real.exp (t * (X ω - H)) / t ∂P :=
    integral_mono_ae (hX.sub hclip) (hexp.div_const t) (Filter.Eventually.of_forall hpoint)
  rw [integral_sub hX hclip, hmean] at hnonneg hupper
  refine ⟨hnonneg, hupper.trans ?_⟩
  rw [integral_div, heq, integral_const_mul]
  have hmgf := hsg.mgf_le t
  have hmul := mul_le_mul_of_nonneg_left hmgf (Real.exp_pos (t * (μ - H))).le
  apply (div_le_div_iff_of_pos_right ht).mpr
  unfold mgf at hmul
  exact hmul.trans_eq (by rw [← Real.exp_add]; congr 1; ring)

lemma exp_le_quadratic {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.norm_exp_sub_one_sub_id_le (by simpa only [Real.norm_eq_abs] using hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs] at h
  have := (le_abs_self (Real.exp x - 1 - x)).trans h
  linarith

lemma bounded_integrable_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} {H : ℝ}
    (hZ : Measurable Z) (_hH : 0 ≤ H) (hbound : ∀ᵐ ω ∂P, Z ω ∈ Set.Icc 0 H)
    (t : ℝ) : Integrable (fun ω => Real.exp (t * Z ω)) P := by
  refine Integrable.of_bound (by fun_prop) (Real.exp (|t| * H)) ?_
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * Z ω ≤ |t * Z ω| := le_abs_self _
    _ = |t| * Z ω := by rw [abs_mul, abs_of_nonneg hω.1]
    _ ≤ |t| * H := mul_le_mul_of_nonneg_left hω.2 (abs_nonneg _)

lemma bounded_centered_mgf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} {H t : ℝ}
    (hZ : Measurable Z) (hH : 0 ≤ H) (hbound : ∀ᵐ ω ∂P, Z ω ∈ Set.Icc 0 H)
    (ht : |t| * H ≤ 1) :
    mgf (fun ω => Z ω - ∫ w, Z w ∂P) P t ≤
      Real.exp ((∫ w, Z w ∂P) * H * t ^ 2) := by
  have hint : Integrable Z P := by
    refine Integrable.of_bound hZ.aestronglyMeasurable H ?_
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2
  have hpoint : ∀ᵐ ω ∂P, Real.exp (t * Z ω) ≤ 1 + t * Z ω + t ^ 2 * H * Z ω := by
    filter_upwards [hbound] with ω hω
    have habs : |t * Z ω| ≤ 1 := by
      calc
        |t * Z ω| = |t| * Z ω := by rw [abs_mul, abs_of_nonneg hω.1]
        _ ≤ |t| * H := mul_le_mul_of_nonneg_left hω.2 (abs_nonneg _)
        _ ≤ 1 := ht
    have hquad := exp_le_quadratic habs
    have hsquare : Z ω ^ 2 ≤ H * Z ω := by nlinarith [hω.1, hω.2]
    have hmul := mul_le_mul_of_nonneg_left hsquare (sq_nonneg t)
    nlinarith
  have hexp := bounded_integrable_exp hZ hH hbound t
  have haffine : Integrable (fun ω => 1 + t * Z ω + t ^ 2 * H * Z ω) P :=
    ((integrable_const 1).add (hint.const_mul t)).add (hint.const_mul (t ^ 2 * H))
  have hintegral := integral_mono_ae hexp haffine hpoint
  rw [integral_add (f := fun ω => 1 + t * Z ω) (g := fun ω => t ^ 2 * H * Z ω)
      ((integrable_const 1).add (hint.const_mul t)) (hint.const_mul (t ^ 2 * H)),
    integral_add (f := fun _ => 1) (g := fun ω => t * Z ω)
      (integrable_const 1) (hint.const_mul t),
    integral_const_mul, integral_const_mul] at hintegral
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hintegral
  unfold mgf
  have heq : (fun ω => Real.exp (t * (Z ω - ∫ w, Z w ∂P))) =
      fun ω => Real.exp (-(t * ∫ w, Z w ∂P)) * Real.exp (t * Z ω) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul]
  calc
    Real.exp (-(t * ∫ w, Z w ∂P)) * (∫ ω, Real.exp (t * Z ω) ∂P) ≤
        Real.exp (-(t * ∫ w, Z w ∂P)) *
          (1 + t * (∫ w, Z w ∂P) + t ^ 2 * H * (∫ w, Z w ∂P)) :=
      mul_le_mul_of_nonneg_left hintegral (Real.exp_pos _).le
    _ ≤ Real.exp (-(t * ∫ w, Z w ∂P)) *
        Real.exp (t * (∫ w, Z w ∂P) + t ^ 2 * H * (∫ w, Z w ∂P)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have h := Real.add_one_le_exp (t * (∫ w, Z w ∂P) +
        t ^ 2 * H * (∫ w, Z w ∂P))
      linarith
    _ = Real.exp ((∫ w, Z w ∂P) * H * t ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma bounded_sum_exponential {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ι → Ω → ℝ} {H u : ℝ} (s : Finset ι)
    (hZ : ∀ i, Measurable (Z i)) (hH : 0 ≤ H)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂P, Z i ω ∈ Set.Icc 0 H)
    (hmean : ∀ i ∈ s, (∫ ω, Z i ω ∂P) ≤ u) (hind : iIndepFun Z P) :
    (∀ η, Integrable (fun ω => Real.exp
      (η * ∑ i ∈ s, (Z i ω - ∫ w, Z i w ∂P))) P) ∧
    ∀ η, |η| * H ≤ 1 →
      mgf (fun ω => ∑ i ∈ s, (Z i ω - ∫ w, Z i w ∂P)) P η ≤
        Real.exp (s.card * u * H * η ^ 2) := by
  let Y : ι → Ω → ℝ := fun i ω => Z i ω - ∫ w, Z i w ∂P
  have hY (i) : Measurable (Y i) := (hZ i).sub_const _
  have hindY : iIndepFun Y P := hind.comp (fun i x => x - ∫ w, Z i w ∂P) (by fun_prop)
  have hint (η : ℝ) (i : ι) (hi : i ∈ s) :
      Integrable (fun ω => Real.exp (η * Y i ω)) P := by
    have heq : (fun ω => Real.exp (η * Y i ω)) =
        fun ω => Real.exp (-(η * ∫ w, Z i w ∂P)) * Real.exp (η * Z i ω) := by
      funext ω
      rw [← Real.exp_add]
      dsimp only [Y]
      congr 1
      ring
    rw [heq]
    exact (bounded_integrable_exp (hZ i) hH (hbound i hi) η).const_mul _
  constructor
  · intro η
    simpa only [Finset.sum_apply] using hindY.integrable_exp_mul_sum hY (hint η)
  · intro η hη
    have hmgf (i : ι) (hi : i ∈ s) : mgf (Y i) P η ≤ Real.exp (u * H * η ^ 2) := by
      have h := bounded_centered_mgf (hZ i) hH (hbound i hi) hη
      exact h.trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hmean i hi) hH)
          (sq_nonneg η)))
    have heq := hindY.mgf_sum hY s (t := η)
    have hsum : (∑ i ∈ s, Y i) = fun ω => ∑ i ∈ s, Y i ω := by
      ext ω
      simp only [Finset.sum_apply]
    rw [hsum] at heq
    change mgf (fun ω => ∑ i ∈ s, Y i ω) P η ≤ _
    rw [heq]
    calc
      (∏ i ∈ s, mgf (Y i) P η) ≤ ∏ _i ∈ s, Real.exp (u * H * η ^ 2) := by
        exact Finset.prod_le_prod₀
          (fun i _ => show 0 ≤ mgf (Y i) P η from
            integral_nonneg (fun ω => (Real.exp_pos _).le)) hmgf
      _ = Real.exp (s.card * u * H * η ^ 2) := by
        rw [← Real.exp_sum]
        congr 1
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

lemma bounded_mgf_absolute_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {v H t : ℝ}
    (hv : 0 ≤ v) (hH : 0 < H) (ht : 0 < t)
    (hint : ∀ η, Integrable (fun ω => Real.exp (η * X ω)) P)
    (hmgf : ∀ η, |η| * H ≤ 1 → mgf X P η ≤ Real.exp (v * η ^ 2)) :
    P.real {ω | 2 * Real.sqrt (v * t) + 2 * H * t ≤ |X ω|} ≤ 2 * Real.exp (-t) := by
  let a := Real.sqrt v
  let b := Real.sqrt t
  let den := a + H * b
  let η := b / den
  let R := 2 * a * b + 2 * H * t
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 < b := Real.sqrt_pos.mpr ht
  have ha2 : a ^ 2 = v := Real.sq_sqrt hv
  have hb2 : b ^ 2 = t := Real.sq_sqrt ht.le
  have hden : 0 < den := add_pos_of_nonneg_of_pos ha (mul_pos hH hb)
  have hη : 0 < η := div_pos hb hden
  have hηH : |η| * H ≤ 1 := by
    rw [abs_of_pos hη]
    change b / den * H ≤ 1
    rw [div_mul_eq_mul_div, div_le_iff₀ hden, one_mul]
    dsimp only [den]
    nlinarith
  have haη : a * η ≤ b := by
    change a * (b / den) ≤ b
    rw [← mul_div_assoc, div_le_iff₀ hden]
    dsimp only [den]
    nlinarith [mul_nonneg hH.le (sq_nonneg b)]
  have hquadratic : v * η ^ 2 ≤ t := by
    have hs := mul_self_le_mul_self (mul_nonneg ha hη.le) haη
    nlinarith [sq_nonneg (a * η - b)]
  have hlinear : η * R = 2 * t := by
    change b / den * (2 * a * b + 2 * H * t) = 2 * t
    apply (div_mul_eq_mul_div b den _).trans
    apply (div_eq_iff hden.ne').mpr
    dsimp only [den]
    nlinarith [hb2]
  have hpos : P.real {ω | R ≤ X ω} ≤ Real.exp (-t) := by
    calc
      _ ≤ Real.exp (-η * R) * mgf X P η :=
        measure_ge_le_exp_mul_mgf R hη.le (hint η)
      _ ≤ Real.exp (-η * R) * Real.exp (v * η ^ 2) :=
        mul_le_mul_of_nonneg_left (hmgf η hηH) (Real.exp_pos _).le
      _ ≤ Real.exp (-t) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
  have hneg : P.real {ω | X ω ≤ -R} ≤ Real.exp (-t) := by
    have hnegη : |-η| * H ≤ 1 := by simpa only [abs_neg] using hηH
    calc
      _ ≤ Real.exp (-(-η) * (-R)) * mgf X P (-η) :=
        measure_le_le_exp_mul_mgf (-R) (neg_nonpos.mpr hη.le) (hint (-η))
      _ ≤ Real.exp (-(-η) * (-R)) * Real.exp (v * (-η) ^ 2) :=
        mul_le_mul_of_nonneg_left (hmgf (-η) hnegη) (Real.exp_pos _).le
      _ ≤ Real.exp (-t) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
  have hR : 2 * Real.sqrt (v * t) + 2 * H * t = R := by
    rw [Real.sqrt_mul hv]
    dsimp only [R, a, b]
    ring
  have hsubset : {ω | 2 * Real.sqrt (v * t) + 2 * H * t ≤ |X ω|} ⊆
      {ω | R ≤ X ω} ∪ {ω | X ω ≤ -R} := by
    intro ω hω
    rw [hR] at hω
    change R ≤ |X ω| at hω
    rcases le_abs.mp hω with hp | hn
    · exact Or.inl hp
    · exact Or.inr (show X ω ≤ -R by linarith)
  calc
    _ ≤ P.real ({ω | R ≤ X ω} ∪ {ω | X ω ≤ -R}) := measureReal_mono hsubset
    _ ≤ P.real {ω | R ≤ X ω} + P.real {ω | X ω ≤ -R} := measureReal_union_le _ _
    _ ≤ Real.exp (-t) + Real.exp (-t) := add_le_add hpos hneg
    _ = _ := by ring

lemma bounded_sum_absolute_tail {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ι → Ω → ℝ} {H u t : ℝ} (s : Finset ι)
    (hZ : ∀ i, Measurable (Z i)) (hH : 0 < H) (hu : 0 ≤ u) (ht : 0 < t)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂P, Z i ω ∈ Set.Icc 0 H)
    (hmean : ∀ i ∈ s, (∫ ω, Z i ω ∂P) ≤ u) (hind : iIndepFun Z P) :
    P.real {ω | 2 * Real.sqrt ((s.card * u * H) * t) + 2 * H * t ≤
      |∑ i ∈ s, (Z i ω - ∫ w, Z i w ∂P)|} ≤ 2 * Real.exp (-t) := by
  obtain ⟨hint, hmgf⟩ := bounded_sum_exponential s hZ hH.le hbound hmean hind
  exact bounded_mgf_absolute_tail (by positivity) hH ht hint hmgf

end LongTailsOnline.Proofs.TaskAllocation

import LongTails.Proofs.ScalarClippedMoments
import LongTails.Proofs.ScalarMomentConcentration
import LongTails.Proofs.StoppedVectorConcentration
import LongTails.Proofs.ClippedTwoPointExecution
import LongTails.Proofs.WeakGradientSegments
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory

set_option maxHeartbeats 2000000

namespace LongTails.Proofs.ClippedSelection

open OracleTemplate ScalarClippedMoments

lemma clipped_shift_bias {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {s V : ℝ}
    (hX : Measurable X) (hXi : Integrable X P) (hX2 : Integrable (fun z => X z ^ 2) P)
    (hV : (∫ z, X z ^ 2 ∂P) ≤ V) (hs : 0 < s) (c : ℝ) :
    Integrable (fun z => clip s (X z + c)) P ∧
      |(∫ z, clip s (X z + c) ∂P) - ∫ z, X z ∂P| ≤ V / s + |c| := by
  have hm : Measurable (fun z => clip s (X z + c)) := (measurable_clip s).comp (hX.add_const c)
  have hi : Integrable (fun z => clip s (X z + c)) P :=
    Integrable.of_bound hm.aestronglyMeasurable s
      (Filter.Eventually.of_forall (fun z => norm_clip_le hs.le _))
  refine ⟨hi, ?_⟩
  have hb (z : Ω) : |clip s (X z + c) - X z| ≤ X z ^ 2 / s + |c| := by
    have h1 := scalar_clip_difference hs.le (X z + c) (X z)
    have h2 := (le_div_iff₀ hs).mpr (by
      simpa only [mul_comm] using scalar_clip_residual_square hs.le (X z))
    have h3 := abs_sub_le (clip s (X z + c)) (clip s (X z)) (X z)
    rw [add_sub_cancel_left] at h1
    linarith
  have hn : |∫ z, clip s (X z + c) - X z ∂P| ≤
      ∫ z, |clip s (X z + c) - X z| ∂P := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (f := fun z => clip s (X z + c) - X z) (μ := P)
  have hh := hn.trans (integral_mono
    (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hi.sub hXi).norm)
    ((hX2.div_const s).add (integrable_const |c|)) hb)
  simp only [Pi.add_apply] at hh
  rw [integral_sub hi hXi, integral_add (hX2.div_const s) (integrable_const |c|), integral_div] at hh
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hh
  exact hh.trans (add_le_add (div_le_div_of_nonneg_right hV hs.le) (le_refl |c|))

lemma clipped_shift_even_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {s V : ℝ}
    (hX : Measurable X) (hX2 : Integrable (fun z => X z ^ 2) P)
    (hV : (∫ z, X z ^ 2 ∂P) ≤ V) (hs : 0 ≤ s) (c : ℝ) (k : ℕ) :
    Integrable (fun z => |clip s (X z + c)| ^ (2 * (k + 1))) P ∧
      (∫ z, |clip s (X z + c)| ^ (2 * (k + 1)) ∂P) ≤
        (2 * V + 2 * c ^ 2) * s ^ (2 * k) := by
  have hh := scalar_clipped_perturbed_moment (P := P) (a := X) (c := fun _ => c)
    (w := fun _ => (1 : ℝ)) hs hX measurable_const measurable_const
    (fun _ => le_refl |c|) k (by simpa using hX2) (by simp)
  simp only [abs_one, one_pow, mul_one, sq_abs, integral_const, Measure.real,
    measure_univ, ENNReal.toReal_one, one_smul] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hb := mul_le_mul_of_nonneg_right hV (pow_nonneg hs (2 * k))
  nlinarith only [hb]

lemma clipped_shift_mgf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {s V θ : ℝ}
    (hX : Measurable X) (hX2 : Integrable (fun z => X z ^ 2) P)
    (hV : (∫ z, X z ^ 2 ∂P) ≤ V) (hs : 0 ≤ s) (c : ℝ)
    (hsmall : 256 * |θ| * s < 1) :
    Integrable (fun z => Real.exp (θ * (clip s (X z + c) - ∫ w, clip s (X w + c) ∂P))) P ∧
      (∫ z, Real.exp (θ * (clip s (X z + c) - ∫ w, clip s (X w + c) ∂P)) ∂P) ≤
        Real.exp (131072 * (2 * V + 2 * c ^ 2) * θ ^ 2 / (1 - 256 * |θ| * s)) := by
  have hV0 : 0 ≤ V := (integral_nonneg (fun z => sq_nonneg (X z))).trans hV
  have hXm : Measurable (fun z => clip s (X z + c)) := (measurable_clip s).comp (hX.add_const c)
  apply ScalarMomentConcentration.bounded_centered_mgf_bernstein hXm
    (fun z => by simpa only [Real.norm_eq_abs] using norm_clip_le hs (X z + c))
    (by positivity) hs hsmall
  intro k
  have hm := clipped_shift_even_moment hX hX2 hV hs c k
  refine ⟨hm.1, hm.2.trans ?_⟩
  have hp : (1 : ℝ) ≤ 8 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have hf : (1 : ℝ) ≤ ((k + 1).factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (k + 1))
  have hh := mul_le_mul hp hf (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  have hc : (1 : ℝ) ≤ 12 * 8 ^ (k + 1) * ((k + 1).factorial : ℝ) := by nlinarith only [hh]
  have ht := mul_le_mul_of_nonneg_right hc (show 0 ≤ (2 * V + 2 * c ^ 2) * s ^ (2 * k) by positivity)
  nlinarith only [ht]

lemma clipped_shift_mgf_scaled {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {s H T ell θ c : ℝ}
    (hX : Measurable X) (hX2 : Integrable (fun z => X z ^ 2) P)
    (hV : (∫ z, X z ^ 2 ∂P) ≤ H ^ 2) (hs : 0 < s) (hT : 0 < T)
    (hc : c ^ 2 ≤ H ^ 2 / 4) (hscale : T * H ^ 2 = s ^ 2 * ell)
    (hθ : |θ| = 1 / (1024 * s)) :
    Integrable (fun z => Real.exp (θ * (clip s (X z + c) - ∫ w, clip s (X w + c) ∂P))) P ∧
      (∫ z, Real.exp (θ * (clip s (X z + c) - ∫ w, clip s (X w + c) ∂P)) ∂P) ≤
        Real.exp (ell / (2 * T)) := by
  have hd : 256 * |θ| * s = 1 / 4 := by rw [hθ]; field_simp; ring
  have hsmall : 256 * |θ| * s < 1 := by rw [hd]; norm_num
  have hm := clipped_shift_mgf hX hX2 hV hs.le c hsmall
  refine ⟨hm.1, hm.2.trans (Real.exp_le_exp.mpr ?_)⟩
  have hb : 2 * H ^ 2 + 2 * c ^ 2 ≤ 3 * H ^ 2 := by nlinarith [sq_nonneg H]
  have hsq : θ ^ 2 = 1 / (1024 * s) ^ 2 := by rw [← sq_abs, hθ, div_pow, one_pow]
  have he : 131072 * (3 * H ^ 2) * θ ^ 2 / (1 - 256 * |θ| * s) = ell / (2 * T) := by
    rw [hd, hsq]
    field_simp
    nlinarith only [hscale]
  rw [← he]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) (sq_nonneg θ))
    (by rw [hd]; norm_num)

lemma iid_active_sum_upper {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i))
    (hind : ProbabilityTheory.iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = p)
    {Y : (n : ℕ) → (Fin n → Z) × Z → ℝ} (hY : ∀ i, Measurable (Y i))
    (active : ℕ → Bool) (n : ℕ) {s T ell : ℝ} (hs : 0 < s) (hT : 0 < T) (hell : 0 < ell)
    (hcount : (∑ i ∈ Finset.range n, if active i then (1 : ℝ) else 0) ≤ T)
    (hmgf : ∀ i a, Integrable (fun z => Real.exp ((1 / (1024 * s)) * Y i (a, z))) p ∧
      (∫ z, Real.exp ((1 / (1024 * s)) * Y i (a, z)) ∂p) ≤ Real.exp (ell / (2 * T))) :
    P.real {ω | 4096 * s * ell ≤ ∑ i ∈ Finset.range n,
      if active i then Y i ((fun j => ξ j ω), ξ i ω) else 0} ≤ Real.exp (-ell) := by
  let inc := fun i (az : (Fin i → Z) × Z) => if active i then Y i az else 0
  let cost := fun i => if active i then ell / (2 * T) else 0
  have hi : ∀ i, Measurable (inc i) := by
    intro i
    by_cases ha : active i = true
    · simpa only [inc, ha, Bool.true_eq, ↓reduceIte] using hY i
    · simp only [inc, ha]
      exact measurable_const
  have hm (i : ℕ) (a : Fin i → Z) :
      Integrable (fun z => Real.exp ((1 / (1024 * s)) * inc i (a, z))) p ∧
        (∫ z, Real.exp ((1 / (1024 * s)) * inc i (a, z)) ∂p) ≤ Real.exp (cost i) := by
    by_cases ha : active i = true
    · simpa only [inc, cost, ha, Bool.true_eq, ↓reduceIte] using hmgf i a
    · simp [inc, cost, ha]
  have hh := AdaptiveOracleConcentration.iid_predictable_sum_exponential_bound hξ hind hlaw
    cost (1 / (1024 * s)) hi (fun i a => (hm i a).1) (fun i a => (hm i a).2) n
  have hc : (∑ i ∈ Finset.range n, cost i) ≤ ell / 2 := by
    have he : (∑ i ∈ Finset.range n, cost i) =
        ell / (2 * T) * (∑ i ∈ Finset.range n, if active i then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases ha : active i = true <;> simp [cost, ha]
    rw [he]
    calc
      _ ≤ ell / (2 * T) * T := mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = ell / 2 := by field_simp
  have ht := StoppedVectorConcentration.exponential_tail_of_bound
    (show 0 ≤ 1 / (1024 * s) by positivity) hh.1 hh.2 (4096 * s * ell)
  apply ht.trans (Real.exp_le_exp.mpr ?_)
  have he : (1 / (1024 * s)) * (4096 * s * ell) = 4 * ell := by field_simp; ring
  rw [he]
  linarith only [hc, hell]

lemma iid_active_sum_two_sided {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i))
    (hind : ProbabilityTheory.iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = p)
    {Y : (n : ℕ) → (Fin n → Z) × Z → ℝ} (hY : ∀ i, Measurable (Y i))
    (active : ℕ → Bool) (n : ℕ) {s T ell : ℝ} (hs : 0 < s) (hT : 0 < T) (hell : 0 < ell)
    (hcount : (∑ i ∈ Finset.range n, if active i then (1 : ℝ) else 0) ≤ T)
    (hmgf : ∀ i a θ, |θ| = 1 / (1024 * s) →
      Integrable (fun z => Real.exp (θ * Y i (a, z))) p ∧
        (∫ z, Real.exp (θ * Y i (a, z)) ∂p) ≤ Real.exp (ell / (2 * T))) :
    P.real {ω | 4096 * s * ell < |∑ i ∈ Finset.range n,
      if active i then Y i ((fun j => ξ j ω), ξ i ω) else 0|} ≤ 2 * Real.exp (-ell) := by
  have hθ : 0 < 1 / (1024 * s) := by positivity
  have hp := iid_active_sum_upper hξ hind hlaw hY active n hs hT hell hcount
    (fun i a => hmgf i a _ (abs_of_pos hθ))
  have hn := iid_active_sum_upper hξ hind hlaw (Y := fun i az => -Y i az)
    (fun i => (hY i).neg) active n hs hT hell hcount (fun i a => by
      have hh := hmgf i a (-(1 / (1024 * s))) (by rw [abs_neg, abs_of_pos hθ])
      simpa only [neg_mul, mul_neg] using hh)
  have he (ω : Ω) : (∑ i ∈ Finset.range n,
      if active i then -Y i ((fun j => ξ j ω), ξ i ω) else 0) =
      -(∑ i ∈ Finset.range n, if active i then Y i ((fun j => ξ j ω), ξ i ω) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : active i = true <;> simp [ha]
  simp only [he] at hn
  have hsub : {ω | 4096 * s * ell < |∑ i ∈ Finset.range n,
      if active i then Y i ((fun j => ξ j ω), ξ i ω) else 0|} ⊆
      {ω | 4096 * s * ell ≤ ∑ i ∈ Finset.range n,
        if active i then Y i ((fun j => ξ j ω), ξ i ω) else 0} ∪
      {ω | 4096 * s * ell ≤ -(∑ i ∈ Finset.range n,
        if active i then Y i ((fun j => ξ j ω), ξ i ω) else 0)} := by
    intro ω hω
    change 4096 * s * ell < |∑ i ∈ Finset.range n,
      if active i then Y i ((fun j => ξ j ω), ξ i ω) else 0| at hω
    rcases lt_abs.mp hω with hh | hh
    · exact Or.inl hh.le
    · exact Or.inr hh.le
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (by linarith only [hp, hn]))

lemma iid_active_clipped_tail {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i))
    (hind : ProbabilityTheory.iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = p)
    {X : (n : ℕ) → (Fin n → Z) × Z → ℝ} (hX : ∀ i, Measurable (X i))
    {c : (n : ℕ) → (Fin n → Z) → ℝ} (hc : ∀ i, Measurable (c i))
    (active : ℕ → Bool) (n : ℕ) {s H T ell : ℝ}
    (hs : 0 < s) (hT : 0 < T) (hell : 0 < ell)
    (hcount : (∑ i ∈ Finset.range n, if active i then (1 : ℝ) else 0) ≤ T)
    (hX2 : ∀ i a, Integrable (fun z => X i (a, z) ^ 2) p)
    (hV : ∀ i a, (∫ z, X i (a, z) ^ 2 ∂p) ≤ H ^ 2)
    (hcB : ∀ i a, c i a ^ 2 ≤ H ^ 2 / 4)
    (hscale : T * H ^ 2 = s ^ 2 * ell) :
    let V := fun i (az : (Fin i → Z) × Z) => clip s (X i az + c i az.1)
    let Y := fun i (az : (Fin i → Z) × Z) => V i az - ∫ z, V i (az.1, z) ∂p
    P.real {ω | 4096 * s * ell < |∑ i ∈ Finset.range n,
      if active i then Y i ((fun j => ξ j ω), ξ i ω) else 0|} ≤ 2 * Real.exp (-ell) := by
  let V := fun i (az : (Fin i → Z) × Z) => clip s (X i az + c i az.1)
  let Y := fun i (az : (Fin i → Z) × Z) => V i az - ∫ z, V i (az.1, z) ∂p
  have hVm (i : ℕ) : Measurable (V i) :=
    (measurable_clip s).comp ((hX i).add ((hc i).comp measurable_fst))
  have hYm (i : ℕ) : Measurable (Y i) :=
    (hVm i).sub ((hVm i).stronglyMeasurable.integral_prod_right'.measurable.comp measurable_fst)
  apply iid_active_sum_two_sided hξ hind hlaw hYm active n hs hT hell hcount
  intro i a θ hθ
  have hXi : Measurable (fun z : Z => X i (a, z)) :=
    (hX i).comp (measurable_const.prodMk measurable_id)
  exact clipped_shift_mgf_scaled (P := p) (X := fun z : Z => X i (a, z))
    (s := s) (H := H) (T := T) (ell := ell) (θ := θ) (c := c i a)
    hXi (hX2 i a) (hV i a) hs hT (hcB i a) hscale hθ

lemma selection_average_error {T : ℕ} (hT : 0 < T) (values : Fin T → ℝ)
    {s H ell C mean target : ℝ} (hs : 0 < s)
    (hscale : (T : ℝ) * H ^ 2 = s ^ 2 * ell)
    (hcenter : |∑ i, (values i - mean)| ≤ 4096 * s * ell)
    (hbias : |mean - target| ≤ H ^ 2 / s + C) :
    |(T : ℝ)⁻¹ * (∑ i, values i) - target| ≤ 4097 * s * ell / T + C := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have he : (T : ℝ)⁻¹ * (∑ i, values i) - target =
      (∑ i, (values i - mean)) / T + (mean - target) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hb : H ^ 2 / s = s * ell / T := by
    apply (div_eq_div_iff hs.ne' hTR.ne').mpr
    nlinarith only [hscale]
  rw [he]
  have hh := abs_add_le ((∑ i, (values i - mean)) / T) (mean - target)
  rw [abs_div, abs_of_pos hTR] at hh
  have hc := div_le_div_of_nonneg_right hcenter hTR.le
  rw [hb] at hbias
  have ht := hh.trans (add_le_add hc hbias)
  convert ht using 1; ring

lemma iid_fresh_clipped_centered {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i))
    (hind : ProbabilityTheory.iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = p)
    (K T : ℕ) (hT : 0 < T) {X : (Fin K → Z) × Z → ℝ} (hX : Measurable X)
    {c : (Fin K → Z) → ℝ} (hc : Measurable c) {s H ell : ℝ}
    (hs : 0 < s) (hell : 0 < ell)
    (hX2 : ∀ a, Integrable (fun z => X (a, z) ^ 2) p)
    (hV : ∀ a, (∫ z, X (a, z) ^ 2 ∂p) ≤ H ^ 2)
    (hcB : ∀ a, c a ^ 2 ≤ H ^ 2 / 4)
    (hscale : (T : ℝ) * H ^ 2 = s ^ 2 * ell) :
    let V := fun a z => clip s (X (a, z) + c a)
    P.real {ω | 4096 * s * ell < |∑ j : Fin T,
      (V (fun i => ξ i ω) (ξ (K + j) ω) - ∫ z, V (fun i => ξ i ω) z ∂p)|} ≤
        2 * Real.exp (-ell) := by
  let A := fun i (az : (Fin i → Z) × Z) =>
    if hi : K ≤ i then X ((fun j : Fin K => az.1 (j.castLE hi)), az.2) else 0
  let b := fun i (a : Fin i → Z) =>
    if hi : K ≤ i then c (fun j : Fin K => a (j.castLE hi)) else 0
  let active := fun i => decide (K ≤ i)
  have hA (i : ℕ) : Measurable (A i) := by
    by_cases hi : K ≤ i
    · simp only [A, dite_eq_left hi]
      exact hX.comp (((Measurable.of_eval (fun j : Fin K => measurable_pi_apply (j.castLE hi))).comp
        measurable_fst).prodMk measurable_snd)
    · simp only [A, dite_eq_right hi]
      exact measurable_const
  have hb (i : ℕ) : Measurable (b i) := by
    by_cases hi : K ≤ i
    · simp only [b, dite_eq_left hi]
      exact hc.comp (Measurable.of_eval (fun j : Fin K => measurable_pi_apply (j.castLE hi)))
    · simp only [b, dite_eq_right hi]
      exact measurable_const
  have hA2 (i : ℕ) (a : Fin i → Z) : Integrable (fun z => A i (a, z) ^ 2) p := by
    by_cases hi : K ≤ i
    · simpa only [A, dite_eq_left hi] using hX2 (fun j : Fin K => a (j.castLE hi))
    · simp [A, hi]
  have hAV (i : ℕ) (a : Fin i → Z) : (∫ z, A i (a, z) ^ 2 ∂p) ≤ H ^ 2 := by
    by_cases hi : K ≤ i
    · simpa only [A, dite_eq_left hi] using hV (fun j : Fin K => a (j.castLE hi))
    · simp only [A, dite_eq_right hi, zero_pow (by decide : 2 ≠ 0), integral_zero]
      positivity
  have hbB (i : ℕ) (a : Fin i → Z) : b i a ^ 2 ≤ H ^ 2 / 4 := by
    by_cases hi : K ≤ i
    · simpa only [b, dite_eq_left hi] using hcB (fun j : Fin K => a (j.castLE hi))
    · simp only [b, dite_eq_right hi, zero_pow (by decide : 2 ≠ 0)]
      positivity
  have hcount : (∑ i ∈ Finset.range (K + T), if active i then (1 : ℝ) else 0) ≤ (T : ℝ) := by
    rw [Finset.sum_range_add]
    have hz : (∑ i ∈ Finset.range K, if active i then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [active, Nat.not_le_of_gt (Finset.mem_range.mp hi)]
    rw [hz, zero_add]
    simp [active]
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have ht := iid_active_clipped_tail hξ hind hlaw hA hb active (K + T) hs hTR hell
    hcount hA2 hAV hbB hscale
  let W := fun i (az : (Fin i → Z) × Z) => clip s (A i az + b i az.1)
  have he (ω : Ω) : (∑ i ∈ Finset.range (K + T), if active i then
      W i ((fun j => ξ j ω), ξ i ω) - ∫ z, W i ((fun j => ξ j ω), z) ∂p else 0) =
      ∑ j : Fin T, (clip s (X ((fun i => ξ i ω), ξ (K + j) ω) + c (fun i => ξ i ω)) -
        ∫ z, clip s (X ((fun i => ξ i ω), z) + c (fun i => ξ i ω)) ∂p) := by
    rw [Finset.sum_range_add]
    have hz : (∑ i ∈ Finset.range K, if active i then
        W i ((fun j => ξ j ω), ξ i ω) - ∫ z, W i ((fun j => ξ j ω), z) ∂p else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [active, Nat.not_le_of_gt (Finset.mem_range.mp hi)]
    rw [hz, zero_add, Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      clip s (X ((fun i => ξ i ω), ξ (K + j) ω) + c (fun i => ξ i ω)) -
        ∫ z, clip s (X ((fun i => ξ i ω), z) + c (fun i => ξ i ω)) ∂p)]
    apply Finset.sum_congr rfl
    intro j hj
    simp [active, W, A, b]
  change P.real {ω | 4096 * s * ell < |∑ i ∈ Finset.range (K + T), if active i then
    W i ((fun j => ξ j ω), ξ i ω) - ∫ z, W i ((fun j => ξ j ω), z) ∂p else 0|} ≤ _ at ht
  simpa only [he] using ht

lemma iid_fresh_clipped_accuracy {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i))
    (hind : ProbabilityTheory.iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = p)
    (K T : ℕ) (hT : 0 < T) {X : (Fin K → Z) × Z → ℝ} (hX : Measurable X)
    {c : (Fin K → Z) → ℝ} (hc : Measurable c) {s H ell C : ℝ}
    (hs : 0 < s) (hell : 0 < ell)
    (hXi : ∀ a, Integrable (fun z => X (a, z)) p)
    (hX2 : ∀ a, Integrable (fun z => X (a, z) ^ 2) p)
    (hV : ∀ a, (∫ z, X (a, z) ^ 2 ∂p) ≤ H ^ 2)
    (hcB : ∀ a, c a ^ 2 ≤ H ^ 2 / 4)
    (hcAbs : ∀ a, |c a| ≤ C)
    (hscale : (T : ℝ) * H ^ 2 = s ^ 2 * ell) :
    P.real {ω | 4097 * s * ell / T + C <
      |(T : ℝ)⁻¹ * (∑ j : Fin T, clip s (X ((fun i => ξ i ω), ξ (K + j) ω) + c (fun i => ξ i ω))) -
        ∫ z, X ((fun i => ξ i ω), z) ∂p|} ≤ 2 * Real.exp (-ell) := by
  have ht := iid_fresh_clipped_centered hξ hind hlaw K T hT hX hc hs hell hX2 hV hcB hscale
  apply (measureReal_mono ?_).trans ht
  intro ω hbad
  by_contra hgood
  let a := fun i : Fin K => ξ i ω
  let values := fun j : Fin T => clip s (X (a, ξ (K + j) ω) + c a)
  let mean := ∫ z, clip s (X (a, z) + c a) ∂p
  let target := ∫ z, X (a, z) ∂p
  change ¬ (4096 * s * ell < |∑ j : Fin T, (values j - mean)|) at hgood
  have hcenter : |∑ j : Fin T, (values j - mean)| ≤ 4096 * s * ell := le_of_not_gt hgood
  have hXa : Measurable (fun z => X (a, z)) := hX.comp (measurable_const.prodMk measurable_id)
  have hb := (clipped_shift_bias hXa (hXi a) (hX2 a) (hV a) hs (c a)).2
  have hb' : |mean - target| ≤ H ^ 2 / s + C :=
    hb.trans (add_le_add (le_refl _) (hcAbs a))
  have hh := selection_average_error hT values hs hscale hcenter hb'
  change 4097 * s * ell / T + C < |(T : ℝ)⁻¹ * (∑ j : Fin T, values j) - target| at hbad
  exact not_lt_of_ge hh hbad

lemma iid_fresh_selected_value {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i))
    (hind : ProbabilityTheory.iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = p)
    (K T : ℕ) (hT : 0 < T) {X : (Fin K → Z) × Z → ℝ} (hX : Measurable X)
    {c : (Fin K → Z) → ℝ} (hc : Measurable c) {s H ell C : ℝ}
    (hs : 0 < s) (hell : 0 < ell) (hC : 0 ≤ C)
    (hXi : ∀ a, Integrable (fun z => X (a, z)) p)
    (hX2 : ∀ a, Integrable (fun z => X (a, z) ^ 2) p)
    (hV : ∀ a, (∫ z, X (a, z) ^ 2 ∂p) ≤ H ^ 2)
    (hcB : ∀ a, c a ^ 2 ≤ H ^ 2 / 4) (hcAbs : ∀ a, |c a| ≤ C)
    (hscale : (T : ℝ) * H ^ 2 = s ^ 2 * ell)
    (a b : (Fin K → Z) → E) (f : E → ℝ)
    (hmean : ∀ z, (∫ v, X (z, v) ∂p) = f (a z) - f (b z)) :
    let estimate := fun ω => (T : ℝ)⁻¹ * ∑ j : Fin T,
      clip s (X ((fun i => ξ i ω), ξ (K + j) ω) + c (fun i => ξ i ω))
    let output := fun ω => LongTails.Algorithms.ClippedTwoPoint.selectByDifference
      (a (fun i => ξ i ω)) (b (fun i => ξ i ω)) (estimate ω)
    P.real {ω | min (f (a (fun i => ξ i ω))) (f (b (fun i => ξ i ω))) +
      (4097 * s * ell / T + C) < f (output ω)} ≤ 2 * Real.exp (-ell) := by
  dsimp only
  have ht := iid_fresh_clipped_accuracy hξ hind hlaw K T hT hX hc hs hell
    hXi hX2 hV hcB hcAbs hscale
  apply (measureReal_mono ?_).trans ht
  intro ω hbad
  by_contra hgood
  change ¬ (4097 * s * ell / T + C <
    |(T : ℝ)⁻¹ * (∑ j : Fin T, clip s (X ((fun i => ξ i ω), ξ (K + j) ω) +
      c (fun i => ξ i ω))) - ∫ z, X ((fun i => ξ i ω), z) ∂p|) at hgood
  have he := le_of_not_gt hgood
  rw [hmean] at he
  have hr : 0 ≤ 4097 * s * ell / T + C := by positivity
  have hh := ClippedTwoPointExecution.selected_value_le
    (a (fun i => ξ i ω)) (b (fun i => ξ i ω)) hr he
  exact not_lt_of_ge hh hbad

section WeakOracleSelection

open Set Metric
open scoped RealInnerProductSpace ContDiff

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

lemma weak_oracle_selected_value {Ω Ξ Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {ρ : Measure Z} [IsProbabilityMeasure ρ] {ξ : ℕ → Ξ → Z}
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ ρ μ)
    (sample : Z → Ω) (hsample : MeasurePreserving sample ρ P)
    {F : E × Ω → ℝ} {G : E × Ω → E} {C U Q : Set E}
    (hC : IsCompact C) (hUC : U ⊆ C) (hQ : Convex ℝ Q)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ζ ∂P, ContinuousOn (fun z => F (z, ζ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ζ)) U volume ∧
      ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : E, (∫ z, F (z, ζ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ζ), v⟫ * ψ z)
    {B D η Δ H s ell : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hη : 0 < η)
    (hΔ : 0 ≤ Δ) (hδH : Δ ≤ H / 4) (hBH : D ^ 2 * B ≤ H ^ 2)
    (hmargin : ∀ x ∈ Q, closedBall x η ⊆ U)
    (hdiam : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hi : ∀ z ∈ U, Integrable (fun ζ => ‖G (z, ζ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ζ, ‖G (z, ζ)‖ ^ 2 ∂P) ≤ B)
    (f δ : E → ℝ) (hδm : Measurable δ) (hδ : ∀ x ∈ C, |δ x| ≤ Δ)
    (hfi : ∀ x ∈ C, Integrable (fun ζ => F (x, ζ)) P)
    (hfmean : ∀ x ∈ C, (∫ ζ, F (x, ζ) ∂P) = f x)
    (K T : ℕ) (hT : 0 < T) (hs : 0 < s) (hell : 0 < ell)
    (hscale : (T : ℝ) * H ^ 2 = s ^ 2 * ell)
    (a b : (Fin K → Z) → E) (ha : Measurable a) (hbmeas : Measurable b)
    (haQ : ∀ z, a z ∈ Q) (hbQ : ∀ z, b z ∈ Q) :
    let estimate := fun ζ => (T : ℝ)⁻¹ * ∑ j : Fin T,
      clip s ((F (a (fun i => ξ i ζ), sample (ξ (K + j) ζ)) + δ (a (fun i => ξ i ζ))) -
        (F (b (fun i => ξ i ζ), sample (ξ (K + j) ζ)) + δ (b (fun i => ξ i ζ))))
    let output := fun ζ => LongTails.Algorithms.ClippedTwoPoint.selectByDifference
      (a (fun i => ξ i ζ)) (b (fun i => ξ i ζ)) (estimate ζ)
    μ.real {ζ | min (f (a (fun i => ξ i ζ))) (f (b (fun i => ξ i ζ))) +
      (4097 * s * ell / T + 2 * Δ) < f (output ζ)} ≤ 2 * Real.exp (-ell) := by
  let X := fun az : (Fin K → Z) × Z => F (a az.1, sample az.2) - F (b az.1, sample az.2)
  let c := fun z => δ (a z) - δ (b z)
  have hX : Measurable X := (hFm.comp ((ha.comp measurable_fst).prodMk
    (hsample.measurable.comp measurable_snd))).sub
      (hFm.comp ((hbmeas.comp measurable_fst).prodMk (hsample.measurable.comp measurable_snd)))
  have hc : Measurable c := (hδm.comp ha).sub (hδm.comp hbmeas)
  have hQC : Q ⊆ C := fun x hx => hUC (hmargin x hx (mem_closedBall_self hη.le))
  have hXi (z : Fin K → Z) : Integrable (fun w => F (a z, w) - F (b z, w)) P :=
    (hfi _ (hQC (haQ z))).sub (hfi _ (hQC (hbQ z)))
  have hmom (z : Fin K → Z) := WeakGradientSegments.weak_pair_square_on_convex hC hUC hQ hFm hG hF
    hB hD hη hmargin hdiam hi hb (haQ z) (hbQ z)
  have hfixed (z : Fin K → Z) : Measurable (fun w => F (a z, w) - F (b z, w)) :=
    (hFm.comp (measurable_const.prodMk measurable_id)).sub
      (hFm.comp (measurable_const.prodMk measurable_id))
  have hXi' (z : Fin K → Z) : Integrable (fun w => X (z, w)) ρ :=
    hsample.integrable_comp_of_integrable (hXi z)
  have hX2 (z : Fin K → Z) : Integrable (fun w => X (z, w) ^ 2) ρ :=
    hsample.integrable_comp_of_integrable (hmom z).1
  have hmapint (z : Fin K → Z) : (∫ w, X (z, w) ^ 2 ∂ρ) =
      ∫ w, (F (a z, w) - F (b z, w)) ^ 2 ∂P := by
    rw [← hsample.map_eq]
    exact (integral_map (μ := ρ) hsample.measurable.aemeasurable
      ((hfixed z).pow_const 2).aestronglyMeasurable).symm
  have hcabs (z : Fin K → Z) : |c z| ≤ 2 * Δ := by
    have hh := abs_add_le (δ (a z)) (-δ (b z))
    rw [abs_neg] at hh
    change |δ (a z) - δ (b z)| ≤ _
    have h1 := hδ _ (hQC (haQ z))
    have h2 := hδ _ (hQC (hbQ z))
    simpa only [sub_eq_add_neg] using hh.trans (by linarith)
  have hcb (z : Fin K → Z) : c z ^ 2 ≤ H ^ 2 / 4 := by
    have hh : |c z| ≤ H / 2 := (hcabs z).trans (by linarith)
    have hsq := pow_le_pow_left₀ (abs_nonneg (c z)) hh 2
    rw [sq_abs] at hsq
    nlinarith
  have hmean (z : Fin K → Z) : (∫ w, X (z, w) ∂ρ) = f (a z) - f (b z) := by
    have he : (∫ w, X (z, w) ∂ρ) = ∫ w, (F (a z, w) - F (b z, w)) ∂P := by
      rw [← hsample.map_eq]
      exact (integral_map (μ := ρ) hsample.measurable.aemeasurable
        (hfixed z).aestronglyMeasurable).symm
    rw [he, integral_sub (hfi _ (hQC (haQ z))) (hfi _ (hQC (hbQ z))),
      hfmean _ (hQC (haQ z)), hfmean _ (hQC (hbQ z))]
  have ht := iid_fresh_selected_value h_samples.measurable h_samples.independent h_samples.marginal
    K T hT hX hc hs hell (by positivity : 0 ≤ 2 * Δ) hXi' hX2
    (fun z => (hmapint z).le.trans ((hmom z).2.trans hBH)) hcb hcabs hscale a b f hmean
  have he (z : Fin K → Z) (w : Z) : X (z, w) + c z =
      (F (a z, sample w) + δ (a z)) - (F (b z, sample w) + δ (b z)) := by dsimp [X, c]; ring
  dsimp only at ht ⊢
  simpa only [he] using ht

lemma adaptive_weak_oracle_selection {Ω Ξ Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {ρ : Measure Z} [IsProbabilityMeasure ρ] {ξ : ℕ → Ξ → Z}
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ ρ μ)
    (sample : Z → Ω) (hsample : MeasurePreserving sample ρ P)
    {F : E × Ω → ℝ} {G : E × Ω → E} {C U Q : Set E}
    (hC : IsCompact C) (hUC : U ⊆ C) (hQ : Convex ℝ Q)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ζ ∂P, ContinuousOn (fun z => F (z, ζ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ζ)) U volume ∧
      ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : E, (∫ z, F (z, ζ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ζ), v⟫ * ψ z)
    {B D η Δ H s ell : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hη : 0 < η)
    (hΔ : 0 ≤ Δ) (hδH : Δ ≤ H / 4) (hBH : D ^ 2 * B ≤ H ^ 2)
    (hmargin : ∀ x ∈ Q, closedBall x η ⊆ U)
    (hdiam : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hi : ∀ z ∈ U, Integrable (fun ζ => ‖G (z, ζ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ζ, ‖G (z, ζ)‖ ^ 2 ∂P) ≤ B)
    (f δ : E → ℝ) (hδm : Measurable δ) (hδ : ∀ x ∈ C, |δ x| ≤ Δ)
    (hfi : ∀ x ∈ C, Integrable (fun ζ => F (x, ζ)) P)
    (hfmean : ∀ x ∈ C, (∫ ζ, F (x, ζ) ∂P) = f x)
    (N T : ℕ) (hT : 0 < T) (hs : 0 < s) (hell : 0 < ell)
    (hscale : (T : ℝ) * H ^ 2 = s ^ 2 * ell)
    (τ₁ τ₂ γ₁ γ₂ h : ℝ) {project : E → E}
    (hp : Continuous project) (hproject : ∀ x, project x ∈ Q)
    {initial : E × E} (hx0 : initial.1 ∈ Q) (hz0 : initial.2 ∈ Q)
    (batches : ℕ → ℕ) (direction : Z → E) (hd : Measurable direction) :
    let g := fun x ζ => F (x, ζ) + δ x
    let u₁ := fun ζ t (i : Fin (batches t)) => direction (ξ (2 * (∑ k ∈ Finset.range t, batches k) + i) ζ)
    let u₂ := fun ζ t (i : Fin (batches t)) => direction (ξ (2 * (∑ k ∈ Finset.range t, batches k) + batches t + i) ζ)
    let states := fun ζ => LongTails.Algorithms.ClippedTwoPoint.dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial batches
      (u₁ ζ) (u₂ ζ) g (fun i => sample (ξ i ζ)) 0 N
    let output := fun ζ => LongTails.Algorithms.ClippedTwoPoint.adaptiveOutput d τ₁ τ₂ γ₁ γ₂ h s project initial batches
      (u₁ ζ) (u₂ ζ) g (fun i => sample (ξ i ζ)) 0 N T
    μ.real {ζ | min (f (states ζ).1.1) (f (states ζ).2.1) +
      (4097 * s * ell / T + 2 * Δ) < f (output ζ)} ≤ 2 * Real.exp (-ell) := by
  classical
  intro g u₁ u₂ states output
  let K := 2 * (∑ t ∈ Finset.range N, batches t)
  let fallback : Z := (nonempty_of_isProbabilityMeasure ρ).some
  have hg : Measurable (fun p : E × Ω => g p.1 p.2) := hFm.add (hδm.comp measurable_fst)
  obtain ⟨st, hm, hmem, he⟩ := ClippedTwoPointExecution.dual_solver_extended_history hQ hp hproject hx0 hz0
    d τ₁ τ₂ γ₁ γ₂ h batches direction sample hd hsample.measurable fallback g hg N K le_rfl
  have ht := weak_oracle_selected_value h_samples sample hsample hC hUC hQ hFm hG hF
    hB hD hη hΔ hδH hBH hmargin hdiam hi hb f δ hδm hδ hfi hfmean K T hT hs hell hscale
    (fun z => (st z).1.1) (fun z => (st z).2.1) hm.fst.fst hm.snd.fst
    (fun z => (hmem z).1.1) (fun z => (hmem z).2.1)
  have he' (ζ : Ξ) : st (fun i => ξ i ζ) = states ζ := he (fun i => ξ i ζ)
  dsimp only at ht ⊢
  simpa only [he', output, states, LongTails.Algorithms.ClippedTwoPoint.adaptiveOutput,
    g, u₁, u₂, K, Nat.zero_add] using ht

end WeakOracleSelection

end LongTails.Proofs.ClippedSelection

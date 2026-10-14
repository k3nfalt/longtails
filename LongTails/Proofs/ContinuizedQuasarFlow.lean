import LongTails.Algorithms.ContinuizedQuasar
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import LongTails.Proofs.QuasarEnergy

open scoped RealInnerProductSpace BigOperators
open MeasureTheory

namespace OracleTemplate.ContinuizedSimilarQuasar

open LongTails.Setups.ContinuizedSimilarQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma flowWeight_bounds {γ θ t : ℝ} (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (ht : 0 ≤ t) :
    0 ≤ flowWeight γ θ t ∧ flowWeight γ θ t ≤ 1 / (1 + γ) := by
  have hd : 0 < 1 + γ := by positivity
  have he : Real.exp (-(1 + γ) * θ * t) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd.le) hθ) ht)
  unfold flowWeight
  constructor
  · exact div_nonneg (sub_nonneg.mpr he) hd.le
  · exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-(1 + γ) * θ * t)]) hd.le

lemma flowWeight_hasDerivAt {γ θ : ℝ} (hγ : 0 ≤ γ) (t : ℝ) :
    HasDerivAt (flowWeight γ θ) (θ * Real.exp (-(1 + γ) * θ * t)) t := by
  have hd : 1 + γ ≠ 0 := ne_of_gt (by positivity)
  have h := (((hasDerivAt_id t).const_mul (-(1 + γ) * θ)).exp.const_sub 1).div_const (1 + γ)
  change HasDerivAt (fun x => (1 - Real.exp (-(1 + γ) * θ * x)) / (1 + γ)) _ t
  convert h using 1 <;> simp only [id_eq]
  field_simp


lemma flow_hasDerivAt {γ θ : ℝ} (hγ : 0 ≤ γ) (s : E × E) (t : ℝ) :
    HasDerivAt (fun t => (flow γ θ t s).1)
      (θ • ((flow γ θ t s).2 - (flow γ θ t s).1)) t ∧
    HasDerivAt (fun t => (flow γ θ t s).2)
      ((γ * θ) • ((flow γ θ t s).1 - (flow γ θ t s).2)) t := by
  have hd : 1 + γ ≠ 0 := ne_of_gt (by positivity)
  have ha := flowWeight_hasDerivAt (θ := θ) hγ t
  have hx := ((ha.const_sub 1).smul_const s.1).add (ha.smul_const s.2)
  have hz := ((ha.const_mul γ).smul_const s.1).add
    (((ha.const_mul γ).const_sub 1).smul_const s.2)
  constructor
  · have hi : θ • ((flow γ θ t s).2 - (flow γ θ t s).1) =
        -(θ * Real.exp (-(1 + γ) * θ * t)) • s.1 +
          (θ * Real.exp (-(1 + γ) * θ * t)) • s.2 := by
      dsimp [flow, flowWeight]
      match_scalars
      all_goals field_simp; ring
    rw [hi]
    exact hx
  · have hi : (γ * θ) • ((flow γ θ t s).1 - (flow γ θ t s).2) =
        (γ * (θ * Real.exp (-(1 + γ) * θ * t))) • s.1 +
          -(γ * (θ * Real.exp (-(1 + γ) * θ * t))) • s.2 := by
      dsimp [flow, flowWeight]
      match_scalars
      all_goals field_simp; ring
    rw [hi]
    exact hz

lemma flow_norm_bound {γ θ t R : ℝ} (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (ht : 0 ≤ t)
    (s : E × E) (u : E) (hx : ‖s.1 - u‖ ≤ R) (hz : ‖s.2 - u‖ ≤ R) :
    ‖(flow γ θ t s).1 - u‖ ≤ R ∧ ‖(flow γ θ t s).2 - u‖ ≤ R := by
  obtain ⟨ha, hau⟩ := flowWeight_bounds hγ hθ ht
  have hd : 0 < 1 + γ := by positivity
  have hab : flowWeight γ θ t ≤ 1 := hau.trans ((div_le_one hd).mpr (by linarith))
  have hga : γ * flowWeight γ θ t ≤ 1 := by
    have hh := (le_div_iff₀ hd).mp hau
    nlinarith
  have hp : 0 ≤ γ * flowWeight γ θ t := mul_nonneg hγ ha
  have bound (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ 1) :
      ‖(1 - a) • s.1 + a • s.2 - u‖ ≤ R := by
    have he : (1 - a) • s.1 + a • s.2 - u =
        (1 - a) • (s.1 - u) + a • (s.2 - u) := by module
    rw [he]
    calc
      _ ≤ ‖(1 - a) • (s.1 - u)‖ + ‖a • (s.2 - u)‖ := norm_add_le _ _
      _ = (1 - a) * ‖s.1 - u‖ + a * ‖s.2 - u‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha,
          abs_of_nonneg (sub_nonneg.mpr hb)]
      _ ≤ (1 - a) * R + a * R := add_le_add
        (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hb))
        (mul_le_mul_of_nonneg_left hz ha)
      _ = R := by ring
  constructor
  · exact bound _ ha hab
  · convert bound (1 - γ * flowWeight γ θ t) (sub_nonneg.mpr hga) (by linarith) using 1
    simp [flow]

lemma flow_continuous (γ θ : ℝ) : Continuous (fun q : ℝ × (E × E) => flow γ θ q.1 q.2) := by
  unfold flow flowWeight
  fun_prop

lemma continuous_flow_bounded {γ θ : ℝ} (hγ : 0 ≤ γ) (hθ : 0 ≤ θ)
    (H : E × E → ℝ) (hH : Continuous H) (s : E × E) :
    ∃ C : ℝ, ∀ t, 0 ≤ t → ‖H (flow γ θ t s)‖ ≤ C := by
  have hh : Continuous (fun a : ℝ =>
      ‖H ((1 - a) • s.1 + a • s.2, (γ * a) • s.1 + (1 - γ * a) • s.2)‖) := by
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).bddAbove_image hh.continuousOn
  refine ⟨C, fun t ht => ?_⟩
  obtain ⟨ha, hb⟩ := flowWeight_bounds hγ hθ ht
  have hd : 0 < 1 + γ := by positivity
  have ha1 : flowWeight γ θ t ≤ 1 := hb.trans ((div_le_one hd).mpr (by linarith))
  exact hC ⟨flowWeight γ θ t, ⟨ha, ha1⟩, rfl⟩

lemma sample_flow_integrable {n : ℕ} {γ θ : ℝ} (hγ : 0 ≤ γ) (hθ : 0 ≤ θ)
    (H : Fin n → E × E → ℝ) (hH : ∀ i, Continuous (H i)) (s : E × E)
    (P : ProbabilityMeasure (ℝ × Fin n)) :
    Integrable (fun q : ℝ × Fin n => H q.2 (flow γ θ (max 0 q.1) s)) (P : Measure (ℝ × Fin n)) := by
  classical
  choose C hC using fun i => continuous_flow_bounded hγ hθ (H i) (hH i) s
  have hC0 (i : Fin n) : 0 ≤ C i := (norm_nonneg _).trans (hC i 0 le_rfl)
  have hc : Continuous (fun q : ℝ × Fin n => H q.2 (flow γ θ (max 0 q.1) s)) := by
    apply continuous_prod_of_discrete_right.mpr
    intro i
    exact (hH i).comp ((flow_continuous γ θ).comp
      ((continuous_const.max continuous_id).prodMk continuous_const))
  apply (integrable_const (∑ i, C i)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun q => (hC q.2 _ (le_max_left _ _)).trans
    (Finset.single_le_sum (fun i _ => hC0 i) (Finset.mem_univ q.2)))

variable [CompleteSpace E]

lemma flow_energy_hasDerivAt {f : E → ℝ} {G : E → E} {γ θ μ : ℝ}
    (hγ : 0 ≤ γ) (hg : ∀ x, HasGradientAt f (G x) x)
    (s : E × E) (u : E) (t : ℝ) :
    HasDerivAt (fun t => SimilarQuasar.energy f μ u (flow γ θ t s))
      (θ * ⟪G (flow γ θ t s).1, (flow γ θ t s).2 - (flow γ θ t s).1⟫ +
        μ * γ * θ * ⟪(flow γ θ t s).2 - u, (flow γ θ t s).1 - (flow γ θ t s).2⟫) t := by
  obtain ⟨hx, hz⟩ := flow_hasDerivAt (θ := θ) hγ s t
  have hf := (hg (flow γ θ t s).1).hasFDerivAt.comp_hasDerivAt t hx
  have hn := ((hz.sub_const u).norm_sq).const_mul (μ / 2)
  have h := (hf.sub_const (f u)).add hn
  convert h using 1
  · rfl
  · simp only [InnerProductSpace.toDual_apply_apply, inner_smul_right]
    ring

end OracleTemplate.ContinuizedSimilarQuasar

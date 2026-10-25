import LongTails.Proofs.FiniteMomentMirrorGeometry
import LongTails.Proofs.FiniteVarianceBatch

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open LongTails.Proofs.FiniteMomentMirrorGeometry

namespace LongTails.Proofs.PowerMirrorMoments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
lemma measurable_primalOfDual (p : ℝ) : Measurable (primalOfDual (E := E) p) := by
  unfold primalOfDual
  fun_prop

omit [CompleteSpace E] in
lemma integrable_primalOfDual {p : ℝ} (hp : 1 < p) {X : Ω → E}
    (hX : Measurable X) (hXp : Integrable (fun ω => ‖X ω‖ ^ p) P) :
    Integrable (fun ω => primalOfDual p (X ω)) P := by
  apply (integrable_norm_iff ((measurable_primalOfDual p).comp hX).aestronglyMeasurable).mp
  change Integrable (fun ω => ‖primalOfDual p (X ω)‖) P
  simp_rw [norm_primalOfDual hp]
  exact integrable_norm_rpow_of_le hX.aestronglyMeasurable
    (by linarith : 0 ≤ p - 1) (by linarith : 0 ≤ p) (by linarith) hXp

omit [IsProbabilityMeasure P] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma integrable_sum_power {ι : Type*} (s : Finset ι) {p : ℝ} (hp : 0 < p)
    (X : ι → Ω → E) (hX : ∀ i, Measurable (X i))
    (hXp : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ p) P) :
    Integrable (fun ω => ‖∑ i ∈ s, X i ω‖ ^ p) P := by
  have hm (i : ι) : MemLp (X i) (ENNReal.ofReal p) P := by
    apply (integrable_norm_rpow_iff (hX i).aestronglyMeasurable
      (by simpa using hp) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hp.le] using hXp i
  have hs := memLp_finsetSum s (fun i _ => hm i)
  simpa only [ENNReal.toReal_ofReal hp.le] using hs.integrable_norm_rpow
    (by simpa using hp) ENNReal.ofReal_ne_top

lemma independent_sum_power {ι : Type*} (s : Finset ι) {p : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (X : ι → Ω → E)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hXi : ∀ i, Integrable (X i) P)
    (hXp : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ p) P)
    (hzero : ∀ i, (∫ ω, X i ω ∂P) = 0) :
    (∫ ω, ‖∑ i ∈ s, X i ω‖ ^ p ∂P) ≤ 6 * ∑ i ∈ s, ∫ ω, ‖X i ω‖ ^ p ∂P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow (show p ≠ 0 by linarith)]
  | @insert i s hi ih =>
    let S : Ω → E := fun ω => ∑ j ∈ s, X j ω
    have hSm : Measurable S := by dsimp [S]; fun_prop
    have hSp := integrable_sum_power s (show 0 < p by linarith) X hX hXp
    change Integrable (fun ω => ‖S ω‖ ^ p) P at hSp
    have hSi := integrable_primalOfDual hp hSm hSp
    have hInd : IndepFun S (X i) P := by
      have he : S = ∑ j ∈ s, X j := by ext ω; simp [S]
      rw [he]
      exact hind.indepFun_finsetSum_of_notMem hX hi
    have hInd' := hInd.comp (measurable_primalOfDual p) measurable_id
    have hcrossi := hInd'.integrable_bilin hSi (hXi i) (innerSL ℝ)
    change Integrable (fun ω => inner ℝ (primalOfDual p (S ω)) (X i ω)) P at hcrossi
    have hcross := hInd'.integral_bilin hSi (hXi i) (innerSL ℝ)
    change (∫ ω, inner ℝ (primalOfDual p (S ω)) (X i ω) ∂P) =
      inner ℝ (∫ ω, primalOfDual p (S ω) ∂P) (∫ ω, X i ω ∂P) at hcross
    rw [hzero, inner_zero_right] at hcross
    have hsum := integrable_sum_power (insert i s) (show 0 < p by linarith) X hX hXp
    have hpoint (ω : Ω) : ‖S ω + X i ω‖ ^ p ≤ ‖S ω‖ ^ p +
        p * inner ℝ (primalOfDual p (S ω)) (X i ω) + 6 * ‖X i ω‖ ^ p := by
      simpa only [primalOfDual, inner_smul_left, RCLike.conj_to_real, mul_assoc] using
        norm_power_smooth hp hp2 (S ω) (X i ω)
    have hsum' : Integrable (fun ω => ‖S ω + X i ω‖ ^ p) P := by
      simpa only [Finset.sum_insert hi, S, add_comm] using hsum
    have hbound := integral_mono hsum'
      ((hSp.add (hcrossi.const_mul p)).add ((hXp i).const_mul 6)) hpoint
    change (∫ ω, ‖S ω + X i ω‖ ^ p ∂P) ≤
      ∫ ω, (‖S ω‖ ^ p + p * inner ℝ (primalOfDual p (S ω)) (X i ω)) +
        6 * ‖X i ω‖ ^ p ∂P at hbound
    have hleft : Integrable (fun ω => ‖S ω‖ ^ p +
        p * inner ℝ (primalOfDual p (S ω)) (X i ω)) P := hSp.add (hcrossi.const_mul p)
    rw [integral_add hleft ((hXp i).const_mul 6),
      integral_add hSp (hcrossi.const_mul p), integral_const_mul,
      integral_const_mul, hcross] at hbound
    simp only [Finset.sum_insert hi]
    have he : (fun ω => ‖X i ω + ∑ j ∈ s, X j ω‖ ^ p) =
        (fun ω => ‖S ω + X i ω‖ ^ p) := by funext ω; simp [S, add_comm]
    rw [he]
    dsimp [S] at hbound
    linarith

lemma finite_mean_power {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P)
    (hXp : Integrable (fun ω => ‖X ω‖ ^ p) P) (hzero : (∫ ω, X ω ∂P) = 0)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → Ω => ‖(1 / (n : ℝ)) • ∑ i, X (ξ i)‖ ^ p)
      (Measure.pi fun _ : Fin n => P) ∧
    (∫ ξ : Fin n → Ω, ‖(1 / (n : ℝ)) • ∑ i, X (ξ i)‖ ^ p
      ∂Measure.pi (fun _ : Fin n => P)) ≤ 6 / (n : ℝ) ^ (p - 1) * ∫ ω, ‖X ω‖ ^ p ∂P := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hl (i : Fin n) : HasLaw (fun ξ : Fin n → Ω => ξ i) P
      (Measure.pi fun _ : Fin n => P) :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  let Y (i : Fin n) (ξ : Fin n → Ω) := X (ξ i)
  have hYm (i : Fin n) : Measurable (Y i) := hX.comp (measurable_pi_apply i)
  have hYi (i : Fin n) : Integrable (Y i) (Measure.pi fun _ : Fin n => P) :=
    (hl i).integrable_comp hXi
  have hYp (i : Fin n) : Integrable (fun ξ => ‖Y i ξ‖ ^ p) (Measure.pi fun _ : Fin n => P) :=
    (hl i).integrable_comp hXp
  have hs := integrable_sum_power Finset.univ (show 0 < p by linarith) Y hYm hYp
  have ht := independent_sum_power Finset.univ hp hp2 Y hYm
    (iIndepFun_pi (fun _ => hX.aemeasurable)) hYi hYp
    (fun i => ((hl i).integral_comp hXi.aestronglyMeasurable).trans hzero)
  have hm (i : Fin n) : (∫ ξ, ‖Y i ξ‖ ^ p ∂Measure.pi (fun _ : Fin n => P)) =
      ∫ ω, ‖X ω‖ ^ p ∂P := (hl i).integral_comp hXp.aestronglyMeasurable
  simp_rw [hm] at ht
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at ht
  have he (ξ : Fin n → Ω) : ‖(1 / (n : ℝ)) • ∑ i, X (ξ i)‖ ^ p =
      (1 / (n : ℝ)) ^ p * ‖∑ i, Y i ξ‖ ^ p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      Real.mul_rpow (by positivity) (norm_nonneg _)]
  simp_rw [he]
  refine ⟨hs.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg (by positivity : 0 ≤ 1 / (n : ℝ)) p)
  refine hb.trans_eq ?_
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hn0.le, Real.one_rpow,
    Real.rpow_sub hn0, Real.rpow_one]
  field_simp

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma finite_mean_integrable {X : Ω → E} (hXi : Integrable X P) (n : ℕ) :
    Integrable (fun ξ : Fin n → Ω => (1 / (n : ℝ)) • ∑ i, X (ξ i))
      (Measure.pi fun _ : Fin n => P) := by
  apply Integrable.smul
  apply integrable_finsetSum
  intro i _
  exact (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp
    hXi.aestronglyMeasurable |>.mpr hXi

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma finite_mean_mean {X : Ω → E} (hXi : Integrable X P) (n : ℕ) (hn : 0 < n) :
    (∫ ξ : Fin n → Ω, (1 / (n : ℝ)) • ∑ i, X (ξ i)
      ∂Measure.pi (fun _ : Fin n => P)) = ∫ ω, X ω ∂P := by
  have hXi' (i : Fin n) : Integrable (fun ξ : Fin n → Ω => X (ξ i))
      (Measure.pi fun _ : Fin n => P) :=
    (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp
      hXi.aestronglyMeasurable |>.mpr hXi
  rw [integral_smul, integral_finsetSum _ (fun i _ => hXi' i)]
  have he (i : Fin n) : (∫ ξ : Fin n → Ω, X (ξ i) ∂Measure.pi (fun _ : Fin n => P)) =
      ∫ ω, X ω ∂P := by
    have hl : HasLaw (fun ξ : Fin n → Ω => ξ i) P (Measure.pi fun _ : Fin n => P) :=
      ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
    exact hl.integral_comp hXi.aestronglyMeasurable
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [one_div_mul_cancel (Nat.cast_ne_zero.mpr hn.ne'), one_smul]

lemma finite_mean_centered_power {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P) (u : E)
    (hXp : Integrable (fun ω => ‖X ω - u‖ ^ p) P) (hmean : (∫ ω, X ω ∂P) = u)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → Ω => ‖(1 / (n : ℝ)) • ∑ i, X (ξ i) - u‖ ^ p)
      (Measure.pi fun _ : Fin n => P) ∧
    (∫ ξ : Fin n → Ω, ‖(1 / (n : ℝ)) • ∑ i, X (ξ i) - u‖ ^ p
      ∂Measure.pi (fun _ : Fin n => P)) ≤ 6 / (n : ℝ) ^ (p - 1) * ∫ ω, ‖X ω - u‖ ^ p ∂P := by
  simp_rw [OracleTemplate.RobustGradient.finite_mean_centered u n hn]
  exact finite_mean_power hp hp2 (hX.sub measurable_const) (hXi.sub (integrable_const u))
    hXp (by simp only [Pi.sub_apply]; rw [integral_sub hXi (integrable_const u), hmean]; simp) n hn

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma norm_tail_le_power {p r v : ℝ} (hp : 0 < p) (hr : 0 < r) {X : Ω → E}
    (hXp : Integrable (fun ω => ‖X ω‖ ^ p) P)
    (hv : (∫ ω, ‖X ω‖ ^ p ∂P) ≤ v) : P.real {ω | r < ‖X ω‖} ≤ v / r ^ p := by
  have h := (hXp.div_const (r ^ p)).measure_le_integral
    (Filter.Eventually.of_forall fun ω => by positivity)
    (s := {ω | r < ‖X ω‖}) (by
      intro ω hω
      apply (one_le_div (Real.rpow_pos_of_pos hr p)).mpr
      exact Real.rpow_le_rpow hr.le hω.le hp.le)
  have h' : P {ω | r < ‖X ω‖} ≤ ENNReal.ofReal (v / r ^ p) := by
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_div]
    exact div_le_div_of_nonneg_right hv (Real.rpow_nonneg hr.le p)
  have hv0 : 0 ≤ v := (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) p).trans hv
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr h' |>.trans_eq
    (ENNReal.toReal_ofReal (div_nonneg hv0 (Real.rpow_nonneg hr.le p)))

lemma raw_power_of_centered {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P) (u : E)
    (hXp : Integrable (fun ω => ‖X ω - u‖ ^ p) P) (hmean : (∫ ω, X ω ∂P) = u) :
    Integrable (fun ω => ‖X ω‖ ^ p) P ∧
    (∫ ω, ‖X ω‖ ^ p ∂P) ≤ ‖u‖ ^ p + 6 * ∫ ω, ‖X ω - u‖ ^ p ∂P := by
  have hp0 : 0 < p := by linarith
  have hm : MemLp (fun ω => X ω - u) (ENNReal.ofReal p) P := by
    apply (integrable_norm_rpow_iff (hX.sub measurable_const).aestronglyMeasurable
      (by simpa using hp0) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hp0.le, Pi.sub_apply] using hXp
  have hu : MemLp (fun _ : Ω => u) (ENNReal.ofReal p) P := memLp_const u
  have hrawm : MemLp X (ENNReal.ofReal p) P := by
    have hs : MemLp (fun ω => (X ω - u) + u) (ENNReal.ofReal p) P := hm.add hu
    simpa only [sub_add_cancel] using hs
  have hrawi : Integrable (fun ω => ‖X ω‖ ^ p) P := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hrawm.integrable_norm_rpow
      (by simpa using hp0) ENNReal.ofReal_ne_top
  refine ⟨hrawi, ?_⟩
  have hci : Integrable (fun ω => X ω - u) P := hXi.sub (integrable_const u)
  have hcrossi : Integrable (fun ω => inner ℝ (primalOfDual p u) (X ω - u)) P :=
    Integrable.const_inner (primalOfDual p u) hci
  have hcross : (∫ ω, inner ℝ (primalOfDual p u) (X ω - u) ∂P) = 0 := by
    rw [integral_inner hci, integral_sub hXi (integrable_const u), hmean, integral_const]
    simp
  have hpoint (ω : Ω) : ‖X ω‖ ^ p ≤ ‖u‖ ^ p +
      p * inner ℝ (primalOfDual p u) (X ω - u) + 6 * ‖X ω - u‖ ^ p := by
    have h := norm_power_smooth hp hp2 u (X ω - u)
    simpa only [add_sub_cancel, primalOfDual, inner_smul_left, RCLike.conj_to_real, mul_assoc,
      add_sub_cancel_left, sub_add_cancel, add_comm u] using h
  have hleft : Integrable (fun ω => ‖u‖ ^ p +
      p * inner ℝ (primalOfDual p u) (X ω - u)) P := (integrable_const _).add (hcrossi.const_mul p)
  have hb := integral_mono hrawi (hleft.add (hXp.const_mul 6)) hpoint
  change (∫ ω, ‖X ω‖ ^ p ∂P) ≤ ∫ ω, (‖u‖ ^ p +
    p * inner ℝ (primalOfDual p u) (X ω - u)) + 6 * ‖X ω - u‖ ^ p ∂P at hb
  rw [integral_add hleft (hXp.const_mul 6), integral_add (integrable_const _) (hcrossi.const_mul p),
    integral_const_mul, integral_const_mul, hcross, integral_const] at hb
  simpa using hb

end LongTails.Proofs.PowerMirrorMoments

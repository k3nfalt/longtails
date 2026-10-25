import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Prod
import LongTails.Proofs.SgdConvex
import LongTails.Proofs.FiniteVarianceBatch
import Mathlib.Tactic

open scoped RealInnerProductSpace
open MeasureTheory

namespace LongTails.Proofs.HilbertSmallMoments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma symmetric_power_bound (x y : E) {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    ‖x + y‖ ^ p + ‖x - y‖ ^ p ≤ 2 * ‖x‖ ^ p + 2 * ‖y‖ ^ p := by
  have hq : 0 ≤ p / 2 := by positivity
  have hq1 : p / 2 ≤ 1 := by linarith
  have hs (z : E) : (‖z‖ ^ 2 : ℝ) ^ (p / 2) = ‖z‖ ^ p := by
    rw [← Real.rpow_natCast_mul (norm_nonneg z)]
    congr 1
    ring
  have hpar : (1 / 2 : ℝ) * ‖x + y‖ ^ 2 + 1 / 2 * ‖x - y‖ ^ 2 =
      ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    rw [norm_add_sq_real, norm_sub_sq_real]
    ring
  have hc : (1 / 2 : ℝ) * (‖x + y‖ ^ 2 : ℝ) ^ (p / 2) +
      1 / 2 * (‖x - y‖ ^ 2 : ℝ) ^ (p / 2) ≤
      (1 / 2 * ‖x + y‖ ^ 2 + 1 / 2 * ‖x - y‖ ^ 2) ^ (p / 2) :=
    (Real.concaveOn_rpow hq hq1).2 (sq_nonneg ‖x + y‖) (sq_nonneg ‖x - y‖)
      (by norm_num) (by norm_num) (by norm_num)
  simp only [hpar, hs] at hc
  have ha := Real.rpow_add_le_add_rpow (sq_nonneg ‖x‖) (sq_nonneg ‖y‖) hq hq1
  rw [hs, hs] at ha
  linarith

omit [InnerProductSpace ℝ E] in
lemma addition_power_bound (x y : E) {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ‖x + y‖ ^ p ≤ 2 * (‖x‖ ^ p + ‖y‖ ^ p) := by
  have hsum : (‖x‖ + ‖y‖) ^ p ≤ (2 : ℝ) ^ (p - 1) * (‖x‖ ^ p + ‖y‖ ^ p) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ‖x‖₊ ‖y‖₊ hp
  have hc : (2 : ℝ) ^ (p - 1) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show p - 1 ≤ 1 by linarith)
  exact (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le x y) (by linarith)).trans
    (hsum.trans (mul_le_mul_of_nonneg_right hc (by positivity)))

variable {Ω : Type} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] [InnerProductSpace ℝ E] in
lemma integrable_add_power {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hXi : Integrable (fun ω => ‖X ω‖ ^ p) P)
    (hYi : Integrable (fun ω => ‖Y ω‖ ^ p) P) :
    Integrable (fun ω => ‖X ω + Y ω‖ ^ p) P := by
  apply ((hXi.add hYi).const_mul 2).mono'
  · exact ((hX.add hY).norm.pow_const p).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact addition_power_bound _ _ hp hp2)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma norm_integral_power_le {X : Ω → E} {p : ℝ} (hp : 1 ≤ p)
    (hi : Integrable X P) (hpi : Integrable (fun ω => ‖X ω‖ ^ p) P) :
    ‖∫ ω, X ω ∂P‖ ^ p ≤ ∫ ω, ‖X ω‖ ^ p ∂P := by
  have hj := (convexOn_rpow hp).map_integral_le
    (Real.continuous_rpow_const (by linarith : 0 ≤ p)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun ω => norm_nonneg (X ω))) hi.norm hpi
  exact (Real.rpow_le_rpow (norm_nonneg _) (norm_integral_le_integral_norm X)
    (by linarith)).trans hj

lemma symmetric_shift_bound {X : Ω → E} (hX : Measurable X) {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hi : Integrable (fun ω => ‖X ω‖ ^ p) P)
    (s : E)
    (hsym : (∫ ω, ‖s + X ω‖ ^ p ∂P) = ∫ ω, ‖s - X ω‖ ^ p ∂P) :
    (∫ ω, ‖s + X ω‖ ^ p ∂P) ≤ ‖s‖ ^ p + ∫ ω, ‖X ω‖ ^ p ∂P := by
  have hplus : Integrable (fun ω => ‖s + X ω‖ ^ p) P :=
    integrable_add_power measurable_const hX hp hp2 (integrable_const _) hi
  have hneg : Integrable (fun ω => ‖-X ω‖ ^ p) P := by simpa using hi
  have hminus : Integrable (fun ω => ‖s - X ω‖ ^ p) P := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using
      integrable_add_power measurable_const hX.neg hp hp2 (integrable_const _) hneg
  have hb := integral_mono (hplus.add hminus)
    (((integrable_const (‖s‖ ^ p)).const_mul 2).add (hi.const_mul 2))
    (fun ω => symmetric_power_bound s (X ω) (by linarith) hp2)
  simp only [Pi.add_apply] at hb
  rw [integral_add hplus hminus, ← hsym,
    integral_add ((integrable_const (‖s‖ ^ p)).const_mul 2) (hi.const_mul 2),
    integral_const_mul, integral_const_mul] at hb
  simp only [integral_const, probReal_univ, one_smul] at hb
  linarith

lemma centered_increment_bound [CompleteSpace E] {X : Ω → E} (hX : Measurable X)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hi : Integrable X P)
    (hpi : Integrable (fun ω => ‖X ω‖ ^ p) P) (hzero : ∫ ω, X ω ∂P = 0)
    (s : E) :
    (∫ ω, ‖s + X ω‖ ^ p ∂P) ≤ ‖s‖ ^ p + 4 * ∫ ω, ‖X ω‖ ^ p ∂P := by
  let Y : Ω × Ω → E := fun w => X w.1 - X w.2
  have hYm : Measurable Y := (hX.comp measurable_fst).sub (hX.comp measurable_snd)
  have hneg : Integrable (fun w : Ω × Ω => ‖-X w.2‖ ^ p) (P.prod P) := by
    simpa only [norm_neg] using hpi.comp_snd P
  have hYi : Integrable (fun w => ‖Y w‖ ^ p) (P.prod P) := by
    simpa only [Y, sub_eq_add_neg, Pi.neg_apply, Function.comp_apply] using integrable_add_power
      (hX.comp measurable_fst) (hX.comp measurable_snd).neg hp hp2 (hpi.comp_fst P) hneg
  have hSi : Integrable (fun w => ‖s + Y w‖ ^ p) (P.prod P) :=
    integrable_add_power measurable_const hYm hp hp2 (integrable_const _) hYi
  have hsym : (∫ w, ‖s + Y w‖ ^ p ∂P.prod P) = ∫ w, ‖s - Y w‖ ^ p ∂P.prod P := by
    calc
      _ = ∫ w : Ω × Ω, ‖s + Y w.swap‖ ^ p ∂P.prod P := (integral_prod_swap _).symm
      _ = _ := by
        congr 1
        funext w
        congr 2
        dsimp [Y]
        abel
  have hs := symmetric_shift_bound hYm hp hp2 hYi s hsym
  have hJ (ω : Ω) : ‖s + X ω‖ ^ p ≤ ∫ ω', ‖s + Y (ω, ω')‖ ^ p ∂P := by
    have hzi : Integrable (fun ω' => s + X ω - X ω') P :=
      (integrable_const _).sub hi
    have hzpi : Integrable (fun ω' => ‖s + X ω - X ω'‖ ^ p) P := by
      have hn : Integrable (fun ω' => ‖-X ω'‖ ^ p) P := by simpa only [norm_neg] using hpi
      simpa only [sub_eq_add_neg, Pi.neg_apply] using
        integrable_add_power measurable_const hX.neg hp hp2 (integrable_const _) hn
    have hj := norm_integral_power_le hp hzi hzpi
    rw [integral_sub (integrable_const _) hi, hzero] at hj
    simp only [integral_const, probReal_univ, one_smul, sub_zero] at hj
    convert hj using 1
    congr 1
    funext ω'
    congr 2
    dsimp [Y]
    abel
  have hplus : Integrable (fun ω => ‖s + X ω‖ ^ p) P :=
    integrable_add_power measurable_const hX hp hp2 (integrable_const _) hpi
  have hj := integral_mono hplus hSi.integral_prod_left hJ
  rw [← integral_prod (fun w => ‖s + Y w‖ ^ p) hSi] at hj
  have hbi := ((hpi.comp_fst P).add (hpi.comp_snd P)).const_mul 2
  have hb := integral_mono hYi hbi (fun w : Ω × Ω => by
    simpa only [Y, sub_eq_add_neg, norm_neg, Pi.add_apply] using addition_power_bound (X w.1) (-X w.2) hp hp2)
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_add (hpi.comp_fst P) (hpi.comp_snd P)] at hb
  have hf := integral_fun_fst (μ := P) (ν := P) (fun ω => ‖X ω‖ ^ p)
  have hg := integral_fun_snd (μ := P) (ν := P) (fun ω => ‖X ω‖ ^ p)
  simp only [probReal_univ, one_smul] at hf hg
  rw [hf, hg] at hb
  linarith

omit [IsProbabilityMeasure P] [InnerProductSpace ℝ E] in
lemma integrable_sum_power {ι : Type*} (s : Finset ι) (X : ι → Ω → E)
    (hX : ∀ i ∈ s, Measurable (X i)) {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ i ∈ s, Integrable (fun ω => ‖X i ω‖ ^ p) P) :
    Integrable (fun ω => ‖∑ i ∈ s, X i ω‖ ^ p) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow (show p ≠ 0 by linarith)]
  | @insert a s ha ih =>
    have hs := ih (fun i hi => hX i (Finset.mem_insert_of_mem hi))
      (fun i hmem => hi i (Finset.mem_insert_of_mem hmem))
    simp only [Finset.sum_insert ha]
    apply integrable_add_power (hX a (Finset.mem_insert_self _ _)) ?_ hp hp2
      (hi a (Finset.mem_insert_self _ _)) hs
    exact Finset.measurable_sum _ (fun i hi => hX i (Finset.mem_insert_of_mem hi))

lemma iid_sum_power_bound [CompleteSpace E] {X : Ω → E} (hX : Measurable X)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hi : Integrable X P)
    (hpi : Integrable (fun ω => ‖X ω‖ ^ p) P) (hzero : ∫ ω, X ω ∂P = 0)
    (n : ℕ) :
    Integrable (fun ξ : Fin n → Ω => ‖∑ i, X (ξ i)‖ ^ p) (Measure.pi fun _ => P) ∧
    (∫ ξ : Fin n → Ω, ‖∑ i, X (ξ i)‖ ^ p ∂Measure.pi (fun _ => P)) ≤
      4 * n * ∫ ω, ‖X ω‖ ^ p ∂P := by
  have hm (j : ℕ) : Measurable (fun ξ : Fin j → Ω => ‖∑ i, X (ξ i)‖ ^ p) := by fun_prop
  have hI (j : ℕ) : Integrable (fun ξ : Fin j → Ω => ‖∑ i, X (ξ i)‖ ^ p)
      (Measure.pi fun _ => P) := by
    apply integrable_sum_power (Finset.univ : Finset (Fin j))
      (fun (i : Fin j) (ξ : Fin j → Ω) => X (ξ i))
      (fun i _ => hX.comp (measurable_pi_apply i)) hp hp2
    intro i _
    exact ((measurePreserving_eval (fun _ : Fin j => P) i).integrable_comp
      hpi.aestronglyMeasurable).mpr hpi
  refine ⟨hI n, ?_⟩
  induction n with
  | zero => simp [Real.zero_rpow (show p ≠ 0 by linarith)]
  | succ n ih =>
    let Q := Measure.pi (fun _ : Fin n => P)
    let F : Ω × (Fin n → Ω) → ℝ := fun w => ‖∑ i : Fin (n + 1), X ((Fin.cons w.1 w.2 : Fin (n + 1) → Ω) i)‖ ^ p
    have hc := OracleTemplate.StochasticGradient.cons_measurePreserving P n
    have hFi : Integrable F (P.prod Q) :=
      (hc.integrable_comp (hm (n + 1)).aestronglyMeasurable).mpr (hI (n + 1))
    have hpoint (ξ : Fin n → Ω) :
        (∫ ω, F (ω, ξ) ∂P) ≤ ‖∑ i, X (ξ i)‖ ^ p + 4 * ∫ ω, ‖X ω‖ ^ p ∂P := by
      simpa only [F, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_comm] using
        centered_increment_bound hX hp hp2 hi hpi hzero (∑ i, X (ξ i))
    have hb := integral_mono hFi.integral_prod_right
      ((hI n).add (integrable_const (4 * ∫ ω, ‖X ω‖ ^ p ∂P))) hpoint
    simp only [Pi.add_apply] at hb
    rw [integral_add (hI n) (integrable_const (4 * ∫ ω, ‖X ω‖ ^ p ∂P))] at hb
    simp only [integral_const, probReal_univ, one_smul] at hb
    have he : (∫ ξ : Fin (n + 1) → Ω, ‖∑ i, X (ξ i)‖ ^ p
        ∂Measure.pi (fun _ => P)) = ∫ ξ, ∫ ω, F (ω, ξ) ∂P ∂Q := by
      rw [← hc.map_eq, integral_map hc.measurable.aemeasurable
        (hm (n + 1)).aestronglyMeasurable]
      exact integral_prod_symm F hFi
    rw [he]
    push_cast
    dsimp [Q] at hb
    linarith

lemma iid_mean_power_bound [CompleteSpace E] {X : Ω → E} (hX : Measurable X)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hi : Integrable X P)
    (hpi : Integrable (fun ω => ‖X ω‖ ^ p) P) (hzero : ∫ ω, X ω ∂P = 0)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → Ω => ‖(n : ℝ)⁻¹ • ∑ i, X (ξ i)‖ ^ p)
      (Measure.pi fun _ => P) ∧
    (∫ ξ : Fin n → Ω, ‖(n : ℝ)⁻¹ • ∑ i, X (ξ i)‖ ^ p
      ∂Measure.pi (fun _ => P)) ≤ 4 * (n : ℝ) ^ (1 - p) * ∫ ω, ‖X ω‖ ^ p ∂P := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h := iid_sum_power_bound hX hp hp2 hi hpi hzero n
  have he (ξ : Fin n → Ω) : ‖(n : ℝ)⁻¹ • ∑ i, X (ξ i)‖ ^ p =
      (n : ℝ) ^ (-p) * ‖∑ i, X (ξ i)‖ ^ p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnr.le),
      Real.mul_rpow (inv_nonneg.mpr hnr.le) (norm_nonneg _), Real.inv_rpow hnr.le,
      ← Real.rpow_neg hnr.le]
  simp_rw [he]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ (n : ℝ) ^ (-p) * (4 * n * ∫ ω, ‖X ω‖ ^ p ∂P) :=
      mul_le_mul_of_nonneg_left h.2 (Real.rpow_nonneg hnr.le _)
    _ = _ := by
      rw [show 1 - p = -p + 1 by ring, Real.rpow_add hnr, Real.rpow_one]
      ring

lemma iid_centered_mean_power_bound [CompleteSpace E] {X : Ω → E} (hX : Measurable X)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hi : Integrable X P) (u : E)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P) (hmean : ∫ ω, X ω ∂P = u)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → Ω => ‖(n : ℝ)⁻¹ • ∑ i, X (ξ i) - u‖ ^ p)
      (Measure.pi fun _ => P) ∧
    (∫ ξ : Fin n → Ω, ‖(n : ℝ)⁻¹ • ∑ i, X (ξ i) - u‖ ^ p
      ∂Measure.pi (fun _ => P)) ≤ 4 * (n : ℝ) ^ (1 - p) * ∫ ω, ‖X ω - u‖ ^ p ∂P := by
  have hz : (∫ ω, X ω - u ∂P) = 0 := by
    rw [integral_sub hi (integrable_const u), hmean]
    simp
  have h := iid_mean_power_bound (hX.sub measurable_const) hp hp2
    (hi.sub (integrable_const u)) hpi hz n hn
  simpa only [Pi.sub_apply, ← one_div, ← OracleTemplate.RobustGradient.finite_mean_centered u n hn] using h

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma lower_power_from_second {X : Ω → E} (hX : Measurable X) {q : ℝ}
    (hq : 0 ≤ q) (hq2 : q ≤ 2) (hi : Integrable (fun ω => ‖X ω‖ ^ 2) P) :
    Integrable (fun ω => ‖X ω‖ ^ q) P ∧
    (∫ ω, ‖X ω‖ ^ q ∂P) ≤ (∫ ω, ‖X ω‖ ^ 2 ∂P) ^ (q/2) := by
  have hb (ω : Ω) : ‖X ω‖ ^ q ≤ 1 + ‖X ω‖ ^ 2 := by
    by_cases h : ‖X ω‖ ≤ 1
    · have hle := Real.rpow_le_rpow (norm_nonneg _) h hq
      simp only [Real.one_rpow] at hle
      nlinarith [sq_nonneg ‖X ω‖]
    · have hle := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hq2
      rw [Real.rpow_two] at hle
      linarith
  have hqi : Integrable (fun ω => ‖X ω‖ ^ q) P := by
    apply ((integrable_const 1).add hi).mono' (hX.norm.pow_const q).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hb ω)
  have he (ω : Ω) : (‖X ω‖ ^ 2 : ℝ) ^ (q/2) = ‖X ω‖ ^ q := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _)]
    congr 1
    ring
  have hqi' : Integrable (fun ω => (‖X ω‖ ^ 2 : ℝ) ^ (q/2)) P := by
    simpa only [he] using hqi
  refine ⟨hqi, ?_⟩
  have h := (Real.concaveOn_rpow (by positivity : 0 ≤ q/2) (by linarith : q/2 ≤ 1)).le_map_integral
    (Real.continuous_rpow_const (by positivity : 0 ≤ q/2)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun ω => sq_nonneg ‖X ω‖)) hi hqi'
  simpa only [he] using h

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
lemma first_power_from_moment {X : Ω → E} {p r : ℝ} (hp : 1 ≤ p) (hr : 0 ≤ r)
    (hi : Integrable (fun ω => ‖X ω‖) P)
    (hpi : Integrable (fun ω => ‖X ω‖ ^ p) P)
    (hm : (∫ ω, ‖X ω‖ ^ p ∂P) ≤ r ^ p) :
    (∫ ω, ‖X ω‖ ∂P) ≤ r := by
  have h := (convexOn_rpow hp).map_integral_le
    (Real.continuous_rpow_const (by linarith : 0 ≤ p)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun ω => norm_nonneg (X ω))) hi hpi
  exact (Real.rpow_le_rpow_iff (integral_nonneg (fun ω => norm_nonneg _)) hr
    (by linarith : 0 < p)).mp (h.trans hm)

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma second_moment_translate {X : Ω → E} (hX : Measurable X) (u : E)
    (hi : Integrable (fun ω => ‖X ω-u‖ ^ 2) P) :
    Integrable (fun ω => ‖X ω‖ ^ 2) P ∧
    (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ 2 * (∫ ω, ‖X ω-u‖ ^ 2 ∂P) + 2 * ‖u‖ ^ 2 := by
  have hb (ω : Ω) : ‖X ω‖ ^ 2 ≤ 2 * ‖X ω-u‖ ^ 2 + 2 * ‖u‖ ^ 2 := by
    have ht := norm_add_le (X ω-u) u
    rw [sub_add_cancel] at ht
    have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
    nlinarith [sq_nonneg (‖X ω-u‖-‖u‖)]
  have hbi : Integrable (fun ω => 2 * ‖X ω-u‖ ^ 2 + 2 * ‖u‖ ^ 2) P :=
    (hi.const_mul 2).add (integrable_const _)
  have hXi : Integrable (fun ω => ‖X ω‖ ^ 2) P := by
    apply hbi.mono' (hX.norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb ω)
  refine ⟨hXi, (integral_mono hXi hbi hb).trans_eq ?_⟩
  rw [integral_add (hi.const_mul 2) (integrable_const _), integral_const_mul]
  simp

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma small_power_bound_from_second {X : Ω → E} (hX : Measurable X) {q r : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 ≤ r)
    (hi : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    (hm : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ 4*r^2) :
    Integrable (fun ω => ‖X ω‖ ^ q) P ∧
    (∫ ω, ‖X ω‖ ^ q ∂P) ≤ 2*r^q := by
  have h := lower_power_from_second hX hq (by linarith) hi
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    _ ≤ (4*r^2)^(q/2) := Real.rpow_le_rpow
      (integral_nonneg (fun ω => sq_nonneg _)) hm (by positivity)
    _ = (2*r)^q := by
      rw [show 4*r^2 = (2*r)^2 by ring, ← Real.rpow_natCast_mul (by positivity : 0 ≤ 2*r)]
      congr 1
      ring
    _ = (2 : ℝ)^q * r^q := Real.mul_rpow (by norm_num) hr
    _ ≤ 2*r^q := mul_le_mul_of_nonneg_right
      (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hq1)
      (Real.rpow_nonneg hr _)

end LongTails.Proofs.HilbertSmallMoments

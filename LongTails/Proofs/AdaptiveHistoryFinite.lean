import LongTails.Proofs.AdaptiveHistoryExpectation
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open MeasureTheory
open LongTails.Proofs.AdaptiveHistoryField
open LongTails.Proofs.AdaptiveHistoryExpectation

namespace LongTails.Proofs.AdaptiveHistoryFinite

lemma weightedRoot_le {ι : Type*} [Fintype ι] (b x : ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    Real.sqrt (∑ i, b i * (x i) ^ 2) ≤ ∑ i, Real.sqrt (b i) * |x i| := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun i _ => by positivity), ?_⟩
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => Real.sqrt (b i) * |x i|) (fun i _ => by positivity)
  simpa only [mul_pow, Real.sq_sqrt (hb _), sq_abs] using hs

lemma weightedRoot_moment {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} (b : ι → ℝ) (X : ι → Ω → ℝ) (ν : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hX : ∀ i, Measurable (X i))
    (hi : ∀ i, Integrable (X i) P) (hν : ∀ i, (∫ ω, |X i ω| ∂P) ≤ ν i) :
    Integrable (fun ω => Real.sqrt (∑ i, b i * (X i ω) ^ 2)) P ∧
      (∫ ω, Real.sqrt (∑ i, b i * (X i ω) ^ 2) ∂P) ≤ ∑ i, Real.sqrt (b i) * ν i := by
  have hterm (i : ι) : Integrable (fun ω => Real.sqrt (b i) * |X i ω|) P :=
    (hi i).abs.const_mul _
  have hV := integrable_finsetSum Finset.univ (fun i _ => hterm i)
  have hroot : Integrable (fun ω => Real.sqrt (∑ i, b i * (X i ω) ^ 2)) P := by
    apply hV.mono' ((show Measurable (fun ω => Real.sqrt (∑ i, b i * (X i ω) ^ 2)) by
      fun_prop).aestronglyMeasurable)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact weightedRoot_le b (fun i => X i ω) hb
  refine ⟨hroot, (integral_mono hroot hV (fun ω => weightedRoot_le b (fun i => X i ω) hb)).trans ?_⟩
  rw [integral_finsetSum _ (fun i _ => hterm i)]
  apply Finset.sum_le_sum
  intro i _
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hν i) (Real.sqrt_nonneg _)

lemma weightedRoot_product_moment {ι : Type*} [Fintype ι]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (b : ι → ℝ) (g σ : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hm : Integrable (fun x : ℝ => x) μ)
    (hσ : (∫ x, |x| ∂μ) ≤ σ) :
    Integrable (fun z : ι → ℝ => Real.sqrt (∑ i, b i * (g + z i) ^ 2))
        (Measure.pi fun _ : ι => μ) ∧
      (∫ z : ι → ℝ, Real.sqrt (∑ i, b i * (g + z i) ^ 2) ∂Measure.pi (fun _ : ι => μ)) ≤
        (∑ i, Real.sqrt (b i)) * (|g| + σ) := by
  have hi (i : ι) : Integrable (fun z : ι → ℝ => z i) (Measure.pi fun _ : ι => μ) :=
    integrable_comp_eval (μ := fun _ : ι => μ) (i := i) hm
  have hshift (i : ι) : Integrable (fun z : ι → ℝ => g + z i) (Measure.pi fun _ : ι => μ) :=
    (integrable_const g).add (hi i)
  have hν (i : ι) : (∫ z : ι → ℝ, |g + z i| ∂Measure.pi (fun _ : ι => μ)) ≤ |g| + σ := by
    have hbound := integral_mono (hshift i).abs ((integrable_const |g|).add (hi i).abs)
      (fun z : ι → ℝ => abs_add_le g (z i))
    have he := integral_comp_eval (μ := fun _ : ι => μ) (i := i) hm.abs.aestronglyMeasurable
    erw [integral_add (integrable_const |g|) (hi i).abs, he] at hbound
    simp only [integral_const, probReal_univ, one_smul] at hbound
    linarith
  have h := weightedRoot_moment b (fun i (z : ι → ℝ) => g + z i) (fun _ => |g| + σ)
    hb (fun i => by fun_prop) hshift hν
  simpa only [Finset.sum_mul] using h

noncomputable def historyTerm {ι : Type*} [Fintype ι]
    (δ : ℝ) (b : ι → ℝ) (g : ℝ) (i : ι) (z : ι → ℝ) : ℝ :=
  (g + z i) / (δ + Real.sqrt (∑ j, b j * (g + z j) ^ 2))

lemma historyTerm_split {n : ℕ} (δ : ℝ) (b : Fin (n + 1) → ℝ) (g : ℝ)
    (i : Fin (n + 1)) (z : Fin (n + 1) → ℝ) :
    historyTerm δ b g i z = scalarField δ (b i)
      (∑ j : Fin n, b (i.succAbove j) * (g + z (i.succAbove j)) ^ 2) (g + z i) := by
  unfold historyTerm scalarField
  rw [Fin.sum_univ_succAbove (fun j => b j * (g + z j) ^ 2) i]

lemma integral_historyTerm_signed_nonneg {n : ℕ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {δ g : ℝ} (b : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (hδ : 0 < δ) (hb : ∀ j, 0 ≤ b j)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hm : Integrable (fun x : ℝ => x) μ) :
    0 ≤ g * (∫ z, historyTerm δ b g i z ∂Measure.pi (fun _ : Fin (n + 1) => μ)) := by
  let S := fun z : Fin n → ℝ => ∑ j, b (i.succAbove j) * (g + z j) ^ 2
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).trans
    MeasurableEquiv.prodComm
  have hp := Measure.measurePreserving_swap.comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i)
  have hi := hp.integral_comp e.measurableEmbedding
    (fun w : (Fin n → ℝ) × ℝ => scalarField δ (b i) (S w.1) (g + w.2))
  have heq : (∫ z, historyTerm δ b g i z ∂Measure.pi (fun _ : Fin (n + 1) => μ)) =
      ∫ w : (Fin n → ℝ) × ℝ, scalarField δ (b i) (S w.1) (g + w.2)
        ∂(Measure.pi (fun _ : Fin n => μ)).prod μ := by
    rw [← hi]
    apply integral_congr_ae
    filter_upwards [] with z
    exact historyTerm_split δ b g i z
  rw [heq]
  apply integral_shifted_scalarField_random_residual_signed_nonneg hδ (hb i)
    (show Measurable S by dsimp [S]; fun_prop) _ hsym hm
  filter_upwards [] with z
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hb _) (sq_nonneg _))

def splitTwo (n : ℕ) : (Fin (n + 2) → ℝ) ≃ᵐ (Fin n → ℝ) × (ℝ × ℝ) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0))).trans
    (MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm)

lemma splitTwo_apply {n : ℕ} (z : Fin (n + 2) → ℝ) :
    splitTwo n z = (fun j : Fin n => z j.succ.succ, (z 0, z 1)) := by
  simp [splitTwo, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  rfl

lemma measurePreserving_splitTwo (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving (splitTwo n) (Measure.pi fun _ : Fin (n + 2) => μ)
      ((Measure.pi fun _ : Fin n => μ).prod (μ.prod μ)) := by
  have h0 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 2) => μ) 0
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
  have h2 := ((MeasurePreserving.id μ).prod h1).comp h0
  have h3 := (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ μ (Measure.pi fun _ : Fin n => μ))).comp h2
  exact Measure.measurePreserving_swap.comp h3

lemma historyTerm_zero_split {n : ℕ} (δ g β : ℝ) (b : Fin (n + 2) → ℝ)
    (hb1 : b 1 = β * b 0) (z : Fin (n + 2) → ℝ) :
    historyTerm δ b g 0 z = scalarField δ (b 0)
      ((∑ j : Fin n, b j.succ.succ * (g + z j.succ.succ) ^ 2) +
        β * b 0 * (g + z 1) ^ 2) (g + z 0) := by
  have hs : (∑ j, b j * (g + z j) ^ 2) = b 0 * (g + z 0) ^ 2 +
      ((∑ j : Fin n, b j.succ.succ * (g + z j.succ.succ) ^ 2) + β * b 0 * (g + z 1) ^ 2) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    change b 0 * (g + z 0) ^ 2 + (b 1 * (g + z 1) ^ 2 + _) = _
    rw [hb1]
    ring
  unfold historyTerm scalarField
  rw [hs]

lemma integral_historyTerm_zero_coercive {n : ℕ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {δ β g σ : ℝ} (b : Fin (n + 2) → ℝ)
    (hδ : 0 < δ) (hb : ∀ j, 0 ≤ b j) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hb1 : b 1 = β * b 0)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hm : Integrable (fun x : ℝ => x) μ)
    (hσ : (∫ x, |x| ∂μ) ≤ σ) :
    β * g ^ 2 /
      (8 * (δ + ((∑ j : Fin n, Real.sqrt (b j.succ.succ)) + 2 * Real.sqrt (b 0)) * (|g| + σ))) ≤
      g * (∫ z, historyTerm δ b g 0 z ∂Measure.pi (fun _ : Fin (n + 2) => μ)) := by
  let S := fun z : Fin n → ℝ => ∑ j, b j.succ.succ * (g + z j) ^ 2
  have hroot := weightedRoot_product_moment (fun j : Fin n => b j.succ.succ) g σ
    (fun j => hb _) hm hσ
  have hS : Measurable S := by dsimp [S]; fun_prop
  have hS0 : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), 0 ≤ S z := by
    filter_upwards [] with z
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hb _) (sq_nonneg _))
  have h := integral_current_field_random_residual_coercive (g := g) hδ (hb 0) hβ hβ1 hS hS0
    hroot.1 hroot.2 hsym hm hσ
  have hi := (measurePreserving_splitTwo n μ).integral_comp (splitTwo n).measurableEmbedding
    (fun w : (Fin n → ℝ) × (ℝ × ℝ) => scalarField δ (b 0)
      (S w.1 + β * b 0 * (g + w.2.2) ^ 2) (g + w.2.1))
  have heq : (∫ z, historyTerm δ b g 0 z ∂Measure.pi (fun _ : Fin (n + 2) => μ)) =
      ∫ w : (Fin n → ℝ) × (ℝ × ℝ), scalarField δ (b 0)
        (S w.1 + β * b 0 * (g + w.2.2) ^ 2) (g + w.2.1)
        ∂(Measure.pi (fun _ : Fin n => μ)).prod (μ.prod μ) := by
    rw [← hi]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [splitTwo_apply]
    exact historyTerm_zero_split δ g β b hb1 z
  rw [heq]
  convert h using 1
  all_goals ring

lemma integrable_historyTerm {ι : Type*} [Fintype ι]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {δ g : ℝ} (b : ι → ℝ) (i : ι)
    (hδ : 0 < δ) (hm : Integrable (fun x : ℝ => x) μ) :
    Integrable (historyTerm δ b g i) (Measure.pi fun _ : ι => μ) := by
  have hi : Integrable (fun z : ι → ℝ => g + z i) (Measure.pi fun _ : ι => μ) :=
    (integrable_const g).add (integrable_comp_eval (μ := fun _ : ι => μ) (i := i) hm)
  apply (hi.abs.div_const δ).mono'
    ((show Measurable (historyTerm δ b g i) by unfold historyTerm; fun_prop).aestronglyMeasurable)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, historyTerm, abs_div,
    abs_of_pos (show 0 < δ + Real.sqrt (∑ j, b j * (g + z j) ^ 2) by positivity)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hδ
    (le_add_of_nonneg_right (Real.sqrt_nonneg _))

noncomputable def historyField {ι : Type*} [Fintype ι]
    (δ : ℝ) (a b : ι → ℝ) (g : ℝ) (z : ι → ℝ) : ℝ :=
  (∑ i, a i * (g + z i)) / (δ + Real.sqrt (∑ i, b i * (g + z i) ^ 2))

lemma historyField_eq_sum {ι : Type*} [Fintype ι]
    (δ : ℝ) (a b : ι → ℝ) (g : ℝ) (z : ι → ℝ) :
    historyField δ a b g z = ∑ i, a i * historyTerm δ b g i z := by
  simp only [historyField, historyTerm, Finset.sum_div, mul_div_assoc]

lemma integral_historyField_eq_sum {ι : Type*} [Fintype ι]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {δ g : ℝ} (a b : ι → ℝ)
    (hδ : 0 < δ) (hm : Integrable (fun x : ℝ => x) μ) :
    g * (∫ z, historyField δ a b g z ∂Measure.pi (fun _ : ι => μ)) =
      ∑ i, a i * (g * (∫ z, historyTerm δ b g i z ∂Measure.pi (fun _ : ι => μ))) := by
  have hi (i : ι) := (integrable_historyTerm (g := g) b i hδ hm).const_mul (a i)
  simp_rw [historyField_eq_sum]
  rw [integral_finsetSum _ (fun i _ => hi i), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  ring

lemma integral_historyField_coercive {n : ℕ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {δ β g σ : ℝ} (a b : Fin (n + 2) → ℝ)
    (hδ : 0 < δ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hb1 : b 1 = β * b 0)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hm : Integrable (fun x : ℝ => x) μ)
    (hσ : (∫ x, |x| ∂μ) ≤ σ) :
    a 0 * β * g ^ 2 /
      (8 * (δ + ((∑ j : Fin n, Real.sqrt (b j.succ.succ)) + 2 * Real.sqrt (b 0)) * (|g| + σ))) ≤
      g * (∫ z, historyField δ a b g z ∂Measure.pi (fun _ : Fin (n + 2) => μ)) := by
  have h := mul_le_mul_of_nonneg_left
    (integral_historyTerm_zero_coercive (g := g) b hδ hb hβ hβ1 hb1 hsym hm hσ) (ha 0)
  have hs : a 0 * (g * (∫ z, historyTerm δ b g 0 z ∂Measure.pi (fun _ : Fin (n + 2) => μ))) ≤
      ∑ i, a i * (g * (∫ z, historyTerm δ b g i z ∂Measure.pi (fun _ : Fin (n + 2) => μ))) := by
    apply Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin (n + 2) => a i * (g *
        (∫ z, historyTerm δ b g i z ∂Measure.pi (fun _ : Fin (n + 2) => μ))))
    · intro i _
      exact mul_nonneg (ha i) (integral_historyTerm_signed_nonneg b i hδ hb hsym hm)
    · exact Finset.mem_univ 0
  rw [integral_historyField_eq_sum a b hδ hm]
  convert h.trans hs using 1
  all_goals ring


lemma finite_geometric_le (n : ℕ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (∑ i : Fin n, q ^ (i : ℕ)) ≤ 1 / (1 - q) := by
  have hd : 0 < 1 - q := by linarith
  induction n with
  | zero => simpa using (one_div_pos.mpr hd).le
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ]
    rw [← Finset.sum_mul]
    calc
      1 + (∑ i : Fin n, q ^ (i : ℕ)) * q ≤ 1 + (1 / (1 - q)) * q := by gcongr
      _ = 1 / (1 - q) := by field_simp; ring

lemma sqrt_nat_pow {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    Real.sqrt (q ^ n) = (Real.sqrt q) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hq n), ih, pow_succ]

lemma geometric_root_sum_le (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) :
    (∑ i : Fin n, Real.sqrt ((1 - β) * β ^ (i : ℕ))) ≤
      Real.sqrt (1 - β) / (1 - Real.sqrt β) := by
  have hβsub : 0 ≤ 1 - β := by linarith
  have hq : Real.sqrt β < 1 := by
    have hs := Real.sq_sqrt hβ
    nlinarith [Real.sqrt_nonneg β]
  simp_rw [Real.sqrt_mul hβsub, sqrt_nat_pow hβ]
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (finite_geometric_le n (Real.sqrt_nonneg β) hq)
    (Real.sqrt_nonneg (1 - β))
  simpa only [mul_one_div] using h

lemma default_geometric_root_constant :
    Real.sqrt (1 - (999 / 1000 : ℝ)) / (1 - Real.sqrt (999 / 1000 : ℝ)) ≤ 64 := by
  have hs := Real.sq_sqrt (show 0 ≤ (999 / 1000 : ℝ) by norm_num)
  have ht := Real.sq_sqrt (show 0 ≤ 1 - (999 / 1000 : ℝ) by norm_num)
  have hq : Real.sqrt (999 / 1000 : ℝ) ≤ 1999 / 2000 := by
    nlinarith [Real.sqrt_nonneg (999 / 1000 : ℝ)]
  have hr : Real.sqrt (1 - (999 / 1000 : ℝ)) ≤ 4 / 125 := by
    nlinarith [Real.sqrt_nonneg (1 - (999 / 1000 : ℝ))]
  apply (div_le_iff₀ (show 0 < 1 - Real.sqrt (999 / 1000 : ℝ) by linarith)).mpr
  linarith

lemma integral_geometric_history_coercive {n : ℕ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {δ α β g σ : ℝ}
    (hδ : 0 < δ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hm : Integrable (fun x : ℝ => x) μ)
    (hσ : (∫ x, |x| ∂μ) ≤ σ) :
    (1 - α) * β * g ^ 2 /
      (8 * (δ + (Real.sqrt (1 - β) / (1 - Real.sqrt β) + 2 * Real.sqrt (1 - β)) * (|g| + σ))) ≤
      g * (∫ z, historyField δ
        (fun i : Fin (n + 2) => (1 - α) * α ^ (i : ℕ))
        (fun i : Fin (n + 2) => (1 - β) * β ^ (i : ℕ)) g z
        ∂Measure.pi (fun _ : Fin (n + 2) => μ)) := by
  let a := fun i : Fin (n + 2) => (1 - α) * α ^ (i : ℕ)
  let b := fun i : Fin (n + 2) => (1 - β) * β ^ (i : ℕ)
  let B := ∑ j : Fin n, Real.sqrt (b j.succ.succ)
  let C := Real.sqrt (1 - β) / (1 - Real.sqrt β)
  have ha (i : Fin (n + 2)) : 0 ≤ a i := by dsimp [a]; positivity
  have hb (i : Fin (n + 2)) : 0 ≤ b i := by dsimp [b]; positivity
  have hb1 : b 1 = β * b 0 := by dsimp [b]; norm_num; ring
  have hfield := integral_historyField_coercive (g := g) a b hδ ha hb hβ hβ1.le hb1 hsym hm hσ
  have hB : B ≤ C := by
    have hfull := geometric_root_sum_le (n + 2) hβ hβ1
    change (∑ i : Fin (n + 2), Real.sqrt (b i)) ≤ C at hfull
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hfull
    change Real.sqrt (b 0) + (Real.sqrt (b 1) + B) ≤ C at hfull
    linarith [Real.sqrt_nonneg (b 0), Real.sqrt_nonneg (b 1)]
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
  have hσ0 : 0 ≤ σ := (integral_nonneg fun x : ℝ => abs_nonneg x).trans hσ
  have hfrac : a 0 * β * g ^ 2 / (8 * (δ + (C + 2 * Real.sqrt (b 0)) * (|g| + σ))) ≤
      a 0 * β * g ^ 2 / (8 * (δ + (B + 2 * Real.sqrt (b 0)) * (|g| + σ))) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hB (show 0 ≤ |g| + σ by positivity)]
  have hresult := hfrac.trans hfield
  simpa [a, b, C] using hresult


lemma integral_default_history_coercive {n : ℕ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {δ g σ : ℝ}
    (hδ : 0 < δ) (hsym : μ.map (fun x : ℝ => -x) = μ)
    (hm : Integrable (fun x : ℝ => x) μ) (hσ : (∫ x, |x| ∂μ) ≤ σ) :
    g^2/(90*(δ+66*(|g|+σ))) ≤
      g*(∫ z,historyField δ
        (fun i : Fin (n+2) => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ))
        (fun i : Fin (n+2) => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)) g z
        ∂Measure.pi (fun _ : Fin (n+2) => μ)) := by
  have hσ0 : 0 ≤ σ := (integral_nonneg fun x : ℝ => abs_nonneg x).trans hσ
  have hh := integral_geometric_history_coercive (n := n) (g := g) (α := (9/10 : ℝ)) (β := (999/1000 : ℝ))
    hδ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hsym hm hσ
  apply le_trans _ hh
  let C := Real.sqrt (1-(999/1000 : ℝ))/(1-Real.sqrt (999/1000 : ℝ)) +
    2*Real.sqrt (1-(999/1000 : ℝ))
  have hq : Real.sqrt (999/1000 : ℝ) < 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 999/1000 by norm_num), Real.sqrt_nonneg (999/1000 : ℝ)]
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hC : C ≤ 66 := by
    have hs : Real.sqrt (1-(999/1000 : ℝ)) ≤ 1 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    dsimp [C]
    linarith [default_geometric_root_constant]
  change g^2/(90*(δ+66*(|g|+σ))) ≤ (1-(9/10 : ℝ))*(999/1000 : ℝ)*g^2/(8*(δ+C*(|g|+σ)))
  calc
    _ = ((1/90 : ℝ)*g^2)/(δ+66*(|g|+σ)) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ ((((1-(9/10 : ℝ))*(999/1000 : ℝ))/8)*g^2)/(δ+66*(|g|+σ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      norm_num
    _ = (1-(9/10 : ℝ))*(999/1000 : ℝ)*g^2/(8*(δ+66*(|g|+σ))) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have ht := mul_le_mul_of_nonneg_right hC (show 0 ≤ |g|+σ by positivity)
      linarith



lemma sum_weightedRoot_moment {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace Ω]
    {P : Measure Ω} (b : ι → ℝ) (X : κ → ι → Ω → ℝ) (ν : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hX : ∀ j i, Measurable (X j i))
    (hi : ∀ j i, Integrable (X j i) P)
    (hν : ∀ i, (∫ ω,∑ j, |X j i ω| ∂P) ≤ ν i) :
    Integrable (fun ω => ∑ j,Real.sqrt (∑ i,b i*(X j i ω)^2)) P ∧
      (∫ ω,∑ j,Real.sqrt (∑ i,b i*(X j i ω)^2) ∂P) ≤ ∑ i,Real.sqrt (b i)*ν i := by
  have hsum (i : ι) : Integrable (fun ω => ∑ j,|X j i ω|) P :=
    integrable_finsetSum _ (fun j _ => (hi j i).abs)
  have hdom : Integrable (fun ω => ∑ i,Real.sqrt (b i)*(∑ j,|X j i ω|)) P :=
    integrable_finsetSum _ (fun i _ => (hsum i).const_mul _)
  have hp (ω) : (∑ j,Real.sqrt (∑ i,b i*(X j i ω)^2)) ≤ ∑ i,Real.sqrt (b i)*(∑ j,|X j i ω|) := by
    calc
      _ ≤ ∑ j,∑ i,Real.sqrt (b i)*|X j i ω| :=
        Finset.sum_le_sum (fun j _ => weightedRoot_le b (fun i => X j i ω) hb)
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
  have hroot : Integrable (fun ω => ∑ j,Real.sqrt (∑ i,b i*(X j i ω)^2)) P := by
    apply hdom.mono' (by fun_prop)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))]
    exact hp ω
  refine ⟨hroot,(integral_mono hroot hdom hp).trans ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hsum i).const_mul _)]
  apply Finset.sum_le_sum
  intro i _
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hν i) (Real.sqrt_nonneg _)


end LongTails.Proofs.AdaptiveHistoryFinite

import LongTails.Proofs.CenteredDyadicDescent
import LongTails.Proofs.MedianCoupling
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.MedianOracleMoments

open LongTails.Proofs.MedianCoupling OracleTemplate.MedianGradient

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
  {p : Measure Ω} [IsProbabilityMeasure p]

local notation "Q" => Measure.pi fun _ : Fin 3 => p

lemma lifted_integrable {a : Ω → EuclideanSpace ℝ (Fin d)} (hai : Integrable a p)
    (j : Fin 3) : Integrable (fun ξ : Fin 3 → Ω => a (ξ j)) Q :=
  (measurePreserving_eval (fun _ : Fin 3 => p) j).integrable_comp_of_integrable hai

lemma lifted_integral_norm {a : Ω → EuclideanSpace ℝ (Fin d)} (ha : Measurable a)
    (j : Fin 3) :
    ∫ ξ : Fin 3 → Ω, ‖a (ξ j)‖ ∂Q = ∫ ω, ‖a ω‖ ∂p := by
  have hp := measurePreserving_eval (fun _ : Fin 3 => p) j
  have h := integral_map (μ := Q) hp.measurable.aemeasurable ha.norm.aestronglyMeasurable
  rw [hp.map_eq] at h
  exact h.symm

lemma median_variance {a : Ω → EuclideanSpace ℝ (Fin d)} (ha : Measurable a)
    (hai : Integrable a p) {σ : ℝ} (hσ : 0 ≤ σ) (hb : ∫ ω, ‖a ω‖ ∂p ≤ σ) :
    Integrable (fun ξ : Fin 3 → Ω => ‖median (a (ξ 0)) (a (ξ 1)) (a (ξ 2))‖ ^ 2) Q ∧
      ∫ ξ : Fin 3 → Ω, ‖median (a (ξ 0)) (a (ξ 1)) (a (ξ 2))‖ ^ 2 ∂Q ≤ 3 * σ ^ 2 := by
  have hm (j : Fin 3) : Measurable (fun ξ : Fin 3 → Ω => a (ξ j)) :=
    ha.comp (measurable_pi_apply j)
  have hi := iIndepFun_pi (μ := fun _ : Fin 3 => p) (fun _ : Fin 3 => ha.aemeasurable)
  obtain ⟨hI, hV⟩ := median_second_moment (hm 0) (hm 1) (hm 2)
    (lifted_integrable hai 0) (lifted_integrable hai 1) (lifted_integrable hai 2)
    (hi.indepFun (by decide : (0 : Fin 3) ≠ 1))
    (hi.indepFun (by decide : (1 : Fin 3) ≠ 2))
    (hi.indepFun (by decide : (2 : Fin 3) ≠ 0))
  refine ⟨hI, hV.trans ?_⟩
  simp_rw [lifted_integral_norm ha]
  have hnn : 0 ≤ ∫ ω, ‖a ω‖ ∂p := integral_nonneg fun _ => norm_nonneg _
  nlinarith [sq_nonneg (σ - ∫ ω, ‖a ω‖ ∂p)]

lemma lifted_identDistrib {a : Ω → ℝ} (ha : Measurable a) (j : Fin 3) :
    IdentDistrib (fun ξ : Fin 3 → Ω => a (ξ j)) a Q p := by
  refine ⟨(ha.comp (measurable_pi_apply j)).aemeasurable, ha.aemeasurable, ?_⟩
  change (Q).map (a ∘ Function.eval j) = p.map a
  rw [← Measure.map_map ha (measurable_pi_apply j),
    (measurePreserving_eval (fun _ : Fin 3 => p) j).map_eq]

lemma median_mean_zero {a : Ω → EuclideanSpace ℝ (Fin d)} (ha : Measurable a)
    (hai : Integrable a p)
    (hs : ∀ i, IdentDistrib (fun ω => a ω i) (fun ω => -a ω i) p p) :
    ∫ ξ : Fin 3 → Ω, median (a (ξ 0)) (a (ξ 1)) (a (ξ 2)) ∂Q = 0 := by
  apply median_integral_zero (fun j (ξ : Fin 3 → Ω) => a (ξ j))
    (fun j => ha.comp (measurable_pi_apply j)) (lifted_integrable hai)
    (iIndepFun_pi (μ := fun _ : Fin 3 => p) (fun _ : Fin 3 => ha.aemeasurable))
  intro j i
  have hm : Measurable fun ω => a ω i :=
    (EuclideanSpace.proj i).continuous.measurable.comp ha
  exact (lifted_identDistrib hm j).trans ((hs i).trans (lifted_identDistrib hm.neg j).symm)

lemma integral_norm_difference_le {T : Type*} [MeasurableSpace T] {P : Measure T}
    {a b : T → EuclideanSpace ℝ (Fin d)} (hai : Integrable a P) (hbi : Integrable b P) :
    ∫ ω, ‖a ω - b ω‖ ∂P ≤ (∫ ω, ‖a ω‖ ∂P) + ∫ ω, ‖b ω‖ ∂P := by
  have h := integral_mono (hai.sub hbi).norm (hai.norm.add hbi.norm)
    (fun ω => norm_sub_le (a ω) (b ω))
  simpa only [Pi.sub_apply, Pi.add_apply, integral_add hai.norm hbi.norm] using h

lemma median_increment {a b : Ω → EuclideanSpace ℝ (Fin d)}
    (ha : Measurable a) (hb : Measurable b) (hai : Integrable a p) (hbi : Integrable b p)
    {σ r : ℝ} (hr : 0 ≤ r)
    (haσ : ∫ ω, ‖a ω‖ ∂p ≤ σ) (hbσ : ∫ ω, ‖b ω‖ ∂p ≤ σ)
    (hab : ∫ ω, ‖a ω - b ω‖ ∂p ≤ r) :
    Integrable (fun ξ : Fin 3 → Ω => ‖median (a (ξ 0)) (a (ξ 1)) (a (ξ 2)) -
      median (b (ξ 0)) (b (ξ 1)) (b (ξ 2))‖ ^ 2) Q ∧
      ∫ ξ : Fin 3 → Ω, ‖median (a (ξ 0)) (a (ξ 1)) (a (ξ 2)) -
        median (b (ξ 0)) (b (ξ 1)) (b (ξ 2))‖ ^ 2 ∂Q ≤ 18 * σ * r := by
  let E := EuclideanSpace ℝ (Fin d)
  let v : Fin 3 → (Fin 3 → Ω) → E × E := fun j ξ => (a (ξ j), b (ξ j))
  have hm (j : Fin 3) : Measurable (v j) := (ha.prodMk hb).comp (measurable_pi_apply j)
  have hi : iIndepFun v Q := iIndepFun_pi (μ := fun _ : Fin 3 => p)
    (fun _ : Fin 3 => (ha.prodMk hb).aemeasurable)
  have h₁ := (hi.indepFun_prodMk hm 1 2 0 (by decide) (by decide)).symm.comp
    (show Measurable (fun z : E × E => z.1 - z.2) from by fun_prop)
    (show Measurable (fun z : (E × E) × (E × E) => z.1.1 - z.2.1) from by fun_prop)
  have h₂ := (hi.indepFun_prodMk hm 0 2 1 (by decide) (by decide)).symm.comp
    (show Measurable (fun z : E × E => z.1 - z.2) from by fun_prop)
    (show Measurable (fun z : (E × E) × (E × E) => z.1.2 - z.2.1) from by fun_prop)
  have h₃ := (hi.indepFun_prodMk hm 0 1 2 (by decide) (by decide)).symm.comp
    (show Measurable (fun z : E × E => z.1 - z.2) from by fun_prop)
    (show Measurable (fun z : (E × E) × (E × E) => z.1.2 - z.2.2) from by fun_prop)
  obtain ⟨hI, hV⟩ := median_coupled_second_moment
    (ha.comp (measurable_pi_apply 0)) (ha.comp (measurable_pi_apply 1))
    (ha.comp (measurable_pi_apply 2)) (hb.comp (measurable_pi_apply 0))
    (hb.comp (measurable_pi_apply 1)) (hb.comp (measurable_pi_apply 2))
    (lifted_integrable hai 0) (lifted_integrable hai 1) (lifted_integrable hai 2)
    (lifted_integrable hbi 0) (lifted_integrable hbi 1) (lifted_integrable hbi 2) h₁ h₂ h₃
  have hd (j : Fin 3) : ∫ ξ : Fin 3 → Ω, ‖a (ξ j) - b (ξ j)‖ ∂Q ≤ r := by
    have he := lifted_integral_norm (p := p) (ha.sub hb) j
    simp only [Pi.sub_apply] at he
    exact he.trans_le hab
  have haa (i j : Fin 3) : ∫ ξ : Fin 3 → Ω, ‖a (ξ i) - a (ξ j)‖ ∂Q ≤ 2 * σ := by
    have h := integral_norm_difference_le (lifted_integrable hai i) (lifted_integrable hai j)
    rw [lifted_integral_norm ha i, lifted_integral_norm ha j] at h
    linarith
  have hba (i j : Fin 3) : ∫ ξ : Fin 3 → Ω, ‖b (ξ i) - a (ξ j)‖ ∂Q ≤ 2 * σ := by
    have h := integral_norm_difference_le (lifted_integrable hbi i) (lifted_integrable hai j)
    rw [lifted_integral_norm hb i, lifted_integral_norm ha j] at h
    linarith
  have hbb (i j : Fin 3) : ∫ ξ : Fin 3 → Ω, ‖b (ξ i) - b (ξ j)‖ ∂Q ≤ 2 * σ := by
    have h := integral_norm_difference_le (lifted_integrable hbi i) (lifted_integrable hbi j)
    rw [lifted_integral_norm hb i, lifted_integral_norm hb j] at h
    linarith
  have hp₁ := mul_le_mul (hd 0) (haa 1 2) (integral_nonneg fun _ => norm_nonneg _) hr
  have hp₂ := mul_le_mul (hd 1) (hba 0 2) (integral_nonneg fun _ => norm_nonneg _) hr
  have hp₃ := mul_le_mul (hd 2) (hbb 0 1) (integral_nonneg fun _ => norm_nonneg _) hr
  simp only [Function.comp_apply] at hI hV
  exact ⟨hI, by nlinarith only [hV, hp₁, hp₂, hp₃]⟩

end LongTails.Proofs.MedianOracleMoments

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.MedianOracleBridge

open LongTails.Proofs.MedianCoupling LongTails.Proofs.MedianOracleMoments
open OracleTemplate.MedianGradient

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
  {p : Measure Ω} [IsProbabilityMeasure p]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Q" => Measure.pi fun _ : Fin 3 => p

lemma regularized_hyp {F : E → ℝ} {g : E → Ω → E} {L Λ σ : ℝ}
    (hL : 0 < L) (hΛ : 0 ≤ Λ) (hσ : 0 ≤ σ)
    (hgrad : ∀ x, HasGradientAt F (gradient F x) x)
    (hlip : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    (hgm : Measurable (Function.uncurry g)) (hint : ∀ x, Integrable (g x) p)
    (hfirst : ∀ x, ∫ ω, ‖g x ω - gradient F x‖ ∂p ≤ σ)
    (hinc : ∀ x y, ∫ ω, ‖(g x ω - gradient F x) - (g y ω - gradient F y)‖ ∂p ≤ Λ * ‖x - y‖)
    (hsym : ∀ x (i : Fin d), p.map (fun ω => (g x ω - gradient F x) i) =
      p.map (fun ω => -(g x ω - gradient F x) i)) :
    OracleTemplate.CenteredDyadic.Hyp Q F (oracle g) L (18 * Λ * σ) (1 / 2) (2 * σ) := by
  let n : E → Ω → E := fun x ω => g x ω - gradient F x
  have hnm (x : E) : Measurable (n x) :=
    (hgm.comp (measurable_const.prodMk measurable_id)).sub_const _
  have hni (x : E) : Integrable (n x) p := (hint x).sub (integrable_const _)
  have hns (x : E) (i : Fin d) :
      IdentDistrib (fun ω => n x ω i) (fun ω => -n x ω i) p p := by
    have hm : Measurable fun ω => n x ω i :=
      (EuclideanSpace.proj i).continuous.measurable.comp (hnm x)
    exact ⟨hm.aemeasurable, hm.neg.aemeasurable, hsym x i⟩
  have hnv (x : E) := median_variance (hnm x) (hni x) hσ (hfirst x)
  have hnmi (x : E) : Integrable (fun ξ : Fin 3 → Ω =>
      median (n x (ξ 0)) (n x (ξ 1)) (n x (ξ 2))) Q := by
    have hm : Measurable (fun ξ : Fin 3 → Ω =>
        median (n x (ξ 0)) (n x (ξ 1)) (n x (ξ 2))) := measurable_median ((hnm x).comp (measurable_pi_apply 0))
      ((hnm x).comp (measurable_pi_apply 1)) ((hnm x).comp (measurable_pi_apply 2))
    exact ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr (hnv x).1).integrable
      one_le_two
  have htrans (x : E) (ξ : Fin 3 → Ω) : oracle g x ξ =
      median (n x (ξ 0)) (n x (ξ 1)) (n x (ξ 2)) + gradient F x := by
    rw [← median_translate]
    simp only [n, sub_add_cancel, oracle]
  have hdiff (x y : E) (ξ : Fin 3 → Ω) :
      (oracle g x ξ - oracle g y ξ) - (gradient F x - gradient F y) =
      median (n x (ξ 0)) (n x (ξ 1)) (n x (ξ 2)) -
        median (n y (ξ 0)) (n y (ξ 1)) (n y (ξ 2)) := by
    rw [htrans, htrans]
    abel
  have hnd (x y : E) := median_increment (hnm x) (hnm y) (hni x) (hni y)
    (mul_nonneg hΛ (norm_nonneg _)) (hfirst x) (hfirst y) (hinc x y)
  refine ⟨hgrad, hlip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hL, by positivity, by norm_num⟩
  · have hm (j : Fin 3) : Measurable (fun z : E × (Fin 3 → Ω) => g z.1 (z.2 j)) :=
      hgm.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
    exact measurable_median (hm 0) (hm 1) (hm 2)
  · intro x
    change Integrable (fun ξ => oracle g x ξ) Q
    simp_rw [htrans]
    exact (hnmi x).add (integrable_const _)
  · intro x
    simp_rw [htrans]
    rw [integral_add (hnmi x) (integrable_const _), median_mean_zero (hnm x) (hni x) (hns x)]
    simp
  · intro x
    simp_rw [htrans, add_sub_cancel_right]
    exact (hnv x).1
  · intro x
    simp_rw [htrans, add_sub_cancel_right]
    exact (hnv x).2.trans (by nlinarith [sq_nonneg σ])
  · intro x y
    simp_rw [hdiff]
    exact (hnd x y).1
  · intro x y
    simp_rw [hdiff]
    refine (hnd x y).2.trans_eq ?_
    norm_num
    ring

end LongTails.Proofs.MedianOracleBridge

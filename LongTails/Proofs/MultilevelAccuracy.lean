import LongTails.Proofs.MultilevelMartingale
import LongTails.Proofs.MultilevelExecution

namespace LongTails.Proofs.MultilevelAccuracy

open MeasureTheory ProbabilityTheory DistributedTemplate
open LongTails.Setups.DistributedMeanSquaredSmooth
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Algorithms.MultilevelPipeline
open LongTails.Algorithms.MultilevelWorkerSchedule
open LongTails.Algorithms.MultilevelTransport (Bits Selection reply ordinal)
open MultilevelPath MultilevelTrajectory MultilevelPacketMoments MultilevelStream MultilevelTransportState
open MultilevelDraws MultilevelMartingale MultilevelInformation MultilevelTimetable
open scoped MultilevelStream

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p}
    {μ : Fin p.n → ProbabilityMeasure p.Ω} {f : Point p → ℝ} {a : ℝ}

lemma bias_bound (H : Data p f g μ a) (hh : ∀ i, 0 < p.h i) (k : ℕ) (hk : k ≤ wanted p)
    (b : ℕ → Bits) :
    ‖estimate p b k - gradient f (iterate p b k) - noise p g μ k (table p).length b‖ ≤ 4*precision p := by
  let w := weight p k
  let M := fun r => meanValue p g μ ((script p).worker r) (payload (script p) b r)
  let G := fun r => target p b (entry p r).1 (gradient f)
  let I := Finset.range (table p).length
  let ξ := precision p / (height p+1 : ℕ)
  have hδ : 0 ≤ precision p := by unfold precision; linarith [H.accuracy]
  have ht : (∑ r ∈ I, w r • G r) = gradient f (gridPoint p b (anchor 1 k)) :=
    (weighted_jobs p hh hk (fun job => target p b job (gradient f))).trans (target_telescope _ _ _ _)
  have hb : ‖∑ r ∈ I, w r • (M r-G r)‖ ≤ 2*precision p := by
    refine (norm_sum_le _ _).trans ?_
    have he (r : ℕ) (hr : r ∈ I) : ‖w r • (M r-G r)‖ ≤ w r * (2*precision p / (height p+1 : ℕ)) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (weight_nonneg p k r)]
      exact mul_le_mul_of_nonneg_left (conditional_moments H hh r (Finset.mem_range.mp hr) b).2.1 (weight_nonneg p k r)
    refine (Finset.sum_le_sum he).trans ?_
    rw [← Finset.sum_mul, weight_sum p hh hk]
    have hm : ((path p k).card:ℝ) ≤ (height p+1:ℕ) := by exact_mod_cast path_size p k
    calc
      _ ≤ ((height p + 1 : ℕ):ℝ) * (2*precision p / (height p+1:ℕ)) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      _ = _ := by field_simp
  have hs := stale p f H.smooth H.accuracy H.lip b hk
  have heq : estimate p b k - gradient f (iterate p b k) - noise p g μ k (table p).length b =
      (∑ r ∈ I, w r • (M r-G r)) + (gradient f (gridPoint p b (anchor 1 k)) - gradient f (iterate p b k)) := by
    rw [← ht,average_representation p b hk]
    simp only [noise,smul_sub,Finset.sum_sub_distrib,I,w,M,G,readValue]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith)

lemma path_measurable {α E : Type*} [MeasurableSpace α] [MeasurableSpace E] (p : Params)
    (bits : α → ℕ → Bits) (hm : ∀ j, Measurable (fun z => bits z j)) (F : (ℕ → Bits) → E)
    (hs : ∀ x y, (∀ j < (table p).length, x j = y j) → F x = F y) :
    Measurable fun z => F (bits z) := by
  let P := fun z => priorBits (bits z) (table p).length
  have hp : Measurable P := Measurable.of_eval (fun j => hm j)
  convert (measurable_of_countable (fun a : Fin (table p).length → Bits => F (extend a))).comp hp using 1
  funext z
  exact (hs _ _ (extend_eq _ _)).symm

lemma estimate_measurable {α : Type*} [MeasurableSpace α] (hh : ∀ i, 0 < p.h i) (k : ℕ) (hk : k ≤ wanted p)
    (bits : α → ℕ → Bits) (hm : ∀ j, Measurable fun z => bits z j) :
    Measurable fun z => estimate p (bits z) k :=
  path_measurable p bits hm _ (fun x y h => estimate_agree p hh x y k hk (fun j hj _ => h j hj))

lemma iterate_measurable {α : Type*} [MeasurableSpace α] (hh : ∀ i, 0 < p.h i) (k : ℕ) (hk : k ≤ wanted p)
    (bits : α → ℕ → Bits) (hm : ∀ j, Measurable fun z => bits z j) :
    Measurable fun z => iterate p (bits z) k :=
  path_measurable p bits hm _ (fun x y h => iterate_agree p hh x y k hk (fun j hj _ => h j hj))

lemma grad_measurable (H : Data p f g μ a) : Measurable (gradient f) := by
  have hl : LipschitzWith ⟨p.L,H.smooth.le⟩ (gradient f) :=
    lipschitzWith_iff_norm_sub_le.mpr H.lip
  exact hl.continuous.measurable

lemma on_columns (H : Data p f g μ a) (hh : ∀ i, 0 < p.h i) (k : ℕ) (hk : k ≤ wanted p) :
    let P := timeline μ
    let b := history p g
    let E := fun z => ‖estimate p (b z) k - gradient f (iterate p (b z) k)‖^2
    Integrable E P ∧ (∫ z, E z ∂P) ≤ 168*precision p^2 := by
  intro P b E
  let N := fun z => noise p g μ k (table p).length (b z)
  obtain ⟨hN,hbound⟩ := noise_energy H hh k (table p).length le_rfl
  have hb : (∫ z, ‖N z‖^2 ∂P) ≤ 68*precision p^2 := by
    have hsum : (∑ r ∈ Finset.range (table p).length, weight p k r^2 * (4*units p (entry p r).1*precision p^2)) =
        (∑ r ∈ Finset.range (table p).length, weight p k r^2 * units p (entry p r).1) * (4*precision p^2) := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro _ _; ring
    rw [hsum] at hbound
    have h := mul_le_mul_of_nonneg_right (variance_weight p hh hk) (by positivity : 0 ≤ 4*precision p^2)
    exact hbound.trans (by linarith)
  have hm : Measurable E :=
    ((estimate_measurable hh k hk b (measurable_history H)).sub
      ((grad_measurable H).comp (iterate_measurable hh k hk b (measurable_history H)))).norm.pow_const 2
  have hdom : Integrable (fun z => 2*‖N z‖^2 + 32*precision p^2) P := (hN.const_mul _).add (integrable_const _)
  have he (z) : E z ≤ 2*‖N z‖^2 + 32*precision p^2 := by
    let e := estimate p (b z) k - gradient f (iterate p (b z) k)
    have hs : ‖e-N z‖ ≤ 4*precision p := bias_bound H hh k hk (b z)
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) hs 2
    have hf := DistributedSmoothNonconvex.norm_add_square (N z) (e-N z)
    rw [add_sub_cancel] at hf
    change ‖e‖^2 ≤ _
    linarith
  have hi : Integrable E P := hdom.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
    simpa [E] using he z)
  refine ⟨hi,(integral_mono hi hdom he).trans ?_⟩
  rw [integral_add (hN.const_mul 2) (integrable_const _),integral_const_mul,integral_const]
  simp only [probReal_univ,one_smul]
  linarith

lemma physical_error (H : Data p f g μ a) (hh : ∀ i, 0 < p.h i) (k : ℕ) (hk : k ≤ wanted p)
    (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hi : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) P) :
    let b := fun xs => row (script p) g (actual (script p) xs)
    let E := fun xs => ‖estimate p (b xs) k - gradient f (iterate p (b xs) k)‖^2
    Integrable E P ∧ (∫ xs, E xs ∂P) ≤ 168*precision p^2 := by
  let b := fun d => row (script p) g d
  let F := fun d => ‖estimate p (b d) k - gradient f (iterate p (b d) k)‖^2
  have hm : Measurable F := ((estimate_measurable hh k hk b (row_measurable H)).sub
    ((grad_measurable H).comp (iterate_measurable hh k hk b (row_measurable H)))).norm.pow_const 2
  let R : Measure (ℕ → p.Ω) := Measure.infinitePi fun j => (μ ((script p).worker j) : Measure p.Ω)
  have hA := actual_preserving (script p) P μ hw hi
  have hC := columns_preserving (script p) μ
  have la : HasLaw (actual (script p)) R P := ⟨hA.measurable.aemeasurable,hA.map_eq⟩
  have lc : HasLaw (columns (script p)) R (timeline μ) := ⟨hC.measurable.aemeasurable,hC.map_eq⟩
  obtain ⟨hInt,hBound⟩ := on_columns H hh k hk
  have hF : Integrable F R := (hC.integrable_comp hm.aestronglyMeasurable).mp hInt
  refine ⟨hA.integrable_comp_of_integrable hF, ?_⟩
  change (∫ xs, (F ∘ actual (script p)) xs ∂P) ≤ _
  rw [la.integral_comp hm.aestronglyMeasurable, ← lc.integral_comp hm.aestronglyMeasurable]
  exact hBound

lemma output_agree (hh : ∀ i, 0 < p.h i) (seed : Selection p) (x y : ℕ → Bits)
    (h : ∀ j < (table p).length, x j = y j) : output p seed x = output p seed y := by
  have hv (i : Fin (wanted p)) := estimate_agree p hh x y i i.isLt.le (fun j hj _ => h j hj)
  unfold output
  rw [hv seed.1,hv seed.2]
  split <;> exact iterate_agree p hh x y _ (Fin.isLt _).le (fun j hj _ => h j hj)

lemma execution_output (hh : ∀ i, 0 < p.h i) (P : ProbabilityMeasure (Samples p))
    (seed : Selection p) (xs : Samples p) :
    execute (system p g P) (algorithm p (duration p)) (duration p) seed xs =
      output p seed (row (script p) g (actual (script p) xs)) := by
  let u : MultilevelDeadline.Context p := ⟨script p,duration p,g,P,xs,seed⟩
  refine (MultilevelExecution.execute_script u (certified p hh) hh).trans ?_
  apply output_agree hh
  intro j hj
  change (if j < (table p).length then reply (script p) g xs j else []) = _
  rw [ite_eq_left hj,reply_row]

set_option maxHeartbeats 320000 in
lemma successful (H : Data p f g μ a) (hh : ∀ i, 0 < p.h i)
    (P : ProbabilityMeasure (Samples p))
    (hw : iIndepFun (fun i (s : Samples p) => s i) (P : Measure (Samples p)))
    (hi : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) (P : Measure (Samples p))) :
    spec.successful p f (fun z : Selection p × Samples p => output p z.1 (row (script p) g (actual (script p) z.2)))
      (law (system p g P) (algorithm p (duration p))) := by
  let b := fun xs => row (script p) g (actual (script p) xs)
  let x := fun (i : Fin (wanted p)) xs => iterate p (b xs) i
  let v := fun (i : Fin (wanted p)) xs => estimate p (b xs) i
  let G := fun (i : Fin (wanted p)) xs => gradient f (x i xs)
  let o := fun (ij : Selection p) xs => if ‖v ij.1 xs‖ ≤ ‖v ij.2 xs‖ then x ij.1 xs else x ij.2 xs
  have hA : Measurable (actual (script p)) := Measurable.of_eval
    (fun j => (hi ((script p).worker j)).measurable (ordinal (script p) j))
  have hm (j : ℕ) : Measurable (fun xs : Samples p => b xs j) := (row_measurable H j).comp hA
  have hx (i : Fin (wanted p)) : Measurable (x i) := iterate_measurable hh i i.isLt.le b hm
  have hv (i : Fin (wanted p)) : Measurable (v i) := estimate_measurable hh i i.isLt.le b hm
  have hg (i : Fin (wanted p)) : Measurable (G i) := (grad_measurable H).comp (hx i)
  have hE (i : Fin (wanted p)) := physical_error H hh i i.isLt.le (P : Measure (Samples p)) hw hi
  have hs (xs : Samples p) := estimated_sum p (b xs) H.smooth H.accuracy f H.grad H.lip a H.low H.gap
  let : NeZero (wanted p) := ⟨by unfold wanted; omega⟩
  have hp := LeonPairAccuracy.expected (P : Measure (Samples p)) v G (precision p) hv hg
    (fun i => (hE i).1) (fun i => (hE i).2.trans (by nlinarith [sq_nonneg (precision p)])) hs
  let Q := (PMF.uniformOfFintype (Selection p)).toMeasure.prod (P : Measure (Samples p))
  let F := fun z : Selection p × Samples p => output p z.1 (b z.2)
  change Measurable F ∧ Integrable (fun z => ‖gradient f (F z)‖^2) Q ∧ (∫ z, ‖gradient f (F z)‖^2 ∂Q) ≤ p.ε^2
  have hF : F = fun z => o z.1 z.2 := by
    funext z
    change output p z.1 (b z.2) = _
    by_cases h : ‖v z.1.1 z.2‖ ≤ ‖v z.1.2 z.2‖ <;> simp only [output, o, v, b] at h ⊢ <;> simp [h,x,b]
  rw [hF]
  refine ⟨measurable_from_prod_countable_right (fun (ij : Selection p) =>
    Measurable.ite (measurableSet_le (hv ij.1).norm (hv ij.2).norm) (hx ij.1) (hx ij.2)),?_⟩
  have hG (z : Selection p × Samples p) : gradient f (o z.1 z.2) =
      if ‖v z.1.1 z.2‖ ≤ ‖v z.1.2 z.2‖ then G z.1.1 z.2 else G z.1.2 z.2 := by
    by_cases h : ‖v z.1.1 z.2‖ ≤ ‖v z.1.2 z.2‖ <;> simp [o,G,h]
  simp_rw [hG]
  exact ⟨hp.1,hp.2.trans_eq (by unfold precision; ring)⟩

end LongTails.Proofs.MultilevelAccuracy

import LongTails.Proofs.LeonTreeError
import LongTails.Proofs.LeonCalendar
import LongTails.Proofs.DistributedNormalizedConvergence
import LongTails.Proofs.DistributedSmoothNonconvex

namespace LongTails.Proofs.LeonSelection

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E]

lemma pair_sum {ι : Type*} [Fintype ι] (v g : ι → E) :
    (∑ i, ∑ j, ‖if ‖v i‖ ≤ ‖v j‖ then g i else g j‖ ^ 2) ≤
      2 * ((∑ i, ‖v i‖) ^ 2 + 2 * Fintype.card ι * ∑ i, ‖v i - g i‖ ^ 2) := by
  classical
  have ht (i : ι) : ‖g i‖ ≤ ‖v i‖ + ‖v i - g i‖ := by
    linarith [norm_sub_norm_le (g i) (v i), norm_sub_rev (g i) (v i)]
  calc
    _ ≤ ∑ i, ∑ j, 2 * (‖v i‖ * ‖v j‖ + ‖v i - g i‖ ^ 2 + ‖v j - g j‖ ^ 2) := by
      gcongr with i _ j _
      rw [apply_ite norm]
      exact LeonDyadicTracking.smaller_estimate_sq (norm_nonneg _) (norm_nonneg _)
        (norm_nonneg _) (norm_nonneg _) (ht i) (ht j)
    _ = _ := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul]
      ring

end LongTails.Proofs.LeonSelection

namespace LongTails.Proofs.LeonHistory

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTrajectory
open LongTails.Algorithms.LeonTuning
open LeonRoundTrace LeonStage

def visits (ls : List ℕ) : ℕ → List ℕ
  | 0 => []
  | t+1 => if ls[t]?.getD 0 = 0 then t :: visits ls t else visits ls t

lemma visits_length (ls : List ℕ) (t : ℕ) (h : t ≤ ls.length) :
    (visits ls t).length = (ls.take t).count 0 := by
  induction t with
  | zero => simp [visits]
  | succ t ih =>
    have ht : t < ls.length := by omega
    rw [List.take_succ_eq_append_getElem ht]
    rw [List.count_append]
    by_cases hz : ls[t] = 0 <;> simp [visits, List.getElem?_eq_getElem ht, hz, ih ht.le]

lemma visited {ls : List ℕ} {t i : ℕ} (hi : i ∈ visits ls t) : i < t ∧ ls[i]?.getD 0 = 0 := by
  induction t with
  | zero => simp [visits] at hi
  | succ t ih =>
    unfold visits at hi
    split_ifs at hi with h
    · rcases List.mem_cons.mp hi with he | hold
      · subst i; exact ⟨Nat.lt_succ_self _, h⟩
      · exact ⟨Nat.lt_succ_of_lt (ih hold).1, (ih hold).2⟩
    · exact ⟨Nat.lt_succ_of_lt (ih hi).1, (ih hi).2⟩

lemma history_eq (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (ls : List ℕ) (t : ℕ) :
    (trajectory p g s ls t).history = (visits ls t).map (fun k =>
      ((trajectory p g s ls k).point, ‖observed (actualRound p g s ls k)‖)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [stage_step]
    by_cases hz : ls[t]?.getD 0 = 0 <;> simp [visits, applyEstimate, hz, ih]

lemma descent (p : Params) (hL : 0 < p.L) (hε : 0 < p.ε)
    (f : Point p → ℝ) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (ls : List ℕ) (t : ℕ) :
    let x := fun k => (trajectory p g s ls k).point
    let v := fun k => observed (actualRound p g s ls k)
    let η := resolution p / p.L
    η * ((visits ls t).map (fun k => ‖v k‖)).sum ≤ f p.x0 - f (x t) +
      3 * η * ((visits ls t).map (fun k => ‖v k - gradient f (x k)‖)).sum +
      (visits ls t).length * (p.L / 2 * η^2) := by
  let x := fun k => (trajectory p g s ls k).point
  let v := fun k => observed (actualRound p g s ls k)
  let η := resolution p / p.L
  have hη : 0 ≤ η := div_nonneg (LeonBatchTuning.resolution_pos p hε).le hL.le
  induction t with
  | zero => simp [visits, trajectory, initial]
  | succ t ih =>
    by_cases hz : ls[t]?.getD 0 = 0
    · have he : x (t+1) = x t - (η / ‖v t‖) • v t := by
        dsimp only [x]; rw [stage_step]; simp [applyEstimate, hz, v, η]
      have hs := ParameterFreeNsgdmRun.descent_step hf hlip hL.le η hη (x t) (v t)
      rw [← he] at hs
      have ht := mul_le_mul_of_nonneg_left (norm_sub_norm_le (v t) (gradient f (x t))) hη
      dsimp only at ih ⊢
      simp only [visits, ite_eq_left hz, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      dsimp only [x, v, η] at hs ht
      linarith
    · have he : x (t+1) = x t := by
        dsimp only [x]; rw [stage_step]; simp [applyEstimate, hz]
      simpa only [visits, ite_eq_right hz, show (trajectory p g s ls (t+1)).point = _ from he] using ih

end LongTails.Proofs.LeonHistory

namespace LongTails.Proofs.LeonReturnedPoint

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonCalendar
open LongTails.Algorithms.LeonTrajectory
open LongTails.Algorithms.LeonTuning
open LeonRoundTrace LeonHistory LeonStage

def leaves (J : ℕ) := visits (levels J) (levels J).length

lemma leaves_length (J : ℕ) : (leaves J).length = 4^J := by
  simp [leaves, visits_length _ _ le_rfl, LeonCalendar.leaf_count]

def index (J : ℕ) (i : Fin (4^J)) : ℕ :=
  (leaves J)[i.val]'(by simp [leaves_length])

lemma index_valid (J : ℕ) (i : Fin (4^J)) :
    index J i < (levels J).length ∧ (levels J)[index J i]?.getD 0 = 0 :=
  visited (List.getElem_mem _)

lemma sum_get {α : Type*} (xs : List α) (K : ℕ) (h : xs.length = K) (a : α → ℝ) :
    (xs.map a).sum = ∑ i : Fin K, a (xs[i.val]'(h ▸ i.isLt)) := by
  subst K
  conv_lhs => rw [← List.ofFn_get xs, List.map_ofFn, List.sum_ofFn]
  rfl

lemma output_eq (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (J : ℕ) (i j : Fin (4^J)) :
    let ls := levels J
    let R := fun t => actualRound p g s ls (index J t)
    output p (trajectory p g s ls ls.length) i j =
      if ‖observed (R i)‖ ≤ ‖observed (R j)‖ then (R i).model.point else (R j).model.point := by
  let ls := levels J
  let R := fun t => actualRound p g s ls (index J t)
  have lookup (k : Fin (4^J)) : (trajectory p g s ls ls.length).history[k.val]? =
      some ((R k).model.point, ‖observed (R k)‖) := by
    rw [history_eq, List.getElem?_map]
    change Option.map _ ((leaves J)[k.val]?) = _
    rw [List.getElem?_eq_getElem (show k.val < (leaves J).length by simp [leaves_length])]
    rfl
  change output p (trajectory p g s ls ls.length) i j = _
  unfold output
  rw [lookup i, lookup j]
  rfl

lemma estimated_sum (p : Params) (hL : 0 < p.L) (hε : 0 < p.ε)
    (f : Point p → ℝ) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ)
    (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) :
    let J := height p
    let R := fun i => actualRound p g s (levels J) (index J i)
    (∑ i, ‖observed (R i)‖) ≤ iterations p * resolution p +
      3 * ∑ i, ‖observed (R i) - gradient f (R i).model.point‖ := by
  let J := height p
  let ls := levels J
  let δ := resolution p
  let η := δ / p.L
  let K : ℝ := iterations p
  have hδ := LeonBatchTuning.resolution_pos p hε
  have hη : 0 < η := div_pos hδ hL
  have hk := (div_le_iff₀ (sq_pos_of_pos hδ)).mp (LeonBatchTuning.iterations_lower p)
  have hg₀ := hgap (trajectory p g s ls ls.length).point
  have hd := descent p hL hε f hf hlip g s ls ls.length
  dsimp only at hd ⊢
  change η * ((leaves J).map _).sum ≤ _ + 3 * η * ((leaves J).map _).sum +
    (leaves J).length * (p.L / 2 * η^2) at hd
  rw [leaves_length J, sum_get _ _ (leaves_length J), sum_get _ _ (leaves_length J)] at hd
  have hηL : η * p.L = δ := div_mul_cancel₀ _ hL.ne'
  have hgap' : p.Δ ≤ K * (η * δ) / 2 := by
    apply le_of_mul_le_mul_left (a := p.L) _ hL
    change 2*p.L*p.Δ ≤ K * δ^2 at hk
    nlinarith [congrArg (fun a => K*a*δ) hηL]
  have hcost : p.L / 2 * η^2 = η*δ/2 := by nlinarith [congrArg (fun a => η*a) hηL]
  rw [hcost] at hd
  apply le_of_mul_le_mul_left (a := η) _ hη
  change η * _ ≤ η * (K * δ + 3 * _)
  change η * (∑ i, ‖observed (actualRound p g s ls (index J i))‖) ≤ _ +
    3 * η * (∑ i, ‖observed (actualRound p g s ls (index J i)) -
      gradient f (trajectory p g s ls (index J i)).point‖) + K * _ at hd
  change η * (∑ i, ‖observed (actualRound p g s ls (index J i))‖) ≤
    η * (K * δ + 3 * (∑ i, ‖observed (actualRound p g s ls (index J i)) -
      gradient f (trajectory p g s ls (index J i)).point‖))
  linarith only [hd, hg₀, hgap']

end LongTails.Proofs.LeonReturnedPoint

namespace LongTails.Proofs.LeonPairAccuracy

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]

lemma pair_bound {K : ℕ} (v g : Fin K → E) (δ : ℝ)
    (h : (∑ i, ‖v i‖) ≤ K * δ + 3 * ∑ i, ‖v i - g i‖) :
    (∑ i, ∑ j, ‖if ‖v i‖ ≤ ‖v j‖ then g i else g j‖ ^ 2) ≤
      8 * (K : ℝ)^2 * δ^2 + 28 * K * ∑ i, ‖v i - g i‖^2 := by
  have hp := LeonSelection.pair_sum v g
  simp only [Fintype.card_fin] at hp
  have he := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin K => (1:ℝ)) (fun i => ‖v i - g i‖)
  simp only [one_pow, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at he
  have hv := mul_self_le_mul_self (Finset.sum_nonneg (fun i _ => norm_nonneg (v i))) h
  linarith only [hp, he, hv, sq_nonneg ((K:ℝ)*δ - ∑ i, ‖v i-g i‖)]

lemma expected {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    {K : ℕ} [NeZero K] (P : Measure Ω) [IsProbabilityMeasure P]
    (v g : Fin K → Ω → E) (δ : ℝ)
    (hmv : ∀ i, Measurable (v i)) (hmg : ∀ i, Measurable (g i))
    (hi : ∀ i, Integrable (fun s => ‖v i s - g i s‖^2) P)
    (he : ∀ i, (∫ s, ‖v i s - g i s‖^2 ∂P) ≤ 7142*δ^2)
    (hs : ∀ s, (∑ i, ‖v i s‖) ≤ K * δ + 3 * ∑ i, ‖v i s - g i s‖) :
    let Q := (PMF.uniformOfFintype (Fin K × Fin K)).toMeasure.prod P
    let X := fun (z : (Fin K × Fin K) × Ω) =>
      ‖if ‖v z.1.1 z.2‖ ≤ ‖v z.1.2 z.2‖ then g z.1.1 z.2 else g z.1.2 z.2‖^2
    Integrable X Q ∧ (∫ z, X z ∂Q) ≤ (512*δ)^2 := by
  let D := fun i s => ‖v i s - g i s‖^2
  let B := fun s => 8*(K:ℝ)^2*δ^2 + 28*K*∑ i, D i s
  let U := fun (ij : Fin K × Fin K) s =>
    ‖if ‖v ij.1 s‖ ≤ ‖v ij.2 s‖ then g ij.1 s else g ij.2 s‖^2
  have hb (s) : ∑ ij, U ij s ≤ B s := by
    simpa only [Fintype.sum_prod_type, U, B, D] using pair_bound (fun i => v i s) (fun i => g i s) δ (hs s)
  have hBI : Integrable B P := (integrable_const _).add
    ((integrable_finsetSum _ (fun i _ => hi i)).const_mul _)
  have hm (ij) : Measurable (U ij) := by
    apply Measurable.pow_const
    apply Measurable.norm
    exact Measurable.ite (measurableSet_le (hmv _).norm (hmv _).norm) (hmg _) (hmg _)
  have hI (ij) : Integrable (U ij) P := hBI.mono' (hm ij).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (Finset.single_le_sum (f := fun k => U k s) (fun _ _ => sq_nonneg _) (Finset.mem_univ ij)).trans (hb s)))
  have hall : Measurable (fun z : (Fin K × Fin K) × Ω => U z.1 z.2) :=
    measurable_from_prod_countable_right hm
  have hUI := OracleTemplate.ZerothOrder.finite_prod_integrable
    (μ := (PMF.uniformOfFintype (Fin K × Fin K)).toMeasure) (ν := P) hall.aestronglyMeasurable hI
  refine ⟨hUI, ?_⟩
  change (∫ z, U z.1 z.2 ∂(PMF.uniformOfFintype (Fin K × Fin K)).toMeasure.prod P) ≤ _
  rw [integral_prod _ hUI, OracleTemplate.ZerothOrder.uniform_integral_explicit]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, smul_eq_mul]
  have hpos : 0 < (K:ℝ)*(K:ℝ) := by have := NeZero.pos K; positivity
  rw [← div_eq_inv_mul, div_le_iff₀ hpos, ← integral_finsetSum _ (fun i _ => hI i)]
  apply (integral_mono (integrable_finsetSum _ (fun i _ => hI i)) hBI hb).trans
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => he i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hDI : Integrable (fun s => ∑ i, D i s) P := integrable_finsetSum _ (fun i _ => hi i)
  simp only [B, integral_add (integrable_const _) (hDI.const_mul _), integral_const, probReal_univ,
    one_smul, integral_const_mul, integral_finsetSum _ (fun i _ => hi i), D]
  nlinarith [mul_le_mul_of_nonneg_left hsum (show (0:ℝ) ≤ 28*K by positivity),
    sq_nonneg ((K:ℝ)*δ)]

end LongTails.Proofs.LeonPairAccuracy

namespace LongTails.Proofs.LeonAccuracy

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Algorithms.LeonCalendar
open LongTails.Algorithms.LeonTrajectory
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonProtocol (algorithm)
open LeonRoundTrace LeonStage LeonReturnedPoint

lemma accuracy (p : Params) (hh : ∀ i, 0 < p.h i) (hε : 0 < p.ε) (hL : 0 < p.L)
    (P : ProbabilityMeasure (Samples p)) (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (f : Functions p) (g : Fin p.n → Point p → p.Ω → Point p)
    (hw : iIndepFun (fun i (s : Samples p) => s i) (P : Measure _))
    (hi : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) (P : Measure _))
    (hg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) p.σ)
    (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (a : ℝ) (ha : ∀ x, a ≤ objective p f x) (hgap : objective p f p.x0 - a ≤ p.Δ)
    (T : DistributedTemplate.Time) :
    let ls := levels (height p)
    spec.successful p f (fun z : (Fin (iterations p) × Fin (iterations p)) × Samples p =>
      output p (trajectory p g z.2 ls ls.length) z.1.1 z.1.2)
      (DistributedTemplate.law (system p g P) (algorithm p T)) := by
  let J := height p
  let ls := levels J
  let K := iterations p
  let x := fun (i : Fin K) s => (trajectory p g s ls (index J i)).point
  let v := fun (i : Fin K) s => observed (actualRound p g s ls (index J i))
  let F := gradient (objective p f)
  let trueGrad := fun i s => F (x i s)
  let out := fun (ij : Fin K × Fin K) (s : Samples p) =>
    if ‖v ij.1 s‖ ≤ ‖v ij.2 s‖ then x ij.1 s else x ij.2 s
  have heq (ij : Fin K × Fin K) (s : Samples p) :
      output p (trajectory p g s ls ls.length) ij.1 ij.2 = out ij s := output_eq p g s J ij.1 ij.2
  have hagg (y) : HasGradientAt (objective p f) (F y) y := by
    have h := OracleTemplate.FiniteSum.objective_gradient (f := f)
      (oracle := fun ix : Fin p.n × Point p => gradient (f ix.1) ix.2) hf y
    rw [← h.gradient] at h
    exact h
  have h₀ := DistributedSmoothNonconvex.initial_gradient_bound (p := p) hL hagg hlip a ha hgap
  have hδ := LeonBatchTuning.resolution_pos p hε
  have hk := (div_le_iff₀ (sq_pos_of_pos hδ)).mp (LeonBatchTuning.iterations_lower p)
  have hK : 1 ≤ (4:ℝ)^J := one_le_pow₀ (by norm_num)
  have hstart : ‖F p.x0‖ ≤ 4^J * resolution p := by
    change _ ≤ (K:ℝ) * _ at hk
    have hcast : (K:ℝ) = (4:ℝ)^J := by simp [K, J, iterations]
    rw [hcast] at hk
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) (show 0 ≤ (4:ℝ)^J * resolution p^2 by positivity),
      norm_nonneg (F p.x0), show 0 ≤ (4:ℝ)^J * resolution p by positivity]
  have hst (i : Fin K) := LeonMeasurability.measurable_state p g (fun i => (hg i).measurable)
    id ls (index J i) (index_valid J i).1.le (fun i j _ => (hi i).measurable j)
  have hx (i : Fin K) : Measurable (x i) := (hst i).1
  have hv (i : Fin K) : Measurable (v i) := LeonMeasurability.measurable_estimate p g
    (fun i => (hg i).measurable) id _ _ _ (hst i).1 (hst i).2 (fun i _ _ => (hi i).measurable _)
  have hLipF : LipschitzWith p.L.toNNReal F := lipschitzWith_iff_norm_sub_le.mpr (by
    simpa only [Real.coe_toNNReal _ hL.le] using hlip)
  have htrue (i : Fin K) : Measurable (trueGrad i) := hLipF.continuous.measurable.comp (hx i)
  have hei (i : Fin K) := LeonTreeError.leaf_error p hh hε hL P μ f g hw hi hg hf hlip J hstart
    (index J i) (index_valid J i).1 (index_valid J i).2
  have hsum (s : Samples p) := estimated_sum p hL hε _ hagg hlip (fun y => by linarith [ha y]) g s
  let : NeZero K := ⟨by dsimp [K, iterations]; positivity⟩
  have hpair := LeonPairAccuracy.expected (K := K) (P : Measure (Samples p)) v trueGrad (resolution p) hv htrue
    (fun i => (hei i).1) (fun i => (hei i).2) hsum
  have hm (ij : Fin K × Fin K) : Measurable (out ij) :=
    Measurable.ite (measurableSet_le (hv _).norm (hv _).norm) (hx _) (hx _)
  have hval (z : (Fin K × Fin K) × Samples p) : F (out z.1 z.2) =
      if ‖v z.1.1 z.2‖ ≤ ‖v z.1.2 z.2‖ then trueGrad z.1.1 z.2 else trueGrad z.1.2 z.2 := by
    by_cases h : ‖v z.1.1 z.2‖ ≤ ‖v z.1.2 z.2‖ <;> simp [out,trueGrad,h]
  let Q := (PMF.uniformOfFintype (Fin K × Fin K)).toMeasure.prod (P : Measure (Samples p))
  let Y := fun z : (Fin K × Fin K) × Samples p => output p (trajectory p g z.2 ls ls.length) z.1.1 z.1.2
  change Measurable Y ∧ Integrable (fun z => ‖F (Y z)‖^2) Q ∧ (∫ z, ‖F (Y z)‖^2 ∂Q) ≤ p.ε^2
  have hY : Y = fun z => out z.1 z.2 := funext (fun z => heq z.1 z.2)
  rw [hY]
  refine ⟨measurable_from_prod_countable_right hm, ?_⟩
  simp_rw [hval]
  exact ⟨hpair.1, hpair.2.trans_eq (by unfold resolution; ring)⟩

end LongTails.Proofs.LeonAccuracy

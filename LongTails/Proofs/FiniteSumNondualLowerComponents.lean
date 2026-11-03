import LongTails.Proofs.FiniteSumNondualLowerGeometry
import LongTails.Setups.FiniteSumNondualSmoothConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace Topology

namespace LongTails.Proofs.FiniteSumNondualLowerComponents

open FiniteSumNondualLowerGeometry

noncomputable def separableEnergy {ι : Type*} [Fintype ι] (φ : ι → ℝ → ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ := ∑ j, φ j (x j)

noncomputable def separableSlope {ι : Type*} (g : ι → ℝ → ℝ)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun j => g j (x j))

lemma separable_model {ι : Type*} [Fintype ι] (φ g : ι → ℝ → ℝ)
    (h : ∀ j x y, 0 ≤ φ j y - φ j x - g j x * (y - x) ∧
      φ j y - φ j x - g j x * (y - x) ≤ (y - x) ^ 2)
    (x y : EuclideanSpace ℝ ι) :
    0 ≤ separableEnergy φ y - separableEnergy φ x - ⟪separableSlope g x, y - x⟫ ∧
    separableEnergy φ y - separableEnergy φ x - ⟪separableSlope g x, y - x⟫ ≤ ‖y - x‖ ^ 2 := by
  have he : separableEnergy φ y - separableEnergy φ x - ⟪separableSlope g x, y - x⟫ =
      ∑ j, (φ j (y j) - φ j (x j) - g j (x j) * (y j - x j)) := by
    simp [separableEnergy, separableSlope, PiLp.inner_apply, RCLike.inner_apply,
      Finset.sum_sub_distrib, mul_comm]
  rw [he, EuclideanSpace.real_norm_sq_eq]
  exact ⟨Finset.sum_nonneg (fun j _ => (h j (x j) (y j)).1),
    Finset.sum_le_sum (fun j _ => (h j (x j) (y j)).2)⟩

lemma separable_hasGradientAt {ι : Type*} [Fintype ι] (φ g : ι → ℝ → ℝ)
    (h : ∀ j x y, 0 ≤ φ j y - φ j x - g j x * (y - x) ∧
      φ j y - φ j x - g j x * (y - x) ≤ (y - x) ^ 2)
    (x : EuclideanSpace ℝ ι) :
    HasGradientAt (separableEnergy φ) (separableSlope g x) x := by
  rw [hasGradientAt_iff_isLittleO]
  have hb : (fun y => separableEnergy φ y - separableEnergy φ x -
      ⟪separableSlope g x, y - x⟫) =O[nhds x] (fun y => ‖y - x‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with y
    have hm := separable_model φ g h x y
    simpa only [Real.norm_eq_abs, abs_of_nonneg hm.1,
      abs_of_nonneg (sq_nonneg ‖y - x‖), one_mul] using hm.2
  exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub x (by norm_num : 1 < 2))

lemma separable_convex {ι : Type*} [Fintype ι] (φ g : ι → ℝ → ℝ)
    (h : ∀ j x y, 0 ≤ φ j y - φ j x - g j x * (y - x) ∧
      φ j y - φ j x - g j x * (y - x) ≤ (y - x) ^ 2) :
    ConvexOn ℝ Set.univ (separableEnergy φ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := (separable_model φ g h z x).1
  have hy := (separable_model φ g h z y).1
  have hv : a • (x - z) + b • (y - z) = 0 := by
    calc
      _ = (a • x + b • y) - (a + b) • z := by module
      _ = 0 := by rw [hab, one_smul]; exact sub_self _
  have hi := congrArg (fun v => ⟪separableSlope g z, v⟫) hv
  simp only [inner_add_right, inner_smul_right, inner_zero_right] at hi
  have he := congrArg (fun t => t * separableEnergy φ z) hab
  change separableEnergy φ z ≤ a * separableEnergy φ x + b * separableEnergy φ y
  nlinarith only [mul_nonneg ha hx, mul_nonneg hb hy, hi, he]

lemma separableSlope_lipschitz {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ)
    (h : ∀ j x y, |g j x - g j y| ≤ 2 * |x - y|)
    (x y : EuclideanSpace ℝ ι) :
    ‖separableSlope g x - separableSlope g y‖ ≤ 2 * ‖x - y‖ := by
  have hs : ‖separableSlope g x - separableSlope g y‖ ^ 2 ≤ 4 * ‖x - y‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    change (g j (x j) - g j (y j)) ^ 2 ≤ 4 * (x j - y j) ^ 2
    have hh := pow_le_pow_left₀ (abs_nonneg _) (h j (x j) (y j)) 2
    norm_num [sq_abs, mul_pow] at hh ⊢
    exact hh
  nlinarith [norm_nonneg (separableSlope g x - separableSlope g y), norm_nonneg (x - y)]

def maskedProfile (active : Bool) (δ b t : ℝ) : ℝ :=
  if active then deadZone δ (t - b) ^ 2 else 0

def maskedSlope (active : Bool) (δ b t : ℝ) : ℝ :=
  if active then 2 * softThreshold δ (t - b) else 0

lemma masked_model (active : Bool) (δ b x y : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ maskedProfile active δ b y - maskedProfile active δ b x -
      maskedSlope active δ b x * (y - x) ∧
    maskedProfile active δ b y - maskedProfile active δ b x -
      maskedSlope active δ b x * (y - x) ≤ (y - x) ^ 2 := by
  cases active with
  | false => simp [maskedProfile, maskedSlope, sq_nonneg]
  | true =>
    have h := deadZone_quadratic_model δ (x - b) (y - b) hδ
    have he : y - b - (x - b) = y - x := by ring
    simpa [maskedProfile, maskedSlope, he] using h

lemma masked_lipschitz (active : Bool) (δ b x y : ℝ) (hδ : 0 ≤ δ) :
    |maskedSlope active δ b x - maskedSlope active δ b y| ≤ 2 * |x - y| := by
  cases active with
  | false => simp [maskedSlope, abs_nonneg]
  | true =>
    have h := mul_le_mul_of_nonneg_left (softThreshold_lipschitz δ (x - b) (y - b) hδ)
      (by norm_num : (0 : ℝ) ≤ 2)
    have he : x - b - (y - b) = x - y := by ring
    simpa [maskedSlope, ← mul_sub, abs_mul, he] using h

lemma composed_separable_gradient {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (φ g : κ → ℝ → ℝ)
    (h : ∀ j x y, 0 ≤ φ j y - φ j x - g j x * (y - x) ∧
      φ j y - φ j x - g j x * (y - x) ≤ (y - x) ^ 2)
    (x : EuclideanSpace ℝ ι) :
    HasGradientAt (fun y => separableEnergy φ (A y))
      (A.adjoint (separableSlope g (A x))) x := by
  have hd := (separable_hasGradientAt φ g h (A x)).hasFDerivAt.comp x A.hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · rfl
  · ext v
    exact A.adjoint_inner_left v (separableSlope g (A x))

lemma composed_separable_lipschitz {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (g : κ → ℝ → ℝ)
    (hA : ‖A‖ ≤ 2) (hg : ∀ j x y, |g j x - g j y| ≤ 2 * |x - y|)
    (x y : EuclideanSpace ℝ ι) :
    ‖A.adjoint (separableSlope g (A x)) - A.adjoint (separableSlope g (A y))‖ ≤
      8 * ‖x - y‖ := by
  rw [← map_sub]
  have ha : ‖A.adjoint‖ ≤ 2 := by simpa using hA
  have h₁ := A.adjoint.le_opNorm (separableSlope g (A x) - separableSlope g (A y))
  have h₂ := separableSlope_lipschitz g hg (A x) (A y)
  have h₃ : ‖A x - A y‖ ≤ 2 * ‖x - y‖ := by
    rw [← map_sub]
    exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have h₄ := mul_le_mul_of_nonneg_right ha
    (norm_nonneg (separableSlope g (A x) - separableSlope g (A y)))
  nlinarith

noncomputable def chainMap (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (Fin.cases (x 0)
        (fun j => x j.castSucc - x j.succ))
      map_add' := by
        intro x y
        ext j
        refine Fin.cases ?_ (fun i => ?_) j
        · rfl
        · simp; ring
      map_smul' := by
        intro a x
        ext j
        refine Fin.cases ?_ (fun i => ?_) j
        · rfl
        · simp; ring }

lemma chainMap_apply_zero (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) :
    chainMap k x 0 = x 0 := rfl

lemma chainMap_apply_succ (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) (j : Fin k) :
    chainMap k x j.succ = x j.castSucc - x j.succ := rfl

lemma chainMap_norm (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) :
    ‖chainMap k x‖ ≤ 2 * ‖x‖ := by
  have he : ‖chainMap k x‖ ^ 2 = x 0 ^ 2 +
      ∑ j : Fin k, (x j.castSucc - x j.succ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    simp only [chainMap_apply_zero, chainMap_apply_succ]
  have h := chain_difference_energy_fin k (fun j => x j)
  rw [← EuclideanSpace.real_norm_sq_eq] at h
  nlinarith [norm_nonneg (chainMap k x), norm_nonneg x]

noncomputable def coordinateMap {ι κ : Type*} [Fintype ι] [Fintype κ] (π : κ ↪ ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun j => x (π j))
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }

lemma coordinateMap_norm {ι κ : Type*} [Fintype ι] [Fintype κ] (π : κ ↪ ι)
    (x : EuclideanSpace ℝ ι) : ‖coordinateMap π x‖ ≤ ‖x‖ := by
  classical
  have hs : ‖coordinateMap π x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    change (∑ j, x (π j) ^ 2) ≤ ∑ i, x i ^ 2
    calc
      _ = ∑ i ∈ Finset.univ.map π, x i ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => sq_nonneg (x i))
  nlinarith [norm_nonneg (coordinateMap π x), norm_nonneg x]

noncomputable def selectedChain {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  (chainMap k).comp (coordinateMap π)

lemma selectedChain_opNorm {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) :
    ‖selectedChain π‖ ≤ 2 := by
  apply (selectedChain π).opNorm_le_bound (by norm_num)
  intro x
  exact (chainMap_norm k (coordinateMap π x)).trans
    (mul_le_mul_of_nonneg_left (coordinateMap_norm π x) (by norm_num))

noncomputable def hardComponent {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  L / 8 * separableEnergy (fun j => maskedProfile (decide (owner j = i))
    (Fin.cases (0 : ℝ) (fun _ => δ) j) (Fin.cases a (fun _ => 0) j)) (selectedChain π x)

noncomputable def hardGradient {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (L / 8) • (selectedChain π).adjoint (separableSlope
    (fun j => maskedSlope (decide (owner j = i))
      (Fin.cases (0 : ℝ) (fun _ => δ) j) (Fin.cases a (fun _ => 0) j)) (selectedChain π x))

lemma hardComponent_gradient {d k n : ℕ} (L δ a : ℝ) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (hardComponent L δ a π owner i) (hardGradient L δ a π owner i x) x := by
  have hθ (j : Fin (k + 1)) : (0 : ℝ) ≤ Fin.cases (0 : ℝ) (fun _ => δ) j := by
    refine Fin.cases ?_ (fun _ => ?_) j <;> simp [hδ]
  let φ : Fin (k + 1) → ℝ → ℝ := fun j => maskedProfile (decide (owner j = i))
    (Fin.cases (0 : ℝ) (fun _ => δ) j) (Fin.cases a (fun _ => 0) j)
  let g : Fin (k + 1) → ℝ → ℝ := fun j => maskedSlope (decide (owner j = i))
    (Fin.cases (0 : ℝ) (fun _ => δ) j) (Fin.cases a (fun _ => 0) j)
  have hm : ∀ j u v, 0 ≤ φ j v - φ j u - g j u * (v - u) ∧
      φ j v - φ j u - g j u * (v - u) ≤ (v - u) ^ 2 := by
    intro j u v
    dsimp only [φ, g]
    refine Fin.cases ?_ (fun j => ?_) j
    · exact masked_model (decide (owner 0 = i)) 0 a u v (le_refl 0)
    · exact masked_model (decide (owner j.succ = i)) δ 0 u v hδ
  have h := composed_separable_gradient (selectedChain π) φ g hm x
  change HasGradientAt (fun y => L / 8 * separableEnergy φ (selectedChain π y))
    ((L / 8) • (selectedChain π).adjoint (separableSlope g (selectedChain π x))) x
  rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
  rw [map_smul]
  exact h.const_mul (L / 8)

lemma hardGradient_lipschitz {d k n : ℕ} (L δ a : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (i : Fin n)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖hardGradient L δ a π owner i x - hardGradient L δ a π owner i y‖ ≤ L * ‖x - y‖ := by
  have hθ (j : Fin (k + 1)) : (0 : ℝ) ≤ Fin.cases (0 : ℝ) (fun _ => δ) j := by
    refine Fin.cases ?_ (fun _ => ?_) j <;> simp [hδ]
  have h := composed_separable_lipschitz (selectedChain π)
    (fun j => maskedSlope (decide (owner j = i))
      (Fin.cases (0 : ℝ) (fun _ => δ) j) (Fin.cases a (fun _ => 0) j))
    (selectedChain_opNorm π) (fun j u v => masked_lipschitz _ _ _ u v (hθ j)) x y
  unfold hardGradient
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ L / 8)]
  have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ L / 8)
  nlinarith

lemma hardComponent_convex {d k n : ℕ} (L δ a : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (i : Fin n) :
    ConvexOn ℝ Set.univ (hardComponent L δ a π owner i) := by
  have hθ (j : Fin (k + 1)) : (0 : ℝ) ≤ Fin.cases (0 : ℝ) (fun _ => δ) j := by
    refine Fin.cases ?_ (fun _ => ?_) j <;> simp [hδ]
  let φ : Fin (k + 1) → ℝ → ℝ := fun j => maskedProfile (decide (owner j = i))
    (Fin.cases (0 : ℝ) (fun _ => δ) j) (Fin.cases a (fun _ => 0) j)
  let g : Fin (k + 1) → ℝ → ℝ := fun j => maskedSlope (decide (owner j = i))
    (Fin.cases (0 : ℝ) (fun _ => δ) j) (Fin.cases a (fun _ => 0) j)
  have hm : ∀ j u v, 0 ≤ φ j v - φ j u - g j u * (v - u) ∧
      φ j v - φ j u - g j u * (v - u) ≤ (v - u) ^ 2 := by
    intro j u v
    dsimp only [φ, g]
    refine Fin.cases ?_ (fun j => ?_) j
    · exact masked_model (decide (owner 0 = i)) 0 a u v (le_refl 0)
    · exact masked_model (decide (owner j.succ = i)) δ 0 u v hδ
  have hc := separable_convex φ g hm
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ c e hc₀ he₀ hce
  have hm := hc.2 (Set.mem_univ (selectedChain π x)) (Set.mem_univ (selectedChain π y))
    hc₀ he₀ hce
  have hs := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ L / 8)
  change L / 8 * separableEnergy φ (selectedChain π (c • x + e • y)) ≤
    c * (L / 8 * separableEnergy φ (selectedChain π x)) +
    e * (L / 8 * separableEnergy φ (selectedChain π y))
  rw [map_add, map_smul, map_smul]
  simpa only [smul_eq_mul, mul_add, mul_left_comm (L / 8)] using hs

lemma hardComponent_nonneg {d k n : ℕ} (L δ a : ℝ) (hL : 0 ≤ L)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ hardComponent L δ a π owner i x := by
  unfold hardComponent separableEnergy
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro j _
  dsimp only [maskedProfile]
  split <;> positivity

lemma hardComponent_sum {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (x : EuclideanSpace ℝ (Fin d)) :
    (∑ i, hardComponent L δ a π owner i x) = L / 8 *
      ((x (π 0) - a) ^ 2 + ∑ j : Fin k,
        deadZone δ (x (π j.castSucc) - x (π j.succ)) ^ 2) := by
  classical
  simp only [hardComponent, separableEnergy, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [maskedProfile]
  rw [Fin.sum_univ_succ]
  simp [selectedChain, coordinateMap, chainMap, deadZone, sq_abs]

noncomputable def hiddenPoint {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (a : ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => if i ∈ Finset.univ.map π then a else 0)

lemma hiddenPoint_apply {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (a : ℝ)
    (j : Fin (k + 1)) : hiddenPoint π a (π j) = a := by
  simp [hiddenPoint]

lemma hiddenPoint_l1 {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (a : ℝ) :
    (∑ i, |hiddenPoint π a i|) = (k + 1 : ℕ) * |a| := by
  change (∑ i : Fin d, |if i ∈ Finset.univ.map π then a else 0|) = _
  simp only [apply_ite, abs_zero]
  rw [Finset.sum_ite_mem]
  simp

lemma selectedChain_apply_zero {d k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : selectedChain π x 0 = x (π 0) := rfl

lemma selectedChain_apply_succ {d k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin k) :
    selectedChain π x j.succ = x (π j.castSucc) - x (π j.succ) := rfl

lemma hardComponent_hiddenPoint {d k n : ℕ} (L δ a : ℝ) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (i : Fin n) :
    hardComponent L δ a π owner i (hiddenPoint π a) = 0 := by
  unfold hardComponent separableEnergy
  have hz (j : Fin (k + 1)) : maskedProfile (decide (owner j = i))
      (Fin.cases (0 : ℝ) (fun _ => δ) j) (Fin.cases a (fun _ => 0) j)
      (selectedChain π (hiddenPoint π a) j) = 0 := by
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [selectedChain_apply_zero, hiddenPoint_apply, maskedProfile, deadZone]
    · simp [selectedChain_apply_succ, hiddenPoint_apply, maskedProfile, deadZone,
        max_eq_right (neg_nonpos.mpr hδ)]
  simp_rw [hz]
  simp

lemma hardComponent_gap {d k n : ℕ} (L δ a : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (ha : 0 ≤ a) (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (x : EuclideanSpace ℝ (Fin d)) (m : ℕ) (hm : m ≤ k)
    (hscale : ((k : ℝ) + 1) * δ ≤ a / 8)
    (htail : |x (π ⟨m, by omega⟩)| ≤ δ / 4) :
    L * a ^ 2 ≤ 16 * ((k : ℝ) + 1) * ∑ i, hardComponent L δ a π owner i x := by
  have he := chain_gap_fin δ a k m (fun j => x (π j)) ha hδ hm hscale htail
  calc
    L * a ^ 2 ≤ L * (2 * ((k : ℝ) + 1) * ((x (π 0) - a) ^ 2 +
        ∑ j : Fin k, deadZone δ (x (π j.castSucc) - x (π j.succ)) ^ 2)) :=
      mul_le_mul_of_nonneg_left he hL
    _ = _ := by rw [hardComponent_sum]; ring

open LongTails.Setups.FiniteSumNondualSmoothConvex

noncomputable def hardOracle (p : Params) {k : ℕ} (δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin p.d) (owner : Fin (k + 1) → Fin p.n) :
    OracleTemplate.Oracle (Fin p.n × Feasible p) (Point p) where
  answer := fun _ q _ => hardGradient p.L δ a π owner q.2.1 q.2.2.val

lemma hard_admissible (p : Params) {k : ℕ} (δ a : ℝ) (hL : 0 ≤ p.L) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin p.d) (owner : Fin (k + 1) → Fin p.n) :
    spec.admissible p (hardComponent p.L δ a π owner) (hardOracle p δ a π owner) := by
  refine ⟨fun i => hardComponent_convex p.L δ a hL hδ π owner i, ?_, ?_, ?_⟩
  · intro i x
    have hg := hardComponent_gradient p.L δ a hδ π owner i x
    rw [hg.gradient]
    exact hg
  · intro i x y
    rw [(hardComponent_gradient p.L δ a hδ π owner i x).gradient,
      (hardComponent_gradient p.L δ a hδ π owner i y).gradient]
    exact hardGradient_lipschitz p.L δ a hL hδ π owner i x y
  · intro history seed i x
    exact (hardComponent_gradient p.L δ a hδ π owner i x.val).gradient.symm

lemma hard_objective_nonneg (p : Params) {k : ℕ} (δ a : ℝ) (hL : 0 ≤ p.L)
    (π : Fin (k + 1) ↪ Fin p.d) (owner : Fin (k + 1) → Fin p.n) (x : Point p) :
    0 ≤ objective (hardComponent p.L δ a π owner) x := by
  unfold objective LongTails.Setups.FiniteSumSmoothAndConvex.objective
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun i _ => hardComponent_nonneg p.L δ a hL π owner i x))

lemma hard_objective_hiddenPoint (p : Params) {k : ℕ} (δ a : ℝ) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin p.d) (owner : Fin (k + 1) → Fin p.n) :
    objective (hardComponent p.L δ a π owner) (hiddenPoint π a) = 0 := by
  unfold objective LongTails.Setups.FiniteSumSmoothAndConvex.objective
  simp [hardComponent_hiddenPoint p.L δ a hδ π owner]

lemma hiddenPoint_mem (p : Params) {k : ℕ} (a : ℝ) (π : Fin (k + 1) ↪ Fin p.d)
    (hR : ((k : ℝ) + 1) * |a| ≤ p.R) : hiddenPoint π a ∈ domain p := by
  change (∑ i, |hiddenPoint π a i|) ≤ p.R
  rw [hiddenPoint_l1]
  simpa using hR

lemma hard_objective_minimum (p : Params) {k : ℕ} (δ a : ℝ) (hL : 0 ≤ p.L)
    (hδ : 0 ≤ δ) (π : Fin (k + 1) ↪ Fin p.d) (owner : Fin (k + 1) → Fin p.n) :
    IsMinOn (objective (hardComponent p.L δ a π owner)) (domain p) (hiddenPoint π a) := by
  intro y _
  rw [hard_objective_hiddenPoint p δ a hδ π owner]
  exact hard_objective_nonneg p δ a hL π owner y

lemma hard_objective_gap (p : Params) {k : ℕ} (δ a : ℝ) (hL : 0 ≤ p.L)
    (hδ : 0 ≤ δ) (ha : 0 ≤ a) (π : Fin (k + 1) ↪ Fin p.d)
    (owner : Fin (k + 1) → Fin p.n) (x : Point p) (m : ℕ) (hm : m ≤ k)
    (hscale : ((k : ℝ) + 1) * δ ≤ a / 8)
    (htail : |x (π ⟨m, by omega⟩)| ≤ δ / 4) :
    p.L * a ^ 2 / (16 * ((k : ℝ) + 1) * p.n) ≤
      objective (hardComponent p.L δ a π owner) x := by
  have he := hardComponent_gap p.L δ a hL hδ ha π owner x m hm hscale htail
  have hn : (0 : ℝ) < p.n := by exact_mod_cast (NeZero.pos p.n)
  have hk : (0 : ℝ) < 16 * ((k : ℝ) + 1) := by positivity
  have hd : p.L * a ^ 2 / (16 * ((k : ℝ) + 1)) ≤
      ∑ i, hardComponent p.L δ a π owner i x := (div_le_iff₀ hk).mpr (by nlinarith)
  unfold objective LongTails.Setups.FiniteSumSmoothAndConvex.objective
  calc
    _ = (p.n : ℝ)⁻¹ * (p.L * a ^ 2 / (16 * ((k : ℝ) + 1))) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hn.le)

end LongTails.Proofs.FiniteSumNondualLowerComponents

import Mathlib.Data.Nat.Log
import Mathlib.Probability.Independence.InfinitePi
import LongTails.Algorithms.RobustValue
import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.FiniteVarianceConfidence

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OracleTemplate.FiniteVariance

noncomputable def treeLaw {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) :
    (k : ℕ) → Measure (TreeSample Ω k)
  | 0 => p
  | k + 1 => Measure.pi (fun _ : Fin 3 => treeLaw p k)

instance treeLaw_probability {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω)
    [IsProbabilityMeasure p] : (k : ℕ) → IsProbabilityMeasure (treeLaw p k)
  | 0 => inferInstanceAs (IsProbabilityMeasure p)
  | k + 1 => by
      have := treeLaw_probability p k
      exact inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin 3 => treeLaw p k)))

lemma measurable_treeValue {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}
    (hX : Measurable X) (k : ℕ) : Measurable (treeValue X k) := by
  induction k with
  | zero => exact hX
  | succ k ih =>
      have h (i : Fin 3) : Measurable (fun ξ : TreeSample Ω (k+1) => treeValue X k (ξ i)) :=
        ih.comp (measurable_pi_apply i)
      exact ((h 0).min (h 1)).max (((h 1).min (h 2)).max ((h 2).min (h 0)))

lemma treeValue_deviation {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω}
    [IsProbabilityMeasure p] {X : Ω → ℝ} (hX : Measurable X)
    {m r : ℝ} (hb : p {ω | r < |X ω - m|} ≤ ENNReal.ofReal (1/12)) (k : ℕ) :
    treeLaw p k {ω | r < |treeValue X k ω - m|} ≤
      ENNReal.ofReal ((1/3 : ℝ) * (1/4 : ℝ) ^ (2^k)) := by
  induction k with
  | zero =>
    change p {ω | r < |X ω - m|} ≤ ENNReal.ofReal ((1/3 : ℝ) * (1/4 : ℝ) ^ (2^0))
    convert hb using 1; norm_num
  | succ k ih =>
    have hm := measurable_treeValue hX k
    have hi := iIndepFun_pi (μ := fun _ : Fin 3 => treeLaw p k) (fun _ : Fin 3 => hm.aemeasurable)
    have hs : MeasurableSet {ω | r < |treeValue X k ω - m|} :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hm.sub_const m))
    have hc (i : Fin 3) :
        treeLaw p (k+1) {ω | r < |treeValue X k (ω i) - m|} ≤
          ENNReal.ofReal ((1/3 : ℝ) * (1/4 : ℝ) ^ (2^k)) := by
      have hp := measurePreserving_eval (fun _ : Fin 3 => treeLaw p k) i
      have he := hp.measure_preimage hs.nullMeasurableSet
      exact he.trans_le ih
    have h := median3_deviation (hi.indepFun (by decide : (0 : Fin 3) ≠ 1))
      (hi.indepFun (by decide : (1 : Fin 3) ≠ 2))
      (hi.indepFun (by decide : (2 : Fin 3) ≠ 0)) (hc 0) (hc 1) (hc 2)
    change treeLaw p (k+1) {ω | r < |treeValue X (k+1) ω - m|} ≤ _ at h
    refine h.trans_eq ?_
    rw [← ENNReal.ofReal_pow (by positivity)]
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    rw [pow_succ (2 : ℕ) k, pow_mul]
    ring

lemma averaged_tree_deviation {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω}
    [IsProbabilityMeasure p] {X : Ω → ℝ} (hX : Measurable X)
    {b σ a : ℝ} (ha : 0 < a) (hmean : (∫ ω, X ω ∂p) = b)
    (hi : Integrable (fun ω => (X ω - b)^2) p)
    (hv : (∫ ω, (X ω - b)^2 ∂p) ≤ σ^2) (k : ℕ) :
    let n := max 1 ⌈12 * σ^2 / a^2⌉₊
    treeLaw (Measure.pi fun _ : Fin n => p) k
      {ω | a < |treeValue (fun ξ : Fin n → Ω => (∑ i, X (ξ i)) / n) k ω - b|} ≤
      ENNReal.ofReal ((1/3 : ℝ) * (1/4 : ℝ) ^ (2^k)) := by
  dsimp only
  let n := max 1 ⌈12 * σ^2 / a^2⌉₊
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnat : ⌈12 * σ^2 / a^2⌉₊ ≤ n := le_max_right _ _
  have hceil : 12 * σ^2 / a^2 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnat)
  have hden : 0 < (n : ℝ) * a^2 := mul_pos hn' (sq_pos_of_pos ha)
  have hbound : σ^2 / ((n : ℝ) * a^2) ≤ 1/12 := by
    have hh := (div_le_iff₀ (sq_pos_of_pos ha)).mp hceil
    apply (div_le_iff₀ hden).mpr
    nlinarith
  apply treeValue_deviation (by fun_prop)
  have hd := (average_deviation_of_centered hX hmean hi hv hn ha).trans
    (ENNReal.ofReal_le_ofReal hbound)
  exact (measure_mono (show {ω : Fin n → Ω | a < |(∑ i, X (ω i)) / n - b|} ⊆
    {ω | a ≤ |(∑ i, X (ω i)) / n - b|} from fun ω hω => le_of_lt (show a < |(∑ i, X (ω i)) / n - b| from hω))).trans hd

lemma tree_depth_tail {δ : ℝ} (hδ : 0 < δ) :
    let k := Nat.clog 2 ⌈Real.log (1/δ) / Real.log 4⌉₊
    (1/3 : ℝ) * (1/4 : ℝ) ^ (2^k) ≤ δ := by
  dsimp only
  let n := ⌈Real.log (1/δ) / Real.log 4⌉₊
  let k := Nat.clog 2 n
  have hl : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hn : Real.log (1/δ) / Real.log 4 ≤ ((2^k : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) n)
  have hh := (div_le_iff₀ hl).mp hn
  rw [one_div, Real.log_inv] at hh
  have hp : (0 : ℝ) < (1/4 : ℝ) ^ (2^k) := by positivity
  have hb : (1/4 : ℝ) ^ (2^k) ≤ δ := by
    apply (Real.log_le_log_iff hp hδ).mp
    rw [Real.log_pow, one_div, Real.log_inv]
    linarith
  exact (mul_le_of_le_one_left hp.le (by norm_num : (1/3 : ℝ) ≤ 1)).trans hb

lemma averaged_tree_confidence {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω}
    [IsProbabilityMeasure p] {X : Ω → ℝ} (hX : Measurable X)
    {b σ a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hmean : (∫ ω, X ω ∂p) = b)
    (hi : Integrable (fun ω => (X ω - b)^2) p)
    (hv : (∫ ω, (X ω - b)^2 ∂p) ≤ σ^2) :
    let n := max 1 ⌈12 * σ^2 / a^2⌉₊
    let k := Nat.clog 2 ⌈Real.log (1/δ) / Real.log 4⌉₊
    treeLaw (Measure.pi fun _ : Fin n => p) k
      {ω | a < |treeValue (fun ξ : Fin n → Ω => (∑ i, X (ξ i)) / n) k ω - b|} ≤
      ENNReal.ofReal δ := by
  exact (averaged_tree_deviation hX ha hmean hi hv _).trans
    (ENNReal.ofReal_le_ofReal (tree_depth_tail hδ))

def consPathEquiv (k : ℕ) : (Fin 3 × (Fin k → Fin 3)) ≃ (Fin (k+1) → Fin 3) where
  toFun v := Fin.cons v.1 v.2
  invFun v := (v 0, Fin.tail v)
  left_inv := by intro v; simp
  right_inv := by intro v; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def packTree {Ω : Type*} : (k : ℕ) → ((Fin k → Fin 3) → Ω) → TreeSample Ω k
  | 0, ξ => ξ (fun i => Fin.elim0 i)
  | k+1, ξ => fun i => packTree k (fun path => ξ (Fin.cons i path))

lemma packTree_law {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω)
    [IsProbabilityMeasure p] (k : ℕ) :
    MeasurePreserving (packTree (Ω := Ω) k)
      (Measure.pi fun _ : Fin k → Fin 3 => p) (treeLaw p k) := by
  induction k with
  | zero => exact measurePreserving_eval _ _
  | succ k ih =>
    have hr := measurePreserving_piCongrLeft
      (fun _ : Fin 3 × (Fin k → Fin 3) => p) (consPathEquiv k).symm
    have hc : MeasurePreserving (MeasurableEquiv.curry (Fin 3) (Fin k → Fin 3) Ω)
        (Measure.pi fun _ : Fin 3 × (Fin k → Fin 3) => p)
        (Measure.pi fun _ : Fin 3 => Measure.pi fun _ : Fin k → Fin 3 => p) := by
      refine ⟨(MeasurableEquiv.curry (Fin 3) (Fin k → Fin 3) Ω).measurable, ?_⟩
      simpa only [Measure.infinitePi_eq_pi] using
        (Measure.infinitePi_map_curry (fun (_ : Fin 3) (_ : Fin k → Fin 3) => p))
    have hp := measurePreserving_pi
      (fun _ : Fin 3 => Measure.pi fun _ : Fin k → Fin 3 => p)
      (fun _ : Fin 3 => treeLaw p k) (fun _ => ih)
    exact hp.comp (hc.comp hr)

def pathIndex : (k : ℕ) → (Fin k → Fin 3) → ℕ
  | 0, _ => 0
  | k+1, path => (path 0).val * 3^k + pathIndex k (Fin.tail path)

lemma pathIndex_lt (k : ℕ) (path : Fin k → Fin 3) : pathIndex k path < 3^k := by
  induction k with
  | zero => simp [pathIndex]
  | succ k ih =>
    have ht := ih (Fin.tail path)
    have hh := (path 0).isLt
    simp only [pathIndex, pow_succ]
    nlinarith

lemma pathIndex_injective (k : ℕ) : Function.Injective (pathIndex k) := by
  induction k with
  | zero => intro a b h; ext i; exact Fin.elim0 i
  | succ k ih =>
    intro a b h
    have hp : 0 < 3^k := by positivity
    have ha := pathIndex_lt k (Fin.tail a)
    have hb := pathIndex_lt k (Fin.tail b)
    have hd := congrArg (fun n => n / 3^k) h
    dsimp only [pathIndex] at hd h
    rw [Nat.mul_comm (a 0).val, Nat.mul_comm (b 0).val,
      Nat.mul_add_div hp, Nat.mul_add_div hp, Nat.div_eq_of_lt ha,
      Nat.div_eq_of_lt hb] at hd
    simp only [Nat.add_zero] at hd
    have hhead : a 0 = b 0 := Fin.ext hd
    have htail : Fin.tail a = Fin.tail b := ih (by rw [hd] at h; exact Nat.add_left_cancel h)
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrArg Fin.val hhead
    · exact congrArg Fin.val (congrFun htail j)

lemma indexed_tree_law {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω)
    [IsProbabilityMeasure p] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hind : iIndepFun (fun i (ξ : ℕ → Ω) => ξ i) P)
    (hmarg : ∀ i, P.map (fun ξ => ξ i) = p) (k j : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => packTree k (fun path => ξ (j*3^k+pathIndex k path)))
      P (treeLaw p k) := by
  have hi : Function.Injective (fun path : Fin k → Fin 3 => j*3^k+pathIndex k path) := by
    intro a b h
    exact pathIndex_injective k (Nat.add_left_cancel h)
  have hp : MeasurePreserving (fun ξ : ℕ → Ω => fun path : Fin k → Fin 3 =>
      ξ (j*3^k+pathIndex k path)) P (Measure.pi fun _ : Fin k → Fin 3 => p) := by
    refine ⟨by fun_prop, ?_⟩
    have h := (iIndepFun_iff_map_fun_eq_pi_map
      (fun path => (measurable_pi_apply (j*3^k+pathIndex k path)).aemeasurable)).mp
      (hind.precomp hi)
    simpa only [hmarg] using h
  exact (packTree_law p k).comp hp

end OracleTemplate.FiniteVariance

end

section

open MeasureTheory
open OracleTemplate.StochasticGradient OracleTemplate.HeavyTailedMarkovGradient
open LongTails.Setups.StochasticSmoothAndConvex

namespace OracleTemplate.FiniteVariance

lemma output_liftState {Q U : Type} (A : Algorithm Q ℝ U) (k : ℕ) (s : A.State) :
    (robustify k A).output (liftState k A s) = A.output s := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih => exact ih (medianBatched A) _

lemma advance_robustify {Q U : Type} (g : Q → ℕ → ℝ) (A : Algorithm Q ℝ U)
    (k K j : ℕ) (s : A.State) :
    advance (fun call state => (robustify k A).update state
        (g (((robustify k A).query state).2) call)) (K * 3^k) (j * 3^k) (liftState k A s) =
      liftState k A (advance (fun call state => A.update state (blockValue g k ((A.query state).2) call)) K j s) := by
  induction k generalizing A K j with
  | zero => simp [robustify, liftState, blockValue]
  | succ k ih =>
    change advance (fun call state => (robustify k (medianBatched A)).update state
      (g (((robustify k (medianBatched A)).query state).2) call))
      (K * 3^(k+1)) (j * 3^(k+1)) (liftState k (medianBatched A) (0,s,fun _ => 0)) = _
    erw [show K * 3^(k+1) = (K*3) * 3^k by ring,
      show j * 3^(k+1) = (j*3) * 3^k by ring, ih]
    have hb := advance_batched (by decide : 0 < 3) A (fun s _ => (A.query s).2)
      (fun _ v => median3 (v 0) (v 1) (v 2)) 0
      (fun x call => blockValue g k x call) (fun call => call) K j s
    change advance (fun call state => (medianBatched A).update state
      (blockValue g k (((medianBatched A).query state).2) call)) (K*3) (j*3) (0,s,fun _ => 0) = _ at hb
    erw [hb]
    simp [liftState, blockValue]

lemma initial_liftSeed {Q U : Type} (A : Algorithm Q ℝ U) (k : ℕ) (s : A.Seed) :
    (robustify k A).initial (liftSeed k A s) = liftState k A (A.initial s) := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih => exact ih (medianBatched A) s

lemma execute_robustify {Q U Ω : Type} [MeasurableSpace Ω]
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (g : Q → Ω → ℝ)
    (A : Algorithm Q ℝ U) (k K : ℕ) (s : A.Seed) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (robustify k A) (fun _ => (K * 3^k)) (liftSeed k A s) ξ =
      A.output (advance (fun call state => A.update state
        (blockValue (fun x i => g x (ξ i)) k ((A.query state).2) call)) K 0 (A.initial s)) := by
  rw [execute_advance, initial_liftSeed]
  have h := advance_robustify (fun x i => g x (ξ i)) A k K 0 (A.initial s)
  simp only [Nat.zero_mul] at h
  rw [h, output_liftState]

lemma execute_averagedRobustify {Q U Ω : Type} [MeasurableSpace Ω]
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (g : Q → Ω → ℝ)
    {n : ℕ} (hn : 0 < n) (A : Algorithm Q ℝ U) (k K : ℕ) (s : A.Seed) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (averagedRobustify hn k A) (fun _ => (K * 3^k * n)) (liftSeed k A s) ξ =
      A.output (advance (fun call state => A.update state
        (blockValue (fun x j => (∑ i : Fin n, g x (ξ (j*n+i.val))) / n)
          k ((A.query state).2) call)) K 0 (A.initial s)) := by
  dsimp only [averagedRobustify]
  rw [execute_batched, initial_liftSeed]
  have h := advance_robustify (fun x j => (∑ i : Fin n, g x (ξ (j*n+i.val))) / n)
    A k K 0 (A.initial s)
  simp only [Nat.zero_mul] at h
  rw [h, output_liftState]

lemma liftSeed_law {Q U : Type} (A : Algorithm Q ℝ U) (k : ℕ) :
    MeasurePreserving (liftSeed k A) (A.law : Measure A.Seed)
      ((robustify k A).law : Measure (robustify k A).Seed) := by
  induction k generalizing A with
  | zero => exact MeasurePreserving.id _
  | succ k ih => exact ih (medianBatched A)

end OracleTemplate.FiniteVariance

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OracleTemplate.FiniteVariance

lemma averaged_indexed_tree_law {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω)
    [IsProbabilityMeasure p] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hind : iIndepFun (fun i (ξ : ℕ → Ω) => ξ i) P)
    (hmarg : ∀ i, P.map (fun ξ => ξ i) = p) {n : ℕ} (hn : 0 < n) (k j : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => packTree k (fun path => fun i : Fin n =>
      ξ ((j*3^k+pathIndex k path)*n+i.val))) P (treeLaw (Measure.pi fun _ : Fin n => p) k) := by
  let index : (Fin k → Fin 3) × Fin n → ℕ := fun v =>
    (j*3^k+pathIndex k v.1)*n+v.2.val
  have hi : Function.Injective index := by
    intro a b h
    have hd := congrArg (fun t => t / n) h
    dsimp only [index] at hd h
    rw [Nat.mul_comm (j*3^k+pathIndex k a.1), Nat.mul_comm (j*3^k+pathIndex k b.1),
      Nat.mul_add_div hn, Nat.mul_add_div hn, Nat.div_eq_of_lt a.2.isLt,
      Nat.div_eq_of_lt b.2.isLt] at hd
    simp only [Nat.add_zero] at hd
    have hpath := pathIndex_injective k (Nat.add_left_cancel hd)
    have hfin : a.2 = b.2 := Fin.ext (by rw [hpath] at h; exact Nat.add_left_cancel h)
    exact Prod.ext hpath hfin
  have hp : MeasurePreserving (fun ξ : ℕ → Ω => fun v => ξ (index v))
      P (Measure.pi fun _ : (Fin k → Fin 3) × Fin n => p) := by
    refine ⟨by fun_prop, ?_⟩
    have h := (iIndepFun_iff_map_fun_eq_pi_map
      (fun v => (measurable_pi_apply (index v)).aemeasurable)).mp (hind.precomp hi)
    simpa only [hmarg] using h
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin k → Fin 3) (Fin n) Ω)
      (Measure.pi fun _ : (Fin k → Fin 3) × Fin n => p)
      (Measure.pi fun _ : Fin k → Fin 3 => Measure.pi fun _ : Fin n => p) := by
    refine ⟨(MeasurableEquiv.curry (Fin k → Fin 3) (Fin n) Ω).measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry (fun (_ : Fin k → Fin 3) (_ : Fin n) => p))
  exact (packTree_law (Measure.pi fun _ : Fin n => p) k).comp (hc.comp hp)

lemma blockValue_eq_tree {Q : Type} {Ω : Type*} {n : ℕ} (X : Q → (Fin n → Ω) → ℝ)
    (ξ : ℕ → Ω) (k : ℕ) (x : Q) (j : ℕ) :
    blockValue (fun y q => X y (fun i => ξ (q*n+i.val))) k x j =
      treeValue (X x) k (packTree k (fun path => fun i : Fin n =>
        ξ ((j*3^k+pathIndex k path)*n+i.val))) := by
  induction k generalizing j with
  | zero => simp [blockValue, treeValue, packTree, pathIndex]
  | succ k ih =>
    simp only [blockValue, treeValue, packTree]
    rw [ih, ih, ih]
    congr 1 <;> apply congrArg (fun y => treeValue (X x) k (packTree k y)) <;>
      funext path t <;> congr 1 <;> simp [pathIndex, pow_succ] <;> ring_nf <;> simp

lemma block_value_confidence {Q Ω : Type} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hind : iIndepFun (fun i (ξ : ℕ → Ω) => ξ i) P)
    (hmarg : ∀ i, P.map (fun ξ => ξ i) = p)
    (g : Q → Ω → ℝ) (x : Q) (hX : Measurable (g x))
    {b σ a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hmean : (∫ ω, g x ω ∂p) = b)
    (hi : Integrable (fun ω => (g x ω - b)^2) p)
    (hv : (∫ ω, (g x ω - b)^2 ∂p) ≤ σ^2) (j : ℕ) :
    let n := max 1 ⌈12 * σ^2 / a^2⌉₊
    let k := Nat.clog 2 ⌈Real.log (1/δ) / Real.log 4⌉₊
    P {ξ | a < |blockValue (fun y q => (∑ i : Fin n, g y (ξ (q*n+i.val))) / n) k x j - b|} ≤
      ENNReal.ofReal δ := by
  dsimp only
  let n := max 1 ⌈12 * σ^2 / a^2⌉₊
  let k := Nat.clog 2 ⌈Real.log (1/δ) / Real.log 4⌉₊
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hp := averaged_indexed_tree_law p P hind hmarg hn k j
  have hm : Measurable (treeValue (fun ξ : Fin n → Ω => (∑ i, g x (ξ i)) / n) k) :=
    measurable_treeValue (by fun_prop) k
  have hs : MeasurableSet {ω | a < |treeValue (fun ξ : Fin n → Ω => (∑ i, g x (ξ i)) / n) k ω - b|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hm.sub_const b))
  have he := hp.measure_preimage hs.nullMeasurableSet
  have hbound := averaged_tree_confidence hX ha hδ hmean hi hv
  dsimp only at hbound
  rw [← he] at hbound
  have heq (ξ : ℕ → Ω) := blockValue_eq_tree
    (fun (y : Q) (v : Fin n → Ω) => (∑ i, g y (v i)) / n) ξ k x j
  convert hbound using 1
  congr 1
  ext ξ
  change (a < |blockValue (fun y q => (∑ i : Fin n, g y (ξ (q*n+i.val))) / n) k x j - b|) ↔ _
  rw [heq ξ]
  rfl

lemma execute_valueRequest {Q Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Q → Ω → ℝ) (x : Q)
    {n : ℕ} (hn : 0 < n) (k : ℕ) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, y) ω => g y ω }
      (averagedRobustify hn k (valueRequest x)) (fun _ => (3^k*n))
      (liftSeed k (valueRequest x) ()) ξ =
      blockValue (fun y q => (∑ i : Fin n, g y (ξ (q*n+i.val))) / n) k x 0 := by
  simpa [valueRequest, OracleTemplate.StochasticGradient.advance] using
    execute_averagedRobustify P g hn (valueRequest x) k 1 () ξ

attribute [local irreducible] robustify medianBatched blockValue treeValue packTree pathIndex liftSeed

lemma execute_value_confidence {Q Ω : Type} [MeasurableSpace Ω]
    (p : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hind : iIndepFun (fun i (ξ : ℕ → Ω) => ξ i) (P : Measure _))
    (hmarg : ∀ i, (P : Measure (ℕ → Ω)).map (fun ξ : ℕ → Ω => ξ i) = (p : Measure Ω))
    (g : Q → Ω → ℝ) (x : Q) (hX : Measurable (g x))
    {b σ a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hmean : (∫ ω, g x ω ∂(p : Measure _)) = b)
    (hi : Integrable (fun ω => (g x ω - b)^2) (p : Measure _))
    (hv : (∫ ω, (g x ω - b)^2 ∂(p : Measure _)) ≤ σ^2) :
    let n := max 1 ⌈12 * σ^2 / a^2⌉₊
    let k := Nat.clog 2 ⌈Real.log (1/δ) / Real.log 4⌉₊
    let hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    (P : Measure _) {ξ | a < |(execute
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, y) ω => g y ω }
      (averagedRobustify hn k (valueRequest x)) (fun _ => (3^k*n))
      (liftSeed k (valueRequest x) ()) ξ) - b|} ≤ ENNReal.ofReal δ := by
  dsimp only
  simp_rw [execute_valueRequest]
  exact block_value_confidence (p : Measure Ω) (P : Measure (ℕ → Ω)) hind hmarg g x hX
    (b := b) (σ := σ) (a := a) (δ := δ) ha hδ hmean hi hv 0

end OracleTemplate.FiniteVariance

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OracleTemplate.FiniteVariance

lemma measurable_averaged_blockValue {Q Ω : Type} [MeasurableSpace Q] [MeasurableSpace Ω]
    {g : Q → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (n k j : ℕ) :
    Measurable (fun v : Q × (ℕ → Ω) => blockValue
      (fun y q => (∑ i : Fin n, g y (v.2 (q*n+i.val))) / n) k v.1 j) := by
  induction k generalizing j with
  | zero =>
    simp only [blockValue]
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i hi
    exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd))
  | succ k ih =>
    change Measurable (fun v : Q × (ℕ → Ω) => median3
      (blockValue (fun y q => (∑ i : Fin n, g y (v.2 (q*n+i.val))) / n) k v.1 (j*3))
      (blockValue (fun y q => (∑ i : Fin n, g y (v.2 (q*n+i.val))) / n) k v.1 (j*3+1))
      (blockValue (fun y q => (∑ i : Fin n, g y (v.2 (q*n+i.val))) / n) k v.1 (j*3+2)))
    exact ((ih _).min (ih _)).max (((ih _).min (ih _)).max ((ih _).min (ih _)))

lemma independent_query_confidence {Q Ω : Type} [MeasurableSpace Q] [MeasurableSpace Ω]
    (H : Measure Q) [IsProbabilityMeasure H] (p : Measure Ω) [IsProbabilityMeasure p]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hind : iIndepFun (fun i (ξ : ℕ → Ω) => ξ i) P)
    (hmarg : ∀ i, P.map (fun ξ => ξ i) = p)
    {g : Q → Ω → ℝ} (hg : Measurable (Function.uncurry g)) {f : Q → ℝ} (hf : Measurable f)
    {σ a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hi : ∀ x, Integrable (fun ω => (g x ω - f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x)^2 ∂p) ≤ σ^2) (j : ℕ) :
    let n := max 1 ⌈12 * σ^2 / a^2⌉₊
    let k := Nat.clog 2 ⌈Real.log (1/δ) / Real.log 4⌉₊
    (H.prod P) {v | a < |blockValue
      (fun y q => (∑ i : Fin n, g y (v.2 (q*n+i.val))) / n) k v.1 j - f v.1|} ≤
      ENNReal.ofReal δ := by
  dsimp only
  let n := max 1 ⌈12 * σ^2 / a^2⌉₊
  let k := Nat.clog 2 ⌈Real.log (1/δ) / Real.log 4⌉₊
  have hs : MeasurableSet {v : Q × (ℕ → Ω) | a < |blockValue
      (fun y q => (∑ i : Fin n, g y (v.2 (q*n+i.val))) / n) k v.1 j - f v.1|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp
      ((measurable_averaged_blockValue hg n k j).sub (hf.comp measurable_fst)))
  rw [Measure.prod_apply hs]
  calc
    _ ≤ ∫⁻ _ : Q, ENNReal.ofReal δ ∂H := by
      apply lintegral_mono
      intro x
      exact block_value_confidence p P hind hmarg g x hg.of_uncurry_left
        (σ := σ) ha hδ (hmean x) (hi x) (hv x) j
    _ = ENNReal.ofReal δ := by simp

end OracleTemplate.FiniteVariance

end

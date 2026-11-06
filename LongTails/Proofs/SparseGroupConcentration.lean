import LongTails.Proofs.SparseGroupEmpirical

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LongTails.Proofs.SparseGroupConcentration

open LongTails.Setups.OptimumGapGroupDro LongTails.Algorithms.SparseGroupSampling
open SparseGroupEmpirical

lemma iid_loss_mean (q : Public) (p : ProbabilityMeasure (Rows q))
    (P : ProbabilityMeasure (Reservoir q))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ω : Reservoir q) => ω k) (p : Measure _) (P : Measure _))
    (i : Fin q.K) (k : ℕ) (x : Space q.d)
    (hm : Measurable (Function.uncurry q.loss)) :
    (∫ ω : Reservoir q, q.loss x (ω k i) ∂(P : Measure _)) = risk q p i x := by
  have hf : Measurable (fun z : Rows q => q.loss x (z i)) :=
    hm.comp (measurable_const.prodMk (measurable_pi_apply i))
  have h := integral_map (μ := (P : Measure _)) (hIID.measurable k).aemeasurable hf.aestronglyMeasurable
  rw [hIID.marginal] at h
  exact h.symm

lemma iid_loss_independent (q : Public) (p : ProbabilityMeasure (Rows q))
    (P : ProbabilityMeasure (Reservoir q))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ω : Reservoir q) => ω k) (p : Measure _) (P : Measure _))
    (i : Fin q.K) (n : ℕ) (x : Space q.d)
    (hm : Measurable (Function.uncurry q.loss)) :
    iIndepFun (fun k : Fin n => fun ω : Reservoir q => q.loss x (ω k i)) (P : Measure _) := by
  have hf : Measurable (fun z : Rows q => q.loss x (z i)) :=
    hm.comp (measurable_const.prodMk (measurable_pi_apply i))
  exact (hIID.independent.precomp (g := fun k : Fin n => k.val) Fin.val_injective).comp
    (fun _ z => q.loss x (z i)) (fun _ => hf)

lemma empirical_tail (q : Public) (p : ProbabilityMeasure (Rows q))
    (P : ProbabilityMeasure (Reservoir q))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ω : Reservoir q) => ω k) (p : Measure _) (P : Measure _))
    (i : Fin q.K) (n : ℕ) (hn : 0 < n) {x : Space q.d} (hx : x ∈ q.domain)
    (hm : Measurable (Function.uncurry q.loss))
    (hb : ∀ z, ∀ x ∈ q.domain, 0 ≤ q.loss x z ∧ q.loss x z ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) :
    (P : Measure _).real {ω | r < |empirical q ω i n x - risk q p i x|} ≤
      2 * Real.exp (-2 * n * r ^ 2) := by
  have hf : Measurable (fun z : Rows q => q.loss x (z i)) :=
    hm.comp (measurable_const.prodMk (measurable_pi_apply i))
  have he (ω : Reservoir q) : empirical q ω i n x =
      (∑ k : Fin n, q.loss x (ω k i)) / n := by
    rw [Fin.sum_univ_eq_sum_range (fun k => q.loss x (ω k i)) n]
    rfl
  simp_rw [he]
  apply SparseConfidenceProbability.bounded_mean_abs_tail (P : Measure _) hn
    (fun k : Fin n => fun ω : Reservoir q => q.loss x (ω k i))
  · intro k
    exact hf.comp (hIID.measurable k)
  · exact iid_loss_independent q p P hIID i n x hm
  · intro k ω
    exact hb (ω k i) x hx
  · intro k
    exact iid_loss_mean q p P hIID i k x hm
  · exact hr

lemma empirical_radius_tail (q : Public) (p : ProbabilityMeasure (Rows q))
    (P : ProbabilityMeasure (Reservoir q))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ω : Reservoir q) => ω k) (p : Measure _) (P : Measure _))
    (i : Fin q.K) (n : ℕ) {x : Space q.d} (hx : x ∈ q.domain)
    (hm : Measurable (Function.uncurry q.loss))
    (hb : ∀ z, ∀ x ∈ q.domain, 0 ≤ q.loss x z ∧ q.loss x z ≤ 1)
    (hL : 0 ≤ confidenceLog q) :
    (P : Measure _).real {ω | radius q n < |empirical q ω i n x - risk q p i x|} ≤
      2 * Real.exp (-16 * confidenceLog q) := by
  have hrisk := risk_bounds q p i hx hm hb
  have hbounded (ω : Reservoir q) : |empirical q ω i n x - risk q p i x| ≤ 1 := by
    have he := empirical_bounds q ω i n hx hb
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  by_cases hcap : radius q n = 1
  · have he : {ω | radius q n < |empirical q ω i n x - risk q p i x|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [hcap]
      exact not_lt_of_ge (hbounded ω)
    rw [he, measureReal_empty]
    positivity
  have hn : n ≠ 0 := by intro hn; apply hcap; simp [radius, hn]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hr : radius q n = Real.sqrt (8 * confidenceLog q / n) := by
    rw [radius, ite_eq_right hn] at hcap ⊢
    exact min_eq_right (le_of_not_ge (by intro h; exact hcap (min_eq_left h)))
  have h := empirical_tail q p P hIID i n (Nat.pos_of_ne_zero hn) hx hm hb
    (radius q n) (radius_nonneg q n)
  have he : -2 * (n : ℝ) * radius q n ^ 2 = -16 * confidenceLog q := by
    rw [hr, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  simpa only [he] using h

def Confidence (q : Public) (p : ProbabilityMeasure (Rows q)) (T : ℕ)
    (ω : Reservoir q) : Prop :=
  ∀ i, ∀ h : PrimalIndex q, ∀ n ≤ T,
    |empirical q ω i n h.val - risk q p i h.val| ≤ radius q n

lemma confidence_failure_le (q : Public) (p : ProbabilityMeasure (Rows q))
    (P : ProbabilityMeasure (Reservoir q))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ω : Reservoir q) => ω k) (p : Measure _) (P : Measure _))
    (T : ℕ) (hmesh : ∀ h : PrimalIndex q, h.val ∈ q.domain)
    (hm : Measurable (Function.uncurry q.loss))
    (hb : ∀ z, ∀ x ∈ q.domain, 0 ≤ q.loss x z ∧ q.loss x z ≤ 1)
    (hL : 0 ≤ confidenceLog q) :
    (P : Measure _).real {ω | ¬ Confidence q p T ω} ≤
      2 * q.K * (primalMesh q).card * (T + 1 : ℝ) * Real.exp (-16 * confidenceLog q) := by
  classical
  let I := Fin q.K × PrimalIndex q × Fin (T + 1)
  let event : I → Set (Reservoir q) := fun j =>
    {ω | radius q j.2.2 < |empirical q ω j.1 j.2.2 j.2.1.val - risk q p j.1 j.2.1.val|}
  have heq : {ω | ¬ Confidence q p T ω} = ⋃ j, event j := by
    ext ω
    simp only [Set.mem_ofPred_eq, Confidence, not_forall, not_le, Set.mem_iUnion]
    constructor
    · rintro ⟨i, h, n, hn, hn'⟩
      exact ⟨⟨i, h, ⟨n, by omega⟩⟩, hn'⟩
    · rintro ⟨⟨i, h, n⟩, hn⟩
      exact ⟨i, h, n.val, by omega, hn⟩
  rw [heq]
  calc
    _ ≤ ∑ j : I, (P : Measure _).real (event j) := measureReal_iUnion_fintype_le event
    _ ≤ ∑ _j : I, 2 * Real.exp (-16 * confidenceLog q) := by
      apply Finset.sum_le_sum
      intro j _
      exact empirical_radius_tail q p P hIID j.1 j.2.2 (hmesh j.2.1) hm hb hL
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, I, Fintype.card_prod,
        Fintype.card_fin, PrimalIndex, Fintype.card_coe, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

end LongTails.Proofs.SparseGroupConcentration

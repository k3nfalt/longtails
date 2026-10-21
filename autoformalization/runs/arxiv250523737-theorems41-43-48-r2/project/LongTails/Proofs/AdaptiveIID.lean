import LongTails.Algorithms.StochasticGeneralizedAccelerated
import LongTails.Proofs.IIDBlocks
import LongTails.Proofs.NormSubGaussian

open MeasureTheory ProbabilityTheory

namespace LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID

lemma stream_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    (h : IID ξ p P) :
    MeasurePreserving (fun ω k => ξ k ω) P (Measure.infinitePi fun _ : ℕ => p) := by
  refine ⟨Measurable.of_eval h.measurable, ?_⟩
  simpa only [h.marginal] using h.independent.map_fun_eq_infinitePi_map h.measurable

lemma prefix_tail_independent {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    (h : IID ξ p P) (n : ℕ) :
    IndepFun (fun ω (i : Fin n) => ξ i ω) (fun ω (i : ℕ) => ξ (n+i) ω) P := by
  let m : ℕ → MeasurableSpace Ξ := fun i => MeasurableSpace.comap (ξ i) (inferInstance : MeasurableSpace Ω)
  have hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ξ) := fun i => (h.measurable i).comap_le
  have hind : iIndep m P := h.independent
  have hd : Disjoint {i : ℕ | i < n} {i : ℕ | n ≤ i} := by
    exact Set.disjoint_left.mpr (fun i hi hj => Nat.not_lt_of_ge hj hi)
  have hh := indep_iSup_of_disjoint hm hind hd
  change Indep ((inferInstance : MeasurableSpace (Fin n → Ω)).comap
      (fun ω (i : Fin n) => ξ i ω))
    ((inferInstance : MeasurableSpace (ℕ → Ω)).comap (fun ω i => ξ (n+i) ω)) P
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def]
  apply indep_of_indep_of_le hh
  · exact iSup_le (fun i : Fin n => le_iSup_of_le i.val (le_iSup_of_le i.isLt le_rfl))
  · exact iSup_le (fun i : ℕ => le_iSup_of_le (n+i) (le_iSup_of_le (Nat.le_add_right n i) le_rfl))

lemma prefix_tail_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure P] (h : IID ξ p P) (n : ℕ) :
    MeasurePreserving (fun ω => ((fun i : Fin n => ξ i ω), (fun i : ℕ => ξ (n+i) ω)))
      P ((Measure.pi fun _ : Fin n => p).prod (Measure.infinitePi fun _ : ℕ => p)) := by
  have hpre : P.map (fun ω (i : Fin n) => ξ i ω) = Measure.pi (fun _ : Fin n => p) := by
    have hi := h.independent.precomp (g := fun i : Fin n => i.val) Fin.val_injective
    have hp := hi.map_fun_eq_pi_map (fun i : Fin n => (h.measurable i.val).aemeasurable)
    simpa only [h.marginal] using hp
  have htail : P.map (fun ω i => ξ (n+i) ω) = Measure.infinitePi (fun _ : ℕ => p) := by
    have hi := h.independent.precomp (show Function.Injective (fun i : ℕ => n+i) from
      fun _ _ hh => Nat.add_left_cancel hh)
    have hp := hi.map_fun_eq_infinitePi_map (fun i => h.measurable (n+i))
    simpa only [h.marginal] using hp
  have hm := h.measurable
  refine ⟨by fun_prop, ?_⟩
  rw [(h.prefix_tail_independent n).map_prod_eq_prod_map_map (by fun_prop) (by fun_prop), hpre, htail]

end LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

lemma infinitePi_iid {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p] :
    IID (fun k (ξ : ℕ → Ω) => ξ k) p (Measure.infinitePi fun _ : ℕ => p) where
  measurable _ := measurable_pi_apply _
  independent := iIndepFun_infinitePi (X := fun _ (ω : Ω) => ω) (fun _ => measurable_id)
  marginal _ := Measure.infinitePi_map_eval _ _

noncomputable def splitStream {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) :
    (ℕ → Ω) ≃ᵐ ((Fin n → Ω) × (ℕ → Ω)) where
  toFun ξ := (fun i => ξ i, fun i => ξ (n+i))
  invFun z i := if h : i < n then z.1 ⟨i, h⟩ else z.2 (i-n)
  left_inv ξ := by
    funext i
    dsimp
    split_ifs with hi
    · rfl
    · rw [Nat.add_sub_of_le (Nat.le_of_not_gt hi)]
  right_inv z := by
    apply Prod.ext
    · funext i
      simp
    · funext i
      simp
  measurable_toFun := by
    change Measurable (fun ξ : ℕ → Ω => ((fun i : Fin n => ξ i), (fun i : ℕ => ξ (n+i))))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : (Fin n → Ω) × (ℕ → Ω) => fun i =>
      if h : i < n then z.1 ⟨i, h⟩ else z.2 (i-n))
    refine Measurable.of_eval (fun i => ?_)
    by_cases hi : i < n
    · simp only [dite_eq_left hi]
      fun_prop
    · simp only [dite_eq_right hi]
      fun_prop

lemma splitStream_preserving {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (n : ℕ) :
    MeasurePreserving (splitStream (Ω := Ω) n) (Measure.infinitePi fun _ : ℕ => p)
      ((Measure.pi fun _ : Fin n => p).prod (Measure.infinitePi fun _ : ℕ => p)) :=
  (infinitePi_iid p).prefix_tail_law n

noncomputable def accumulated {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (increment : (n : ℕ) → S → (Fin n → Ω) → ℝ) : ℕ → S → (ℕ → Ω) → ℝ
  | 0, _, _ => 0
  | k+1, s, ξ =>
    increment (cost s) s (fun i => ξ i)+
      accumulated cost next increment k (next (cost s) s (fun i => ξ i)) (fun i => ξ (cost s+i))

lemma accumulated_measurable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {cost : S → ℕ} {next : (n : ℕ) → S → (Fin n → Ω) → S}
    {increment : (n : ℕ) → S → (Fin n → Ω) → ℝ}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hi : ∀ n, Measurable (Function.uncurry (increment n))) (k : ℕ) :
    Measurable (Function.uncurry (accumulated cost next increment k)) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    let f : ℕ → (S × (ℕ → Ω)) → ℝ := fun n w =>
      increment n w.1 (fun i => w.2 i)+
        accumulated cost next increment k (next n w.1 (fun i => w.2 i)) (fun i => w.2 (n+i))
    have hf (n : ℕ) : Measurable (f n) := by
      have hblock : Measurable (fun w : S × (ℕ → Ω) => (w.1, (fun i : Fin n => w.2 i))) := by fun_prop
      exact ((hi n).comp hblock).add
        (ih.comp (((hn n).comp hblock).prodMk (by fun_prop)))
    have hp : Measurable (fun w : (S × (ℕ → Ω)) × ℕ => f w.2 w.1) :=
      measurable_from_prod_countable_left hf
    exact hp.comp (measurable_id.prodMk (hc.comp measurable_fst))

lemma accumulated_exp_control {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] {cost : S → ℕ}
    {next : (n : ℕ) → S → (Fin n → Ω) → S}
    {increment : (n : ℕ) → S → (Fin n → Ω) → ℝ}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hi : ∀ n, Measurable (Function.uncurry (increment n)))
    (hint : ∀ s, Integrable (fun b => Real.exp (increment (cost s) s b))
      (Measure.pi fun _ : Fin (cost s) => p))
    (hbound : ∀ s, (∫ b, Real.exp (increment (cost s) s b)
      ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ 1) (k : ℕ) (s : S) :
    Integrable (fun ξ => Real.exp (accumulated cost next increment k s ξ))
      (Measure.infinitePi fun _ : ℕ => p) ∧
      (∫ ξ, Real.exp (accumulated cost next increment k s ξ)
        ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ 1 := by
  induction k generalizing s with
  | zero => simp [accumulated]
  | succ k ih =>
    let m := cost s
    let F : (Fin m → Ω) × (ℕ → Ω) → ℝ := fun z =>
      increment m s z.1+accumulated cost next increment k (next m s z.1) z.2
    have hnext : Measurable (fun b : Fin m → Ω => next m s b) :=
      (hn m).comp measurable_prodMk_left
    have hinc : Measurable (fun b : Fin m → Ω => increment m s b) :=
      (hi m).comp measurable_prodMk_left
    have hF : Measurable F := by
      exact (hinc.comp measurable_fst).add
        ((accumulated_measurable hc hn hi k).comp
          ((hnext.comp measurable_fst).prodMk measurable_snd))
    have hintF (b : Fin m → Ω) : Integrable (fun ξ => Real.exp (F (b, ξ)))
        (Measure.infinitePi fun _ : ℕ => p) := by
      simpa only [F, Real.exp_add] using (ih (next m s b)).1.const_mul (Real.exp (increment m s b))
    have hboundF (b : Fin m → Ω) : (∫ ξ, Real.exp (F (b, ξ))
        ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ Real.exp (increment m s b) := by
      simp only [F, Real.exp_add, integral_const_mul]
      exact mul_le_of_le_one_right (Real.exp_nonneg _) (ih (next m s b)).2
    have hprod := LightTail.integral_prod_exp_control hF hintF hboundF (hint s) (hbound s)
    have hsplit := splitStream_preserving p m
    have he : (fun ξ => Real.exp (accumulated cost next increment (k+1) s ξ)) =
        (fun z => Real.exp (F z)) ∘ splitStream m := rfl
    rw [he]
    refine ⟨hsplit.integrable_comp_of_integrable hprod.1, ?_⟩
    simpa only [Function.comp_def, hsplit.integral_comp' (fun z => Real.exp (F z))] using hprod.2

lemma accumulated_linear {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (f g : (n : ℕ) → S → (Fin n → Ω) → ℝ) (r q : ℝ) (k : ℕ) (s : S) (ξ : ℕ → Ω) :
    accumulated cost next (fun n s b => r*f n s b+q*g n s b) k s ξ =
      r*accumulated cost next f k s ξ+q*accumulated cost next g k s ξ := by
  induction k generalizing s ξ with
  | zero => simp [accumulated]
  | succ k ih =>
    simp only [accumulated, ih]
    ring

lemma prefix_preserving {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (n : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun i : Fin n => ξ i)
      (Measure.infinitePi fun _ : ℕ => p) (Measure.pi fun _ : Fin n => p) :=
  measurePreserving_fst.comp (splitStream_preserving p n)

lemma two_blocks_preserving {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (n : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => ((fun i : Fin n => ξ i), (fun i : Fin n => ξ (n+i))))
      (Measure.infinitePi fun _ : ℕ => p)
      ((Measure.pi fun _ : Fin n => p).prod (Measure.pi fun _ : Fin n => p)) := by
  have hp := (MeasurePreserving.id (Measure.pi fun _ : Fin n => p)).prod (prefix_preserving p n)
  exact hp.comp (splitStream_preserving p n)

lemma finite_two_blocks_preserving {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (n : ℕ) :
    MeasurePreserving (fun ξ : Fin (2*n) → Ω =>
      ((fun i : Fin n => ξ ⟨i, by have hi := i.isLt; omega⟩),
        (fun i : Fin n => ξ ⟨n+i, by have hi := i.isLt; omega⟩)))
      (Measure.pi fun _ : Fin (2*n) => p)
      ((Measure.pi fun _ : Fin n => p).prod (Measure.pi fun _ : Fin n => p)) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← (prefix_preserving p (2*n)).map_eq, Measure.map_map (by fun_prop) (by fun_prop)]
  exact (two_blocks_preserving p n).map_eq

lemma blockTrace_zero {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S) (s : S) (ξ : ℕ → Ω) :
    blockTrace cost next s ξ 0 = (s, ξ) := rfl

lemma blockTrace_succ {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S) (s : S) (ξ : ℕ → Ω) (n : ℕ) :
    blockTrace cost next s ξ (n+1) = blockAdvance cost next (blockTrace cost next s ξ n) :=
  Function.iterate_succ_apply' _ _ _

lemma blockTrace_start_succ {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S) (s : S) (ξ : ℕ → Ω) (n : ℕ) :
    blockTrace cost next s ξ (n+1) =
      blockTrace cost next (next (cost s) s (fun i => ξ i)) (fun i => ξ (cost s+i)) n :=
  Function.iterate_succ_apply _ _ _

lemma blockCalls_succ {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S) (s : S) (ξ : ℕ → Ω) (n : ℕ) :
    blockCalls cost next s ξ (n+1) =
      blockCalls cost next s ξ n+cost (blockTrace cost next s ξ n).1 :=
  Finset.sum_range_succ _ _

lemma blockTrace_tail {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S) (s : S) (ξ : ℕ → Ω) (n k : ℕ) :
    (blockTrace cost next s ξ n).2 k = ξ (blockCalls cost next s ξ n+k) := by
  induction n generalizing k with
  | zero => simp [blockTrace, blockCalls]
  | succ n ih =>
    rw [blockTrace_succ, blockCalls_succ]
    change (blockTrace cost next s ξ n).2 (cost (blockTrace cost next s ξ n).1+k) = _
    rw [ih, Nat.add_assoc]

lemma accumulated_eq_sum {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (increment : (n : ℕ) → S → (Fin n → Ω) → ℝ) (n : ℕ) (s : S) (ξ : ℕ → Ω) :
    accumulated cost next increment n s ξ =
      ∑ i ∈ Finset.range n, increment (cost (blockTrace cost next s ξ i).1)
        (blockTrace cost next s ξ i).1 (fun j => (blockTrace cost next s ξ i).2 j) := by
  induction n generalizing s ξ with
  | zero => simp [accumulated]
  | succ n ih =>
    rw [accumulated, Finset.sum_range_succ']
    rw [ih]
    simp_rw [blockTrace_start_succ, blockTrace_zero]
    exact add_comm _ _

lemma accumulated_nonneg {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (increment : (n : ℕ) → S → (Fin n → Ω) → ℝ)
    (hinc : ∀ n s ξ, 0 ≤ increment n s ξ) (n : ℕ) (s : S) (ξ : ℕ → Ω) :
    0 ≤ accumulated cost next increment n s ξ := by
  rw [accumulated_eq_sum]
  exact Finset.sum_nonneg (fun i _ => hinc _ _ _)

lemma blockTrace_add {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S) (s : S) (ξ : ℕ → Ω) (m n : ℕ) :
    blockTrace cost next s ξ (m+n) =
      blockTrace cost next (blockTrace cost next s ξ m).1 (blockTrace cost next s ξ m).2 n := by
  change (blockAdvance cost next)^[m+n] (s, ξ) =
    (blockAdvance cost next)^[n] ((blockAdvance cost next)^[m] (s, ξ))
  rw [Nat.add_comm, Function.iterate_add_apply]

end OracleTemplate.StochasticGeneralized

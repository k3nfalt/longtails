import LongTails.Proofs.BirchNonEuclideanCoefficients

namespace LongTails.Proofs.BirchNonEuclideanExtensions

open LongTails.Setups.BirchNonEuclidean
open LongTails.Proofs.BirchNonEuclideanSymbolic
open LongTails.Proofs.BirchNonEuclideanCoefficients

lemma sum_extension {ι α : Type*} [AddCommMonoid α]
    (s t : Finset ι) (f g : ι → α) (hst : s ⊆ t)
    (hold : ∀ i ∈ s, g i = f i) (hnew : ∀ i ∈ t, i ∉ s → g i = 0) :
    ∑ i ∈ t, g i = ∑ i ∈ s, f i := by
  rw [← Finset.sum_subset hst hnew]
  exact Finset.sum_congr rfl hold

lemma sharp_raw_outside (a : Program) (e q : ℕ) (hq : q ∉ a.symbolic.queries) :
    (a.symbolic.sharpInputs e).1 q = 0 :=
  (Finsupp.mem_supported' ℝ _).mp ((symbolic_maps_supported a).sharpInputs e).1 q hq

lemma direction_outside (a : Program) (hu : a.symbolic.units = ∅) (j t : ℕ)
    (ht : t ∉ a.symbolic.sharps) :
    (a.symbolic.queryPoints j).2 t = 0 ∧ (a.symbolic.points j).2 t = 0 := by
  have hnot : t ∉ a.symbolic.sharps ∪ a.symbolic.units := by simpa [hu] using ht
  exact ⟨(Finsupp.mem_supported' ℝ _).mp ((symbolic_maps_supported a).queryPoints j).2 t hnot,
    (Finsupp.mem_supported' ℝ _).mp ((symbolic_maps_supported a).points j).2 t hnot⟩

lemma transport_outside (a : Program) (main own : ℕ → ℕ) (η : ℝ) (e t : ℕ)
    (hu : a.symbolic.units = ∅) (ht : t ∉ a.symbolic.sharps) :
    transportCoefficient a main own η e t = 0 := by
  apply Finset.sum_eq_zero
  intro q _
  rw [(direction_outside a hu q t ht).1, (direction_outside a hu (main (own e)) t ht).2]
  simp

structure CertificateExtension (a b : Program) (main : ℕ → ℕ) (K : ℕ) : Prop where
  queries : a.symbolic.queries ⊆ b.symbolic.queries
  sharps : a.symbolic.sharps ⊆ b.symbolic.sharps
  sharpInputs : ∀ e ∈ a.symbolic.sharps, b.symbolic.sharpInputs e = a.symbolic.sharpInputs e
  queryPoints : ∀ q ∈ a.symbolic.queries, b.symbolic.queryPoints q = a.symbolic.queryPoints q
  mainPoints : ∀ k ≤ K, b.symbolic.points (main k) = a.symbolic.points (main k)
  no_units : b.symbolic.units = ∅
  query_linear : ∀ q ∈ b.symbolic.queries, (b.symbolic.queryPoints q).1 = 0
  new_linear : ∀ e ∈ b.symbolic.sharps, e ∉ a.symbolic.sharps → (b.symbolic.sharpInputs e).2 = 0
  new_mass : ∀ e ∈ b.symbolic.sharps, e ∉ a.symbolic.sharps →
    (∑ q ∈ b.symbolic.queries, (b.symbolic.sharpInputs e).1 q) = 1
  output_count : b.outputCount = a.outputCount
  output_points : ∀ j, b.outputPoint j = a.outputPoint (Fin.cast (congrArg (fun n => n + 1) output_count) j)

noncomputable def extendedOwner (a : Program) (own : ℕ → ℕ) (e : ℕ) : ℕ :=
  if e ∈ a.symbolic.sharps then own e else 0

noncomputable def extendedWeight (a : Program) (w : ℕ → ℝ) (e : ℕ) : ℝ :=
  if e ∈ a.symbolic.sharps then w e else 0

lemma extended_owner_old (a : Program) (own : ℕ → ℕ) (e : ℕ) (he : e ∈ a.symbolic.sharps) :
    extendedOwner a own e = own e := by simp [extendedOwner, he]

lemma extended_weight_old (a : Program) (w : ℕ → ℝ) (e : ℕ) (he : e ∈ a.symbolic.sharps) :
    extendedWeight a w e = w e := by simp [extendedWeight, he]

lemma extended_weight_new (a : Program) (w : ℕ → ℝ) (e : ℕ) (he : e ∉ a.symbolic.sharps) :
    extendedWeight a w e = 0 := by simp [extendedWeight, he]

lemma extension_raw_sum {a b : Program} {main : ℕ → ℕ} {K : ℕ}
    (E : CertificateExtension a b main K) (e : ℕ) (he : e ∈ a.symbolic.sharps)
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ q ∈ b.symbolic.queries, f ((b.symbolic.sharpInputs e).1 q)) =
      ∑ q ∈ a.symbolic.queries, f ((a.symbolic.sharpInputs e).1 q) := by
  apply sum_extension _ _ _ _ E.queries
  · intro q _
    rw [E.sharpInputs e he]
  · intro q _ hq
    rw [E.sharpInputs e he, sharp_raw_outside a e q hq, hf]

lemma extension_transport {a b : Program} {main : ℕ → ℕ} {K : ℕ}
    (E : CertificateExtension a b main K) (own : ℕ → ℕ) (η : ℝ)
    (e t : ℕ) (he : e ∈ a.symbolic.sharps) (hk : own e < K) :
    transportCoefficient b main (extendedOwner a own) η e t =
      transportCoefficient a main own η e t := by
  unfold transportCoefficient
  rw [extended_owner_old a own e he, E.mainPoints (own e) hk.le, E.sharpInputs e he]
  apply sum_extension _ _ _ _ E.queries
  · intro q hq
    rw [E.queryPoints q hq]
  · intro q _ hq
    rw [sharp_raw_outside a e q hq]
    simp

lemma extension_row {a b : Program} {main : ℕ → ℕ} {K : ℕ}
    (E : CertificateExtension a b main K) (own : ℕ → ℕ) (η : ℝ)
    (e : ℕ) (he : e ∈ a.symbolic.sharps) (hk : own e < K) (hu : a.symbolic.units = ∅) :
    (∑ t ∈ b.symbolic.sharps, transportCoefficient b main (extendedOwner a own) η e t) =
      ∑ t ∈ a.symbolic.sharps, transportCoefficient a main own η e t := by
  apply sum_extension _ _ _ _ E.sharps
  · intro t _
    exact extension_transport E own η e t he hk
  · intro t _ ht
    rw [extension_transport E own η e t he hk, transport_outside a main own η e t hu ht]

lemma extension_partition_sum {a b : Program} {main : ℕ → ℕ} {K : ℕ} {α : Type*}
    [AddCommMonoid α] [Module ℝ α] (E : CertificateExtension a b main K)
    (own : ℕ → ℕ) (w : ℕ → ℝ) (k : ℕ) (v : ℕ → α) :
    (∑ e ∈ b.symbolic.sharps.filter (fun e => extendedOwner a own e = k), extendedWeight a w e • v e) =
      ∑ e ∈ a.symbolic.sharps.filter (fun e => own e = k), w e • v e := by
  rw [Finset.sum_filter, Finset.sum_filter]
  apply sum_extension _ _ _ _ E.sharps
  · intro e he
    rw [extended_owner_old a own e he, extended_weight_old a w e he]
  · intro e _ he
    rw [extended_weight_new a w e he]
    simp

noncomputable def extendCertificate {a b : Program} {K : ℕ} {η D V : ℝ}
    (C : ProgramCertificate a K η D V) (E : CertificateExtension a b C.main K) :
    ProgramCertificate b K η D V := by
  refine {
    main := C.main
    owner := extendedOwner a C.owner
    weight := extendedWeight a C.weight
    positive_horizon := C.positive_horizon
    sharp_only := E.no_units
    estimator_linear := ?_
    estimator_mass := ?_
    query_linear := E.query_linear
    main_initial := C.main_initial
    main_linear := fun k hk => by rw [E.mainPoints k hk]; exact C.main_linear k hk
    weight_nonneg := ?_
    owner_lt := ?_
    partition := ?_
    chain := ?_
    output_count := by rw [E.output_count, C.output_count]
    output_indices := ?_
    transport := ?_
    noise := ?_ }
  · intro e he
    by_cases ho : e ∈ a.symbolic.sharps
    · rw [E.sharpInputs e ho]
      exact C.estimator_linear e ho
    · exact E.new_linear e he ho
  · intro e he
    by_cases ho : e ∈ a.symbolic.sharps
    · exact (extension_raw_sum E e ho (fun x => x) rfl).trans (C.estimator_mass e ho)
    · exact E.new_mass e he ho
  · intro e _
    by_cases he : e ∈ a.symbolic.sharps
    · rw [extended_weight_old a C.weight e he]
      exact C.weight_nonneg e he
    · rw [extended_weight_new a C.weight e he]
  · intro e _
    by_cases he : e ∈ a.symbolic.sharps
    · rw [extended_owner_old a C.owner e he]
      exact C.owner_lt e he
    · simpa [extendedOwner, he] using C.positive_horizon
  · intro k hk
    have hh := extension_partition_sum E C.owner C.weight k (fun _ => (1 : ℝ))
    simpa only [smul_eq_mul, mul_one, C.partition k hk] using hh
  · intro k hk
    rw [E.mainPoints (k + 1) (by omega), E.mainPoints k hk.le, extension_partition_sum E]
    exact C.chain k hk
  · intro j
    rw [E.output_points, C.output_indices]
    rfl
  · intro t ht
    have heq : (∑ e ∈ b.symbolic.sharps, extendedWeight a C.weight e *
        (∑ j ∈ b.symbolic.sharps, transportCoefficient b C.main (extendedOwner a C.owner) η e j) *
          transportCoefficient b C.main (extendedOwner a C.owner) η e t) =
        ∑ e ∈ a.symbolic.sharps, C.weight e *
          (∑ j ∈ a.symbolic.sharps, transportCoefficient a C.main C.owner η e j) *
            transportCoefficient a C.main C.owner η e t := by
      apply sum_extension _ _ _ _ E.sharps
      · intro e he
        rw [extended_weight_old a C.weight e he,
          extension_row E C.owner η e he (C.owner_lt e he) C.sharp_only,
          extension_transport E C.owner η e t he (C.owner_lt e he)]
      · intro e _ he
        rw [extended_weight_new a C.weight e he]
        simp
    rw [heq]
    by_cases ho : t ∈ a.symbolic.sharps
    · rw [extended_weight_old a C.weight t ho]
      exact C.transport t ho
    · rw [extended_weight_new a C.weight t ho]
      simp only [transport_outside a C.main C.owner η _ t C.sharp_only ho, mul_zero, Finset.sum_const_zero, le_refl]
  · have heq : (∑ e ∈ b.symbolic.sharps, extendedWeight a C.weight e *
        ∑ q ∈ b.symbolic.queries, (b.symbolic.sharpInputs e).1 q ^ 2) =
        ∑ e ∈ a.symbolic.sharps, C.weight e * ∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs e).1 q ^ 2 := by
      apply sum_extension _ _ _ _ E.sharps
      · intro e he
        rw [extended_weight_old a C.weight e he, extension_raw_sum E e he (fun x => x ^ 2) (by norm_num)]
      · intro e _ he
        rw [extended_weight_new a C.weight e he, zero_mul]
    rw [heq]
    exact C.noise

lemma symbolic_sharps_mono (s : SymbolicMemory) (i : Instruction) :
    s.sharps ⊆ (symbolicPerform s i).sharps := by
  cases i <;> simp [symbolicPerform, symbolicStore]

lemma symbolic_fold_sets_mono (code : List Instruction) (s : SymbolicMemory) :
    s.queries ⊆ (code.foldl symbolicPerform s).queries ∧
      s.sharps ⊆ (code.foldl symbolicPerform s).sharps := by
  induction code generalizing s with
  | nil => exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | cons i rest ih =>
      have hh := ih (symbolicPerform s i)
      exact ⟨(symbolic_queries_mono s i).trans hh.1, (symbolic_sharps_mono s i).trans hh.2⟩

lemma program_symbolic_append (a b : Program) (tail : List Instruction)
    (hcode : b.instructions = a.instructions ++ tail) :
    b.symbolic = tail.foldl symbolicPerform a.symbolic := by
  simp only [Program.symbolic, hcode, List.foldl_append]

lemma certificateExtension_of_append {a b : Program} {K : ℕ} {main : ℕ → ℕ}
    (tail : List Instruction) (hcode : b.instructions = a.instructions ++ tail)
    (hm : ∀ k ≤ K, main k < a.symbolic.next)
    (hu : b.symbolic.units = ∅)
    (hql : ∀ q ∈ b.symbolic.queries, (b.symbolic.queryPoints q).1 = 0)
    (hel : ∀ e ∈ b.symbolic.sharps, e ∉ a.symbolic.sharps → (b.symbolic.sharpInputs e).2 = 0)
    (hem : ∀ e ∈ b.symbolic.sharps, e ∉ a.symbolic.sharps →
      (∑ q ∈ b.symbolic.queries, (b.symbolic.sharpInputs e).1 q) = 1)
    (hoc : b.outputCount = a.outputCount)
    (hop : ∀ j, b.outputPoint j = a.outputPoint (Fin.cast (congrArg (fun n => n + 1) hoc) j)) :
    CertificateExtension a b main K := by
  have hs := program_symbolic_append a b tail hcode
  have hb := symbolic_beforeNext a
  have hsets := symbolic_fold_sets_mono tail a.symbolic
  refine {
    queries := by rw [hs]; exact hsets.1
    sharps := by rw [hs]; exact hsets.2
    sharpInputs := ?_
    queryPoints := ?_
    mainPoints := ?_
    no_units := hu
    query_linear := hql
    new_linear := hel
    new_mass := hem
    output_count := hoc
    output_points := hop }
  · intro e he
    rw [hs]
    exact (LongTails.Proofs.BirchNonEuclideanRecords.symbolic_old_records tail a.symbolic e
      (hb.2 e (Finset.mem_union_left _ he))).2
  · intro q hq
    rw [hs]
    exact (LongTails.Proofs.BirchNonEuclideanRecords.symbolic_old_records tail a.symbolic q (hb.1 q hq)).1
  · intro k hk
    rw [hs]
    exact (symbolic_fold_old_values tail a.symbolic (main k) (hm k hk)).1

end LongTails.Proofs.BirchNonEuclideanExtensions

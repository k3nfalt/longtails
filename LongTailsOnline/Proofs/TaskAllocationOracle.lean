import LongTailsOnline.Algorithms.ParallelTaskAllocation

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LongTailsOnline.Proofs.TaskAllocation

open LongTailsOnline.Setups.StationaryTaskAllocation
open LongTailsOnline.Algorithms.ParallelTaskAllocation

lemma component_le_loss {k B : ℕ} (v : Worker k → ℝ) (a : Allocation k B)
    (i : Worker k) : (a.val i).val * v i ≤ loss v a := by
  unfold loss
  exact Finset.le_sup' (fun j : Worker k => ((a.val j).val : ℝ) * v j)
    (Finset.mem_univ i)

lemma loss_le_iff {k B : ℕ} (v : Worker k → ℝ) (a : Allocation k B) (L : ℝ) :
    loss v a ≤ L ↔ ∀ i, (a.val i).val * v i ≤ L := by
  simp [loss, Finset.sup'_le_iff]

lemma optimum_le_loss {k B : ℕ} (v : Worker k → ℝ) (a : Allocation k B) :
    optimum (B := B) v ≤ loss v a :=
  (Classical.choose_spec (Finset.exists_min_image
    (Finset.univ : Finset (Allocation k B)) (loss v) Finset.univ_nonempty)).2
      a (Finset.mem_univ a)

lemma loss_mono {k B : ℕ} {v w : Worker k → ℝ} (h : ∀ i, v i ≤ w i)
    (a : Allocation k B) : loss v a ≤ loss w a := by
  apply (loss_le_iff _ _ _).mpr
  intro i
  exact (mul_le_mul_of_nonneg_left (h i) (Nat.cast_nonneg _)).trans
    (component_le_loss w a i)

lemma optimum_mono {k B : ℕ} {v w : Worker k → ℝ} (h : ∀ i, v i ≤ w i) :
    optimum (B := B) v ≤ optimum (B := B) w :=
  (optimum_le_loss v (oracle w)).trans (loss_mono h (oracle w))

lemma loss_nonneg {k B : ℕ} {v : Worker k → ℝ} (h : ∀ i, 0 ≤ v i)
    (a : Allocation k B) : 0 ≤ loss v a :=
  (mul_nonneg (Nat.cast_nonneg _) (h 0)).trans (component_le_loss v a 0)

lemma optimum_nonneg {k B : ℕ} {v : Worker k → ℝ} (h : ∀ i, 0 ≤ v i) :
    0 ≤ optimum (B := B) v := loss_nonneg h _

lemma confidence_sandwich {k B : ℕ} {s μ u : Worker k → ℝ}
    (hs : ∀ i, s i ≤ μ i) (hu : ∀ i, μ i ≤ u i) :
    optimum (B := B) s ≤ optimum (B := B) μ ∧
      optimum (B := B) μ ≤ optimum (B := B) u :=
  ⟨optimum_mono hs, optimum_mono hu⟩

lemma strict_elimination {k B : ℕ} {s μ u : Worker k → ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hs : ∀ i, s i ≤ μ i) (hu : ∀ i, μ i ≤ u i)
    {i : Worker k} (hi : optimum (B := B) u < s i)
    {a : Allocation k B} (ha : loss μ a = optimum (B := B) μ) :
    (a.val i).val = 0 := by
  by_contra hzero
  have hcount : (1 : ℝ) ≤ (a.val i).val := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
  have hlower : μ i ≤ loss μ a := by
    calc
      μ i = 1 * μ i := (one_mul _).symm
      _ ≤ (a.val i).val * μ i := mul_le_mul_of_nonneg_right hcount (hμ i)
      _ ≤ loss μ a := component_le_loss μ a i
  have hupper := optimum_mono (B := B) hu
  linarith [hs i]

lemma allocation_le_capacity {k B : ℕ} {s : Worker k → ℝ} {L : ℝ}
    {a : Allocation k B} (ha : loss s a ≤ L) (i : Worker k) :
    (a.val i).val ≤ capacity B L s i := by
  have hB : (a.val i).val ≤ B := Nat.le_of_lt_succ (a.val i).isLt
  unfold capacity
  split_ifs with hs
  · exact le_min hB (Nat.le_floor ((le_div_iff₀ hs).mpr
      ((loss_le_iff _ _ _).mp ha i)))
  · exact hB

lemma precision_gap {k B : ℕ} {s u : Worker k → ℝ} {θ : ℝ}
    (hsu : ∀ i, s i ≤ u i)
    (hD : ∀ i, uncertainty B (optimum (B := B) u) s u i ≤ θ) :
    0 ≤ optimum (B := B) u - optimum (B := B) s ∧
      optimum (B := B) u - optimum (B := B) s ≤ θ := by
  refine ⟨sub_nonneg.mpr (optimum_mono hsu), ?_⟩
  have hcap := allocation_le_capacity
    (show loss s (oracle (B := B) s) ≤ optimum (B := B) u from optimum_mono hsu)
  have hloss : loss u (oracle (B := B) s) ≤ optimum (B := B) s + θ := by
    apply (loss_le_iff _ _ _).mpr
    intro i
    have hi : ((oracle (B := B) s).val i).val * s i ≤ optimum (B := B) s :=
      component_le_loss s (oracle (B := B) s) i
    have hmul := mul_le_mul_of_nonneg_right
      (show ((oracle (B := B) s).val i).val ≤
        (capacity B (optimum (B := B) u) s i : ℝ) by exact_mod_cast hcap i)
      (sub_nonneg.mpr (hsu i))
    have hdi := hD i
    unfold uncertainty at hdi
    nlinarith
  linarith [optimum_le_loss u (oracle (B := B) s)]

lemma precision_gap_max {k B : ℕ} {s u : Worker k → ℝ}
    (hsu : ∀ i, s i ≤ u i) :
    0 ≤ optimum (B := B) u - optimum (B := B) s ∧
      optimum (B := B) u - optimum (B := B) s ≤
        Finset.univ.sup' Finset.univ_nonempty
          (uncertainty B (optimum (B := B) u) s u) :=
  precision_gap hsu (fun i => Finset.le_sup' _ (Finset.mem_univ i))

lemma optimistic_regret {k B : ℕ} {s μ u : Worker k → ℝ} {θ : ℝ}
    (hs : ∀ i, s i ≤ μ i) (hu : ∀ i, μ i ≤ u i)
    (hD : ∀ i, uncertainty B (optimum (B := B) u) s u i ≤ θ) :
    loss μ (oracle (B := B) u) - optimum (B := B) μ ≤ θ := by
  have hsu (i) := (hs i).trans (hu i)
  have hgap := (precision_gap hsu hD).2
  have hmono := loss_mono hu (oracle (B := B) u)
  have hopt := optimum_mono (B := B) hs
  change loss μ (oracle (B := B) u) - optimum (B := B) μ ≤ θ
  change loss u (oracle (B := B) u) - loss s (oracle (B := B) s) ≤ θ at hgap
  change loss s (oracle (B := B) s) ≤ optimum (B := B) μ at hopt
  linarith

lemma capacity_load_le {k B : ℕ} {s : Worker k → ℝ} {L : ℝ}
    (hs : ∀ i, 0 ≤ s i) (hL : 0 ≤ L) (i : Worker k) :
    (capacity B L s i : ℝ) * s i ≤ L := by
  unfold capacity
  split_ifs with hi
  · have hmin : ((min B ⌊L / s i⌋₊ : ℕ) : ℝ) ≤ (⌊L / s i⌋₊ : ℝ) := by
      exact_mod_cast min_le_right B ⌊L / s i⌋₊
    have hfloor := Nat.floor_le (div_nonneg hL (hs i))
    exact (mul_le_mul_of_nonneg_right (hmin.trans hfloor) (hs i)).trans
      (le_of_eq (div_mul_cancel₀ L hi.ne'))
  · have hzero : s i = 0 := le_antisymm (le_of_not_gt hi) (hs i)
    simp [hzero, hL]

lemma capacity_regret {k B : ℕ} {s μ u : Worker k → ℝ} {θ : ℝ}
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ μ i) (hu : ∀ i, μ i ≤ u i)
    (hD : ∀ i, uncertainty B (optimum (B := B) u) s u i ≤ θ)
    {a : Allocation k B}
    (ha : ∀ i, (a.val i).val ≤ capacity B (optimum (B := B) u) s i) :
    loss μ a - optimum (B := B) μ ≤ 2 * θ := by
  have hsu (i) := (hs i).trans (hu i)
  have hL := optimum_nonneg (B := B) (fun i => (hs0 i).trans (hsu i))
  have hgap := (precision_gap hsu hD).2
  have hopt := optimum_mono (B := B) hs
  have hloss : loss μ a ≤ optimum (B := B) u + θ := by
    apply (loss_le_iff _ _ _).mpr
    intro i
    have hload := capacity_load_le (B := B) hs0 hL i
    have has : ((a.val i).val : ℝ) * s i ≤ optimum (B := B) u :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast ha i) (hs0 i)).trans hload
    have hdu := mul_le_mul_of_nonneg_right
      (show ((a.val i).val : ℝ) ≤ capacity B (optimum (B := B) u) s i by
        exact_mod_cast ha i) (sub_nonneg.mpr (hsu i))
    have hdi := hD i
    unfold uncertainty at hdi
    have hmu := mul_le_mul_of_nonneg_left (hu i) (Nat.cast_nonneg (a.val i).val)
    nlinarith
  linarith

lemma loss_le_batch {k B : ℕ} {μ : Worker k → ℝ} (hμ : ∀ i, μ i ≤ 1)
    (a : Allocation k B) : loss μ a ≤ B := by
  apply (loss_le_iff _ _ _).mpr
  intro i
  calc
    ((a.val i).val : ℝ) * μ i ≤ (a.val i).val * 1 :=
      mul_le_mul_of_nonneg_left (hμ i) (Nat.cast_nonneg _)
    _ ≤ (B : ℝ) := by
      simpa only [mul_one] using
        (show ((a.val i).val : ℝ) ≤ B by exact_mod_cast Nat.le_of_lt_succ (a.val i).isLt)

lemma regret_bounds (p : Params) (hμ : ∀ i, p.μ i ∈ Set.Ioc (0 : ℝ) 1)
    (h : OnlineTemplate.Trace Unit (Allocation p.config.k p.config.B)
      (Feedback p.config.k p.config.B) Unit p.config.T) :
    0 ≤ regret p h ∧ regret p h ≤ p.config.T * p.config.B := by
  have hμ0 (i) := (hμ i).1.le
  have hμ1 (i) := (hμ i).2
  refine ⟨Finset.sum_nonneg (fun t _ => sub_nonneg.mpr (optimum_le_loss _ _)), ?_⟩
  calc
    regret p h ≤ ∑ _t : Fin p.config.T, (p.config.B : ℝ) := by
      apply Finset.sum_le_sum
      intro t _
      exact sub_le_iff_le_add.mpr ((loss_le_batch hμ1 _).trans
        (le_add_of_nonneg_right (optimum_nonneg hμ0)))
    _ = _ := by simp

@[fun_prop]
lemma measurable_regret (p : Params) : Measurable (regret p) := by
  have hm : Measurable (loss p.μ : Allocation p.config.k p.config.B → ℝ) :=
    measurable_of_countable _
  unfold regret
  fun_prop

lemma integrable_regret (p : Params) (hμ : ∀ i, p.μ i ∈ Set.Ioc (0 : ℝ) 1)
    (law : ProbabilityMeasure (OnlineTemplate.Trace Unit
      (Allocation p.config.k p.config.B) (Feedback p.config.k p.config.B) Unit p.config.T)) :
    Integrable (regret p) law.toMeasure :=
  Integrable.of_mem_Icc 0 (p.config.T * p.config.B) (measurable_regret p).aemeasurable
    (Filter.Eventually.of_forall (regret_bounds p hμ))

lemma exists_bounded_counts {n : ℕ} (c : Fin n → ℕ) (B : ℕ)
    (hB : B ≤ ∑ i, c i) :
    ∃ a : Fin n → ℕ, (∀ i, a i ≤ c i) ∧ ∑ i, a i = B := by
  induction n generalizing B with
  | zero =>
    have hz : B = 0 := by simpa using hB
    subst B
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp⟩
  | succ n ih =>
    have htotal : B ≤ c 0 + ∑ i : Fin n, c i.succ := by
      simpa only [Fin.sum_univ_succ] using hB
    have hrest : B - min B (c 0) ≤ ∑ i : Fin n, c i.succ := by omega
    obtain ⟨a, ha, hsum⟩ := ih (fun i => c i.succ) (B - min B (c 0)) hrest
    refine ⟨Fin.cons (min B (c 0)) a, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simpa using ha j
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hsum]
      omega

lemma exists_allocation_le {k B : ℕ} (c : Worker k → ℕ) (hB : B ≤ ∑ i, c i) :
    ∃ a : Allocation k B, ∀ i, (a.val i).val ≤ c i := by
  obtain ⟨a, ha, hsum⟩ := exists_bounded_counts c B hB
  have hcount (i : Worker k) : a i < B + 1 := by
    have hi : a i ≤ ∑ j, a j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    omega
  exact ⟨⟨fun i => ⟨a i, hcount i⟩, hsum⟩, ha⟩

lemma residual_allocation_exists {k B : ℕ} {C e : Worker k → ℕ}
    {b : Allocation k B} (hb : ∀ i, (b.val i).val ≤ C i)
    (he : ∀ i, e i ≤ C i) (heB : ∑ i, e i ≤ B) :
    ∃ r : Worker k → ℕ, (∀ i, r i ≤ (b.val i).val) ∧
      (∀ i, e i + r i ≤ C i) ∧ ∑ i, (e i + r i) = B := by
  have hsum : B - ∑ i, e i ≤ ∑ i, min (b.val i).val (C i - e i) := by
    have hpoint (i : Worker k) :
        (b.val i).val ≤ min (b.val i).val (C i - e i) + e i := by
      have := hb i
      have := he i
      omega
    have htotal := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
    rw [Finset.sum_add_distrib, b.property] at htotal
    omega
  obtain ⟨r, hr, htotal⟩ := exists_bounded_counts
    (fun i => min (b.val i).val (C i - e i)) (B - ∑ i, e i) hsum
  refine ⟨r, fun i => (hr i).trans (min_le_left _ _), ?_, ?_⟩
  · intro i
    have := (hr i).trans (min_le_right _ _)
    have := he i
    omega
  · rw [Finset.sum_add_distrib, htotal]
    omega

lemma optimum_harmonic_bound {k B : ℕ} {u : Worker k → ℝ}
    (hu : ∀ i, 0 < u i) :
    optimum (B := B) u * (∑ i, (u i)⁻¹) ≤ (B : ℝ) + (k + 1 : ℕ) := by
  let V := optimum (B := B) u
  have hV : 0 ≤ V := optimum_nonneg (fun i => (hu i).le)
  by_cases hzero : V = 0
  · change V * (∑ i, (u i)⁻¹) ≤ _
    rw [hzero, zero_mul]
    positivity
  have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hzero)
  let c : Worker k → ℕ := fun i => ⌈V / u i⌉₊ - 1
  have hceil (i) : 0 < ⌈V / u i⌉₊ := Nat.ceil_pos.mpr (div_pos hVpos (hu i))
  have hstrict (i) : (c i : ℝ) * u i < V := by
    have hlt : c i < ⌈V / u i⌉₊ := Nat.sub_lt (hceil i) (by decide)
    exact (lt_div_iff₀ (hu i)).mp (Nat.lt_ceil.mp hlt)
  have hsum : ∑ i, c i < B := by
    by_contra hnot
    obtain ⟨a, ha⟩ := exists_allocation_le c (le_of_not_gt hnot)
    have hpoint (i : Worker k) : ((a.val i).val : ℝ) * u i < V :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast ha i) (hu i).le).trans_lt (hstrict i)
    have hloss : loss u a < V := by
      unfold loss
      exact (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun i _ => hpoint i)
    exact (not_lt_of_ge (optimum_le_loss u a)) hloss
  have hquotient (i : Worker k) : V / u i ≤ (c i : ℝ) + 1 := by
    have heq : c i + 1 = ⌈V / u i⌉₊ := Nat.sub_add_cancel (hceil i)
    have hle := Nat.le_ceil (V / u i)
    exact hle.trans_eq (by exact_mod_cast heq.symm)
  calc
    V * (∑ i, (u i)⁻¹) = ∑ i, V / u i := by
      rw [Finset.mul_sum]
      simp only [div_eq_mul_inv]
    _ ≤ ∑ i, ((c i : ℝ) + 1) := Finset.sum_le_sum (fun i _ => hquotient i)
    _ ≤ (B : ℝ) + (k + 1 : ℕ) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, ← Nat.cast_sum]
      have hc : (∑ i, c i : ℕ) ≤ B := hsum.le
      have hc' : ((∑ i, c i : ℕ) : ℝ) ≤ B := by exact_mod_cast hc
      exact add_le_add hc' le_rfl

end LongTailsOnline.Proofs.TaskAllocation

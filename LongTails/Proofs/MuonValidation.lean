import LongTails.Algorithms.ValidatedMuon
import LongTails.Proofs.MatrixCovariance
import LongTails.Proofs.RobustPilot
import LongTails.Proofs.LaggedAlignment
import LongTails.Proofs.MuonProcess

namespace LongTails.Proofs.MuonValidation

open LongTails.Algorithms.MatrixPolar
open LongTails.Algorithms.ValidatedMuon

lemma nuclearNorm_sub_rev {m n : ℕ} (X Y : Space m n) :
    nuclearNorm (X - Y) = nuclearNorm (Y - X) := by
  rw [← neg_sub Y X, nuclearNorm_neg]

lemma representative_accuracy {m n k : ℕ} {r : ℝ}
    (B : Fin (k + 1) → Space m n) (G : Space m n)
    (hgood : k + 1 < 2 * (Finset.univ.filter fun i => nuclearNorm (B i - G) ≤ r).card) :
    nuclearNorm (representative (2 * r) B - G) ≤ 3 * r := by
  classical
  let good := Finset.univ.filter fun i => nuclearNorm (B i - G) ≤ r
  let neighbors := fun i => Finset.univ.filter fun j => nuclearNorm (B i - B j) ≤ 2 * r
  let S := Finset.univ.filter fun i => k + 1 < 2 * (neighbors i).card
  have hg : k + 1 < 2 * good.card := hgood
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < good.card by omega)
  have hsub : good ⊆ neighbors i := by
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have ht := nuclearNorm_add_le (B i - G) (G - B j)
    rw [sub_add_sub_cancel, nuclearNorm_sub_rev G] at ht
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    linarith
  have hS : S.Nonempty := by
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hc := Finset.card_le_card hsub
    omega
  have hsel : representativeIndex (2 * r) B ∈ S := by
    unfold representativeIndex
    change (if h : S.Nonempty then S.min' h else 0) ∈ S
    rw [dite_eq_left hS]
    exact Finset.min'_mem S hS
  have hmajor := (Finset.mem_filter.mp hsel).2
  obtain ⟨j, hj, hjg⟩ := OracleTemplate.RobustGradient.majorities_intersect
    (neighbors (representativeIndex (2 * r) B)) good hmajor hg
  have hb := (Finset.mem_filter.mp hj).2
  have hj' := (Finset.mem_filter.mp hjg).2
  have ht := nuclearNorm_add_le (B (representativeIndex (2 * r) B) - B j) (B j - G)
  rw [sub_add_sub_cancel] at ht
  change nuclearNorm (B (representativeIndex (2 * r) B) - G) ≤ 3 * r
  linarith

lemma bestIndex_minimizes {m n q : ℕ} (G : Fin (q + 1) → Space m n) (j : Fin (q + 1)) :
    nuclearNorm (G (bestIndex G)) ≤ nuclearNorm (G j) := by
  classical
  let S := Finset.univ.filter fun i => ∀ j, nuclearNorm (G i) ≤ nuclearNorm (G j)
  have hS : S.Nonempty := by
    obtain ⟨i, _, hi⟩ := Finset.univ.exists_min_image (fun i => nuclearNorm (G i))
      (show (Finset.univ : Finset (Fin (q + 1))).Nonempty from ⟨0, Finset.mem_univ _⟩)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => hi j (Finset.mem_univ _)⟩⟩
  have hm : bestIndex G ∈ S := by
    unfold bestIndex
    change (if h : S.Nonempty then S.min' h else 0) ∈ S
    rw [dite_eq_left hS]
    exact Finset.min'_mem S hS
  exact (Finset.mem_filter.mp hm).2 j

lemma selected_gradient_accuracy {m n q : ℕ} {a r : ℝ}
    (G H : Fin (q + 1) → Space m n)
    (herr : ∀ i, nuclearNorm (H i - G i) ≤ r)
    (hgood : ∃ i, nuclearNorm (G i) ≤ a) :
    nuclearNorm (G (bestIndex H)) ≤ a + 2 * r := by
  obtain ⟨i, hi⟩ := hgood
  have hH := nuclearNorm_add_le (H i - G i) (G i)
  rw [sub_add_cancel] at hH
  have hG := nuclearNorm_add_le (G (bestIndex H) - H (bestIndex H)) (H (bestIndex H))
  rw [sub_add_cancel, nuclearNorm_sub_rev] at hG
  have hmin := bestIndex_minimizes H i
  linarith [herr i, herr (bestIndex H)]

lemma measurable_first_satisfying {Ω : Type*} [MeasurableSpace Ω] (k : ℕ)
    (p : Ω → Fin (k + 1) → Prop) [∀ ω i, Decidable (p ω i)]
    (hp : ∀ i, MeasurableSet {ω | p ω i}) :
    Measurable (fun ω =>
      let S := Finset.univ.filter (p ω)
      if h : S.Nonempty then S.min' h else (0 : Fin (k + 1))) := by
  classical
  let choose : (Fin (k + 1) → Bool) → Fin (k + 1) := fun z =>
    let S := Finset.univ.filter fun i => z i = true
    if h : S.Nonempty then S.min' h else 0
  have hchoose : Measurable choose := measurable_of_countable choose
  have hpat : Measurable (fun ω i => decide (p ω i)) := by
    apply Measurable.of_eval
    intro i
    have he : (fun ω => decide (p ω i)) = (fun ω => if p ω i then true else false) := by
      funext ω
      by_cases h : p ω i <;> simp [h]
    rw [he]
    exact Measurable.ite (hp i) measurable_const measurable_const
  simpa only [choose, Function.comp_def, decide_eq_true_eq] using hchoose.comp hpat

lemma measurable_representativeIndex (m n k : ℕ) (ρ : ℝ) :
    Measurable (representativeIndex (m := m) (n := n) (k := k) ρ) := by
  classical
  unfold representativeIndex
  apply measurable_first_satisfying
  intro i
  have hc : Measurable (fun B : Fin (k + 1) → Space m n =>
      (Finset.univ.filter fun j => nuclearNorm (B i - B j) ≤ ρ).card) := by
    simp only [Finset.card_filter]
    apply Finset.measurable_sum
    intro j _
    exact Measurable.ite (measurableSet_le
      ((MatrixCovariance.continuous_nuclearNorm m n).measurable.comp
        ((measurable_pi_apply i).sub (measurable_pi_apply j))) measurable_const)
      measurable_const measurable_const
  exact measurableSet_lt measurable_const (hc.const_mul 2)

lemma measurable_bestIndex (m n q : ℕ) :
    Measurable (bestIndex (m := m) (n := n) (q := q)) := by
  classical
  unfold bestIndex
  apply measurable_first_satisfying
  intro i
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le
    ((MatrixCovariance.continuous_nuclearNorm m n).measurable.comp (measurable_pi_apply i))
    ((MatrixCovariance.continuous_nuclearNorm m n).measurable.comp (measurable_pi_apply j))

lemma measurable_representative (m n k : ℕ) (ρ : ℝ) :
    Measurable (representative (m := m) (n := n) (k := k) ρ) := by
  classical
  have he : representative (m := m) (n := n) (k := k) ρ =
      fun B => ∑ i : Fin (k + 1), if representativeIndex ρ B = i then B i else 0 := by
    funext B
    simp [representative, LongTails.Setups.FiniteVarianceSpectralSmooth.representative]
  rw [he]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite
    (measurableSet_eq_fun (measurable_representativeIndex m n k ρ) measurable_const)
    (measurable_pi_apply i) measurable_const

open MeasureTheory

lemma adapted_half_tail {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : ℕ → MeasurableSpace Ω}
    (hF : ∀ t, F t ≤ m₀) (hmono : Monotone F) {Z : ℕ → Ω → ℝ}
    (hadapt : ∀ t, StronglyMeasurable[F (t + 1)] (Z t))
    (hzero : ∀ t ω, 0 ≤ Z t ω) (hbound : ∀ t ω, Z t ω ≤ 1)
    (hmean : ∀ t, ∀ᵐ ω ∂P, P[Z t | F t] ω ≤ (1 / 16 : ℝ)) (k : ℕ) :
    P.real {ω | (k : ℝ) / 2 ≤ ∑ j ∈ Finset.range k, Z j ω} ≤
      Real.exp (-(3 * (k : ℝ) / 8)) := by
  have hpast (n : ℕ) : StronglyMeasurable[F n]
      (fun ω => Real.exp ((∑ j ∈ Finset.range n, Z j ω) / 1)) := by
    have hh := Finset.stronglyMeasurable_sum (Finset.range n) (fun i hi =>
      (hadapt i).mono (hmono (Nat.succ_le_of_lt (Finset.mem_range.mp hi))))
    simpa only [div_one, Finset.sum_apply] using Real.continuous_exp.comp_stronglyMeasurable hh
  have hh := LaggedAlignment.sum_tail_le hF (H := 1) (μ := 1 / 16) (by norm_num)
    (fun t => ((hadapt t).mono (hF (t + 1))).measurable) hzero hbound hpast hmean k (3 * k / 8)
  have he : 2 * (1 / 16 : ℝ) * k + 1 * (3 * k / 8) = (k : ℝ) / 2 := by ring
  simpa only [he] using hh

lemma half_tail_confidence {k : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (hk : 8 * Real.log (1 / ρ) ≤ k) : Real.exp (-(3 * (k : ℝ) / 8)) ≤ ρ := by
  apply (Real.le_log_iff_exp_le hρ).mp
  rw [one_div, Real.log_inv] at hk
  linarith [Nat.cast_nonneg (α := ℝ) k]

lemma representative_failure_count {m n k : ℕ} {r : ℝ}
    (B : ℕ → Space m n) (G : Space m n)
    (hbad : 3 * r < nuclearNorm (representative (2 * r) (fun i : Fin (k + 1) => B i) - G)) :
    ((k + 1 : ℕ) : ℝ) / 2 ≤ ∑ j ∈ Finset.range (k + 1),
      if r < nuclearNorm (B j - G) then (1 : ℝ) else 0 := by
  classical
  let good := Finset.univ.filter (fun i : Fin (k + 1) => nuclearNorm (B i - G) ≤ r)
  let bad := Finset.univ.filter (fun i : Fin (k + 1) => r < nuclearNorm (B i - G))
  have hn : ¬k + 1 < 2 * good.card := by
    intro hg
    exact (not_lt_of_ge (representative_accuracy (fun i : Fin (k + 1) => B i) G hg)) hbad
  have ht : good.card + bad.card = k + 1 := by
    simpa [good, bad, not_le] using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (k + 1)))) (fun i => nuclearNorm (B i - G) ≤ r)
  have hc : k + 1 ≤ 2 * bad.card := by omega
  have hs : (∑ j ∈ Finset.range (k + 1),
      if r < nuclearNorm (B j - G) then (1 : ℝ) else 0) = (bad.card : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [bad]
  rw [hs]
  have hc' : ((k + 1 : ℕ) : ℝ) ≤ 2 * (bad.card : ℝ) := by exact_mod_cast hc
  linarith

lemma frozen_batch_majority_tail {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    {start b : ℕ} (hb : 0 < b) {X : (ℕ → model.Ω) → Space m n}
    (hX : Measurable[MuonProcess.past start] X) {r : ℝ} (hr : 0 < r)
    (hbudget : 16 * s ^ 2 ≤ (b : ℝ) * r ^ 2) (k : ℕ) :
    P.real {ξ | (k : ℝ) / 2 ≤ ∑ j ∈ Finset.range k,
      if r < nuclearNorm (OracleTemplate.QueryPlan.sampledEval model.sample ξ
        (batchMeanPlan (X ξ) b) (start + b * j) - gradient f (X ξ)) then (1 : ℝ) else 0} ≤
      Real.exp (-(3 * (k : ℝ) / 8)) := by
  classical
  let Z := fun j ξ => if r < nuclearNorm (OracleTemplate.QueryPlan.sampledEval model.sample ξ
    (batchMeanPlan (X ξ) b) (start + b * j) - gradient f (X ξ)) then (1 : ℝ) else 0
  have hx (j : ℕ) : Measurable[MuonProcess.past (start + b * j)] X :=
    hX.mono (MuonProcess.past_mono (Nat.le_add_right start (b * j))) le_rfl
  have ha (j : ℕ) : StronglyMeasurable[MuonProcess.past (start + b * (j + 1))] (Z j) := by
    have he := MuonProcess.adapted_batch_error model (hx j) b
    have hm : Measurable[MuonProcess.past (start + b * j + b)] (Z j) :=
      Measurable.ite (measurableSet_lt measurable_const he) measurable_const measurable_const
    rw [show start + b * j + b = start + b * (j + 1) by ring] at hm
    exact hm.stronglyMeasurable
  exact adapted_half_tail (F := fun j => MuonProcess.past (start + b * j))
    (fun j => MuonProcess.past_le _) (fun _ _ hle =>
      MuonProcess.past_mono (Nat.add_le_add_left (Nat.mul_le_mul_left b hle) start)) ha
    (fun j ξ => by dsimp [Z]; split_ifs <;> norm_num)
    (fun j ξ => by dsimp [Z]; split_ifs <;> norm_num)
    (fun j => MuonProcess.model_frozen_batch_bad_mean model h hb (hx j) hr hbudget) k

lemma frozen_representative_tail {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    {start b : ℕ} (hb : 0 < b) {X : (ℕ → model.Ω) → Space m n}
    (hX : Measurable[MuonProcess.past start] X) {r : ℝ} (hr : 0 < r)
    (hbudget : 16 * s ^ 2 ≤ (b : ℝ) * r ^ 2) (k : ℕ) :
    P.real {ξ | 3 * r < nuclearNorm
      (representative (2 * r) (fun i : Fin (k + 1) =>
        OracleTemplate.QueryPlan.sampledEval model.sample ξ (batchMeanPlan (X ξ) b)
          (start + b * i.val)) - gradient f (X ξ))} ≤
      Real.exp (-(3 * ((k + 1 : ℕ) : ℝ) / 8)) := by
  apply (measureReal_mono (μ := P) ?_).trans
    (frozen_batch_majority_tail model h hb hX hr hbudget (k + 1))
  intro ξ hξ
  exact representative_failure_count (fun j => OracleTemplate.QueryPlan.sampledEval model.sample ξ
    (batchMeanPlan (X ξ) b) (start + b * j)) (gradient f (X ξ)) hξ

lemma frozen_selection_tail {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    {start b k q : ℕ} (hb : 0 < b)
    {X : (ℕ → model.Ω) → Fin (q + 1) → Space m n}
    (hX : ∀ i, Measurable[MuonProcess.past start] (fun ξ => X ξ i))
    {a r : ℝ} (hr : 0 < r) (hbudget : 16 * s ^ 2 ≤ (b : ℝ) * r ^ 2) :
    P.real {ξ | (∃ i, nuclearNorm (gradient f (X ξ i)) ≤ a) ∧
      a + 6 * r < nuclearNorm (gradient f
        (OracleTemplate.QueryPlan.sampledEval model.sample ξ
          (validationPlan (2 * r) b k q (X ξ)) start))} ≤
      ((q + 1 : ℕ) : ℝ) * Real.exp (-(3 * ((k + 1 : ℕ) : ℝ) / 8)) := by
  classical
  let H := fun ξ i => representative (2 * r) (fun j : Fin (k + 1) =>
    OracleTemplate.QueryPlan.sampledEval model.sample ξ (batchMeanPlan (X ξ i) b)
      (start + b * (k + 1) * i.val + b * j.val))
  let bad := fun i => {ξ | 3 * r < nuclearNorm (H ξ i - gradient f (X ξ i))}
  have hsub : {ξ | (∃ i, nuclearNorm (gradient f (X ξ i)) ≤ a) ∧
      a + 6 * r < nuclearNorm (gradient f
        (OracleTemplate.QueryPlan.sampledEval model.sample ξ
          (validationPlan (2 * r) b k q (X ξ)) start))} ⊆ ⋃ i, bad i := by
    intro ξ hξ
    simp only [Set.mem_ofPred_eq] at hξ
    by_contra hn
    have herr : ∀ i, nuclearNorm (H ξ i - gradient f (X ξ i)) ≤ 3 * r := by
      intro i
      by_contra hi
      exact hn (Set.mem_iUnion.mpr ⟨i, lt_of_not_ge hi⟩)
    have hs := selected_gradient_accuracy (fun i => gradient f (X ξ i)) (H ξ) herr hξ.1
    rw [ValidatedMuonExecution.sampledEval_validationPlan] at hξ
    change (∃ i, nuclearNorm (gradient f (X ξ i)) ≤ a) ∧
      a + 6 * r < nuclearNorm (gradient f (X ξ (bestIndex (H ξ)))) at hξ
    linarith [hξ.2]
  have hi (i : Fin (q + 1)) :
      P.real (bad i) ≤ Real.exp (-(3 * ((k + 1 : ℕ) : ℝ) / 8)) := by
    exact frozen_representative_tail model h hb
      ((hX i).mono (MuonProcess.past_mono (Nat.le_add_right start _)) le_rfl) hr hbudget k
  calc
    _ ≤ P.real (⋃ i, bad i) := measureReal_mono hsub
    _ ≤ ∑ i, P.real (bad i) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _i : Fin (q + 1), Real.exp (-(3 * ((k + 1 : ℕ) : ℝ) / 8)) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp

lemma uniform_avoidance_probability (T q : ℕ) (bad : Finset (Fin (T + 1))) :
    (PMF.uniformOfFintype (Fin (q + 1) → Fin (T + 1))).toMeasure.real
      {seed | ∀ i, seed i ∈ bad} = ((bad.card : ℝ) / (T + 1)) ^ (q + 1) := by
  classical
  let S : Set (Fin (q + 1) → Fin (T + 1)) := {seed | ∀ i, seed i ∈ bad}
  let : Fintype S := Fintype.ofFinite S
  let e : S ≃ (Fin (q + 1) → {x : Fin (T + 1) // x ∈ bad}) :=
    { toFun := fun seed i => ⟨seed.val i, seed.property i⟩
      invFun := fun seed => ⟨fun i => (seed i).val, fun i => (seed i).property⟩
      left_inv := fun seed => by apply Subtype.ext; rfl
      right_inv := fun seed => by funext i; apply Subtype.ext; rfl }
  have hc : Fintype.card S = bad.card ^ (q + 1) := by
    simpa using Fintype.card_congr e
  change (PMF.uniformOfFintype (Fin (q + 1) → Fin (T + 1))).toMeasure.real S = _
  rw [measureReal_def, PMF.toMeasure_uniformOfFintype_apply S S.toFinite.measurableSet, hc]
  simp [div_pow, ENNReal.toReal_add]

lemma half_bad_card {T : ℕ} {a : ℝ} (ha : 0 < a) (g : Fin (T + 1) → ℝ)
    (hg : ∀ i, 0 ≤ g i) (hsum : (∑ i, g i) ≤ (T + 1) * a / 2) :
    2 * (Finset.univ.filter fun i => a < g i).card ≤ T + 1 := by
  classical
  let bad := Finset.univ.filter fun i => a < g i
  have hb : a * (bad.card : ℝ) ≤ ∑ i, g i := by
    calc
      _ = ∑ _i ∈ bad, a := by simp [mul_comm]
      _ ≤ ∑ i ∈ bad, g i :=
        Finset.sum_le_sum (fun i hi => ((Finset.mem_filter.mp hi).2).le)
      _ ≤ ∑ i, g i := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _ _ => hg i)
  have hc : 2 * (bad.card : ℝ) ≤ (T + 1) := by nlinarith
  exact_mod_cast hc

lemma uniform_misses_good_half {T q : ℕ} {a : ℝ} (ha : 0 < a) (g : Fin (T + 1) → ℝ)
    (hg : ∀ i, 0 ≤ g i) (hsum : (∑ i, g i) ≤ (T + 1) * a / 2) :
    (PMF.uniformOfFintype (Fin (q + 1) → Fin (T + 1))).toMeasure.real
      {seed | ∀ i, a < g (seed i)} ≤ (1 / 2 : ℝ) ^ (q + 1) := by
  classical
  let bad := Finset.univ.filter fun i => a < g i
  have he : {seed : Fin (q + 1) → Fin (T + 1) | ∀ i, a < g (seed i)} =
      {seed | ∀ i, seed i ∈ bad} := by ext seed; simp [bad]
  rw [he, uniform_avoidance_probability]
  have hc : 2 * (bad.card : ℝ) ≤ (T + 1) := by exact_mod_cast half_bad_card ha g hg hsum
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < T + 1)).mpr
  linarith

lemma measurable_finite_select {Ω : Type*} [MeasurableSpace Ω] {m n q : ℕ}
    {X : Ω → Fin (q + 1) → Space m n} {i : Ω → Fin (q + 1)}
    (hX : ∀ j, Measurable (fun ω => X ω j)) (hi : Measurable i) :
    Measurable (fun ω => X ω (i ω)) := by
  classical
  have he : (fun ω => X ω (i ω)) =
      fun ω => ∑ j : Fin (q + 1), if i ω = j then X ω j else 0 := by
    funext ω
    simp
  rw [he]
  exact Finset.measurable_sum _ (fun j _ => Measurable.ite
    (measurableSet_eq_fun hi measurable_const) (hX j) measurable_const)

lemma measurable_validation_output {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {q : ℕ} {X : (ℕ → model.Ω) → Fin (q + 1) → Space m n}
    (hX : ∀ i, Measurable (fun ξ => X ξ i)) (ρ : ℝ) (b k start : ℕ) :
    Measurable (fun ξ => OracleTemplate.QueryPlan.sampledEval model.sample ξ
      (validationPlan ρ b k q (X ξ)) start) := by
  simp_rw [ValidatedMuonExecution.sampledEval_validationPlan]
  apply measurable_finite_select hX
  apply (measurable_bestIndex m n q).comp
  apply Measurable.of_eval
  intro i
  have hmeans := Measurable.of_eval (fun j : Fin (k + 1) =>
    MuonProcess.measurable_batch_mean model (hX i) (start + b * (k + 1) * i.val + b * j.val) b)
  exact (measurable_representative m n k ρ).comp hmeans

lemma product_event_bound {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {B : Set (Ω × Ξ)} (hB : MeasurableSet B) {c : ℝ}
    (hsections : ∀ ω, Q.real {ξ | (ω, ξ) ∈ B} ≤ c) :
    (P.prod Q).real B ≤ c := by
  have hi : Integrable (B.indicator (1 : Ω × Ξ → ℝ)) (P.prod Q) :=
    (integrable_const 1).indicator hB
  rw [← integral_indicator_one hB, integral_prod _ hi]
  have hb := integral_mono hi.integral_prod_left (integrable_const c) (fun ω => by
    change (∫ ξ, ({ξ | (ω, ξ) ∈ B}).indicator 1 ξ ∂Q) ≤ c
    have hs : MeasurableSet {ξ | (ω, ξ) ∈ B} := hB.preimage measurable_prodMk_left
    rw [integral_indicator_one hs]
    exact hsections ω)
  simpa using hb

lemma product_event_bound_right {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {B : Set (Ω × Ξ)} (hB : MeasurableSet B) {c : ℝ}
    (hsections : ∀ ξ, P.real {ω | (ω, ξ) ∈ B} ≤ c) :
    (P.prod Q).real B ≤ c := by
  have hi : Integrable (B.indicator (1 : Ω × Ξ → ℝ)) (P.prod Q) :=
    (integrable_const 1).indicator hB
  rw [← integral_indicator_one hB, integral_prod_symm _ hi]
  have hb := integral_mono hi.integral_prod_right (integrable_const c) (fun ξ => by
    change (∫ ω, ({ω | (ω, ξ) ∈ B}).indicator 1 ω ∂P) ≤ c
    have hs : MeasurableSet {ω | (ω, ξ) ∈ B} := hB.preimage measurable_prodMk_right
    rw [integral_indicator_one hs]
    exact hsections ξ)
  simpa using hb

lemma random_validation_tail {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    {T q k b start : ℕ} (hb : 0 < b)
    {X : (ℕ → model.Ω) → Fin (T + 1) → Space m n}
    (hX : ∀ i, Measurable[MuonProcess.past start] (fun ξ => X ξ i))
    {a r c : ℝ} (ha : 0 < a) (hr : 0 < r) (hbudget : 16 * s ^ 2 ≤ (b : ℝ) * r ^ 2)
    (htraining : P.real {ξ | (T + 1) * a / 2 < ∑ i, nuclearNorm (gradient f (X ξ i))} ≤ c) :
    let S := (PMF.uniformOfFintype (Fin (q + 1) → Fin (T + 1))).toMeasure
    let output := fun z : (Fin (q + 1) → Fin (T + 1)) × (ℕ → model.Ω) =>
      OracleTemplate.QueryPlan.sampledEval model.sample z.2
        (validationPlan (2 * r) b k q (fun i => X z.2 (z.1 i))) start
    Measurable output ∧ (S.prod P).real {z | a + 6 * r < nuclearNorm (gradient f (output z))} ≤
      c + (1 / 2 : ℝ) ^ (q + 1) + (q + 1 : ℕ) * Real.exp (-(3 * ((k + 1 : ℕ) : ℝ) / 8)) := by
  classical
  let S := (PMF.uniformOfFintype (Fin (q + 1) → Fin (T + 1))).toMeasure
  let output := fun z : (Fin (q + 1) → Fin (T + 1)) × (ℕ → model.Ω) =>
    OracleTemplate.QueryPlan.sampledEval model.sample z.2
      (validationPlan (2 * r) b k q (fun i => X z.2 (z.1 i))) start
  have hx (i : Fin (T + 1)) : Measurable (fun ξ => X ξ i) :=
    (hX i).mono (MuonProcess.past_le start) le_rfl
  have hout : Measurable output := measurable_from_prod_countable_right (fun seed =>
    measurable_validation_output model (fun i => hx (seed i)) (2 * r) b k start)
  have hgrad (i : Fin (T + 1)) : Measurable (fun ξ => nuclearNorm (gradient f (X ξ i))) :=
    (MatrixCovariance.continuous_nuclearNorm m n).measurable.comp
      ((MuonProcess.measurable_gradient f).comp (hx i))
  let A := {ξ | (T + 1) * a / 2 < ∑ i, nuclearNorm (gradient f (X ξ i))}
  let M := {z : (Fin (q + 1) → Fin (T + 1)) × (ℕ → model.Ω) |
    z.2 ∉ A ∧ ∀ i, a < nuclearNorm (gradient f (X z.2 (z.1 i)))}
  let V := {z : (Fin (q + 1) → Fin (T + 1)) × (ℕ → model.Ω) |
    (∃ i, nuclearNorm (gradient f (X z.2 (z.1 i))) ≤ a) ∧
      a + 6 * r < nuclearNorm (gradient f (output z))}
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    (Finset.measurable_sum _ (fun i _ => hgrad i))
  have hsel (i : Fin (q + 1)) : Measurable
      (fun z : (Fin (q + 1) → Fin (T + 1)) × (ℕ → model.Ω) =>
        nuclearNorm (gradient f (X z.2 (z.1 i)))) :=
    measurable_from_prod_countable_right (fun seed => hgrad (seed i))
  have hAc : MeasurableSet (Prod.snd ⁻¹' A :
      Set ((Fin (q + 1) → Fin (T + 1)) × (ℕ → model.Ω))) := hA.preimage measurable_snd
  have hMall : MeasurableSet {z : (Fin (q + 1) → Fin (T + 1)) × (ℕ → model.Ω) |
      ∀ i, a < nuclearNorm (gradient f (X z.2 (z.1 i)))} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_lt measurable_const (hsel i))
  have hM : MeasurableSet M := hAc.compl.inter hMall
  have hVgood : MeasurableSet {z : (Fin (q + 1) → Fin (T + 1)) × (ℕ → model.Ω) |
      ∃ i, nuclearNorm (gradient f (X z.2 (z.1 i))) ≤ a} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun i => measurableSet_le (hsel i) measurable_const)
  have hVbad : MeasurableSet {z | a + 6 * r < nuclearNorm (gradient f (output z))} :=
    measurableSet_lt measurable_const ((MatrixCovariance.continuous_nuclearNorm m n).measurable.comp
      ((MuonProcess.measurable_gradient f).comp hout))
  have hV : MeasurableSet V := hVgood.inter hVbad
  have hAp : (S.prod P).real (Prod.snd ⁻¹' A) ≤ c := by
    unfold Measure.real
    rw [measurePreserving_snd.measure_preimage hA.nullMeasurableSet]
    exact htraining
  have hMp : (S.prod P).real M ≤ (1 / 2 : ℝ) ^ (q + 1) := by
    apply product_event_bound_right hM
    intro ξ
    by_cases hξ : ξ ∈ A
    · have heq : {seed | (seed, ξ) ∈ M} = ∅ := by ext seed; simp [M, hξ]
      rw [heq, measureReal_empty]
      positivity
    · have hh := uniform_misses_good_half (q := q) ha
        (fun i => nuclearNorm (gradient f (X ξ i))) (fun i => nuclearNorm_nonneg _)
        (le_of_not_gt hξ)
      exact (measureReal_mono (fun seed hseed => hseed.2) (by finiteness)).trans hh
  have hVp : (S.prod P).real V ≤
      (q + 1 : ℕ) * Real.exp (-(3 * ((k + 1 : ℕ) : ℝ) / 8)) := by
    apply product_event_bound hV
    intro seed
    exact frozen_selection_tail model h hb (fun i => hX (seed i)) hr hbudget
  refine ⟨hout, ?_⟩
  have hsub : {z | a + 6 * r < nuclearNorm (gradient f (output z))} ⊆
      (Prod.snd ⁻¹' A ∪ M) ∪ V := by
    intro z hz
    by_cases hA : z.2 ∈ A
    · exact Or.inl (Or.inl hA)
    · by_cases hgood : ∃ i, nuclearNorm (gradient f (X z.2 (z.1 i))) ≤ a
      · exact Or.inr ⟨hgood, hz⟩
      · exact Or.inl (Or.inr ⟨hA, fun i => lt_of_not_ge (fun hi => hgood ⟨i, hi⟩)⟩)
  calc
    _ ≤ (S.prod P).real ((Prod.snd ⁻¹' A ∪ M) ∪ V) := measureReal_mono hsub (by finiteness)
    _ ≤ (S.prod P).real (Prod.snd ⁻¹' A ∪ M) + (S.prod P).real V := measureReal_union_le _ _
    _ ≤ (S.prod P).real (Prod.snd ⁻¹' A) + (S.prod P).real M + (S.prod P).real V :=
      add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add hAp hMp) hVp

end LongTails.Proofs.MuonValidation

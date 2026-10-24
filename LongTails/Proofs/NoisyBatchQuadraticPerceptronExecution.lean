import LongTails.Algorithms.NoisyBatchQuadraticPerceptron
import LongTails.Proofs.Execution

namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution

open Classical MeasureTheory OracleTemplate LongTails.Setups.NoisyBatchQuadraticPerceptron
open LongTails.Algorithms.NoisyBatchQuadraticPerceptron

lemma algorithm_family (P : Public) (η : ℝ) (hη : 0 < η) :
    family P (algorithm P η) := by
  refine ⟨η, id, id, hη, measurable_id, ?_, ?_, ?_, ?_, ?_⟩
  · exact Measure.map_id
  · intro ω
    rfl
  · intro s
    rfl
  · intro s reply
    rfl
  · intro s
    rfl

lemma frozen_scanUpdate (P : Public) (η : ℝ) (s : ScanState P)
    (reply : Reply P.dimension) (h : s.frozen = true) : scanUpdate P η s reply = s := by
  simp [scanUpdate, h]

lemma scanUpdate_seed (P : Public) (η : ℝ) (s : ScanState P)
    (reply : Reply P.dimension) : (scanUpdate P η s reply).seed = s.seed := by
  simp only [scanUpdate]
  split_ifs <;> rfl

lemma scanUpdate_batch (P : Public) (η : ℝ) (s : ScanState P)
    (reply : Reply P.dimension) :
    s.batch ≤ (scanUpdate P η s reply).batch ∧
      (scanUpdate P η s reply).batch ≤ s.batch + 1 := by
  simp only [scanUpdate]
  split_ifs <;> simp

noncomputable def trajectory (P : Public) (data : Data P) (η : ℝ) (ω : P.noise.Ω) :
    ℕ → ScanState P
  | 0 => initial P ω
  | k + 1 =>
      let s := trajectory P data η ω k
      scanUpdate P η s (answer (data s.cursor) s.point)

lemma execute_trajectory (P : Public) (data : Data P)
    (O : Oracle (Query P) (Reply P.dimension))
    (hO : ∀ history q ξ, O.answer history (0, q) ξ = answer (data q.1) q.2)
    (η : ℝ) (K : ℕ) (ω : P.noise.Ω) (ξ : (k : ℕ) → O.Seed k) :
    output P O η K ω ξ = (trajectory P data η ω K).point := by
  have h : ∀ k, (fun s : ScanState P => scanUpdate P η s
      (answer (data s.cursor) s.point))^[k] (initial P ω) = trajectory P data η ω k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl
  exact (execute_eq_of_answer_eq O (fun q => answer (data q.1) q.2) hO
    (algorithm P η) K ω ξ).trans
    ((execute_iterate (fun q : Query P => answer (data q.1) q.2)
      (algorithm P η) K ω).trans (congrArg ScanState.point (h K)))

lemma trajectory_seed (P : Public) (data : Data P) (η : ℝ) (ω : P.noise.Ω) (k : ℕ) :
    (trajectory P data η ω k).seed = ω := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [trajectory, scanUpdate_seed] using ih

lemma frozen_trajectory (P : Public) (data : Data P) (η : ℝ) (ω : P.noise.Ω)
    (k t : ℕ) (h : (trajectory P data η ω k).frozen = true) :
    trajectory P data η ω (k + t) = trajectory P data η ω k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ, trajectory, ih]
    exact frozen_scanUpdate P η _ _ h

lemma unfrozen_step_clock (P : Public) (η : ℝ) (s : ScanState P)
    (reply : Reply P.dimension) (hs : s.frozen ≠ true)
    (ht : (scanUpdate P η s reply).frozen ≠ true) :
    (P.count : ℕ) * (scanUpdate P η s reply).batch +
        (scanUpdate P η s reply).cursor.val =
      (P.count : ℕ) * s.batch + s.cursor.val + 1 := by
  have hc := s.cursor.isLt
  simp only [scanUpdate, hs] at ht ⊢
  split_ifs at ht ⊢ <;> simp_all [Nat.mul_add] <;> omega

lemma unfrozen_call_clock (P : Public) (data : Data P) (η : ℝ) (ω : P.noise.Ω)
    (k : ℕ) (h : (trajectory P data η ω k).frozen ≠ true) :
    k = (P.count : ℕ) * (trajectory P data η ω k).batch +
      (trajectory P data η ω k).cursor.val := by
  induction k with
  | zero => simp [trajectory, initial]
  | succ k ih =>
    have hp : (trajectory P data η ω k).frozen ≠ true := by
      intro hp
      have he := frozen_trajectory P data η ω k 1 hp
      have hf : (trajectory P data η ω (k + 1)).frozen = true := by rw [he]; exact hp
      exact h hf
    have hc := unfrozen_step_clock P η (trajectory P data η ω k)
      (answer (data (trajectory P data η ω k).cursor) (trajectory P data η ω k).point) hp h
    simpa only [trajectory] using (congrArg (fun t : ℕ => t + 1) (ih hp)).trans hc.symm

lemma prefix_sum_succ {α : Type*} [AddCommMonoid α] {n k : ℕ}
    (f : Fin n → α) (hk : k < n) :
    (∑ i : Fin n, if i.val < k + 1 then f i else 0) =
      (∑ i : Fin n, if i.val < k then f i else 0) + f ⟨k, hk⟩ := by
  classical
  have h : ∀ i : Fin n, (if i.val < k + 1 then f i else 0) =
      (if i.val < k then f i else 0) + if i = ⟨k, hk⟩ then f i else 0 := by
    intro i
    by_cases hi : i.val < k
    · have hne : i ≠ ⟨k, hk⟩ := by intro he; have heval : i.val = k := congrArg Fin.val he; omega
      simp [hi, hne, show i.val < k + 1 by omega]
    · by_cases he : i = ⟨k, hk⟩
      · subst i; simp
      · have hn : ¬i.val < k + 1 := by
          intro hlt
          apply he
          apply Fin.ext
          change i.val = k
          omega
        simp [hi, he, hn]
  simp_rw [h]
  rw [Finset.sum_add_distrib]
  simp

lemma prefix_exists_succ {n k : ℕ} (p : Fin n → Prop) (hk : k < n) :
    (∃ i : Fin n, i.val < k + 1 ∧ p i) ↔
      (∃ i : Fin n, i.val < k ∧ p i) ∨ p ⟨k, hk⟩ := by
  constructor
  · rintro ⟨i, hi, hp⟩
    by_cases h : i.val < k
    · exact Or.inl ⟨i, h, hp⟩
    · right
      have he : i = ⟨k, hk⟩ := Fin.ext (show i.val = k by omega)
      simpa only [he] using hp
  · rintro (⟨i, hi, hp⟩ | hp)
    · exact ⟨i, by omega, hp⟩
    · exact ⟨⟨k, hk⟩, by simp, hp⟩

noncomputable def scanPrefix (P : Public) (data : Data P) (w : Weights P.dimension)
    (ω : P.noise.Ω) (b k : ℕ) (hk : k < P.count) : ScanState P := by
  classical
  exact ⟨ω, w,
    ∑ i : Fin P.count, if i.val < k then
      (if (answer (data i) w).margin ≤ 0 then (answer (data i) w).direction else 0) else 0,
    decide (∃ i : Fin P.count, i.val < k ∧ (answer (data i) w).margin ≤ 0),
    ⟨k, hk⟩, b, false⟩

lemma scanPrefix_step (P : Public) (data : Data P) (w : Weights P.dimension)
    (ω : P.noise.Ω) (η : ℝ) (b k : ℕ) (hk : k < P.count) (hnext : k + 1 < P.count) :
    scanUpdate P η (scanPrefix P data w ω b k hk) (answer (data ⟨k, hk⟩) w) =
      scanPrefix P data w ω b (k + 1) hnext := by
  classical
  have hs := prefix_sum_succ
    (fun i : Fin P.count => if (answer (data i) w).margin ≤ 0 then
      (answer (data i) w).direction else 0) hk
  have he := prefix_exists_succ (fun i : Fin P.count => (answer (data i) w).margin ≤ 0) hk
  simp only [Nat.lt_succ_iff] at hs he
  simp [scanPrefix, scanUpdate, hnext, hs, he]

lemma scanPrefix_terminal_state (P : Public) (data : Data P) (w : Weights P.dimension)
    (ω : P.noise.Ω) (η : ℝ) (b k : ℕ) (hk : k < P.count) (hlast : k + 1 = P.count) :
    scanUpdate P η (scanPrefix P data w ω b k hk) (answer (data ⟨k, hk⟩) w) =
      if Separates data w then { scanPrefix P data w ω b k hk with frozen := true }
      else scanPrefix P data
        (w + (η / (P.count : ℝ)) • (∑ i : Fin P.count,
          if (answer (data i) w).margin ≤ 0 then (answer (data i) w).direction else 0) +
          P.noiseScale • P.noise.sample b ω) ω (b + 1) 0 P.count.pos := by
  classical
  have hs := prefix_sum_succ
    (fun i : Fin P.count => if (answer (data i) w).margin ≤ 0 then
      (answer (data i) w).direction else 0) hk
  have he := prefix_exists_succ (fun i : Fin P.count => (answer (data i) w).margin ≤ 0) hk
  rw [hlast] at hs he
  simp only [Fin.is_lt, ↓reduceIte, true_and] at hs he
  have hsep : Separates data w ↔ ¬∃ i : Fin P.count, (answer (data i) w).margin ≤ 0 := by
    simp [Separates, answer]
  have hn : ¬k + 1 < P.count := by omega
  by_cases h : Separates data w
  · have hnot := hsep.mp h
    have he' := he.not.mp hnot
    simp [scanPrefix, scanUpdate, hn, h, he']
  · have hex : ∃ i : Fin P.count, (answer (data i) w).margin ≤ 0 := by
      by_contra hh
      exact h (hsep.mpr hh)
    have he' := he.mp hex
    simp [scanPrefix, scanUpdate, hn, h, he', hs]

lemma scanPrefix_iterate (P : Public) (data : Data P) (w : Weights P.dimension)
    (ω : P.noise.Ω) (η : ℝ) (b k : ℕ) (hk : k < P.count) :
    (fun s : ScanState P => scanUpdate P η s (answer (data s.cursor) s.point))^[k]
        (scanPrefix P data w ω b 0 P.count.pos) = scanPrefix P data w ω b k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp : k < P.count := by omega
    rw [Function.iterate_succ_apply', ih hp]
    exact scanPrefix_step P data w ω η b k hp hk

lemma full_scan (P : Public) (data : Data P) (w : Weights P.dimension)
    (ω : P.noise.Ω) (η : ℝ) (b : ℕ) :
    (fun s : ScanState P => scanUpdate P η s (answer (data s.cursor) s.point))^[P.count]
        (scanPrefix P data w ω b 0 P.count.pos) =
      if Separates data w then
        { scanPrefix P data w ω b (P.count - 1) (by have := P.count.pos; omega) with
          frozen := true }
      else scanPrefix P data
        (w + (η / (P.count : ℝ)) • (∑ i : Fin P.count,
          if (answer (data i) w).margin ≤ 0 then (answer (data i) w).direction else 0) +
          P.noiseScale • P.noise.sample b ω) ω (b + 1) 0 P.count.pos := by
  have hk : (P.count : ℕ) - 1 < P.count := by have := P.count.pos; omega
  have he : (P.count : ℕ) - 1 + 1 = P.count := by have := P.count.pos; omega
  conv_lhs => rw [← he]
  rw [Function.iterate_succ_apply', scanPrefix_iterate P data w ω η b _ hk]
  exact scanPrefix_terminal_state P data w ω η b _ hk he

lemma trajectory_add (P : Public) (data : Data P) (η : ℝ) (ω : P.noise.Ω) (k t : ℕ) :
    trajectory P data η ω (k + t) =
      (fun s : ScanState P => scanUpdate P η s (answer (data s.cursor) s.point))^[t]
        (trajectory P data η ω k) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ, trajectory, Function.iterate_succ_apply', ih]

lemma batch_boundary (P : Public) (data : Data P) (η : ℝ) (ω : P.noise.Ω) (t : ℕ) :
    let s := trajectory P data η ω ((P.count : ℕ) * t)
    (s.frozen = true ∧ Separates data s.point) ∨
      s = scanPrefix P data s.point ω t 0 P.count.pos := by
  induction t with
  | zero => right; simp [trajectory, initial, scanPrefix]
  | succ t ih =>
    dsimp only at ih ⊢
    have he := trajectory_add P data η ω ((P.count : ℕ) * t) P.count
    rw [← Nat.mul_succ] at he
    rcases ih with ⟨hf, hs⟩ | hp
    · left
      have hstable := frozen_trajectory P data η ω ((P.count : ℕ) * t) P.count hf
      rw [← Nat.mul_succ] at hstable
      rw [hstable]
      exact ⟨hf, hs⟩
    · rw [he, hp, full_scan]
      split_ifs with hs
      · left
        exact ⟨rfl, hs⟩
      · right
        rfl

lemma batch_recurrence (P : Public) (data : Data P) (η : ℝ) (ω : P.noise.Ω) (t : ℕ) :
    let w := (trajectory P data η ω ((P.count : ℕ) * t)).point
    (trajectory P data η ω ((P.count : ℕ) * (t + 1))).point =
      if Separates data w then w else
        w + (η / (P.count : ℝ)) • (∑ i : Fin P.count,
          if (answer (data i) w).margin ≤ 0 then (answer (data i) w).direction else 0) +
          P.noiseScale • P.noise.sample t ω := by
  dsimp only
  rcases batch_boundary P data η ω t with ⟨hf, hs⟩ | hp
  · have he := frozen_trajectory P data η ω ((P.count : ℕ) * t) P.count hf
    rw [← Nat.mul_succ] at he
    rw [he, ite_eq_left hs]
  · have he := trajectory_add P data η ω ((P.count : ℕ) * t) P.count
    rw [← Nat.mul_succ] at he
    rw [he, hp, full_scan]
    dsimp only [scanPrefix]
    split_ifs with hs <;> simp [hs]
    rfl

lemma frozen_after_separating_batch (P : Public) (data : Data P) (η : ℝ)
    (ω : P.noise.Ω) (t : ℕ)
    (hs : Separates data (trajectory P data η ω ((P.count : ℕ) * t)).point) :
    (trajectory P data η ω ((P.count : ℕ) * (t + 1))).frozen = true ∧
      (trajectory P data η ω ((P.count : ℕ) * (t + 1))).point =
        (trajectory P data η ω ((P.count : ℕ) * t)).point := by
  rcases batch_boundary P data η ω t with ⟨hf, _⟩ | hp
  · have he := frozen_trajectory P data η ω ((P.count : ℕ) * t) P.count hf
    rw [← Nat.mul_succ] at he
    exact ⟨by rw [he]; exact hf, congrArg ScanState.point he⟩
  · have he := trajectory_add P data η ω ((P.count : ℕ) * t) P.count
    rw [← Nat.mul_succ] at he
    rw [he, hp, full_scan, ite_eq_left hs]
    exact ⟨rfl, rfl⟩

lemma output_separates_of_batch (P : Public) (data : Data P)
    (O : Oracle (Query P) (Reply P.dimension))
    (hO : ∀ history q ξ, O.answer history (0, q) ξ = answer (data q.1) q.2)
    (η : ℝ) (ω : P.noise.Ω) (t K : ℕ) (ξ : (k : ℕ) → O.Seed k)
    (hs : Separates data (trajectory P data η ω ((P.count : ℕ) * t)).point)
    (hK : (P.count : ℕ) * (t + 1) ≤ K) : Separates data (output P O η K ω ξ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK
  obtain ⟨hf, hp⟩ := frozen_after_separating_batch P data η ω t hs
  rw [execute_trajectory P data O hO, frozen_trajectory P data η ω _ j hf, hp]
  exact hs

lemma continuous_answer_margin {d : ℕ} (a : Features d) :
    Continuous (fun w : Weights d => (answer a w).margin) := by
  unfold answer
  fun_prop

lemma continuous_answer_direction {d : ℕ} (a : Features d) :
    Continuous (fun w : Weights d => (answer a w).direction) := by
  unfold answer
  fun_prop

lemma measurableSet_separates (P : Public) (data : Data P) :
    MeasurableSet {w : Weights P.dimension | Separates data w} := by
  have h : {w : Weights P.dimension | Separates data w} =
      ⋂ i : Fin P.count, {w | 0 < (answer (data i) w).margin} := by
    ext w
    simp [Separates, answer]
  rw [h]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const
    (continuous_answer_margin (data i)).measurable

lemma measurable_wrong_direction (P : Public) (data : Data P) (i : Fin P.count) :
    Measurable (fun w : Weights P.dimension =>
      if (answer (data i) w).margin ≤ 0 then (answer (data i) w).direction else 0) := by
  exact Measurable.ite (measurableSet_le (continuous_answer_margin (data i)).measurable
    measurable_const) (continuous_answer_direction (data i)).measurable measurable_const

lemma partial_scan_point (P : Public) (data : Data P) (η : ℝ) (ω : P.noise.Ω)
    (t r : ℕ) (hr : r < P.count) :
    (trajectory P data η ω ((P.count : ℕ) * t + r)).point =
      (trajectory P data η ω ((P.count : ℕ) * t)).point := by
  rcases batch_boundary P data η ω t with ⟨hf, _⟩ | hp
  · rw [frozen_trajectory P data η ω _ r hf]
  · rw [trajectory_add, hp, scanPrefix_iterate P data _ ω η t r hr]
    rfl

lemma output_batch_point (P : Public) (data : Data P)
    (O : Oracle (Query P) (Reply P.dimension))
    (hO : ∀ history q ξ, O.answer history (0, q) ξ = answer (data q.1) q.2)
    (η : ℝ) (K : ℕ) (ω : P.noise.Ω) (ξ : (k : ℕ) → O.Seed k) :
    output P O η K ω ξ =
      (trajectory P data η ω ((P.count : ℕ) * (K / P.count))).point := by
  rw [execute_trajectory P data O hO]
  have he := partial_scan_point P data η ω (K / P.count) (K % P.count)
    (Nat.mod_lt _ P.count.pos)
  simpa only [Nat.div_add_mod] using he

lemma measurable_batch_point (P : Public) (data : Data P) (η : ℝ)
    (hξ : ∀ k, Measurable (P.noise.sample k)) (t : ℕ) :
    Measurable (fun ω => (trajectory P data η ω ((P.count : ℕ) * t)).point) := by
  induction t with
  | zero => simp [trajectory, initial]
  | succ t ih =>
    have he : (fun ω => (trajectory P data η ω ((P.count : ℕ) * (t + 1))).point) =
        (fun ω => let w := (trajectory P data η ω ((P.count : ℕ) * t)).point
          if Separates data w then w else
            w + (η / (P.count : ℝ)) • (∑ i : Fin P.count,
              if (answer (data i) w).margin ≤ 0 then (answer (data i) w).direction else 0) +
              P.noiseScale • P.noise.sample t ω) := funext fun ω => batch_recurrence P data η ω t
    rw [he]
    dsimp only
    apply Measurable.ite ((measurableSet_separates P data).preimage ih) ih
    have hm : Measurable (fun ω => ∑ i : Fin P.count,
        if (answer (data i) (trajectory P data η ω ((P.count : ℕ) * t)).point).margin ≤ 0 then
          (answer (data i) (trajectory P data η ω ((P.count : ℕ) * t)).point).direction else 0) :=
      Finset.measurable_sum _ fun i _ => (measurable_wrong_direction P data i).comp ih
    exact (ih.add (hm.const_smul (η / (P.count : ℝ)))).add
      ((hξ t).const_smul P.noiseScale)

lemma measurable_output (P : Public) (data : Data P)
    (O : Oracle (Query P) (Reply P.dimension))
    (hO : ∀ history q ξ, O.answer history (0, q) ξ = answer (data q.1) q.2)
    (η : ℝ) (K : ℕ) (hξ : ∀ k, Measurable (P.noise.sample k)) :
    Measurable (fun z : P.noise.Ω × ((k : ℕ) → O.Seed k) => output P O η K z.1 z.2) := by
  have he : (fun z : P.noise.Ω × ((k : ℕ) → O.Seed k) => output P O η K z.1 z.2) =
      (fun z => (trajectory P data η z.1 ((P.count : ℕ) * (K / P.count))).point) :=
    funext fun z => output_batch_point P data O hO η K z.1 z.2
  rw [he]
  exact (measurable_batch_point P data η hξ _).comp measurable_fst

lemma measurableSet_output_failure (P : Public) (data : Data P)
    (O : Oracle (Query P) (Reply P.dimension))
    (hO : ∀ history q ξ, O.answer history (0, q) ξ = answer (data q.1) q.2)
    (η : ℝ) (K : ℕ) (hξ : ∀ k, Measurable (P.noise.sample k)) :
    MeasurableSet {z : P.noise.Ω × ((k : ℕ) → O.Seed k) |
      ¬Separates data (output P O η K z.1 z.2)} :=
  ((measurableSet_separates P data).preimage (measurable_output P data O hO η K hξ)).compl

lemma batch_point_past (P : Public) (data : Data P) (η : ℝ)
    (t : ℕ) (ω ω' : P.noise.Ω)
    (h : ∀ j < t, P.noise.sample j ω = P.noise.sample j ω') :
    (trajectory P data η ω ((P.count : ℕ) * t)).point =
      (trajectory P data η ω' ((P.count : ℕ) * t)).point := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    rw [batch_recurrence, batch_recurrence, hp, h t (Nat.lt_succ_self t)]
noncomputable def pastPoint (P : Public) (data : Data P) (η : ℝ) :
    (t : ℕ) → (Fin t → Weights P.dimension) → Weights P.dimension
  | 0, _ => P.start
  | t + 1, z =>
    let w := pastPoint P data η t (fun j => z j.castSucc)
    if Separates data w then w else
      w + (η / (P.count : ℝ)) • (∑ i : Fin P.count,
        if (answer (data i) w).margin ≤ 0 then (answer (data i) w).direction else 0) +
        P.noiseScale • z (Fin.last t)

lemma batch_point_factor (P : Public) (data : Data P) (η : ℝ)
    (t : ℕ) (ω : P.noise.Ω) :
    (trajectory P data η ω ((P.count : ℕ) * t)).point =
      pastPoint P data η t (fun j => P.noise.sample j ω) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [batch_recurrence, ih]
    rfl

lemma measurable_pastPoint (P : Public) (data : Data P) (η : ℝ) (t : ℕ) :
    Measurable (pastPoint P data η t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hp : Measurable (fun z : Fin (t + 1) → Weights P.dimension =>
        pastPoint P data η t (fun j => z j.castSucc)) :=
      ih.comp (Measurable.of_eval fun j => measurable_pi_apply j.castSucc)
    change Measurable (fun z : Fin (t + 1) → Weights P.dimension =>
      let w := pastPoint P data η t (fun j => z j.castSucc)
      if Separates data w then w else
        w + (η / (P.count : ℝ)) • (∑ i : Fin P.count,
          if (answer (data i) w).margin ≤ 0 then (answer (data i) w).direction else 0) +
          P.noiseScale • z (Fin.last t))
    dsimp only
    apply Measurable.ite ((measurableSet_separates P data).preimage hp) hp
    have hm := Finset.measurable_sum Finset.univ (fun i _ =>
      (measurable_wrong_direction P data i).comp hp)
    exact (hp.add (hm.const_smul (η / (P.count : ℝ)))).add
      ((measurable_pi_apply (Fin.last t)).const_smul P.noiseScale)
open ProbabilityTheory
open scoped RealInnerProductSpace

lemma independent_past_next {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (ξ : ℕ → Ω → E) (hξ : ∀ j, Measurable (ξ j))
    (hi : iIndepFun ξ μ) (t : ℕ) :
    IndepFun (fun ω (j : Fin t) => ξ j ω) (ξ t) μ := by
  have hd : Disjoint (Finset.range t) ({t} : Finset ℕ) := by simp
  have h := hi.indepFun_finset (Finset.range t) {t} hd hξ
  let f : ((j : Finset.range t) → E) → (Fin t → E) := fun z j => z ⟨j, Finset.mem_range.mpr j.isLt⟩
  let g : ((j : ({t} : Finset ℕ)) → E) → E := fun z => z ⟨t, Finset.mem_singleton_self t⟩
  have hf : Measurable f := Measurable.of_eval fun j => measurable_pi_apply _
  have hg : Measurable g := measurable_pi_apply _
  exact h.comp hf hg

lemma independent_batch_next (P : Public) (data : Data P) (η : ℝ) (t : ℕ)
    (hξ : ∀ j, Measurable (P.noise.sample j))
    (hi : iIndepFun P.noise.sample (P.noise.law : Measure P.noise.Ω)) :
    IndepFun (fun ω => (trajectory P data η ω ((P.count : ℕ) * t)).point)
      (P.noise.sample t) (P.noise.law : Measure P.noise.Ω) := by
  have h := independent_past_next (P.noise.law : Measure P.noise.Ω) P.noise.sample hξ hi t
  have hc := h.comp (measurable_pastPoint P data η t) measurable_id
  have he : (fun ω => (trajectory P data η ω ((P.count : ℕ) * t)).point) =
      (pastPoint P data η t) ∘ (fun ω (j : Fin t) => P.noise.sample j ω) :=
    funext fun ω => batch_point_factor P data η t ω
  rw [he]
  exact hc
lemma integral_past_next {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : Measure E) [SFinite p]
    (ξ : ℕ → Ω → E) (hξ : ∀ j, Measurable (ξ j)) (hi : iIndepFun ξ μ)
    (t : ℕ) (hp : μ.map (ξ t) = p)
    (H : (Fin t → E) × E → ℝ)
    (hH : Integrable H ((μ.map (fun ω (j : Fin t) => ξ j ω)).prod p)) :
    (∫ ω, H ((fun j : Fin t => ξ j ω), ξ t ω) ∂μ) =
      ∫ x, ∫ z, H (x, z) ∂p ∂μ.map (fun ω (j : Fin t) => ξ j ω) := by
  have hP : Measurable (fun ω (j : Fin t) => ξ j ω) := Measurable.of_eval fun j => hξ j
  have hpair := hP.prodMk (hξ t)
  have hm := (independent_past_next μ ξ hξ hi t).map_prod_eq_prod_map_map
    hP.aemeasurable (hξ t).aemeasurable
  rw [hp] at hm
  have hHm : AEStronglyMeasurable H (μ.map (fun ω => ((fun j : Fin t => ξ j ω), ξ t ω))) := by
    rw [hm]
    exact hH.aestronglyMeasurable
  rw [← integral_map hpair.aemeasurable hHm, hm]
  exact integral_prod H hH

lemma memLp_answer_direction {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {d : ℕ} (a : Features d) (w : Ω → Weights d) (hw : MemLp w 2 μ) :
    MemLp (fun ω => (answer a (w ω)).direction) 2 μ := by
  let L : Weights d →L[ℝ] Weights d :=
    { toFun := fun z => (answer a z).direction
      map_add' := by
        intro x y
        apply WithLp.ofLp_injective
        simp [answer, WithLp.ofLp_add, add_smul, inner_add_right]
      map_smul' := by
        intro r x
        apply WithLp.ofLp_injective
        simp [answer, WithLp.ofLp_smul, mul_smul, real_inner_smul_right]
      cont := continuous_answer_direction a }
  exact L.comp_memLp' hw
lemma memLp_wrong_direction {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (P : Public) (data : Data P) (i : Fin P.count) (w : Ω → Weights P.dimension)
    (hw : MemLp w 2 μ) (hm : Measurable w) :
    MemLp (fun ω => if (answer (data i) (w ω)).margin ≤ 0 then
      (answer (data i) (w ω)).direction else 0) 2 μ := by
  have hs : MeasurableSet {ω | (answer (data i) (w ω)).margin ≤ 0} :=
    measurableSet_le ((continuous_answer_margin (data i)).measurable.comp hm) measurable_const
  exact MemLp.indicator hs (memLp_answer_direction (data i) w hw)

lemma memLp_batch_point (P : Public) (data : Data P) (η : ℝ)
    (hξ : ∀ j, Measurable (P.noise.sample j))
    (hM : ∀ j, MemLp (P.noise.sample j) 2 (P.noise.law : Measure P.noise.Ω)) (t : ℕ) :
    MemLp (fun ω => (trajectory P data η ω ((P.count : ℕ) * t)).point) 2
      (P.noise.law : Measure P.noise.Ω) := by
  induction t with
  | zero => exact memLp_const P.start
  | succ t ih =>
    let w := fun ω => (trajectory P data η ω ((P.count : ℕ) * t)).point
    have hm : Measurable w := measurable_batch_point P data η hξ t
    have hs := memLp_finsetSum Finset.univ (fun i _ => memLp_wrong_direction P data i w ih hm)
    have hinc := (hs.const_smul (η / (P.count : ℝ))).add ((hM t).const_smul P.noiseScale)
    have hset : MeasurableSet {ω | ¬Separates data (w ω)} :=
      ((measurableSet_separates P data).preimage hm).compl
    have h := ih.add (MemLp.indicator hset hinc)
    have he : (fun ω => (trajectory P data η ω ((P.count : ℕ) * (t + 1))).point) =
        (fun ω => w ω + {ω | ¬Separates data (w ω)}.indicator
          (fun ω => (η / (P.count : ℝ)) • (∑ i : Fin P.count,
            if (answer (data i) (w ω)).margin ≤ 0 then (answer (data i) (w ω)).direction else 0) +
            P.noiseScale • P.noise.sample t ω) ω) := by
      funext ω
      rw [batch_recurrence]
      change (if Separates data (w ω) then w ω else _) = _
      by_cases hh : Separates data (w ω) <;> simp [hh, Set.indicator, add_assoc, w]
    rw [he]
    exact h
lemma memLp_noise_sample (P : Public)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω)) (t : ℕ) :
    MemLp (P.noise.sample t) 2 (P.noise.law : Measure P.noise.Ω) := by
  have hm : MemLp (id : Weights P.dimension → Weights P.dimension) 2
      ((P.noise.law : Measure P.noise.Ω).map (P.noise.sample t)) := by
    rw [h.marginal t]
    exact IsGaussian.memLp_two_id
  exact (memLp_map_measure_iff (by fun_prop) (h.measurable t).aemeasurable).mp hm

lemma integral_past_next_of_integrable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : Measure E) [SFinite p]
    (ξ : ℕ → Ω → E) (hξ : ∀ j, Measurable (ξ j)) (hi : iIndepFun ξ μ)
    (t : ℕ) (hp : μ.map (ξ t) = p)
    (H : (Fin t → E) × E → ℝ) (hm : Measurable H)
    (hH : Integrable (fun ω => H ((fun j : Fin t => ξ j ω), ξ t ω)) μ) :
    (∫ ω, H ((fun j : Fin t => ξ j ω), ξ t ω) ∂μ) =
      ∫ x, ∫ z, H (x, z) ∂p ∂μ.map (fun ω (j : Fin t) => ξ j ω) := by
  have hP : Measurable (fun ω (j : Fin t) => ξ j ω) := Measurable.of_eval fun j => hξ j
  have hpair := hP.prodMk (hξ t)
  have hmap := (independent_past_next μ ξ hξ hi t).map_prod_eq_prod_map_map
    hP.aemeasurable (hξ t).aemeasurable
  rw [hp] at hmap
  apply integral_past_next μ p ξ hξ hi t hp H
  rw [← hmap]
  exact (integrable_map_measure hm.aestronglyMeasurable hpair.aemeasurable).mpr hH

lemma measurable_snoc {E : Type*} [MeasurableSpace E] (t : ℕ) :
    Measurable (fun z : (Fin t → E) × E => (Fin.snoc z.1 z.2 : Fin (t + 1) → E)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using (measurable_snd : Measurable (fun z : (Fin t → E) × E => z.2))
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using (measurable_pi_apply j).comp
      (measurable_fst : Measurable (fun z : (Fin t → E) × E => z.1))

lemma sample_snoc {Ω E : Type*} (ξ : ℕ → Ω → E) (t : ℕ) (ω : Ω) :
    Fin.snoc (fun j : Fin t => ξ j ω) (ξ t ω) = (fun j : Fin (t + 1) => ξ j ω) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

lemma pastPoint_snoc (P : Public) (data : Data P) (η : ℝ) (t : ℕ)
    (x : Fin t → Weights P.dimension) (z : Weights P.dimension) :
    pastPoint P data η (t + 1) (Fin.snoc x z) =
      let w := pastPoint P data η t x
      if Separates data w then w else
        w + (η / (P.count : ℝ)) • (∑ i : Fin P.count,
          if (answer (data i) w).margin ≤ 0 then (answer (data i) w).direction else 0) +
          P.noiseScale • z := by
  simp [pastPoint]
lemma integral_past_next_le {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : Measure E) [SFinite p]
    (ξ : ℕ → Ω → E) (hξ : ∀ j, Measurable (ξ j)) (hi : iIndepFun ξ μ)
    (t : ℕ) (hp : μ.map (ξ t) = p)
    (H : (Fin t → E) × E → ℝ) (hm : Measurable H)
    (hH : Integrable (fun ω => H ((fun j : Fin t => ξ j ω), ξ t ω)) μ)
    (B : (Fin t → E) → ℝ) (hB : Measurable B)
    (hBi : Integrable (fun ω => B (fun j : Fin t => ξ j ω)) μ)
    (hbound : ∀ x, (∫ z, H (x, z) ∂p) ≤ B x) :
    (∫ ω, H ((fun j : Fin t => ξ j ω), ξ t ω) ∂μ) ≤
      ∫ ω, B (fun j : Fin t => ξ j ω) ∂μ := by
  have hP : Measurable (fun ω (j : Fin t) => ξ j ω) := Measurable.of_eval fun j => hξ j
  have hpair := hP.prodMk (hξ t)
  have hmap := (independent_past_next μ ξ hξ hi t).map_prod_eq_prod_map_map
    hP.aemeasurable (hξ t).aemeasurable
  rw [hp] at hmap
  have hHp : Integrable H ((μ.map (fun ω (j : Fin t) => ξ j ω)).prod p) := by
    rw [← hmap]
    exact (integrable_map_measure hm.aestronglyMeasurable hpair.aemeasurable).mpr hH
  have hBp : Integrable B (μ.map (fun ω (j : Fin t) => ξ j ω)) :=
    (integrable_map_measure hB.aestronglyMeasurable hP.aemeasurable).mpr hBi
  rw [integral_past_next μ p ξ hξ hi t hp H hHp]
  calc
    _ ≤ ∫ x, B x ∂μ.map (fun ω (j : Fin t) => ξ j ω) :=
      integral_mono hHp.integral_prod_left hBp hbound
    _ = _ := integral_map hP.aemeasurable hB.aestronglyMeasurable

lemma independent_past_block {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (ξ : ℕ → Ω → E) (hξ : ∀ j, Measurable (ξ j))
    (hi : iIndepFun ξ μ) (t B : ℕ) :
    IndepFun (fun ω (j : Fin t) => ξ j ω) (fun ω (j : Fin B) => ξ (t + j) ω) μ := by
  have hd : Disjoint (Finset.range t) (Finset.Ico t (t + B)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Ico] at hj
    omega
  have h := hi.indepFun_finset (Finset.range t) (Finset.Ico t (t + B)) hd hξ
  let f : ((j : Finset.range t) → E) → (Fin t → E) := fun z j => z ⟨j, Finset.mem_range.mpr j.isLt⟩
  let g : ((j : Finset.Ico t (t + B)) → E) → (Fin B → E) := fun z j =>
    z ⟨t + j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
  have hf : Measurable f := Measurable.of_eval fun j => measurable_pi_apply _
  have hg : Measurable g := Measurable.of_eval fun j => measurable_pi_apply _
  exact h.comp hf hg
lemma iid_block_law {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (p : Measure E) (ξ : ℕ → Ω → E) (hξ : ∀ j, Measurable (ξ j))
    (hi : iIndepFun ξ μ) (hp : ∀ j, μ.map (ξ j) = p) (t B : ℕ) :
    μ.map (fun ω (j : Fin B) => ξ (t + j) ω) = Measure.pi (fun _ : Fin B => p) := by
  have hinj : Function.Injective (fun j : Fin B => t + j.val) := by
    intro i j hij
    exact Fin.ext (Nat.add_left_cancel hij)
  have hb := iIndepFun.precomp hinj hi
  have hm := hb.map_fun_eq_pi_map (fun j : Fin B => (hξ (t + j)).aemeasurable)
  simpa only [hp] using hm
lemma iid_block_event_probability {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (p : Measure E) [IsProbabilityMeasure p]
    (ξ : ℕ → Ω → E) (hξ : ∀ j, Measurable (ξ j))
    (hi : iIndepFun ξ μ) (hp : ∀ j, μ.map (ξ j) = p) (t B : ℕ)
    (S : Set E) (hS : MeasurableSet S) :
    μ {ω | ∀ j : Fin B, ξ (t + j) ω ∈ S} = (p S) ^ B := by
  have hm := iid_block_law μ p ξ hξ hi hp t B
  have hh := congrArg (fun ν : Measure (Fin B → E) => ν (Set.pi Set.univ (fun _ => S))) hm
  rw [Measure.map_apply (Measurable.of_eval fun j : Fin B => hξ (t + j))
    (MeasurableSet.univ_pi fun _ => hS), Measure.pi_pi] at hh
  simpa only [Set.pi, Set.mem_univ, true_implies, Set.preimage_ofPred_eq,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hh
lemma past_block_event_probability {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (p : Measure E) [IsProbabilityMeasure p]
    (ξ : ℕ → Ω → E) (hξ : ∀ j, Measurable (ξ j))
    (hi : iIndepFun ξ μ) (hp : ∀ j, μ.map (ξ j) = p) (t B : ℕ)
    (A : Set (Fin t → E)) (hA : MeasurableSet A) (S : Set E) (hS : MeasurableSet S) :
    μ ({ω | (fun j : Fin t => ξ j ω) ∈ A} ∩ {ω | ∀ j : Fin B, ξ (t + j) ω ∈ S}) =
      μ {ω | (fun j : Fin t => ξ j ω) ∈ A} * (p S) ^ B := by
  have hd := (independent_past_block μ ξ hξ hi t B).measure_inter_preimage_eq_mul
    A (Set.pi Set.univ fun _ : Fin B => S) hA (MeasurableSet.univ_pi fun _ => hS)
  have he : (fun ω (j : Fin B) => ξ (t + j) ω) ⁻¹' Set.pi Set.univ (fun _ => S) =
      {ω | ∀ j : Fin B, ξ (t + j) ω ∈ S} := by ext ω; simp
  rw [he, iid_block_event_probability μ p ξ hξ hi hp t B S hS] at hd
  exact hd

lemma product_success_lower {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (A : Set X) (hA : MeasurableSet A) (J : Set (X × Y)) (hJ : MeasurableSet J)
    (q : ENNReal) (hq : ∀ x ∈ A, q ≤ ν {y | (x, y) ∈ J}) :
    q * μ A ≤ (μ.prod ν) (Prod.fst ⁻¹' A ∩ J) := by
  rw [Measure.prod_apply ((hA.preimage measurable_fst).inter hJ)]
  calc
    _ = ∫⁻ x, A.indicator (fun _ => q) x ∂μ := by rw [lintegral_indicator hA, setLIntegral_const]
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx]
        have he : Prod.mk x ⁻¹' (Prod.fst ⁻¹' A ∩ J) = {y | (x, y) ∈ J} := by ext y; simp [hx]
        rw [he]
        exact hq x hx
      · simp only [Set.indicator_of_notMem hx]
        exact zero_le
lemma past_block_success_lower {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Measure E) [IsProbabilityMeasure p]
    (ξ : ℕ → Ω → E) (hξ : ∀ j, Measurable (ξ j))
    (hi : iIndepFun ξ μ) (hp : ∀ j, μ.map (ξ j) = p) (t B : ℕ)
    (A : Set (Fin t → E)) (hA : MeasurableSet A)
    (J : Set ((Fin t → E) × (Fin B → E))) (hJ : MeasurableSet J)
    (q : ENNReal) (hq : ∀ x ∈ A, q ≤ (Measure.pi (fun _ : Fin B => p)) {y | (x, y) ∈ J}) :
    q * μ {ω | (fun j : Fin t => ξ j ω) ∈ A} ≤
      μ {ω | (fun j : Fin t => ξ j ω) ∈ A ∧
        ((fun j : Fin t => ξ j ω), (fun j : Fin B => ξ (t + j) ω)) ∈ J} := by
  have hP : Measurable (fun ω (j : Fin t) => ξ j ω) := Measurable.of_eval fun j => hξ j
  have hQ : Measurable (fun ω (j : Fin B) => ξ (t + j) ω) := Measurable.of_eval fun j => hξ (t + j)
  have hm := (independent_past_block μ ξ hξ hi t B).map_prod_eq_prod_map_map hP.aemeasurable hQ.aemeasurable
  rw [iid_block_law μ p ξ hξ hi hp t B] at hm
  have hb := product_success_lower (μ.map (fun ω (j : Fin t) => ξ j ω))
    (Measure.pi (fun _ : Fin B => p)) A hA J hJ q hq
  rw [← hm, Measure.map_apply (hP.prodMk hQ) ((hA.preimage measurable_fst).inter hJ),
    Measure.map_apply hP hA] at hb
  exact hb
lemma measurable_append {E : Type*} [MeasurableSpace E] (t B : ℕ) :
    Measurable (fun z : (Fin t → E) × (Fin B → E) => Fin.append z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left, Function.comp_def] using (measurable_pi_apply j).comp measurable_fst
  · simpa only [Fin.append_right, Function.comp_def] using (measurable_pi_apply j).comp measurable_snd
lemma sample_append {Ω E : Type*} (ξ : ℕ → Ω → E) (t B : ℕ) (ω : Ω) :
    Fin.append (fun j : Fin t => ξ j ω) (fun j : Fin B => ξ (t + j) ω) =
      (fun j : Fin (t + B) => ξ j ω) := by
  simpa only [Fin.val_castAdd, Fin.val_natAdd] using
    (Fin.append_castAdd_natAdd (f := fun j : Fin (t + B) => ξ j ω))
lemma block_point_factor (P : Public) (data : Data P) (η : ℝ) (t B : ℕ) (ω : P.noise.Ω) :
    (trajectory P data η ω ((P.count : ℕ) * (t + B))).point =
      pastPoint P data η (t + B)
        (Fin.append (fun j : Fin t => P.noise.sample j ω) (fun j : Fin B => P.noise.sample (t + j) ω)) := by
  rw [batch_point_factor, sample_append]
lemma measurableSet_block_success (P : Public) (data : Data P) (η : ℝ) (t B : ℕ) :
    MeasurableSet {z : (Fin t → Weights P.dimension) × (Fin B → Weights P.dimension) |
      Separates data (pastPoint P data η (t + B) (Fin.append z.1 z.2))} :=
  (measurableSet_separates P data).preimage ((measurable_pastPoint P data η (t + B)).comp (measurable_append t B))
lemma tested_block_success_lower (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (t B : ℕ) (A : Set (Fin t → Weights P.dimension)) (hA : MeasurableSet A)
    (q : ENNReal)
    (hq : ∀ x ∈ A, q ≤ (Measure.pi (fun _ : Fin B => stdGaussian (Weights P.dimension)))
      {y | Separates data (pastPoint P data η (t + B) (Fin.append x y))}) :
    q * (P.noise.law : Measure P.noise.Ω) {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A} ≤
      (P.noise.law : Measure P.noise.Ω) {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A ∧
        Separates data (trajectory P data η ω ((P.count : ℕ) * (t + B))).point} := by
  have hb := past_block_success_lower (P.noise.law : Measure P.noise.Ω)
    (stdGaussian (Weights P.dimension)) P.noise.sample h.measurable h.independent h.marginal t B A hA
    {z | Separates data (pastPoint P data η (t + B) (Fin.append z.1 z.2))}
    (measurableSet_block_success P data η t B) q hq
  simpa only [Set.mem_ofPred_eq, ← block_point_factor] using hb

end LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution

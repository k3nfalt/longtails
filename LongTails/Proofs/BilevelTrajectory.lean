import LongTails.Proofs.BilevelEpochConvergence
import LongTails.Algorithms.BilevelAccelerated

namespace LongTails.Proofs.BilevelTrajectory

open Finset LongTails.Setups.HigherSmoothBilevel LongTails.Algorithms.BilevelAccelerated
open BilevelEpochVector BilevelEpochConvergence

structure EpochTrace (p : Params) (t : Tuning) (g : p.X → p.X) (σ : ℝ) (s : OuterState p.X) where
  Z : ℕ → p.X
  D : ℕ → p.X
  V : ℕ → p.X
  zero_position : Z 0 = 0
  zero_velocity : D 0 = 0
  position : ∀ k, k < s.index → Z (k + 1) = Z k + D (k + 1)
  velocity : ∀ k, k < s.index → D (k + 1) = (1 - t.θ) • D k - t.η • V k
  error : ∀ k, k < s.index → ‖V k - g (s.start + (Z k + (1 - t.θ) • D k))‖ ≤ σ
  current : s.x = s.start + Z s.index
  previous : s.previous = s.start + Z s.index - D s.index
  movement : s.movement = ∑ k ∈ range s.index, ‖D (k + 1)‖ ^ 2
  querySum : s.querySum = (s.index : ℝ) • s.start + ∑ k ∈ range s.index, (Z k + (1 - t.θ) • D k)
  prefixBound : ∀ k, k ≤ s.index → (k : ℝ) * (∑ j ∈ range k, ‖D (j + 1)‖ ^ 2) ≤ t.B ^ 2
  selection : t.K / 2 < s.index → ∃ j ∈ Ico (t.K / 2) s.index,
    s.bestMovement = ‖D (j + 1)‖ ^ 2 ∧
    s.bestOutput = s.start + ((j + 1 : ℕ) : ℝ)⁻¹ •
      (∑ k ∈ range (j + 1), (Z k + (1 - t.θ) • D k)) ∧
    ∀ k ∈ Ico (t.K / 2) s.index, ‖D (j + 1)‖ ^ 2 ≤ ‖D (k + 1)‖ ^ 2

noncomputable def initialTrace (p : Params) (t : Tuning) (g : p.X → p.X) (σ : ℝ) (a : p.X) :
    EpochTrace p t g σ (initial a) where
  Z := fun _ => 0
  D := fun _ => 0
  V := fun _ => 0
  zero_position := rfl
  zero_velocity := rfl
  position := by simp [initial]
  velocity := by simp [initial]
  error := by simp [initial]
  current := by simp [initial]
  previous := by simp [initial]
  movement := by simp [initial]
  querySum := by simp [initial]
  prefixBound := by
    intro k hk
    have hk0 : k = 0 := by simpa [initial] using hk
    subst k
    simpa using sq_nonneg t.B
  selection := by simp [initial]

lemma query_relative {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (hf : s.finished = false) :
    context p t s = s.start + (T.Z s.index + (1 - t.θ) • T.D s.index) := by
  unfold context
  rw [hf]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [T.current, T.previous]
  module

lemma query_radius {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (hf : s.finished = false) (hB : 0 ≤ t.B)
    (hθ : 0 ≤ t.θ) (hθ1 : t.θ ≤ 1) : ‖context p t s - s.start‖ ≤ 2 * t.B := by
  rw [query_relative T hf, add_sub_cancel_left]
  have hp := prefix_radius T.Z T.D s.index hB T.zero_position T.zero_velocity T.position
    (T.prefixBound s.index le_rfl)
  exact extrapolated_radius hθ hθ1 hp.1 hp.2

noncomputable def extendZ {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) : ℕ → p.X :=
  Function.update T.Z (s.index + 1) (T.Z s.index + (1 - t.θ) • T.D s.index - t.η • v)

noncomputable def extendD {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) : ℕ → p.X :=
  Function.update T.D (s.index + 1) ((1 - t.θ) • T.D s.index - t.η • v)

noncomputable def extendV {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) : ℕ → p.X := Function.update T.V s.index v

lemma extend_old {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) {k : ℕ} (hk : k ≤ s.index) :
    extendZ T v k = T.Z k ∧ extendD T v k = T.D k := by
  simp [extendZ, extendD, show k ≠ s.index + 1 by omega]

lemma extend_position {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) :
    ∀ k, k < s.index + 1 → extendZ T v (k + 1) = extendZ T v k + extendD T v (k + 1) := by
  intro k hk
  by_cases heq : k = s.index
  · subst k
    simp [extendZ, extendD]
    module
  · have hki : k < s.index := by omega
    rw [(extend_old T v (by omega : k + 1 ≤ s.index)).1,
      (extend_old T v (by omega : k ≤ s.index)).1,
      (extend_old T v (by omega : k + 1 ≤ s.index)).2]
    exact T.position k hki

lemma extend_velocity {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) :
    ∀ k, k < s.index + 1 → extendD T v (k + 1) = (1 - t.θ) • extendD T v k - t.η • extendV T v k := by
  intro k hk
  by_cases heq : k = s.index
  · subst k
    simp [extendD, extendV]
  · have hki : k < s.index := by omega
    rw [(extend_old T v (by omega : k + 1 ≤ s.index)).2,
      (extend_old T v (by omega : k ≤ s.index)).2]
    simpa [extendV, heq] using T.velocity k hki

lemma extend_error {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) (hf : s.finished = false)
    (herr : ‖v - g (context p t s)‖ ≤ σ) :
    ∀ k, k < s.index + 1 → ‖extendV T v k -
      g (s.start + (extendZ T v k + (1 - t.θ) • extendD T v k))‖ ≤ σ := by
  intro k hk
  rw [(extend_old T v (by omega : k ≤ s.index)).1, (extend_old T v (by omega : k ≤ s.index)).2]
  by_cases heq : k = s.index
  · subst k
    simpa [extendV, query_relative T hf] using herr
  · simpa [extendV, heq] using T.error k (by omega)

lemma extend_movement_prefix {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) {k : ℕ} (hk : k ≤ s.index) :
    (∑ j ∈ range k, ‖extendD T v (j + 1)‖ ^ 2) = ∑ j ∈ range k, ‖T.D (j + 1)‖ ^ 2 := by
  apply sum_congr rfl
  intro j hj
  rw [(extend_old T v (by have := mem_range.mp hj; omega : j + 1 ≤ s.index)).2]

lemma extend_query_sum {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) {k : ℕ} (hk : k ≤ s.index + 1) :
    (∑ j ∈ range k, (extendZ T v j + (1 - t.θ) • extendD T v j)) =
      ∑ j ∈ range k, (T.Z j + (1 - t.θ) • T.D j) := by
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ s.index := by have := mem_range.mp hj; omega
  rw [(extend_old T v hj').1, (extend_old T v hj').2]

lemma selected_extension {X : Type*} (value : ℕ → ℝ) (output : ℕ → X)
    (lo i : ℕ) (best : ℝ) (bestOutput : X)
    (hold : lo < i → ∃ j ∈ Ico lo i, best = value j ∧ bestOutput = output j ∧
      ∀ k ∈ Ico lo i, value j ≤ value k) (hnew : lo < i + 1) :
    let choose := lo ≤ i ∧ (i = lo ∨ value i < best)
    ∃ j ∈ Ico lo (i + 1), (if choose then value i else best) = value j ∧
      (if choose then output i else bestOutput) = output j ∧
      ∀ k ∈ Ico lo (i + 1), value j ≤ value k := by
  classical
  dsimp only
  by_cases hc : lo ≤ i ∧ (i = lo ∨ value i < best)
  · simp only [ite_eq_left hc]
    refine ⟨i, mem_Ico.mpr ⟨hc.1, by omega⟩, rfl, rfl, ?_⟩
    intro k hk
    by_cases hki : k = i
    · subst k; exact le_rfl
    have hkl : lo ≤ k := (mem_Ico.mp hk).1
    have hki' : k < i := by have := (mem_Ico.mp hk).2; omega
    have hlo : lo < i := by omega
    obtain ⟨j, hj, hb, _, hmin⟩ := hold hlo
    have hv : value i < best := hc.2.resolve_left (by omega)
    rw [hb] at hv
    exact hv.le.trans (hmin k (mem_Ico.mpr ⟨hkl, hki'⟩))
  · simp only [ite_eq_right hc]
    have hlo : lo < i := by
      by_contra hh
      have hi : i = lo := by omega
      exact hc ⟨by omega, Or.inl hi⟩
    obtain ⟨j, hj, hb, ho, hmin⟩ := hold hlo
    refine ⟨j, mem_Ico.mpr ⟨(mem_Ico.mp hj).1, by have := (mem_Ico.mp hj).2; omega⟩, hb, ho, ?_⟩
    intro k hk
    by_cases hki : k = i
    · subst k
      have hv : best ≤ value i := by
        by_contra hh
        exact hc ⟨by omega, Or.inr (lt_of_not_ge hh)⟩
      simpa [hb] using hv
    · exact hmin k (mem_Ico.mpr ⟨(mem_Ico.mp hk).1, by have := (mem_Ico.mp hk).2; omega⟩)

lemma next_point {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) (hf : s.finished = false) :
    context p t s - t.η • v = s.start + extendZ T v (s.index + 1) := by
  rw [query_relative T hf]
  simp only [extendZ, Function.update_self]
  module

lemma next_movement {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) (hf : s.finished = false) :
    context p t s - t.η • v - s.x = extendD T v (s.index + 1) := by
  rw [query_relative T hf, T.current]
  simp only [extendD, Function.update_self]
  module

lemma next_query_sum {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) (hf : s.finished = false) :
    s.querySum + context p t s = ((s.index + 1 : ℕ) : ℝ) • s.start +
      ∑ k ∈ range (s.index + 1), (extendZ T v k + (1 - t.θ) • extendD T v k) := by
  rw [extend_query_sum T v le_rfl, sum_range_succ, T.querySum, query_relative T hf]
  push_cast
  module

lemma next_movement_sum {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) (hf : s.finished = false) :
    s.movement + ‖context p t s - t.η • v - s.x‖ ^ 2 =
      ∑ k ∈ range (s.index + 1), ‖extendD T v (k + 1)‖ ^ 2 := by
  rw [sum_range_succ, extend_movement_prefix T v le_rfl, T.movement, next_movement T v hf]

noncomputable def retainedTrace {p : Params} {t : Tuning} {g : p.X → p.X} {σ : ℝ} {s : OuterState p.X}
    (T : EpochTrace p t g σ s) (v : p.X) (hf : s.finished = false)
    (herr : ‖v - g (context p t s)‖ ≤ σ)
    (hstay : ((s.index + 1 : ℕ) : ℝ) *
      (s.movement + ‖context p t s - t.η • v - s.x‖ ^ 2) ≤ t.B ^ 2) :
    EpochTrace p t g σ (advance p t s v) := by
  classical
  have hstay' := not_lt.mpr hstay
  simp only [advance, hf, Bool.false_eq_true, ↓reduceIte, hstay']
  refine {
    Z := extendZ T v
    D := extendD T v
    V := extendV T v
    zero_position := ?_
    zero_velocity := ?_
    position := extend_position T v
    velocity := extend_velocity T v
    error := extend_error T v hf herr
    current := next_point T v hf
    previous := ?_
    movement := next_movement_sum T v hf
    querySum := next_query_sum T v hf
    prefixBound := ?_
    selection := ?_ }
  · exact (extend_old T v (Nat.zero_le _)).1.trans T.zero_position
  · exact (extend_old T v (Nat.zero_le _)).2.trans T.zero_velocity
  · rw [T.current]
    simp only [extendZ, extendD, Function.update_self]
    module
  · intro k hk
    change k ≤ s.index + 1 at hk
    by_cases heq : k = s.index + 1
    · subst k
      rw [← next_movement_sum T v hf]
      exact hstay
    · rw [extend_movement_prefix T v (by omega)]
      exact T.prefixBound k (by omega)
  · intro hlo
    let value := fun k => ‖extendD T v (k + 1)‖ ^ 2
    let output := fun k => s.start + ((k + 1 : ℕ) : ℝ)⁻¹ •
      (∑ j ∈ range (k + 1), (extendZ T v j + (1 - t.θ) • extendD T v j))
    have hold : t.K / 2 < s.index → ∃ j ∈ Ico (t.K / 2) s.index,
        s.bestMovement = value j ∧ s.bestOutput = output j ∧
        ∀ k ∈ Ico (t.K / 2) s.index, value j ≤ value k := by
      intro hi
      obtain ⟨j, hj, hb, ho, hmin⟩ := T.selection hi
      have hj' : j + 1 ≤ s.index := by have := (mem_Ico.mp hj).2; omega
      have hvj : value j = ‖T.D (j + 1)‖ ^ 2 := by dsimp [value]; rw [(extend_old T v hj').2]
      refine ⟨j, hj, hb.trans hvj.symm, ?_, ?_⟩
      · dsimp [output]
        rw [extend_query_sum T v (by omega)]
        exact ho
      · intro k hk
        rw [hvj]
        dsimp [value]
        rw [(extend_old T v (by have := (mem_Ico.mp hk).2; omega : k + 1 ≤ s.index)).2]
        exact hmin k hk
    have hh := selected_extension value output (t.K / 2) s.index s.bestMovement s.bestOutput hold hlo
    dsimp only at hh
    rw [next_movement T v hf, next_query_sum T v hf, average_translate _ _ (Nat.succ_pos s.index)]
    exact hh

lemma advance_frozen {p : Params} {t : Tuning} {s : OuterState p.X} (v : p.X)
    (hf : s.finished = true) : advance p t s v = s := by simp [advance, hf]

lemma advance_restart {p : Params} {t : Tuning} {s : OuterState p.X} (v : p.X)
    (hf : s.finished = false)
    (hexit : t.B ^ 2 < ((s.index + 1 : ℕ) : ℝ) *
      (s.movement + ‖context p t s - t.η • v - s.x‖ ^ 2)) :
    advance p t s v = initial (context p t s - t.η • v) := by simp only [advance, hf, Bool.false_eq_true, ↓reduceIte, hexit]

lemma trace_success_accuracy {p : Params} {t : Tuning} {g : p.X → p.X} {A : p.X → p.X →L[ℝ] p.X}
    {s : OuterState p.X} {ρ e : ℝ} (T : EpochTrace p t g (e / 100) s)
    (hg : ∀ x, HasFDerivAt g (A x) x) (hη : 0 < t.η) (hρ : 0 ≤ ρ) (hB : 0 < t.B)
    (he : 0 < e) (hK : 2 ≤ t.K) (hθ : t.θ = 1 / (t.K : ℝ))
    (hLip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖)
    (hBe : ρ * t.B ^ 2 = e) (hlower : t.B ≤ 128 * t.η * (t.K : ℝ) ^ 2 * e)
    (hi : s.index = t.K) (hresult : s.result = s.bestOutput) : ‖g s.result‖ ≤ 773 * e := by
  have hlo : t.K / 2 < s.index := by omega
  obtain ⟨j, hj, _, hout, hmin⟩ := T.selection hlo
  rw [hresult, hout]
  have hj' : j ∈ Ico (t.K / 2) t.K := by simpa [hi] using hj
  have hm' : ∀ k ∈ Ico (t.K / 2) t.K, ‖T.D (j + 1)‖ ^ 2 ≤ ‖T.D (k + 1)‖ ^ 2 := by simpa [hi] using hmin
  have hh := successful_epoch_accuracy hg hη hρ hB he hK hLip hBe hlower s.start T.Z T.D T.V
    T.zero_position T.zero_velocity
    (fun k hk => T.position k (by omega))
    (fun k hk => by simpa [hθ] using T.velocity k (by omega))
    (fun k hk => by simpa [hθ] using T.error k (by omega))
    (T.prefixBound t.K (by omega)) hj' hm'
  simpa [hθ] using hh

lemma trace_failure_decrease {p : Params} {t : Tuning} {f : p.X → ℝ} {g : p.X → p.X}
    {A : p.X → p.X →L[ℝ] p.X} {s : OuterState p.X} {L ρ e : ℝ}
    (T : EpochTrace p t g (e / 100) s) (v : p.X) (hs : s.finished = false)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (A x) x)
    (hL : 0 ≤ L) (hρ : 0 < ρ) (hη : 0 < t.η) (hB : 0 < t.B) (he : 0 < e)
    (hK : 2 ≤ t.K) (hθ : t.θ = 1 / (t.K : ℝ)) (hi : s.index < t.K)
    (hηL : t.η * L ≤ 1 / 4) (hgrad : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hHess : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖)
    (hBe : ρ * t.B ^ 2 = e) (hmaster : 32 * t.η * (t.K : ℝ) ^ 2 * e ≤ t.B)
    (hsym : (A s.start).toLinearMap.IsSymmetric) (hA : ‖A s.start‖ ≤ L)
    (herr : ‖v - g (context p t s)‖ ≤ e / 100)
    (hexit : t.B ^ 2 < ((s.index + 1 : ℕ) : ℝ) *
      (s.movement + ‖context p t s - t.η • v - s.x‖ ^ 2)) :
    f (context p t s - t.η • v) - f s.start ≤ -(e * t.B) := by
  rw [next_point T v hs]
  have hzeroZ := (extend_old T v (Nat.zero_le _)).1.trans T.zero_position
  have hzeroD := (extend_old T v (Nat.zero_le _)).2.trans T.zero_velocity
  have hvel : ∀ k, k < s.index + 1 → extendD T v (k + 1) =
      (1 - 1 / (t.K : ℝ)) • extendD T v k - t.η • extendV T v k := by
    simpa [hθ] using extend_velocity T v
  have herr' : ∀ k, k < s.index + 1 → ‖extendV T v k -
      g (s.start + (extendZ T v k + (1 - 1 / (t.K : ℝ)) • extendD T v k))‖ ≤ e / 100 := by
    simpa [hθ] using extend_error T v hs herr
  have hpref : ∀ k, k < s.index + 1 → (k : ℝ) *
      (∑ j ∈ range k, ‖extendD T v (j + 1)‖ ^ 2) ≤ t.B ^ 2 := by
    intro k hk
    rw [extend_movement_prefix T v (by omega)]
    exact T.prefixBound k (by omega)
  rw [next_movement_sum T v hs] at hexit
  exact failed_epoch_decrease hf hg hL hρ hη hB he hK (Nat.succ_pos _) (by omega) hηL
    hgrad hHess hBe hmaster s.start hsym hA (extendZ T v) (extendD T v) (extendV T v)
    hzeroZ hzeroD (extend_position T v) hvel herr' hpref hexit

lemma advance_retained_fields {p : Params} {t : Tuning} {s : OuterState p.X} (v : p.X)
    (hf : s.finished = false)
    (hstay : ((s.index + 1 : ℕ) : ℝ) *
      (s.movement + ‖context p t s - t.η • v - s.x‖ ^ 2) ≤ t.B ^ 2) :
    (advance p t s v).index = s.index + 1 ∧ (advance p t s v).start = s.start ∧
    (advance p t s v).finished = decide (s.index + 1 = t.K) ∧
    (advance p t s v).result = (advance p t s v).bestOutput := by
  simp only [advance, hf, Bool.false_eq_true, ↓reduceIte, not_lt.mpr hstay, and_self]

end LongTails.Proofs.BilevelTrajectory

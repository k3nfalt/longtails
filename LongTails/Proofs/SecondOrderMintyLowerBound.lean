import LongTails.Setups.HighDimensionalWeakMintySecondOrder
import LongTails.Proofs.Execution
import LongTails.Proofs.SecondOrderMintyHiding
import LongTails.Proofs.LocalizedMonotoneLowerBound
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic
import LongTails.Setups.WeakMintySecondOrderExpected

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SecondOrderMintyLowerBound

open SecondOrderMintyChain SecondOrderMintyInstance SecondOrderMintyHiding

noncomputable def link (R : ℝ) (n : ℕ) : ℝ := R / Real.sqrt ((n : ℝ) + 1)

noncomputable def slope (R ε : ℝ) (n : ℕ) : ℝ := 8 * ε / link R n

lemma link_pos (R : ℝ) (hR : 0 < R) (n : ℕ) : 0 < link R n := by
  dsimp [link]
  positivity

lemma link_sq (R : ℝ) (n : ℕ) : link R n ^ 2 = R ^ 2 / ((n : ℝ) + 1) := by
  have hm : 0 ≤ (n : ℝ) + 1 := by positivity
  rw [link, div_pow, Real.sq_sqrt hm]

lemma link_count (R : ℝ) (n : ℕ) : ((n : ℝ) + 1) * link R n ^ 2 ≤ R ^ 2 := by
  have hm : 0 < (n : ℝ) + 1 := by positivity
  rw [link_sq]
  field_simp
  exact le_rfl

lemma link_le (R : ℝ) (hR : 0 < R) (n : ℕ) : link R n ≤ R := by
  have hs : 1 ≤ Real.sqrt ((n : ℝ) + 1) :=
    Real.one_le_sqrt.mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  exact div_le_self hR.le hs

lemma slope_mul_link (R ε : ℝ) (hR : 0 < R) (n : ℕ) : slope R ε n * link R n = 8 * ε := by
  have := link_pos R hR n
  dsimp [slope]
  field_simp

lemma first_order_scale (L₁ R ε : ℝ) (hL₁ : 0 < L₁) (hR : 0 < R) (hε : 0 < ε) (n : ℕ)
    (hn : ((n : ℝ) + 1) ≤ L₁ ^ 2 * R ^ 2 / (16384 * ε ^ 2)) :
    14 * slope R ε n ≤ L₁ := by
  have hs : Real.sqrt ((n : ℝ) + 1) ≤ L₁ * R / (128 * ε) := by
    rw [Real.sqrt_le_left (by positivity)]
    calc
      _ ≤ L₁ ^ 2 * R ^ 2 / (16384 * ε ^ 2) := hn
      _ = (L₁ * R / (128 * ε)) ^ 2 := by field_simp; ring
  have he : slope R ε n = 8 * ε * Real.sqrt ((n : ℝ) + 1) / R := by
    dsimp [slope, link]
    field_simp
  rw [he, show 14 * (8 * ε * Real.sqrt ((n : ℝ) + 1) / R) =
    112 * ε * Real.sqrt ((n : ℝ) + 1) / R by ring, div_le_iff₀ hR]
  have := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 112 * ε)
  have e : 112 * ε * (L₁ * R / (128 * ε)) = 7 / 8 * (L₁ * R) := by field_simp; ring
  nlinarith [mul_pos hL₁ hR]

lemma second_order_scale (L₂ R ε : ℝ) (hL₂ : 0 < L₂) (hR : 0 < R) (hε : 0 < ε) (n : ℕ)
    (hn : ((n : ℝ) + 1) ≤ L₂ * R ^ 2 / (16384 * ε)) :
    256 * slope R ε n / link R n + 416 * slope R ε n / (8 * R) ≤ L₂ := by
  set m : ℝ := (n : ℝ) + 1 with hm
  have hm1 : 1 ≤ m := by rw [hm]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hsq : Real.sqrt m ≤ m := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hl := link_pos R hR n
  have h1 : slope R ε n / link R n = 8 * ε * m / R ^ 2 := by
    have h2 := link_sq R n
    dsimp [slope]
    rw [div_div, ← sq, h2, ← hm]
    field_simp
  have h3 : slope R ε n / (8 * R) = ε * Real.sqrt m / R ^ 2 := by
    dsimp [slope, link]
    field_simp
    ring
  have hA : 256 * slope R ε n / link R n = 256 * (8 * ε * m / R ^ 2) := by
    rw [mul_div_assoc, h1]
  have hB : 416 * slope R ε n / (8 * R) = 416 * (ε * Real.sqrt m / R ^ 2) := by
    rw [mul_div_assoc, h3]
  rw [hA, hB]
  have hR2 : 0 < R ^ 2 := by positivity
  have hb : 416 * (ε * Real.sqrt m / R ^ 2) ≤ 416 * (ε * m / R ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hε.le) hR2.le
  have hc : 256 * (8 * ε * m / R ^ 2) + 416 * (ε * m / R ^ 2) = 2464 * ε * m / R ^ 2 := by ring
  have hd : 2464 * ε * m / R ^ 2 ≤ L₂ := by
    rw [div_le_iff₀ hR2]
    have := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 2464 * ε)
    have e : 2464 * ε * (L₂ * R ^ 2 / (16384 * ε)) = 2464 / 16384 * (L₂ * R ^ 2) := by
      field_simp
    nlinarith [mul_pos hL₂ hR2]
  linarith

noncomputable def shift {d : ℕ} (x0 : Space d) (q : Query d) : Query d :=
  Sum.map (fun x => x - x0) (fun x => x - x0) q

noncomputable def oracle {d n : ℕ} (x0 : Space d) (κ r b : ℝ) (π : Fin (n + 1) ↪ Fin d) :
    Oracle (Query d) (Reply d) where
  answer _ q _ := reply κ r b π (shift x0 q.2)

lemma execute_translated {d n : ℕ} (x0 : Space d) (κ r b : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (A : Algorithm (Query d) (Reply d) (Space d)) (N : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) :
    execute (oracle x0 κ r b π) A (fun _ => N) seed ξ =
      A.output ((fun s => A.update s (reply κ r b π (shift x0 (A.query s).2)))^[N]
        (A.initial seed)) := by
  rw [execute_eq_of_answer_eq (oracle x0 κ r b π) (fun q => reply κ r b π (shift x0 q))
    (by intros; rfl)]
  exact execute_iterate (fun q => reply κ r b π (shift x0 q)) A N seed

lemma instance_admissible (q : LongTails.Setups.HighDimensionalWeakMintySecondOrder.Params)
    (hL₁ : 0 < q.L₁) (hL₂ : 0 < q.L₂) (hρ : 0 ≤ q.ρ) (hR : 0 < q.R) (hε : 0 < q.ε) (n : ℕ)
    (hn1 : ((n : ℝ) + 1) ≤ q.L₁ ^ 2 * q.R ^ 2 / (16384 * q.ε ^ 2))
    (hn2 : ((n : ℝ) + 1) ≤ q.L₂ * q.R ^ 2 / (16384 * q.ε))
    (π : Fin (n + 1) ↪ Fin q.d) :
    let r := link q.R n
    let κ := slope q.R q.ε n
    LongTails.Setups.HighDimensionalWeakMintySecondOrder.spec.admissible q
      (fun x => field κ r (8 * q.R) π (x - q.x0)) (oracle q.x0 κ r (8 * q.R) π) := by
  intro r κ
  have hr : 0 < r := link_pos q.R hR n
  have hκ : 0 ≤ κ := by dsimp [κ, slope]; exact div_nonneg (by positivity) hr.le
  have hb : 0 < 8 * q.R := by positivity
  have hnr : ((n : ℝ) + 1) * r ^ 2 ≤ q.R ^ 2 := link_count q.R n
  refine ⟨fun x => jacobian κ r (8 * q.R) π (x - q.x0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k seed x
    rfl
  · intro k seed x
    rfl
  · intro x
    exact LocalizedMonotoneLowerBound.derivative_translate q.x0 (field κ r (8 * q.R) π)
      (jacobian κ r (8 * q.R) π) (field_hasFDerivAt κ r (8 * q.R) hr hb π) x
  · intro x y
    have h := jacobian_difference κ r (8 * q.R) hκ hr hb π (x - q.x0) (y - q.x0)
    rw [sub_sub_sub_cancel_right] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (second_order_scale q.L₂ q.R q.ε hL₂ hR hε n hn2) (norm_nonneg _))
  · intro x y
    have h := field_lipschitz κ r (8 * q.R) hκ hr hb π (x - q.x0) (y - q.x0)
    rw [sub_sub_sub_cancel_right] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (first_order_scale q.L₁ q.R q.ε hL₁ hR hε n hn1) (norm_nonneg _))
  · refine ⟨q.x0 + target r π, ?_, ?_, ?_⟩
    · change field κ r (8 * q.R) π (q.x0 + target r π - q.x0) = 0
      rw [add_sub_cancel_left]
      exact field_target κ r (8 * q.R) q.R hR.le (by linarith) π hnr
    · simpa only [sub_add_cancel_left, norm_neg] using target_norm_le r q.R hR.le π hnr
    · intro x
      have hm := field_minty κ r (8 * q.R) q.R hκ hr hb hR.le (by linarith) π hnr (x - q.x0)
      have he : x - (q.x0 + target r π) = x - q.x0 - target r π := by abel
      rw [he]
      have : 0 ≤ q.ρ / 2 * ‖field κ r (8 * q.R) π (x - q.x0)‖ ^ 2 := by positivity
      linarith

lemma exists_failure (q : LongTails.Setups.HighDimensionalWeakMintySecondOrder.Params)
    (hL₁ : 0 < q.L₁) (hL₂ : 0 < q.L₂) (hρ : 0 ≤ q.ρ) (hR : 0 < q.R) (hε : 0 < q.ε)
    (n k : ℕ) (hk : k ≤ n)
    (hn1 : ((n : ℝ) + 1) ≤ q.L₁ ^ 2 * q.R ^ 2 / (16384 * q.ε ^ 2))
    (hn2 : ((n : ℝ) + 1) ≤ q.L₂ * q.R ^ 2 / (16384 * q.ε))
    (hd : 4609 * ((n : ℝ) + 1) ^ 3 ≤ q.d)
    (A : Algorithm (Query q.d) (Reply q.d) (Space q.d)) :
    ∃ (F : Space q.d → Space q.d) (O : Oracle (Query q.d) (Reply q.d)),
      LongTails.Setups.HighDimensionalWeakMintySecondOrder.spec.admissible q F O ∧
        ¬ LongTails.Setups.HighDimensionalWeakMintySecondOrder.spec.successful q F
          (fun w : A.Seed × ((j : ℕ) → O.Seed j) => execute O A (fun _ => k) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  let r := link q.R n
  let κ := slope q.R q.ε n
  let b := 8 * q.R
  set m : ℝ := (n : ℝ) + 1 with hm
  have hr : 0 < r := link_pos q.R hR n
  have hκ : 0 ≤ κ := by dsimp [κ, slope]; exact div_nonneg (by positivity) hr.le
  have hb : 0 < b := by dsimp [b]; positivity
  have hnr : ((n : ℝ) + 1) * r ^ 2 ≤ q.R ^ 2 := link_count q.R n
  have hm1 : 1 ≤ m := by rw [hm]; linarith [Nat.cast_nonneg (α := ℝ) n]
  let D : ℝ := 4608 * m ^ 3
  have hD : 0 < D := by dsimp [D]; positivity
  have hDs : D + (n + 1 : ℕ) ≤ (q.d : ℝ) := by
    push_cast
    change 4608 * m ^ 3 + m ≤ (q.d : ℝ)
    have : m ≤ m ^ 3 := by
      simpa using pow_le_pow_right₀ hm1 (by norm_num : 1 ≤ 3)
    linarith
  have hratio : (3 * b / 2) ^ 2 / (r / 4) ^ 2 = 2304 * m := by
    have h2 := link_sq q.R n
    have hR2 : 0 < q.R ^ 2 := by positivity
    dsimp [b]
    rw [div_pow, div_pow, h2, ← hm]
    field_simp
    ring
  have hsize : 2 * (k + 1 : ℕ) * (n + 1 : ℕ) * ((3 * b / 2) ^ 2 / (r / 4) ^ 2) ≤ D := by
    rw [hratio]
    have hkn : ((k + 1 : ℕ) : ℝ) ≤ m := by rw [hm]; exact_mod_cast Nat.succ_le_succ hk
    push_cast
    change 2 * ((k : ℝ) + 1) * m * (2304 * m) ≤ 4608 * m ^ 3
    have hh := mul_le_mul_of_nonneg_right hkn (show 0 ≤ 4608 * m ^ 2 by positivity)
    push_cast at hh
    nlinarith
  have hgap : 2 * q.ε < 3 / 10 * (κ * r) := by
    rw [show κ * r = 8 * q.ε from slope_mul_link q.R q.ε hR n]
    linarith
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure A.Seed).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  let query := fun s => shift q.x0 (A.query s).2
  let output := fun s => A.output s - q.x0
  obtain ⟨π, hbad⟩ := SecondOrderMintyHiding.exists_failure κ r b q.R D q.ε hκ hr hb hR.le
    (by dsimp [b]; linarith) hk hnr hD hDs hsize hgap query output A.update
    (fun w : A.Seed × (ℕ → Unit) => A.initial w.1) P
  let F := field κ r b π
  refine ⟨fun x => F (x - q.x0), oracle q.x0 κ r b π,
    instance_admissible q hL₁ hL₂ hρ hR hε n hn1 hn2 π, ?_⟩
  intro hsuccess
  apply hbad
  have hout :
      (fun w : A.Seed × (ℕ → Unit) =>
        ‖F (execute (oracle q.x0 κ r b π) A (fun _ => k) w.1 w.2 - q.x0)‖) =
      fun w => ‖F (output ((fun s => A.update s (reply κ r b π (query s)))^[k]
        (A.initial w.1)))‖ := by
    funext w
    rw [execute_translated q.x0 κ r b π A k w.1 w.2]
  change Integrable (fun w : A.Seed × (ℕ → Unit) =>
    ‖F (output ((fun s => A.update s (reply κ r b π (query s)))^[k] (A.initial w.1)))‖)
      (P : Measure _) ∧
      (∫ w : A.Seed × (ℕ → Unit),
        ‖F (output ((fun s => A.update s (reply κ r b π (query s)))^[k] (A.initial w.1)))‖
          ∂(P : Measure _)) ≤ q.ε
  rw [← hout]
  exact hsuccess

end LongTails.Proofs.SecondOrderMintyLowerBound

namespace LongTails.Proofs.SecondOrderMintyLowerBudget

lemma lower_parameters {L₁ L₂ R ε M : ℝ}
    (hMdef : M = min (L₂ * R ^ 2 / ε) (L₁ ^ 2 * R ^ 2 / ε ^ 2)) (hε : 0 < ε)
    (hM : 2 ^ 15 ≤ M) (k : ℕ) (hk : k ≤ ⌊M / 2 ^ 15⌋₊) :
    k ≤ ⌊M / 2 ^ 14⌋₊ - 1 ∧
      (((⌊M / 2 ^ 14⌋₊ - 1 : ℕ) : ℝ) + 1) ≤ L₁ ^ 2 * R ^ 2 / (16384 * ε ^ 2) ∧
      (((⌊M / 2 ^ 14⌋₊ - 1 : ℕ) : ℝ) + 1) ≤ L₂ * R ^ 2 / (16384 * ε) ∧
      4609 * (((⌊M / 2 ^ 14⌋₊ - 1 : ℕ) : ℝ) + 1) ^ 3 ≤ M ^ 3 := by
  set m := ⌊M / 2 ^ 14⌋₊ with hmdef
  have hM0 : 0 ≤ M := by linarith
  have hm2 : 2 ≤ m := Nat.le_floor (by push_cast; rw [le_div_iff₀ (by norm_num)]; linarith)
  have hmle : (m : ℝ) ≤ M / 2 ^ 14 := Nat.floor_le (by positivity)
  have hcast : ((m - 1 : ℕ) : ℝ) + 1 = m := by
    have : m - 1 + 1 = m := by omega
    exact_mod_cast this
  set a := ⌊M / 2 ^ 15⌋₊ with hadef
  have ha1 : 1 ≤ a := Nat.le_floor (by push_cast; rw [le_div_iff₀ (by norm_num)]; linarith)
  have hale : (a : ℝ) ≤ M / 2 ^ 15 := Nat.floor_le (by positivity)
  have h2a : 2 * a ≤ m := Nat.le_floor (by push_cast; linarith)
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rw [hcast]
    have h1 : M ≤ L₁ ^ 2 * R ^ 2 / ε ^ 2 := hMdef ▸ min_le_right _ _
    calc
      (m : ℝ) ≤ M / 2 ^ 14 := hmle
      _ ≤ L₁ ^ 2 * R ^ 2 / ε ^ 2 / 2 ^ 14 := by gcongr
      _ = L₁ ^ 2 * R ^ 2 / (16384 * ε ^ 2) := by field_simp; ring
  · rw [hcast]
    have h1 : M ≤ L₂ * R ^ 2 / ε := hMdef ▸ min_le_left _ _
    calc
      (m : ℝ) ≤ M / 2 ^ 14 := hmle
      _ ≤ L₂ * R ^ 2 / ε / 2 ^ 14 := by gcongr
      _ = L₂ * R ^ 2 / (16384 * ε) := by field_simp; ring
  · rw [hcast]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h3 := pow_le_pow_left₀ hm0 hmle 3
    have he : (M / 2 ^ 14) ^ 3 = M ^ 3 / 2 ^ 42 := by ring
    rw [he] at h3
    have hM3 : 0 ≤ M ^ 3 := by positivity
    nlinarith

end LongTails.Proofs.SecondOrderMintyLowerBudget

namespace LongTails.Proofs.SecondOrderMintyInclusion

open OracleTemplate

abbrev General := LongTails.Setups.WeakMintySecondOrderExpected.spec
abbrev Restricted := LongTails.Setups.HighDimensionalWeakMintySecondOrder.spec

noncomputable def toGeneral (q : LongTails.Setups.HighDimensionalWeakMintySecondOrder.Params) :
    LongTails.Setups.WeakMintySecondOrderExpected.Params where
  E := EuclideanSpace ℝ (Fin q.d)
  L₁ := q.L₁
  L₂ := q.L₂
  ρ := q.ρ
  ε := q.ε
  x0 := q.x0
  R := q.R

lemma valid_toGeneral (q : LongTails.Setups.HighDimensionalWeakMintySecondOrder.Params)
    (hq : Restricted.valid q) : General.valid (toGeneral q) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := hq
  exact ⟨h1, h2, h3, h4, h5.le, h6⟩

lemma admissible_iff (q : LongTails.Setups.HighDimensionalWeakMintySecondOrder.Params)
    (F : EuclideanSpace ℝ (Fin q.d) → EuclideanSpace ℝ (Fin q.d))
    (O : Oracle (EuclideanSpace ℝ (Fin q.d) ⊕ EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d) × (EuclideanSpace ℝ (Fin q.d) →L[ℝ] EuclideanSpace ℝ (Fin q.d)))) :
    Restricted.admissible q F O ↔ General.admissible (toGeneral q) F O := Iff.rfl

lemma successful_iff (q : LongTails.Setups.HighDimensionalWeakMintySecondOrder.Params)
    (F : EuclideanSpace ℝ (Fin q.d) → EuclideanSpace ℝ (Fin q.d)) {Ω : Type}
    [MeasurableSpace Ω] (output : Ω → EuclideanSpace ℝ (Fin q.d))
    (P : MeasureTheory.ProbabilityMeasure Ω) :
    Restricted.successful q F output P ↔ General.successful (toGeneral q) F output P := Iff.rfl

end LongTails.Proofs.SecondOrderMintyInclusion

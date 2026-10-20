import LongTails.Proofs.SilverCertificate

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SilverTrace

open LongTails.Algorithms.SilverSchedule
open LongTails.Proofs.SilverCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def nodes (g : E → E) : List ℝ → E → List E
  | [], x => [x]
  | h :: hs, x => x :: nodes g hs (x - h • g x)

noncomputable def values (f : E → ℝ) (g : E → E) : List ℝ → E → ℝ
  | [], _ => 0
  | h :: hs, x => h * f x + values f g hs (x - h • g x)

noncomputable def energy (g : E → E) (o : E) : List ℝ → E → ℝ
  | [], _ => 0
  | h :: hs, x =>
      h * (‖g x‖ ^ 2 - 2 * ⟪g x, x - o⟫) + energy g o hs (x - h • g x)

noncomputable def defectSum (f : E → ℝ) (g : E → E) (z : E) :
    List ℝ → E → ℝ
  | [], _ => 0
  | h :: hs, x =>
      h * defect (f z) (f x) z x (g z) (g x) +
        defectSum f g z hs (x - h • g x)

lemma run_append (g : E → E) (hs ts : List ℝ) (x : E) :
    run g (hs ++ ts) x = run g ts (run g hs x) := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih => simpa only [List.cons_append, run] using ih (x - h • g x)

lemma values_append (f : E → ℝ) (g : E → E) (hs ts : List ℝ) (x : E) :
    values f g (hs ++ ts) x = values f g hs x + values f g ts (run g hs x) := by
  induction hs generalizing x with
  | nil => simp [values, run]
  | cons h hs ih =>
    simp only [List.cons_append, values, run, ih]
    ring

lemma energy_append (g : E → E) (o : E) (hs ts : List ℝ) (x : E) :
    energy g o (hs ++ ts) x = energy g o hs x + energy g o ts (run g hs x) := by
  induction hs generalizing x with
  | nil => simp [energy, run]
  | cons h hs ih =>
    simp only [List.cons_append, energy, run, ih]
    ring

lemma energy_origin (g : E → E) (o p : E) (hs : List ℝ) (x : E) :
    energy g p hs x = energy g o hs x + 2 * ⟪x - run g hs x, p - o⟫ := by
  induction hs generalizing x with
  | nil => simp [energy, run]
  | cons h hs ih =>
    simp only [energy, run, ih, inner_sub_left, inner_sub_right, real_inner_smul_left]
    ring

lemma run_mem_nodes (g : E → E) (hs : List ℝ) (x : E) :
    run g hs x ∈ nodes g hs x := by
  induction hs generalizing x with
  | nil => simp [run, nodes]
  | cons h hs ih =>
    exact List.mem_cons_of_mem _ (ih (x - h • g x))

lemma start_mem_nodes (g : E → E) (hs : List ℝ) (x : E) :
    x ∈ nodes g hs x := by
  cases hs <;> simp [nodes]

lemma nodes_append (g : E → E) (hs ts : List ℝ) (x y : E) :
    y ∈ nodes g (hs ++ ts) x ↔
      y ∈ nodes g hs x ∨ y ∈ nodes g ts (run g hs x) := by
  induction hs generalizing x with
  | nil =>
    simp only [List.nil_append, nodes, List.mem_singleton, run]
    exact ⟨Or.inr, fun h => h.elim (fun h => h ▸ start_mem_nodes g ts x) id⟩
  | cons h hs ih =>
    simp only [List.cons_append, nodes, List.mem_cons, run, ih]
    tauto

lemma defectSum_formula (f : E → ℝ) (g : E → E) (z o : E) (hs : List ℝ) (x : E) :
    defectSum f g z hs x =
      2 * hs.sum * f z - 2 * values f g hs x -
        2 * ⟪x - run g hs x, z - o⟫ - energy g o hs x -
        hs.sum * ‖g z‖ ^ 2 + 2 * ⟪g z, x - run g hs x⟫ := by
  induction hs generalizing x with
  | nil => simp [defectSum, values, energy, run]
  | cons h hs ih =>
    simp only [defectSum, defect, values, energy, run, List.sum_cons, ih,
      ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      real_inner_smul_left, inner_smul_right, real_inner_comm (g x) (g z)]
    ring

lemma defectSum_lower (f : E → ℝ) (g : E → E) (z : E) (hs : List ℝ) (x : E) (δ : ℝ)
    (hw : ∀ h ∈ hs, 0 ≤ h)
    (hq : ∀ y ∈ nodes g hs x, -δ ≤ defect (f z) (f y) z y (g z) (g y)) :
    -hs.sum * δ ≤ defectSum f g z hs x := by
  induction hs generalizing x with
  | nil => simp [defectSum]
  | cons h hs ih =>
    have hh : 0 ≤ h := hw h (by simp)
    have ht : ∀ a ∈ hs, 0 ≤ a := fun a ha => hw a (by simp [ha])
    have htail : ∀ y ∈ nodes g hs (x - h • g x),
        -δ ≤ defect (f z) (f y) z y (g z) (g y) :=
      fun y hy => hq y (List.mem_cons_of_mem _ hy)
    have he := ih (x - h • g x) ht htail
    have hhead := mul_le_mul_of_nonneg_left (hq x (by simp [nodes])) hh
    simp only [List.sum_cons, defectSum]
    nlinarith

noncomputable def primitive (f : E → ℝ) (g : E → E) (hs : List ℝ) (x : E) : ℝ :=
  history hs.sum (values f g hs x) (energy g x hs x) (f (run g hs x))
    (run g hs x - x) (g (run g hs x))

lemma primitive_join (f : E → ℝ) (g : E → E) (hs : List ℝ) (x : E) :
    let μ := (ratio - 2) * (hs.sum + 1) + 1
    let y := run g hs x
    let p := y - μ • g y
    let z := run g hs p
    primitive f g (hs ++ [μ] ++ hs) x =
      primitive f g hs x + (1 + 2 * ratio) * primitive f g hs p +
        ratio * (defectSum f g y hs p + defectSum f g z hs p) +
        ratio * defect (f y) (f z) y z (g y) (g z) +
        ratio * (μ - 1) * defect (f z) (f y) z y (g z) (g y) := by
  let μ := (ratio - 2) * (hs.sum + 1) + 1
  let y := run g hs x
  let p := y - μ • g y
  let z := run g hs p
  change primitive f g (hs ++ [μ] ++ hs) x =
    primitive f g hs x + (1 + 2 * ratio) * primitive f g hs p +
      ratio * (defectSum f g y hs p + defectSum f g z hs p) +
      ratio * defect (f y) (f z) y z (g y) (g z) +
      ratio * (μ - 1) * defect (f z) (f y) z y (g z) (g y)
  have hj := history_join_identity hs.sum (values f g hs x) (values f g hs p)
    (energy g x hs x) (energy g x hs p) (f y) (f z)
    (y - x) (z - x) (g y) (g z)
  change history (2 * hs.sum + μ) (values f g hs x + μ * f y + values f g hs p)
    (energy g x hs x + μ * (‖g y‖ ^ 2 - 2 * ⟪g y, y - x⟫) + energy g x hs p)
    (f z) (z - x) (g z) = _ at hj
  have hp : y - x - μ • g y = p - x := by dsimp [p]; module
  have hz : z - x - (p - x) = z - p := by module
  have hpz : p - x - (z - x) = p - z := by module
  rw [hp, hz, hpz, defect_translate, defect_translate] at hj
  have he := energy_origin g x p hs p
  have hq₁ := defectSum_formula f g y x hs p
  have hq₂ := defectSum_formula f g z x hs p
  change energy g p hs p = energy g x hs p + 2 * ⟪p - z, p - x⟫ at he
  change defectSum f g y hs p =
    2 * hs.sum * f y - 2 * values f g hs p - 2 * ⟪p - z, y - x⟫ -
      energy g x hs p - hs.sum * ‖g y‖ ^ 2 + 2 * ⟪g y, p - z⟫ at hq₁
  change defectSum f g z hs p =
    2 * hs.sum * f z - 2 * values f g hs p - 2 * ⟪p - z, z - x⟫ -
      energy g x hs p - hs.sum * ‖g z‖ ^ 2 + 2 * ⟪g z, p - z⟫ at hq₂
  have hr : run g (hs ++ [μ] ++ hs) x = z := by
    simp only [run_append, run, y, p, z]
  have hv : values f g (hs ++ [μ] ++ hs) x =
      values f g hs x + μ * f y + values f g hs p := by
    simp only [values_append, values, run_append, run, y, p]
    ring
  have ht : energy g x (hs ++ [μ] ++ hs) x =
      energy g x hs x + μ * (‖g y‖ ^ 2 - 2 * ⟪g y, y - x⟫) + energy g x hs p := by
    simp only [energy_append, energy, run_append, run, y, p]
    ring
  have hs' : (hs ++ [μ] ++ hs).sum = 2 * hs.sum + μ := by simp; ring
  unfold primitive
  rw [hr, hv, ht, hs', he, hq₁, hq₂]
  change history (2 * hs.sum + μ) (values f g hs x + μ * f y + values f g hs p)
    (energy g x hs x + μ * (‖g y‖ ^ 2 - 2 * ⟪g y, y - x⟫) + energy g x hs p)
    (f z) (z - x) (g z) = _
  rw [hj]
  simp only [inner_add_left, inner_add_right]
  ring

lemma endpoint_identity (f : E → ℝ) (g : E → E) (hs : List ℝ) (x z : E)
    (hz : g z = 0) :
    primitive f g hs x + defectSum f g z hs x =
      ‖x - z‖ ^ 2 - ‖run g hs x - z‖ ^ 2 -
        hs.sum * (hs.sum + 1) * ‖g (run g hs x)‖ ^ 2 -
        2 * hs.sum * (f (run g hs x) - f z) := by
  rw [defectSum_formula f g z x, hz]
  simp only [primitive, history, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    inner_zero_left, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_comm z x, real_inner_comm (run g hs x) x,
    real_inner_comm (run g hs x) z]
  ring

lemma primitive_lower (f : E → ℝ) (g : E → E) (P : E → Prop) (δ : ℝ)
    (hq : ∀ u v, P u → P v → -δ ≤ defect (f u) (f v) u v (g u) (g v))
    (k : ℕ) (x : E) (hnodes : ∀ y ∈ nodes g (steps k) x, P y) :
    -historyMass k * δ ≤ primitive f g (steps k) x := by
  induction k generalizing x with
  | zero => simp [steps, historyMass, primitive, history, values, energy, run]
  | succ k ih =>
    let μ := 1 + ratio ^ k / ratio
    let y := run g (steps k) x
    let p := y - μ • g y
    let z := run g (steps k) p
    change ∀ w ∈ nodes g (steps k ++ [μ] ++ steps k) x, P w at hnodes
    have hleft : ∀ w ∈ nodes g (steps k) x, P w := by
      intro w hw
      apply hnodes w
      apply (nodes_append g (steps k ++ [μ]) (steps k) x w).2
      exact Or.inl ((nodes_append g (steps k) [μ] x w).2 (Or.inl hw))
    have hright : ∀ w ∈ nodes g (steps k) p, P w := by
      intro w hw
      apply hnodes w
      apply (nodes_append g (steps k ++ [μ]) (steps k) x w).2
      right
      simpa only [run_append, run, y, p] using hw
    have hy : P y := hleft y (run_mem_nodes g (steps k) x)
    have hz : P z := hright z (run_mem_nodes g (steps k) p)
    have hw : ∀ h ∈ steps k, 0 ≤ h := fun h hh => (steps_positive k h hh).le
    have hl := ih x hleft
    have hr := ih p hright
    have hsy := defectSum_lower f g y (steps k) p δ hw
      (fun w hm => hq y w hy (hright w hm))
    have hsz := defectSum_lower f g z (steps k) p δ hw
      (fun w hm => hq z w hz (hright w hm))
    have hμ : 0 ≤ μ - 1 := by
      dsimp [μ]
      linarith [div_nonneg (pow_nonneg ratio_pos.le k) ratio_pos.le]
    have h₁ := mul_le_mul_of_nonneg_left hr
      (show 0 ≤ 1 + 2 * ratio by linarith [ratio_pos])
    have h₂ := mul_le_mul_of_nonneg_left (add_le_add hsy hsz) ratio_pos.le
    have h₃ := mul_le_mul_of_nonneg_left (hq y z hy hz) ratio_pos.le
    have h₄ := mul_le_mul_of_nonneg_left (hq z y hz hy) (mul_nonneg ratio_pos.le hμ)
    have hj := primitive_join f g (steps k) x
    rw [← join_step k] at hj
    change primitive f g (steps k ++ [μ] ++ steps k) x =
      primitive f g (steps k) x + (1 + 2 * ratio) * primitive f g (steps k) p +
        ratio * (defectSum f g y (steps k) p + defectSum f g z (steps k) p) +
        ratio * defect (f y) (f z) y z (g y) (g z) +
        ratio * (μ - 1) * defect (f z) (f y) z y (g z) (g y) at hj
    change -historyMass (k + 1) * δ ≤ primitive f g (steps k ++ [μ] ++ steps k) x
    rw [hj, historyMass_join]
    change -((2 + 2 * ratio) * historyMass k + ratio * (2 * (steps k).sum + μ)) * δ ≤ _
    nlinarith only [hl, h₁, h₂, h₃, h₄]

lemma endpoint_bound (f : E → ℝ) (g : E → E) (P : E → Prop) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hq : ∀ u v, P u → P v → -δ ≤ defect (f u) (f v) u v (g u) (g v))
    (k : ℕ) (x z : E) (hz : g z = 0) (hPz : P z)
    (hnodes : ∀ y ∈ nodes g (steps k) x, P y) :
    ‖run g (steps k) x - z‖ ^ 2 +
        (steps k).sum * ((steps k).sum + 1) * ‖g (run g (steps k) x)‖ ^ 2 +
        2 * (steps k).sum * (f (run g (steps k) x) - f z) ≤
      ‖x - z‖ ^ 2 + 3 * (2 + 2 * ratio) ^ k * δ := by
  have hp := primitive_lower f g P δ hq k x hnodes
  have hs := defectSum_lower f g z (steps k) x δ
    (fun h hh => (steps_positive k h hh).le)
    (fun y hy => hq z y hPz (hnodes y hy))
  have hi := endpoint_identity f g (steps k) x z hz
  have hm : historyMass k + (steps k).sum ≤ 3 * (2 + 2 * ratio) ^ k := by
    rw [steps_sum]
    have hp₁ : 0 ≤ ratio ^ k := pow_nonneg ratio_pos.le _
    have hp₂ : 0 ≤ (2 + 2 * ratio) ^ k := pow_nonneg (by linarith [ratio_pos]) _
    linarith [historyMass_bound k]
  have hb := mul_le_mul_of_nonneg_right hm hδ
  nlinarith only [hp, hs, hi, hb]

end LongTails.Proofs.SilverTrace

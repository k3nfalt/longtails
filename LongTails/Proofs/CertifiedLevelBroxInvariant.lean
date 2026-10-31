import LongTails.Algorithms.CertifiedLevelBrox
import LongTails.Proofs.LevelBroxState

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.CertifiedLevelBrox

open OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Ctx (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  C : Set E
  f : E → ℝ
  grad : E → E
  L : ℝ
  R : ℝ
  ε : ℝ
  Δ : ℝ
  x0 : E
  xs : E
  convex : Convex ℝ C
  x0_mem : x0 ∈ C
  xs_mem : xs ∈ C
  xs_min : ∀ y ∈ C, f xs ≤ f y
  dist : ‖x0 - xs‖ ≤ R
  gap0 : f x0 - f xs ≤ Δ
  lower : ∀ x ∈ C, ∀ y ∈ C, f x + ⟪grad x, y - x⟫ ≤ f y
  upper : ∀ x ∈ C, ∀ y ∈ C, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2
  L_nonneg : 0 ≤ L
  R_nonneg : 0 ≤ R
  ε_pos : 0 < ε

structure Valid (c : Ctx E) (O : Oracle (Query E) (Reply E)) : Prop where
  first : ∀ k seed x, x ∈ c.C → O.answer k (0, .inl x) seed = .inl (c.f x, c.grad x)
  linear : ∀ k seed x r g, x ∈ c.C → 0 ≤ r →
    ∃ v ∈ c.C, ‖v - x‖ ≤ r ∧
      (∀ z ∈ c.C, ‖z - x‖ ≤ r → ⟪g, v⟫ ≤ ⟪g, z⟫) ∧
      O.answer k (0, .inr (x, r, g)) seed = .inr v

def goodModel (c : Ctx E) (s : State E) (h : c.f c.xs ≤ level s) (hL : 0 ≤ s.Lh) :
    LevelModel E where
  C := c.C
  f := c.f
  grad := c.grad
  L := s.Lh
  level := level s
  anchor := c.xs
  convex := c.convex
  L_nonneg := hL
  anchor_mem := c.xs_mem
  anchor_le := h
  lower := c.lower

def UpperAt (c : Ctx E) (Lh : ℝ) (z y : E) : Prop :=
  c.f y ≤ c.f z + ⟪c.grad z, y - z⟫ + Lh / 2 * ‖y - z‖ ^ 2

structure Feasible (c : Ctx E) (t : SplitBrox.State E) : Prop where
  momentum_mem : t.momentum ∈ c.C
  primal_mem : t.primal ∈ c.C
  previous_mem : match t.phase with
    | .first => True
    | .local _ _ _ previous => previous ∈ c.C

structure Values (c : Ctx E) (s : State E) : Prop where
  lb_le : s.lb ≤ c.f c.xs
  best_mem : s.best ∈ c.C
  ub_eq : s.ub = c.f s.best

structure Params (c : Ctx E) (s : State E) : Prop where
  R_pos : 0 < c.R
  Lh_eq : s.Lh = c.ε / c.R ^ 2 * 2 ^ s.doublings
  Lh_le : s.doublings = 0 ∨ s.Lh ≤ 2 * c.L
  shrink : gap s * (4 / 3 : ℝ) ^ s.phases ≤ c.Δ + c.L * c.R ^ 2 / 2

def Count (c : Ctx E) (s : State E) (T : ℕ) : Prop :=
  (T : ℝ) ≤ 200 * Real.sqrt (s.Lh * c.R ^ 2 / gap s) + 9 * ((s.phases : ℝ) + s.doublings) + 2 + s.calls

structure RunInv (c : Ctx E) (s : State E) : Prop where
  gap_gt : c.ε < gap s
  completed_lt : s.inner.completed < phaseK c.R s
  calls_lt : s.calls < 4 * phaseK c.R s
  feasible : Feasible c s.inner
  zfacts : match s.inner.phase with
    | .first => True
    | .local _ _ _ _ => s.zpt = mix s.inner.completed s.inner.primal s.inner.momentum ∧
        s.zval = c.f s.zpt ∧ s.zg = c.grad s.zpt
  good : ∀ h : c.f c.xs ≤ level s, ∀ hL : 0 ≤ s.Lh,
    LevelInvariant (goodModel c s h hL) (phaseK c.R s) (phaseB c.R s) c.R s.inner ∧
      s.calls ≤ rank s.inner + s.inner.completed

structure CheckInv (c : Ctx E) (s : State E) : Prop where
  gap_gt : c.ε < gap s
  completed_pos : 1 ≤ s.inner.completed
  completed_le : s.inner.completed ≤ phaseK c.R s
  calls_le : s.calls ≤ 4 * phaseK c.R s
  feasible : Feasible c s.inner
  phase_first : s.inner.phase = .first
  zpt_mem : s.zpt ∈ c.C
  zval_eq : s.zval = c.f s.zpt
  zg_eq : s.zg = c.grad s.zpt
  good : ∀ h : c.f c.xs ≤ level s, ∀ hL : 0 ≤ s.Lh,
    (UpperAt c s.Lh s.zpt s.inner.primal →
      LevelInvariant (goodModel c s h hL) (phaseK c.R s) (phaseB c.R s) c.R s.inner) ∧
      s.calls + 1 ≤ rank s.inner + s.inner.completed

def Inv (c : Ctx E) (s : State E) (T : ℕ) : Prop :=
  match s.stage with
  | .init0 => T = 0 ∧ s = (algorithm c.R c.ε c.x0).initial ()
  | .init1 => T = 1 ∧ s.f0 = c.f c.x0 ∧ s.g0 = c.grad c.x0 ∧ s.ub = c.f c.x0 ∧
      s.best = c.x0 ∧ s.phases = 0 ∧ s.doublings = 0
  | .frozen => Values c s ∧ gap s ≤ c.ε
  | .run => Values c s ∧ Params c s ∧ Count c s T ∧ RunInv c s
  | .check => Values c s ∧ Params c s ∧ Count c s T ∧ CheckInv c s

lemma horizon_pos (R Lh g : ℝ) : 0 < horizon R Lh g := by unfold horizon; omega

lemma base_pos {R Lh g : ℝ} (hR : 0 < R) : 0 < base R Lh g := by
  unfold base
  have h : (0 : ℝ) < horizon R Lh g := by exact_mod_cast horizon_pos R Lh g
  exact div_pos hR (Real.sqrt_pos.mpr h)

lemma base_sq (R Lh g : ℝ) : R ^ 2 = (horizon R Lh g : ℝ) * base R Lh g ^ 2 := by
  unfold base
  have h : (0 : ℝ) < horizon R Lh g := by exact_mod_cast horizon_pos R Lh g
  rw [div_pow, Real.sq_sqrt (le_of_lt h)]
  field_simp

lemma horizon_le (R Lh g : ℝ) :
    (horizon R Lh g : ℝ) ≤ Real.sqrt (40 * Lh * R ^ 2 / g) + 2 := by
  unfold horizon
  push_cast
  have := Nat.ceil_lt_add_one (Real.sqrt_nonneg (40 * Lh * R ^ 2 / g))
  linarith

lemma horizon_weight {R Lh g : ℝ} (hg : 0 < g) (hL : 0 ≤ Lh) :
    5 * Lh * R ^ 2 ≤ potentialWeight (horizon R Lh g) * (g / 4) := by
  have ht : 0 ≤ 40 * Lh * R ^ 2 / g := by positivity
  have hc : Real.sqrt (40 * Lh * R ^ 2 / g) ≤ (⌈Real.sqrt (40 * Lh * R ^ 2 / g)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hcs : 40 * Lh * R ^ 2 / g ≤ (⌈Real.sqrt (40 * Lh * R ^ 2 / g)⌉₊ : ℝ) ^ 2 := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hc 2
    rwa [Real.sq_sqrt ht] at hh
  have hK : 40 * Lh * R ^ 2 / g ≤ (horizon R Lh g : ℝ) * ((horizon R Lh g : ℝ) + 1) := by
    unfold horizon
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) ⌈Real.sqrt (40 * Lh * R ^ 2 / g)⌉₊]
  have hid : 40 * Lh * R ^ 2 / g * g = 40 * Lh * R ^ 2 := by field_simp
  have hm := mul_le_mul_of_nonneg_right hK (le_of_lt hg)
  rw [hid] at hm
  unfold potentialWeight
  have he : (horizon R Lh g : ℝ) * ((horizon R Lh g : ℝ) + 1) / 2 * (g / 4) =
      (horizon R Lh g : ℝ) * ((horizon R Lh g : ℝ) + 1) * g / 8 := by ring
  rw [he]
  linarith

end OracleTemplate.CertifiedLevelBrox

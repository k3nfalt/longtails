import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.QuadraticPerceptronCone

structure State where
  a : ℝ
  b : ℝ
  Z : ℝ
  A : ℝ
  B : ℝ
  n : ℕ

structure Gains where
  c1 : ℝ
  c2 : ℝ
  e : ℝ
  m : ℝ

namespace Gains

variable (g : Gains)

def test (x : State) : ℝ :=
  g.c2 * (x.a ^ 2 - x.b ^ 2) - 2 * g.e * x.Z * (x.a + x.b) + g.m * (x.B ^ 2 - x.A ^ 2)

def opt1 (x : State) : State := ⟨(1 + g.c1) * x.a, (1 - g.c1) * x.b, x.Z, x.A, x.B, x.n⟩

noncomputable def opt2 (x : State) : State :=
  ⟨(1 - g.c2) * x.a + g.e * x.Z, (1 + g.c2) * x.b + g.e * x.Z, x.Z + g.e * (x.a + x.b) / 2,
    (1 + g.m) * x.A, (1 - g.m) * x.B, x.n + 1⟩

open Classical in
noncomputable def step (x : State) : State :=
  if x.a ^ 2 ≤ x.b ^ 2 then g.opt1 x else if 0 ≤ g.test x then g.opt2 x else x

def Stopped (x : State) : Prop := ¬ x.a ^ 2 ≤ x.b ^ 2 ∧ g.test x < 0

noncomputable def traj (x : State) (t : ℕ) : State := g.step^[t] x

noncomputable def cm : ℝ := min g.c1 g.c2

noncomputable def potential (x : State) : ℝ := g.c2 * g.cm * (x.a + x.b) - 2 * g.e * x.Z

structure Standing : Prop where
  c1_pos : 0 < g.c1
  c1_le : g.c1 ≤ 1
  c2_pos : 0 < g.c2
  c2_le : g.c2 ≤ 1
  e_pos : 0 < g.e
  m_nonneg : 0 ≤ g.m
  m_le : g.m ≤ 1

variable {g}

lemma step_opt1 {x : State} (h : x.a ^ 2 ≤ x.b ^ 2) : g.step x = g.opt1 x := by
  unfold step; simp [h]

lemma step_opt2 {x : State} (h : ¬ x.a ^ 2 ≤ x.b ^ 2) (h2 : 0 ≤ g.test x) :
    g.step x = g.opt2 x := by
  unfold step; simp [h, h2]

lemma step_stopped {x : State} (h : g.Stopped x) : g.step x = x := by
  unfold step; simp [h.1, not_le.mpr h.2]

lemma not_stopped_cases {x : State} (h : ¬ g.Stopped x) :
    x.a ^ 2 ≤ x.b ^ 2 ∨ (¬ x.a ^ 2 ≤ x.b ^ 2 ∧ 0 ≤ g.test x) := by
  by_cases h1 : x.a ^ 2 ≤ x.b ^ 2
  · exact Or.inl h1
  · exact Or.inr ⟨h1, not_lt.mp fun h2 => h ⟨h1, h2⟩⟩

lemma traj_zero (x : State) : g.traj x 0 = x := rfl

lemma traj_succ (x : State) (t : ℕ) : g.traj x (t + 1) = g.step (g.traj x t) :=
  Function.iterate_succ_apply' _ _ _

lemma traj_add (x : State) (t u : ℕ) : g.traj x (t + u) = g.traj (g.traj x t) u := by
  unfold traj; rw [add_comm, Function.iterate_add_apply]

lemma stopped_succ {x : State} (h : g.Stopped x) : g.Stopped (g.step x) := by
  rw [step_stopped h]; exact h

lemma stopped_mono {x : State} {t u : ℕ} (h : g.Stopped (g.traj x t)) (hle : t ≤ u) :
    g.Stopped (g.traj x u) := by
  induction u, hle using Nat.le_induction with
  | base => exact h
  | succ u _ ih => rw [traj_succ]; exact stopped_succ ih

variable (g)

structure Inv (x0 : State) (N : ℕ) (U0 : ℝ) (x : State) : Prop where
  b_nonneg : 0 ≤ x.b
  Z_ge : x0.Z ≤ x.Z
  a_ge : min x0.a (g.e * x0.Z) ≤ x.a
  A_eq : x.A = (1 + g.m) ^ x.n * x0.A
  B_eq : x.B = (1 - g.m) ^ x.n * x0.B
  early : x.n ≤ N → x.a + x.b + 2 * x.Z ≤ (1 + g.e) ^ x.n * U0
  late : N ≤ x.n → x.a + x.b ≤ (1 + g.e) ^ N * U0

variable {g}

section Phase

variable (hg : g.Standing) {x0 : State} {N : ℕ} {U0 : ℝ}
  (ha0 : 0 < x0.a) (hZ0 : 0 < x0.Z)
  (hN : x0.B ^ 2 ≤ (1 + g.m) ^ (2 * N) * x0.A ^ 2)

include hg ha0 hZ0 in
lemma alpha_pos : 0 < min x0.a (g.e * x0.Z) :=
  lt_min ha0 (mul_pos hg.e_pos hZ0)

include hg ha0 hZ0 in
lemma Inv.a_pos {x : State} (I : g.Inv x0 N U0 x) : 0 < x.a :=
  lt_of_lt_of_le (alpha_pos hg ha0 hZ0) I.a_ge

include hZ0 in
lemma Inv.Z_pos {x : State} (I : g.Inv x0 N U0 x) : 0 < x.Z := lt_of_lt_of_le hZ0 I.Z_ge

include hg hN in
lemma Inv.phase {x : State} (I : g.Inv x0 N U0 x) (hn : N ≤ x.n) : x.B ^ 2 ≤ x.A ^ 2 := by
  have e1 : ((1 - g.m) ^ x.n) ^ 2 = ((1 - g.m) ^ 2) ^ x.n := by rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : ((1 + g.m) ^ x.n) ^ 2 = (1 + g.m) ^ (2 * x.n) := by rw [← pow_mul, mul_comm]
  have hm := hg.m_nonneg
  have hm1 := hg.m_le
  have h1 : ((1 - g.m) ^ 2) ^ x.n ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    nlinarith
  have h2 : (1 + g.m) ^ (2 * N) ≤ (1 + g.m) ^ (2 * x.n) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  rw [I.A_eq, I.B_eq, mul_pow, mul_pow, e1, e2]
  calc ((1 - g.m) ^ 2) ^ x.n * x0.B ^ 2 ≤ 1 * x0.B ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ ≤ (1 + g.m) ^ (2 * N) * x0.A ^ 2 := by rw [one_mul]; exact hN
    _ ≤ (1 + g.m) ^ (2 * x.n) * x0.A ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

include hg ha0 hZ0 in
lemma Inv.opt1_le {x : State} (I : g.Inv x0 N U0 x) (h : x.a ^ 2 ≤ x.b ^ 2) : x.a ≤ x.b := by
  have := I.a_pos hg ha0 hZ0
  nlinarith [I.b_nonneg]

include hg ha0 hZ0 in
lemma Inv.opt2_gt {x : State} (I : g.Inv x0 N U0 x) (h : ¬ x.a ^ 2 ≤ x.b ^ 2) : x.b < x.a := by
  have := I.a_pos hg ha0 hZ0
  rcases le_or_gt x.a x.b with hc | hc
  · exact absurd (by nlinarith [I.b_nonneg]) h
  · exact hc

include hg ha0 hZ0 hN in
lemma Inv.window {x : State} (I : g.Inv x0 N U0 x) (hn : N ≤ x.n)
    (_h1 : ¬ x.a ^ 2 ≤ x.b ^ 2) (h2 : 0 ≤ g.test x) : 2 * g.e * x.Z ≤ g.c2 * (x.a - x.b) := by
  have hph := I.phase hg hN hn
  have ha := I.a_pos hg ha0 hZ0
  have hb := I.b_nonneg
  have hm := hg.m_nonneg
  unfold test at h2
  have hω : g.m * (x.B ^ 2 - x.A ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hm (by linarith)
  have hs : 0 < x.a + x.b := by linarith
  have key : 0 ≤ (x.a + x.b) * (g.c2 * (x.a - x.b) - 2 * g.e * x.Z) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left hs).mp key
  linarith

include hg hZ0 in
lemma Inv.sum_le {x : State} (I : g.Inv x0 N U0 x) (hU : 0 ≤ U0) :
    x.a + x.b ≤ (1 + g.e) ^ N * U0 := by
  rcases le_total x.n N with hn | hn
  · have hZ := I.Z_pos hZ0
    have he := hg.e_pos
    calc x.a + x.b ≤ x.a + x.b + 2 * x.Z := by linarith
      _ ≤ (1 + g.e) ^ x.n * U0 := I.early hn
      _ ≤ (1 + g.e) ^ N * U0 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hn) hU
  · exact I.late hn

include hg ha0 hZ0 hN in
lemma Inv.step {x : State} (I : g.Inv x0 N U0 x) : g.Inv x0 N U0 (g.step x) := by
  have ha := I.a_pos hg ha0 hZ0
  have hb := I.b_nonneg
  have hZ := I.Z_pos hZ0
  have hc1 := hg.c1_pos
  have hc1' := hg.c1_le
  have hc2 := hg.c2_pos
  have hc2' := hg.c2_le
  have he := hg.e_pos
  by_cases hs : g.Stopped x
  · rw [step_stopped hs]; exact I
  rcases not_stopped_cases hs with h1 | ⟨h1, h2⟩
  · rw [step_opt1 h1]
    have hab := I.opt1_le hg ha0 hZ0 h1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [opt1]; nlinarith
    · simp only [opt1]; exact I.Z_ge
    · simp only [opt1]; nlinarith [I.a_ge]
    · simp only [opt1]; exact I.A_eq
    · simp only [opt1]; exact I.B_eq
    · intro hn; simp only [opt1] at hn ⊢
      have := mul_nonpos_of_nonneg_of_nonpos hc1.le (sub_nonpos.mpr hab)
      nlinarith [I.early hn]
    · intro hn; simp only [opt1] at hn ⊢
      have := mul_nonpos_of_nonneg_of_nonpos hc1.le (sub_nonpos.mpr hab)
      nlinarith [I.late hn]
  · rw [step_opt2 h1 h2]
    have hab := I.opt2_gt hg ha0 hZ0 h1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [opt2]; nlinarith
    · simp only [opt2]; nlinarith [I.Z_ge]
    · simp only [opt2]
      have : min x0.a (g.e * x0.Z) ≤ g.e * x0.Z := min_le_right _ _
      nlinarith [I.Z_ge]
    · simp only [opt2]; rw [I.A_eq, pow_succ]; ring
    · simp only [opt2]; rw [I.B_eq, pow_succ]; ring
    · intro hn
      simp only [opt2] at hn ⊢
      have hU := I.early (by omega)
      have hU' := mul_le_mul_of_nonneg_right hU (by linarith : (0:ℝ) ≤ 1 + g.e)
      have hcab : 0 ≤ g.c2 * (x.a - x.b) := mul_nonneg hc2.le (by linarith)
      rw [pow_succ]
      nlinarith
    · intro hn
      simp only [opt2] at hn ⊢
      rcases Nat.lt_or_ge x.n N with hlt | hge
      · have hU := I.early (by omega)
        have hN' : x.n + 1 = N := by omega
        have hU' := mul_le_mul_of_nonneg_right hU (by linarith : (0:ℝ) ≤ 1 + g.e)
        have hcab : 0 ≤ g.c2 * (x.a - x.b) := mul_nonneg hc2.le (by linarith)
        rw [← hN', pow_succ]
        nlinarith
      · have hw := I.window hg ha0 hZ0 hN hge h1 h2
        have := I.late hge
        nlinarith

end Phase

end Gains

end LongTails.Proofs.QuadraticPerceptronCone

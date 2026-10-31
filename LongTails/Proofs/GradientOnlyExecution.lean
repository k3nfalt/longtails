import LongTails.Proofs.GradientOnlyEpochResult
import LongTails.Proofs.QueryPlan
import LongTails.Proofs.Execution
import Mathlib.Data.List.GetD

namespace LongTails.Proofs.GradientOnlyExecution

open OracleTemplate
open LongTails.Algorithms.GradientOnlyGuarded LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.GradientOnlyGeometry LongTails.Proofs.GradientOnlyEpoch
open LongTails.Proofs.GradientOnlyEpochResult
open LongTails.Setups.GradientOnlyThirdOrderNonconvex

section Eval

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma eval_agdPlan (t : Tuning) (g : E → E) (c : E) (n : ℕ) (s : E × E) :
    QueryPlan.eval g (agdPlan t c n s) = fun k => (advance t g c)^[min k n] s := by
  induction n generalizing s with
  | zero =>
    funext k
    simp [agdPlan, QueryPlan.eval]
  | succ n ih =>
    funext k
    simp only [agdPlan, QueryPlan.eval, QueryPlan.eval_map, ih]
    cases k with
    | zero => simp
    | succ k =>
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, Nat.succ_min_succ,
        Function.iterate_succ_apply]
      rfl

omit [InnerProductSpace ℝ E] in
lemma eval_batch {ι : Type} [Fintype ι] (g : E → E) (pts : ι → E) :
    QueryPlan.eval g (batch pts) = fun j => g (pts j) := by
  unfold batch
  rw [QueryPlan.eval_map, QueryPlan.eval_traverse]
  funext j
  rw [List.getD_eq_getElem]
  · simp [QueryPlan.eval]
  · simp

lemma eval_epochPlan (t : Tuning) (g : E → E) (c : E) :
    QueryPlan.eval g (epochPlan t c) = epochResult t g c := by
  unfold epochPlan
  erw [QueryPlan.eval_bind]
  simp only [QueryPlan.eval_bind, QueryPlan.eval_map, eval_agdPlan, eval_batch, QueryPlan.eval]
  rfl

noncomputable def stepSem (t : Tuning) (g : E → E) : Verdict E → Verdict E
  | .moved c => epochResult t g c
  | .finished x => .finished x
  | .witness w => .witness w

lemma eval_step (t : Tuning) (g : E → E) (x0 : E) (v : Verdict E) :
    QueryPlan.eval g (step t x0 v) = stepSem t g v := by
  cases v <;> simp [step, stepSem, QueryPlan.eval_map, eval_epochPlan]

lemma eval_loop (t : Tuning) (g : E → E) (x0 : E) (K : ℕ) (v : Verdict E) :
    QueryPlan.eval g (loop t x0 K v) = (stepSem t g)^[K] v := by
  induction K generalizing v with
  | zero => rfl
  | succ K ih =>
    show QueryPlan.eval g ((step t x0 v).bind (loop t x0 K)) = _
    rw [QueryPlan.eval_bind, eval_step, ih, Function.iterate_succ_apply]

end Eval

section Invariant

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma loop_good {f : E → ℝ} {t : Tuning} {L₁ L₃ Δ : ℝ} (hb : Bounds t L₁ L₃ Δ)
    (hf : ContDiff ℝ 3 f) (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L₃ * ‖x - y‖)
    (x0 : E) (hgap : ∀ x, f x0 - f x ≤ Δ) (k : ℕ) :
    (∃ x, (stepSem t (gradient f))^[k] (.moved x0) = .finished x ∧ ‖gradient f x‖ ≤ t.ε) ∨
      (∃ c, (stepSem t (gradient f))^[k] (.moved x0) = .moved c ∧
        f c ≤ f x0 - k * (t.α ^ 2 / (8192 * L₃))) := by
  have hgain : 0 ≤ t.α ^ 2 / (8192 * L₃) := by have := hb.L₃_pos; positivity
  induction k with
  | zero => exact Or.inr ⟨x0, rfl, by simp⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with ⟨x, hx, hg⟩ | ⟨c, hc, hv⟩
    · exact Or.inl ⟨x, by rw [hx]; rfl, hg⟩
    · rw [hc]
      have hck : f c ≤ f x0 := by
        have : 0 ≤ (k : ℝ) * (t.α ^ 2 / (8192 * L₃)) := by positivity
        linarith
      rcases epoch_result hb hf hlip hT x0 c hgap hck with ⟨x, hx, hg⟩ | ⟨c', hc', hv'⟩
      · exact Or.inl ⟨x, hx, hg⟩
      · refine Or.inr ⟨c', hc', ?_⟩
        push_cast
        linarith

end Invariant

section Tuning

lemma rpow_third_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma rpow_two_thirds_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma rpow_four_thirds {x : ℝ} (hx : 0 ≤ x) : x ^ (4 / 3 : ℝ) = (x ^ (2 / 3 : ℝ)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma pow_le_exp {a : ℝ} (ha₁ : a ≤ 1) (n : ℕ) :
    (1 - a) ^ n ≤ Real.exp (-(a * n)) := by
  have h1 : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
  calc
    (1 - a) ^ n ≤ Real.exp (-a) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = Real.exp (-(a * n)) := by rw [← Real.exp_nat_mul]; ring_nf

lemma tuning_bounds (p : Params) (hp : spec.valid p) : Bounds (tuning p) p.L₁ p.L₃ p.Δ := by
  obtain ⟨hL₁, hL₃, hΔ, hε⟩ := hp
  set s := p.L₃ ^ (1 / 3 : ℝ) with hs
  set e := p.ε ^ (2 / 3 : ℝ) with he
  have hs0 : 0 < s := Real.rpow_pos_of_pos hL₃ _
  have he0 : 0 < e := Real.rpow_pos_of_pos hε _
  have hs3 : s ^ 3 = p.L₃ := rpow_third_cube hL₃.le
  have he3 : e ^ 3 = p.ε ^ 2 := rpow_two_thirds_cube hε.le
  have hα : alpha p = 2 * s * e := by simp only [alpha, hs, he]
  have hα0 : 0 < alpha p := by rw [hα]; positivity
  have hL : 0 < p.L₁ + 2 * alpha p := by linarith
  have hμL : alpha p / 2 / (p.L₁ + 2 * alpha p) ≤ 1 := by
    rw [div_le_one hL]; linarith
  have hμL0 : 0 ≤ alpha p / 2 / (p.L₁ + 2 * alpha p) := by positivity
  set a := Real.sqrt (alpha p / 2 / (p.L₁ + 2 * alpha p)) with ha
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha1 : a ≤ 1 := Real.sqrt_le_one.mpr hμL
  have ha2 : a ^ 2 = alpha p / 2 / (p.L₁ + 2 * alpha p) := Real.sq_sqrt hμL0
  have hvalid : Valid (tuning p) := by
    refine ⟨hα0, hL, rfl, ha0.le, ha1, ?_, by simp only [tuning]; positivity⟩
    simp only [tuning]
    rw [← ha, ha2]
    field_simp
  refine ⟨hvalid, hL₁.le, hL₃, rfl, rfl, rfl, ?_, by simp only [tuning]; positivity, ?_, rfl, hε,
    ?_, by simp [tuning, horizon], ?_⟩
  · simp only [tuning]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  · simp only [tuning]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  · simp only [tuning]
    rw [hα]
    field_simp
    rw [← hs3, ← he3]
    ring
  · simp only [tuning]
    rw [← ha]
    set X := 200 * (p.L₁ + 2 * alpha p) * p.Δ / p.ε ^ 2 with hX
    have hX0 : 0 < X := by positivity
    have hroot : Real.sqrt (p.L₁ / (s * e) + 4) = a⁻¹ := by
      have hin : p.L₁ / (s * e) + 4 = (alpha p / 2 / (p.L₁ + 2 * alpha p))⁻¹ := by
        rw [hα]; field_simp; ring
      rw [hin, Real.sqrt_inv, ← ha]
    have hlog : Real.log (1 + 200 * (p.L₁ + 4 * s * e) * p.Δ / p.ε ^ 2) = Real.log (1 + X) := by
      rw [hX, hα]; ring_nf
    have hN : a⁻¹ * Real.log (1 + X) ≤ (horizon p : ℝ) - 1 := by
      have h := Nat.le_ceil (Real.sqrt (p.L₁ / (s * e) + 4) * Real.log (1 + 200 * (p.L₁ + 4 * s * e) *
        p.Δ / p.ε ^ 2))
      rw [hroot, hlog] at h
      simp only [horizon, ← hs, ← he]
      rw [hroot, hlog]
      push_cast
      linarith
    have hexp : Real.exp (-(a * horizon p)) ≤ (1 + X)⁻¹ := by
      have hlog0 : 0 ≤ Real.log (1 + X) := Real.log_nonneg (by linarith)
      have : Real.log (1 + X) ≤ a * horizon p := by
        have := mul_le_mul_of_nonneg_left hN ha0.le
        rw [← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul] at this
        nlinarith
      rw [← Real.exp_log (show 0 < 1 + X by linarith), ← Real.exp_neg]
      exact Real.exp_le_exp.mpr (by linarith)
    have hp1 := pow_le_exp ha1 (horizon p)
    have hfin : (1 + X)⁻¹ * p.Δ ≤ p.ε ^ 2 / (200 * (p.L₁ + 2 * alpha p)) := by
      rw [inv_mul_eq_div, div_le_div_iff₀ (by linarith) (by positivity), hX]
      field_simp
      nlinarith [sq_nonneg p.ε, mul_pos hL hΔ]
    calc
      (1 - a) ^ horizon p * p.Δ ≤ (1 + X)⁻¹ * p.Δ :=
        mul_le_mul_of_nonneg_right (hp1.trans hexp) hΔ.le
      _ ≤ _ := hfin

lemma epochs_gain (p : Params) (hp : spec.valid p) :
    p.Δ < epochs p * ((tuning p).α ^ 2 / (8192 * p.L₃)) := by
  obtain ⟨hL₁, hL₃, hΔ, hε⟩ := hp
  set s := p.L₃ ^ (1 / 3 : ℝ) with hs
  set e := p.ε ^ (2 / 3 : ℝ) with he
  have hs0 : 0 < s := Real.rpow_pos_of_pos hL₃ _
  have he0 : 0 < e := Real.rpow_pos_of_pos hε _
  have hs3 : s ^ 3 = p.L₃ := rpow_third_cube hL₃.le
  have hgain : (tuning p).α ^ 2 / (8192 * p.L₃) = e ^ 2 / (2048 * s) := by
    simp only [tuning, alpha, ← hs, ← he]
    rw [← hs3]
    field_simp
    ring
  have hK : 2048 * p.Δ * s / e ^ 2 < epochs p := by
    simp only [epochs, ← hs, rpow_four_thirds hε.le, ← he]
    push_cast
    exact Nat.lt_floor_add_one _
  rw [hgain]
  rw [div_lt_iff₀ (by positivity)] at hK
  rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
  nlinarith

end Tuning

section Run

lemma eval_plan (p : Params) (g : p.E → p.E) :
    QueryPlan.eval g (plan p) = output ((stepSem (tuning p) g)^[epochs p] (.moved p.x0)) := by
  simp only [plan, QueryPlan.eval_map, eval_loop]

lemma epochLength_eq (t : Tuning) :
    epochLength t = 6 * (t.m * 2) + t.N * (t.m * 2) + t.N * 2 * (t.m * 2) + 1 + t.N := by
  simp [epochLength, Fintype.card_prod]

lemma epochLength_tuning (p : Params) :
    epochLength (tuning p) * epochs p = (⌊2048 * p.Δ * p.L₃ ^ (1 / 3 : ℝ) / p.ε ^ (4 / 3 : ℝ)⌋₊ + 1) *
      (97 * ⌈Real.sqrt (p.L₁ / (p.L₃ ^ (1 / 3 : ℝ) * p.ε ^ (2 / 3 : ℝ)) + 4) *
        Real.log (1 + 200 * (p.L₁ + 4 * p.L₃ ^ (1 / 3 : ℝ) * p.ε ^ (2 / 3 : ℝ)) * p.Δ / p.ε ^ 2)⌉₊ +
          290) := by
  rw [epochLength_eq]
  simp only [tuning, horizon, epochs]
  ring

lemma run_accuracy (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (O : Oracle p.E p.E) (ho : spec.admissible p f O) (K : ℕ)
    (hK : epochLength (tuning p) * epochs p ≤ K) (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    ‖gradient f (execute O (algorithm p) (fun _ => K) seed ξ)‖ ≤ p.ε := by
  obtain ⟨hf, hlip, hT, hgap, hO⟩ := ho
  have hb := tuning_bounds p hp
  rw [execute_eq_of_answer_eq O (gradient f) hO]
  erw [QueryPlan.execute_plan_of_le _ _ _ _ _ _ _ _ hK, eval_plan]
  rcases loop_good hb hf hlip hT p.x0 hgap (epochs p) with ⟨x, hx, hg⟩ | ⟨c, hc, hv⟩
  · rw [hx]
    exact hg
  · exfalso
    have := hgap c
    have := epochs_gain p hp
    linarith

end Run

end LongTails.Proofs.GradientOnlyExecution

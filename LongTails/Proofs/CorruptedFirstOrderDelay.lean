import LongTails.Setups.HighDimensionalCorruptedFirstOrderNonconvex
import LongTails.Proofs.CorruptedFirstOrderChain

open OracleTemplate
open LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardOracle
open LongTails.Proofs.CorruptedFirstOrderChain
open LongTails.Setups.CorruptedFirstOrderNonconvex hiding Space

namespace LongTails.Proofs.CorruptedFirstOrderDelay

variable {d n : ℕ}

noncomputable def oracle (m : ℕ) (f : Space d → ℝ) : Oracle (Space d) (ℝ × Space d) where
  answer h q _ := if h.length < m then (0, 0) else (f q.2, gradient f q.2)

lemma error_bound (p : Params) (m : ℕ) (f : Space p.d → ℝ) (hL : 0 < p.L)
    (h : List ((Fin 1 × Space p.d) × (ℝ × Space p.d))) (hh : Reachable (oracle m f) h) :
    errors (accurate p f (gradient f)) h ≤ min h.length m := by
  classical
  induction hh with
  | nil => simp [errors]
  | @snoc h hh q z ih =>
    change errors _ (h ++ [(q, if h.length < m then (0, 0) else _)]) ≤ _
    by_cases hlt : h.length < m
    · rw [min_eq_left (by simp; omega)]
      exact List.length_filter_le _ _
    · have hc : accurate p f (gradient f) q.2 (f q.2, gradient f q.2) := by
        refine ⟨?_, rfl⟩
        simp only [sub_self, abs_zero]
        positivity
      simp [errors, hlt, hc] at ih ⊢
      omega

def warm (A : Method d) (s : A.State) (m : ℕ) := (fun z => A.update z (0, 0))^[m] s

lemma delayed_output (m : ℕ) (A : Method d) (seed : A.Seed) (x0 : Space d) (S : Scale)
    (π : Fin (n + 1) ↪ Fin d) (ξ : (k : ℕ) → (oracle m (objective S π x0)).Seed k) :
    execute (oracle m (objective S π x0)) A (fun _ => n + m) seed ξ =
      A.output ((realStep A S x0 π)^[n] (warm A (A.initial seed) m)) := by
  let f := objective S π x0
  let resp := fun (t : ℕ) (q : Fin 1 × Space d) =>
    if t < m then ((0, 0) : ℝ × Space d) else (f q.2, gradient f q.2)
  let step := fun z : A.State × ℕ => (A.update z.1 (resp z.2 (A.query z.1)), z.2 + 1)
  rw [execute_indexed_of_answer _ A (n + m) seed ξ resp (fun _ _ => rfl)]
  change A.output ((step^[n + m]) (A.initial seed, 0)).1 = _
  have hpre (j : ℕ) (hj : j ≤ m) :
      (step^[j]) (A.initial seed, 0) = (warm A (A.initial seed) j, j) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      simp only [step, resp, ite_eq_left (show j < m by omega), warm, Function.iterate_succ_apply']
  have hpost (j : ℕ) :
      (step^[j]) (warm A (A.initial seed) m, m) =
        ((realStep A S x0 π)^[j] (warm A (A.initial seed) m), m + j) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      simp [step, realStep, resp, f, objective_gradient, Nat.add_assoc]
  rw [Function.iterate_add_apply, hpre m le_rfl, hpost]

noncomputable def scale (p : Params) (hL : 0 < p.L) (he : 0 < p.ε) : Scale :=
  ⟨3686400 * p.ε ^ 2 / p.L, 61440 * p.ε / p.L, by positivity, by positivity⟩

lemma scale_ratio (p : Params) (hL : 0 < p.L) (he : 0 < p.ε) :
    (scale p hL he).a / (scale p hL he).lam = 60 * p.ε := by
  dsimp [scale]
  field_simp
  ring

lemma instance_admissible (p : Params) (hp : Setups.HighDimensionalCorruptedFirstOrderNonconvex.spec.valid p)
    (m n : ℕ) (hm : m ≤ p.k) (hn : n ≤ ⌊p.L * p.Δ / (2 ^ 25 * p.ε ^ 2)⌋₊)
    (π : Fin (n + 1) ↪ Fin p.d) :
    let S := scale p hp.1 hp.2.1
    let f := objective S π p.x0
    Setups.HighDimensionalCorruptedFirstOrderNonconvex.spec.admissible p f (oracle m f) := by
  obtain ⟨hL, he, hreg, _⟩ := hp
  let S := scale p hL he
  have ha := S.ha
  have hΔ : 0 ≤ p.Δ := by nlinarith [sq_nonneg p.ε]
  have hf : (n : ℝ) ≤ (⌊p.L * p.Δ / (2 ^ 25 * p.ε ^ 2)⌋₊ : ℕ) := by exact_mod_cast hn
  have hn' := hf.trans (Nat.floor_le (by positivity))
  rw [le_div_iff₀ (by positivity)] at hn'
  have hs : 1024 * S.a / S.lam ^ 2 = p.L := by
    dsimp [S, scale]; field_simp; ring
  refine ⟨fun x => ?_, fun x y => ?_, ⟨S.a * (-3 * ((n : ℝ) + 1)), fun x => ?_, ?_⟩,
    gradient (objective S π p.x0), fun x => ?_, fun h hh => ?_⟩
  · rw [objective_gradient]; exact objective_hasGradientAt _ _ _ _
  · simp only [objective_gradient]
    exact (objGrad_lipschitz S π p.x0 x y).trans_eq (by rw [hs])
  · exact mul_le_mul_of_nonneg_left (hardValue_lower π _) ha.le
  · simp only [objective, toUnit, sub_self, smul_zero, hardValue_zero]
    dsimp [S, scale]
    field_simp
    nlinarith only [hn', hreg, mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg p.ε)]
  · change ‖gradient (objective S π p.x0) x - gradient (objective S π p.x0) x‖ ≤ p.ε / 8
    rw [sub_self, norm_zero]
    positivity
  · exact (error_bound p m _ hL h hh).trans ((min_le_right _ _).trans hm)

end LongTails.Proofs.CorruptedFirstOrderDelay

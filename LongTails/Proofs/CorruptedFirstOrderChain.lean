import LongTails.Setups.CorruptedFirstOrderNonconvex
import LongTails.Proofs.AbcHardSimulation
import LongTails.Proofs.Execution

open OracleTemplate
open LongTails.Proofs.AbcChain LongTails.Proofs.AbcChainMask LongTails.Proofs.AbcHardFunction
open LongTails.Proofs.AbcHardGeometry LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcHardSimulation
open LongTails.Proofs.SmoothConvexFiniteGeometry

namespace LongTails.Proofs.CorruptedFirstOrderChain

variable {d n : ℕ}

abbrev Method (d : ℕ) := Algorithm (Space d) (ℝ × Space d) (Space d)

noncomputable def partialReply (S : Scale) (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (x0 x : Space d) :
    ℝ × Space d :=
  let w := toUnit S x0 x
  (S.a * (if 2 * radius n ≤ ‖w‖ then wallFn n w else
    smoothMax (width n) (chain (trunc r (sel π w))) (wallFn n w)),
    (S.a / S.lam) • visibleGrad π r w)

lemma partial_prefix (S : Scale) (π ρ : Fin (n + 1) ↪ Fin d) (r : ℕ) (x0 x : Space d)
    (h : ∀ i : Fin (n + 1), i.val < r → π i = ρ i) :
    partialReply S π r x0 x = partialReply S ρ r x0 x := by
  have hc := trunc_congr r (sel π (toUnit S x0 x)) (sel ρ (toUnit S x0 x))
    (fun i hi => by rw [sel_apply, sel_apply, h i hi])
  simp only [partialReply, hc, visibleGrad_prefix π ρ r _ h]

lemma partial_exact (S : Scale) (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (x0 x : Space d)
    (h : ‖toUnit S x0 x‖ ≤ 2 * radius n →
      ∀ i : Fin (n + 1), r ≤ i.val → |sel π (toUnit S x0 x) i| ≤ 1 / 4) :
    partialReply S π (r + 1) x0 x = (objective S π x0 x, objGrad S π x0 x) := by
  let w := toUnit S x0 x
  by_cases hw : 2 * radius n ≤ ‖w‖
  · have hh := (weight_zero_outside π r w hw).2.2
    simp only [partialReply, objective, objGrad, ← show toUnit S x0 x = w from rfl,
      hardValue] at *
    change (S.a * (if 2 * radius n ≤ ‖w‖ then _ else _), _) = _
    rw [ite_eq_left hw, hh, visibleGrad_outside π _ w hw, hardGrad_outside π w hw]
  · have hh : ∀ i : Fin (n + 1), r ≤ i.val → |sel π w i| ≤ 1 / 4 := h (le_of_not_ge hw)
    simp only [partialReply, objective, objGrad, hardValue, show toUnit S x0 x = w from rfl,
      ite_eq_right hw, chain_trunc_succ r _ hh, visibleGrad_eq π r w hh]

noncomputable def simulated (A : Method d) (s : A.State) (S : Scale) (x0 : Space d)
    (π : Fin (n + 1) ↪ Fin d) : ℕ → A.State
  | 0 => s
  | j + 1 =>
    let st := simulated A s S x0 π j
    A.update st (partialReply S π (j + 1) x0 (A.query st).2)

lemma simulated_prefix (A : Method d) (s : A.State) (S : Scale) (x0 : Space d)
    (π ρ : Fin (n + 1) ↪ Fin d) (j : ℕ) (h : ∀ i : Fin (n + 1), i.val < j → π i = ρ i) :
    simulated A s S x0 π j = simulated A s S x0 ρ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [simulated, ih (fun i hi => h i (by omega)), partial_prefix S π ρ _ _ _ h]

noncomputable def observation (A : Method d) (s : A.State) (S : Scale) (x0 : Space d)
    (j : Fin (n + 1)) (π : Fin (n + 1) ↪ Fin d) : Space d :=
  let st := simulated A s S x0 π j.val
  toUnit S x0 (if j.val < n then (A.query st).2 else A.output st)

lemma observation_prefix (A : Method d) (s : A.State) (S : Scale) (x0 : Space d)
    (j : Fin (n + 1)) (π ρ : Fin (n + 1) ↪ Fin d) (h : ∀ i : Fin (n + 1), i.val < j → π i = ρ i) :
    observation A s S x0 j π = observation A s S x0 j ρ := by
  simp only [observation, simulated_prefix A s S x0 π ρ j.val h]

noncomputable def realStep (A : Method d) (S : Scale) (x0 : Space d)
    (π : Fin (n + 1) ↪ Fin d) (st : A.State) : A.State :=
  let x := (A.query st).2
  A.update st (objective S π x0 x, objGrad S π x0 x)

lemma hard_output (A : Method d) (s : A.State) (S : Scale) (x0 : Space d)
    (π : Fin (n + 1) ↪ Fin d) (h : ∀ j : Fin (n + 1),
      ‖observation A s S x0 j π‖ ≤ 2 * radius n →
      ∀ i : Fin (n + 1), j.val ≤ i.val → |sel π (observation A s S x0 j π) i| ≤ 1 / 4) :
    S.a / S.lam / 20 ≤ ‖objGrad S π x0 (A.output ((realStep A S x0 π)^[n] s))‖ := by
  have eqsim (j : ℕ) (hj : j ≤ n) : (realStep A S x0 π)^[j] s = simulated A s S x0 π j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hlt : j < n := by omega
      have hh := h ⟨j, by omega⟩
      simp only [observation, hlt, ↓reduceIte] at hh
      rw [Function.iterate_succ_apply', ih (by omega), simulated, partial_exact _ _ _ _ _ hh]
      rfl
  rw [eqsim n le_rfl]
  let w := toUnit S x0 (A.output (simulated A s S x0 π n))
  change S.a / S.lam / 20 ≤ ‖(S.a / S.lam) • hardGrad π w‖
  have hpos := div_pos S.ha S.hlam
  rw [norm_smul, Real.norm_of_nonneg hpos.le]
  have hg : 1 / 20 ≤ ‖hardGrad π w‖ := by
    by_cases hw : 2 * radius n ≤ ‖w‖
    · rw [hardGrad_outside π w hw, wallGrad_norm]
      have hr := radius_pos n
      rw [le_div_iff₀ hr]
      linarith
    · have hh := h (Fin.last n)
      simp only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] at hh
      have ht := hh (le_of_not_ge hw) (Fin.last n) le_rfl
      exact hardGrad_lower π w (lt_of_le_of_lt ht (by norm_num))
  linarith [mul_le_mul_of_nonneg_left hg hpos.le]

end LongTails.Proofs.CorruptedFirstOrderChain

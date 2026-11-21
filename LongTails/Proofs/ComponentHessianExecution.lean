import LongTails.Proofs.ComponentHessianAveraging
import LongTails.Proofs.ComponentHessianCounting

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.ComponentHessianExecution

open OracleTemplate MeasureTheory LongTails.Setups.ConvexFiniteSumMeanSquareHessian
open ComponentHessianSimulation ComponentHessianCounting ComponentHessianInstance ComponentHessianAveraging
open ComponentHessianFamily ComponentHessianGap FiniteSumNondualLowerAveraging
open FiniteSumNondualLowerSearch FiniteSumNondualLowerHiding RelativeHessianOracle

variable {p : Params} {k : ℕ}

noncomputable def normalized (A : Method p) (seed : A.Seed) (c β : ℝ) : Policy p.d p.n A.State where
  initial := A.initial seed
  query s := ((A.query s).2.1, β • (A.query s).2.2)
  update s v := A.update s (RelativeHessianScaling.scaleReply c β v)
  output s := β • A.output s

lemma scaled_jet (π : Fin (k+1) ↪ Fin p.d) (o : Fin (k+1) → Fin p.n) (hn : 0 < p.n)
    (c β : ℝ) (i : Fin p.n) (x : Point p) :
    jet ((problem (p := p) π o hn c β).f i) x =
      RelativeHessianScaling.scaleReply c β (jet (part π (owned o i) p.n) (β • x)) := by
  unfold jet problem RelativeHessianScaling.scaleReply
  rw [ThirdOrderAffineCalculus.scale_gradient (part_smooth _ _ _),
    ThirdOrderAffineCalculus.scale_hessian (part_smooth _ _ _)]

lemma scaled_execution (A : Method p) (ω : A.Seed × (ℕ → Unit)) (c β : ℝ) (hn : 0 < p.n)
    (π : Fin (k+1) ↪ Fin p.d) (anchor : Fin p.n) (w : List (Fin p.n)) (hw : w.length = k) (T : ℕ) :
    let P := normalized A ω.1 c β
    let I := problem (p := p) π (owner anchor w) hn c β
    β • execute (exactOracle I) A (fun _ => T) ω.1 ω.2 = P.output (P.actual π (anchor :: w) T) := by
  dsimp only
  let I := problem (p := p) π (owner anchor w) hn c β
  let reply := fun q : Fin p.n × Point p => jet (I.f q.1) q.2
  have h := execute_iterate reply A T ω.1
  have hh : execute (exactOracle I) A (fun _ => T) ω.1 ω.2 =
      A.output ((fun s => A.update s (reply (A.query s).2))^[T] (A.initial ω.1)) := by
    have he : ω.2 = fun _ => () := Subsingleton.elim _ _
    rw [he]
    exact h
  change β • execute (exactOracle I) A _ _ _ = _
  rw [hh]
  simp only [Policy.actual, normalized, indices_full anchor w hw, reply, I, scaled_jet]

lemma failure (hn : 0 < p.n) {c β D : ℝ} (hc : 0 < c) (hβ : 0 < β)
    (hR : ∀ π : Fin (k+1) ↪ Fin p.d, ‖anchorPoint π‖ ≤ β*p.R)
    (hH : 2^56 * (c*β^3)^2 ≤ p.n*p.H^2) (hε : 32*p.ε < 23*(c*((k+1 : ℕ) : ℝ)/p.n))
    (hD : 0 < D) (hd : D + (k+1 : ℕ) ≤ p.d) (hk : 0 < k) (hkd : k+1 ≤ p.d)
    (A : Method p) (b : Fin 1 → ℕ) (hT : 8*b 0 ≤ p.n*k)
    (hsize : 32 * (b 0 + 1 : ℕ) * (k + 1 : ℕ) * ((2 * radius p.n (k + 1 : ℕ)) ^ 2 / (1 / 80 : ℝ)^2) ≤ D) :
    ∃ (J : Instance p) (O : Oracle (Fin p.n × Point p) (LongTails.Setups.ConvexFiniteSumMeanSquareHessian.Reply p)),
      spec.admissible p J O ∧ ¬ spec.successful p J
        (fun s : A.Seed × ((k : ℕ) → O.Seed k) => execute O A b s.1 s.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  let a : Fin p.n := ⟨0, hn⟩
  let I := fun (u : OwnerWords p.n k) (v : CoordinateWords p.d k) =>
    problem (p := p) (coordinateEmbedding v) (owner a u.val) hn c β
  have hI (u : OwnerWords p.n k) (v : CoordinateWords p.d k) := problem_admissible (p := p) (coordinateEmbedding v) (owner a u.val) hn hc.le hβ (hR _) hH
  apply extract I A b (FiniteSumNondualLowerBound.ownerWords_card_pos _ _ hn)
    (FiniteSumNondualLowerBound.coordinateWords_card_pos _ _ hkd) (fun u v => hI u v) hε
  intro ω
  let P := normalized A ω.1 c β
  let T := b 0
  let g := fun u v => gap (I u v) A T ω
  have hw (u : OwnerWords p.n k) := (mem_words p.n k u.val).mp u.property
  rw [← Finset.card_univ, ← Finset.card_univ]
  refine finite_gap_average (U := OwnerWords p.n k) (V := CoordinateWords p.d k) Finset.univ Finset.univ
      (fun u v => complete P (coordinateEmbedding v) a T u.val)
      (fun u v => P.bad a u.val T (coordinateEmbedding v)) g (c*(k+1 : ℕ)/p.n) (by positivity)
      ?_ ?_ ?_ ?_
  · intro u _ v _
    exact sub_nonneg.mpr ((hI u v).2.2.2.2.1 _)
  · intro u _ v _ ho hcoord
    let π := coordinateEmbedding v
    let o : Fin (k+1) → Fin p.n := owner a u.val
    have hh := output_penalty P hn π a u.val (hw u) T ho hcoord
    have hm := (Classical.choose_spec (mean_exists_minimum π o hn)).2 (anchorPoint π)
    change mean π o (minimizer (p := p) π o hn) ≤ _ at hm
    change _ ≤ objective (problem (p := p) π o hn c β) _ - objective (problem (p := p) π o hn c β) _
    rw [objective_eq, objective_eq]
    change _ ≤ c * mean π o (β • execute (exactOracle (I u v)) A _ ω.1 ω.2) -
      c * mean π o (β • β⁻¹ • minimizer (p := p) π o hn)
    rw [smul_inv_smul₀ hβ.ne', scaled_execution A ω c β hn π a u.val (hw u) T]
    change _ ≤ c * mean π o (P.output (P.actual π (a :: u.val) T)) - _
    change _ ≤ mean π o _ - mean π o _ at hh
    rw [mul_div_assoc, ← mul_sub]
    exact mul_le_mul_of_nonneg_left (hh.trans (sub_le_sub_left hm _)) hc.le
  · intro v _
    simpa only [Finset.card_univ] using owner_fraction P (coordinateEmbedding v) a T hn hk hT
  · intro u _
    simpa only [Finset.card_univ] using coordinate_fraction P u.val (hw u) a T D hD hd hsize

end LongTails.Proofs.ComponentHessianExecution

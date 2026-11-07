import LongTails.Algorithms.ChiSquareBracket
import LongTails.Proofs.ChiSquareSgd
import LongTails.Proofs.Execution

open MeasureTheory Set

namespace OracleTemplate.ChiSquareDro

open LongTails.Setups.ChiSquareConstrainedDro

variable (q : Params) (proj : q.E → q.E) (loss : q.E → q.Ξ → ℝ) (sub : q.E → q.Ξ → q.E)

noncomputable def cfg (j : ℕ) : Cfg :=
  ⟨radius q, stepX q, stepEta q, stepScale q j, etaLow q, q.B, scaleLow q j, 4 * scaleLow q j⟩

noncomputable def start (j : ℕ) : q.E × ℝ × ℝ := (q.x0, 0, scaleLow q j)

noncomputable def block (j : ℕ) (ξ : ℕ → q.Ξ) : ℕ → q.Ξ := fun i => ξ (j * bracketLength q + i)

noncomputable def traj (j : ℕ) (ξ : ℕ → q.Ξ) (t : ℕ) : q.E × ℝ × ℝ :=
  run (cfg q j) proj loss sub (start q j) (block q j ξ) t

noncomputable def xbar (j : ℕ) (ξ : ℕ → q.Ξ) : q.E :=
  avgX (cfg q j) proj loss sub (start q j) (sgdSteps q) (block q j ξ)

noncomputable def ebar (j : ℕ) (ξ : ℕ → q.Ξ) : ℝ :=
  avgE (cfg q j) proj loss sub (start q j) (sgdSteps q) (block q j ξ)

noncomputable def sbar (j : ℕ) (ξ : ℕ → q.Ξ) : ℝ :=
  avgS (cfg q j) proj loss sub (start q j) (sgdSteps q) (block q j ξ)

noncomputable def accAt (j : ℕ) (ξ : ℕ → q.Ξ) (u : ℕ) : ℝ :=
  ∑ i ∈ Finset.range u, max (loss (proj (xbar q proj loss sub j ξ))
    (block q j ξ (sgdSteps q + i)) - ebar q proj loss sub j ξ) 0 ^ 2

noncomputable def fhat (j : ℕ) (ξ : ℕ → q.Ξ) : ℝ :=
  ebar q proj loss sub j ξ +
    radius q * Real.sqrt (accAt q proj loss sub j ξ (selectionSamples q) / selectionSamples q)

noncomputable def best (ξ : ℕ → q.Ξ) : ℕ → q.E × ℝ
  | 0 => (q.x0, 0)
  | j + 1 => if j = 0 ∨ fhat q proj loss sub j ξ < (best ξ j).2 then
      (xbar q proj loss sub j ξ, fhat q proj loss sub j ξ) else best ξ j

noncomputable def response (ξ : ℕ → q.Ξ) (n : ℕ) (y : Fin 1 × q.E) : q.E × ℝ × q.E :=
  (proj y.2, loss (proj y.2) (ξ n), sub (proj y.2) (ξ n))

noncomputable def algStep (ξ : ℕ → q.Ξ) (sc : BracketState q.E × ℕ) : BracketState q.E × ℕ :=
  (bracketUpdate q sc.1 (response q proj loss sub ξ sc.2 (0, bracketQuery q sc.1)), sc.2 + 1)

lemma sgd_phase (ξ : ℕ → q.Ξ) {j : ℕ} (hj : j < numBrackets q) (bx : q.E) (bv : ℝ) :
    ∀ t, t ≤ sgdSteps q →
      (algStep q proj loss sub ξ)^[t] (bracketStart q j bx bv, j * bracketLength q) =
        (⟨j, t, (traj q proj loss sub j ξ t).1, (traj q proj loss sub j ξ t).2.1,
          (traj q proj loss sub j ξ t).2.2,
          ∑ i ∈ Finset.range t, proj (traj q proj loss sub j ξ i).1,
          ∑ i ∈ Finset.range t, (traj q proj loss sub j ξ i).2.1,
          ∑ i ∈ Finset.range t, (traj q proj loss sub j ξ i).2.2, 0, bx, bv⟩,
          j * bracketLength q + t) := by
  intro t
  induction t with
  | zero => intro _; simp [bracketStart, traj, run, start]
  | succ t ih =>
    intro ht
    have ht' : t < sgdSteps q := ht
    rw [Function.iterate_succ_apply', ih ht'.le]
    have hnot : ¬ numBrackets q ≤ j := not_le.mpr hj
    simp only [↓reduceIte, algStep, bracketUpdate, bracketQuery, hnot, ht', sgdUpdate,
      response, Finset.sum_range_succ]
    rfl

lemma select_phase (ξ : ℕ → q.Ξ) {j : ℕ} (hj : j < numBrackets q) (bx : q.E) (bv : ℝ) :
    ∀ u, u < selectionSamples q →
      (algStep q proj loss sub ξ)^[sgdSteps q + u] (bracketStart q j bx bv, j * bracketLength q) =
        (⟨j, sgdSteps q + u, (traj q proj loss sub j ξ (sgdSteps q)).1,
          (traj q proj loss sub j ξ (sgdSteps q)).2.1, (traj q proj loss sub j ξ (sgdSteps q)).2.2,
          ∑ i ∈ Finset.range (sgdSteps q), proj (traj q proj loss sub j ξ i).1,
          ∑ i ∈ Finset.range (sgdSteps q), (traj q proj loss sub j ξ i).2.1,
          ∑ i ∈ Finset.range (sgdSteps q), (traj q proj loss sub j ξ i).2.2,
          accAt q proj loss sub j ξ u, bx, bv⟩,
          j * bracketLength q + (sgdSteps q + u)) := by
  intro u
  induction u with
  | zero =>
    intro _
    rw [Nat.add_zero, sgd_phase q proj loss sub ξ hj bx bv _ le_rfl]
    simp [accAt]
  | succ u ih =>
    intro hu
    rw [show sgdSteps q + (u + 1) = (sgdSteps q + u) + 1 from rfl, Function.iterate_succ_apply',
      ih (Nat.lt_of_succ_lt hu)]
    have hnot : ¬ numBrackets q ≤ j := not_le.mpr hj
    have hlt : ¬ sgdSteps q + u < sgdSteps q := by omega
    have hlen : sgdSteps q + u + 1 < bracketLength q := by
      unfold bracketLength; omega
    simp only [↓reduceIte, algStep, bracketUpdate, bracketQuery, hnot, hlt, selectUpdate,
      hlen, response]
    congr 1
    simp only [BracketState.mk.injEq, true_and]
    refine ⟨?_, trivial⟩
    show _ = ∑ i ∈ Finset.range (u + 1), _
    rw [Finset.sum_range_succ]
    rfl

lemma selectionSamples_pos : 0 < selectionSamples q := by
  unfold selectionSamples numBrackets sgdSteps
  positivity

lemma bracket_full (ξ : ℕ → q.Ξ) {j : ℕ} (hj : j < numBrackets q) (bx : q.E) (bv : ℝ) :
    (algStep q proj loss sub ξ)^[bracketLength q] (bracketStart q j bx bv, j * bracketLength q) =
      (if j = 0 ∨ fhat q proj loss sub j ξ < bv then
        bracketStart q (j + 1) (xbar q proj loss sub j ξ) (fhat q proj loss sub j ξ)
       else bracketStart q (j + 1) bx bv, (j + 1) * bracketLength q) := by
  have hm := selectionSamples_pos q
  obtain ⟨u, hu⟩ : ∃ u, selectionSamples q = u + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hm).symm⟩
  have hL : bracketLength q = (sgdSteps q + u) + 1 := by unfold bracketLength; omega
  rw [hL, Function.iterate_succ_apply', ← hL,
    select_phase q proj loss sub ξ hj bx bv u (by omega)]
  have hnot : ¬ numBrackets q ≤ j := not_le.mpr hj
  have hlt : ¬ sgdSteps q + u < sgdSteps q := by omega
  have hlen : ¬ sgdSteps q + u + 1 < bracketLength q := by omega
  have hacc : accAt q proj loss sub j ξ u + max (loss (proj ((sgdSteps q : ℝ)⁻¹ •
      ∑ i ∈ Finset.range (sgdSteps q), proj (traj q proj loss sub j ξ i).1))
      (ξ (j * bracketLength q + (sgdSteps q + u))) - (sgdSteps q : ℝ)⁻¹ *
      ∑ i ∈ Finset.range (sgdSteps q), (traj q proj loss sub j ξ i).2.1) 0 ^ 2 =
      accAt q proj loss sub j ξ (selectionSamples q) := by
    rw [hu, accAt, accAt, Finset.sum_range_succ]
    rfl
  simp only [↓reduceIte, algStep, bracketUpdate, bracketQuery, hnot, hlt, selectUpdate,
    hlen, response, hacc]
  have hcnt : j * bracketLength q + (sgdSteps q + u) + 1 = (j + 1) * bracketLength q := by
    rw [Nat.succ_mul]; omega
  rw [hcnt]
  rfl

lemma all_brackets (ξ : ℕ → q.Ξ) :
    ∀ j, j ≤ numBrackets q →
      (algStep q proj loss sub ξ)^[j * bracketLength q] (bracketStart q 0 q.x0 0, 0) =
        (bracketStart q j (best q proj loss sub ξ j).1 (best q proj loss sub ξ j).2,
          j * bracketLength q) := by
  intro j
  induction j with
  | zero => intro _; simp [best]
  | succ j ih =>
    intro hj
    have e : (algStep q proj loss sub ξ)^[(j + 1) * bracketLength q] (bracketStart q 0 q.x0 0, 0) =
        (algStep q proj loss sub ξ)^[bracketLength q]
          ((algStep q proj loss sub ξ)^[j * bracketLength q] (bracketStart q 0 q.x0 0, 0)) := by
      rw [← Function.iterate_add_apply,
        show bracketLength q + j * bracketLength q = (j + 1) * bracketLength q by ring]
    rw [e, ih (Nat.le_of_succ_le hj), bracket_full q proj loss sub ξ hj]
    simp only [best]
    split_ifs <;> rfl

lemma idle (ξ : ℕ → q.Ξ) {st : BracketState q.E} (hst : numBrackets q ≤ st.j) :
    ∀ k n, (algStep q proj loss sub ξ)^[k] (st, n) = (st, n + k) := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    rw [Function.iterate_succ_apply', ih]
    simp only [↓reduceIte, algStep, bracketUpdate, hst]
    rfl

lemma iterate_output (ξ : ℕ → q.Ξ) {K : ℕ} (hK : numBrackets q * bracketLength q ≤ K) :
    ((algStep q proj loss sub ξ)^[K] (bracketStart q 0 q.x0 0, 0)).1.bx =
      (best q proj loss sub ξ (numBrackets q)).1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
  rw [Nat.add_comm, Function.iterate_add_apply, all_brackets q proj loss sub ξ _ le_rfl,
    idle q proj loss sub ξ (st := bracketStart q (numBrackets q) _ _) le_rfl]
  rfl

lemma execute_eq (I : Instance q) (P : ProbabilityMeasure (ℕ → q.Ξ)) (ξ : ℕ → q.Ξ) {K : ℕ}
    (hK : numBrackets q * bracketLength q ≤ K) :
    execute (sampleOracle I proj P) (bracketAlgorithm q) (fun _ => K) () ξ =
      (best q proj I.loss I.sub ξ (numBrackets q)).1 := by
  rw [execute_indexed_of_answer (sampleOracle I proj P) (bracketAlgorithm q) K () ξ
    (response q proj I.loss I.sub ξ) (fun _ _ => rfl)]
  exact iterate_output q proj I.loss I.sub ξ hK

end OracleTemplate.ChiSquareDro

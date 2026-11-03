import LongTails.Proofs.FiniteSumNondualLowerComponents
import LongTails.Proofs.Execution

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.FiniteSumNondualLowerSimulation

open FiniteSumNondualLowerComponents FiniteSumNondualLowerGeometry

noncomputable def partialGradient {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (i : Fin n)
    (r : ℕ) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (L / 8) • (selectedChain π).adjoint (separableSlope
    (fun j t => if j.val ≤ r then maskedSlope (decide (owner j = i))
      (Fin.cases (0 : ℝ) (fun _ => δ) j) (Fin.cases a (fun _ => 0) j) t else 0)
    (selectedChain π x))

lemma partialGradient_eq {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (i : Fin n)
    (r : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ j : Fin k, r < j.succ.val → owner j.succ = i →
      |x (π j.castSucc) - x (π j.succ)| ≤ δ) :
    partialGradient L δ a π owner i r x = hardGradient L δ a π owner i x := by
  unfold partialGradient hardGradient
  congr 2
  apply PiLp.ext
  intro j
  change (if j.val ≤ r then _ else 0) = maskedSlope (decide (owner j = i))
    (Fin.cases (0 : ℝ) (fun _ => δ) j) (Fin.cases a (fun _ => 0) j) (selectedChain π x j)
  by_cases hj : j.val ≤ r
  · simp [hj]
  · rw [ite_eq_right hj]
    have hpos : 0 < j.val := by omega
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (show j ≠ 0 from by intro he; subst j; simp at hpos)
    by_cases ho : owner j.succ = i
    · have hz := (deadZone_inactive δ _ (h j (by omega) ho)).2
      simp [maskedSlope, ho, selectedChain_apply_succ, hz]
    · simp [maskedSlope, ho]

lemma partialGradient_full {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin d)) :
    partialGradient L δ a π owner i k x = hardGradient L δ a π owner i x := by
  apply partialGradient_eq
  intro j hj
  omega

lemma partialGradient_prequery {d k n : ℕ} (L δ a : ℝ) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (i : Fin n)
    (r rnext : ℕ) (hr : r ≤ rnext) (x : EuclideanSpace ℝ (Fin d))
    (hfront : ∀ j : Fin k, j.succ.val = r + 1 → owner j.succ = i →
      j.succ.val ≤ rnext)
    (hsmall : ∀ j : Fin (k + 1), r < j.val → |x (π j)| ≤ δ / 4) :
    partialGradient L δ a π owner i rnext x = hardGradient L δ a π owner i x := by
  apply partialGradient_eq
  intro j hj ho
  have hj₁ : r < j.castSucc.val := by
    have hf := hfront j
    simp only [Fin.val_succ, Fin.val_castSucc] at *
    omega
  have hj₂ : r < j.succ.val := by omega
  have ha := hsmall j.castSucc hj₁
  have hb := hsmall j.succ hj₂
  have ht := abs_sub (x (π j.castSucc)) (x (π j.succ))
  linarith

lemma selectedChain_prefix {d k : ℕ} (π π' : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (hπ : ∀ j : Fin (k + 1), j.val ≤ r → π j = π' j)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin (k + 1)) (hj : j.val ≤ r) :
    selectedChain π x j = selectedChain π' x j := by
  refine Fin.cases ?_ (fun j => ?_) j hj
  · intro h
    simp only [selectedChain_apply_zero, hπ 0 h]
  · intro h
    rw [selectedChain_apply_succ, selectedChain_apply_succ,
      hπ j.succ h, hπ j.castSucc (by simpa using Nat.le_trans (Nat.le_succ j.val) h)]

lemma partialGradient_prefix {d k n : ℕ} (L δ a : ℝ)
    (π π' : Fin (k + 1) ↪ Fin d) (owner owner' : Fin (k + 1) → Fin n)
    (i : Fin n) (r : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (hπ : ∀ j : Fin (k + 1), j.val ≤ r → π j = π' j)
    (ho : ∀ j : Fin (k + 1), j.val ≤ r → owner j = owner' j) :
    partialGradient L δ a π owner i r x = partialGradient L δ a π' owner' i r x := by
  unfold partialGradient
  congr 1
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro j _
  change selectedChain π v j * (if j.val ≤ r then _ else 0) =
    selectedChain π' v j * (if j.val ≤ r then _ else 0)
  by_cases hj : j.val ≤ r
  · simp only [hj, ↓reduceIte, ho j hj, selectedChain_prefix π π' r hπ x j hj,
      selectedChain_prefix π π' r hπ v j hj]
  · simp [hj]

def revealedStep {k n : ℕ} (owner : Fin (k + 1) → Fin n) (i : Fin n) (r : ℕ) : ℕ :=
  if h : r < k then if owner ⟨r + 1, by omega⟩ = i then r + 1 else r else r

lemma revealedStep_ge {k n : ℕ} (owner : Fin (k + 1) → Fin n) (i : Fin n) (r : ℕ) :
    r ≤ revealedStep owner i r := by
  unfold revealedStep
  split_ifs <;> omega

lemma revealedStep_le {k n : ℕ} (owner : Fin (k + 1) → Fin n) (i : Fin n) (r : ℕ)
    (hr : r ≤ k) : revealedStep owner i r ≤ k := by
  unfold revealedStep
  split_ifs <;> omega

lemma revealedStep_front {k n : ℕ} (owner : Fin (k + 1) → Fin n) (i : Fin n)
    (r : ℕ) (j : Fin k) (hj : j.succ.val = r + 1) (ho : owner j.succ = i) :
    j.succ.val ≤ revealedStep owner i r := by
  have hr : r < k := by have := j.isLt; simp only [Fin.val_succ] at hj; omega
  have he : (⟨r + 1, by omega⟩ : Fin (k + 1)) = j.succ := Fin.ext hj.symm
  simp only [revealedStep, hr, ↓reduceDIte, he, ho, ↓reduceIte]
  omega

noncomputable def simulatedState {d k n : ℕ} {S : Type*} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) : ℕ → S × ℕ
  | 0 => (initial, 0)
  | t + 1 =>
    let state := simulatedState L δ a π owner query update initial t
    let q := query state.1
    let r := revealedStep owner q.1 state.2
    (update state.1 (partialGradient L δ a π owner q.1 r q.2), r)

noncomputable def trueState {d k n : ℕ} {S : Type*} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) : ℕ → S
  | 0 => initial
  | t + 1 =>
    let state := trueState L δ a π owner query update initial t
    let q := query state
    update state (hardGradient L δ a π owner q.1 q.2)

lemma simulatedState_coupling {d k n : ℕ} {S : Type*} (L δ a : ℝ) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) (T : ℕ)
    (hgood : ∀ t < T, ∀ j : Fin (k + 1),
      (simulatedState L δ a π owner query update initial t).2 < j.val →
      |(query (simulatedState L δ a π owner query update initial t).1).2 (π j)| ≤ δ / 4) :
    (simulatedState L δ a π owner query update initial T).1 =
      trueState L δ a π owner query update initial T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have he := ih (fun t ht => hgood t (by omega))
    simp only [simulatedState, trueState]
    rw [← he]
    congr 1
    apply partialGradient_prequery L δ a hδ
    · exact revealedStep_ge _ _ _
    · exact fun j hj ho => revealedStep_front _ _ _ j hj ho
    · exact hgood T (by omega)

lemma simulatedState_revealed_le_succ {d k n : ℕ} {S : Type*} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) (T : ℕ) :
    (simulatedState L δ a π owner query update initial T).2 ≤
      (simulatedState L δ a π owner query update initial (T + 1)).2 :=
  revealedStep_ge _ _ _

lemma simulatedState_revealed_le {d k n : ℕ} {S : Type*} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) (T : ℕ) :
    (simulatedState L δ a π owner query update initial T).2 ≤ k := by
  induction T with
  | zero => simp [simulatedState]
  | succ T ih => exact revealedStep_le _ _ _ ih

lemma simulatedState_prefix {d k n : ℕ} {S : Type*} (L δ a : ℝ)
    (π π' : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) (T : ℕ)
    (hπ : ∀ j : Fin (k + 1),
      j.val ≤ (simulatedState L δ a π owner query update initial T).2 → π j = π' j) :
    simulatedState L δ a π owner query update initial T =
      simulatedState L δ a π' owner query update initial T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have hm := simulatedState_revealed_le_succ L δ a π owner query update initial T
    have he := ih (fun j hj => hπ j (hj.trans hm))
    simp only [simulatedState]
    rw [← he]
    congr 2
    exact partialGradient_prefix L δ a π π' owner owner _ _ _ hπ (fun _ _ => rfl)

lemma trueState_iterate {d k n : ℕ} {S : Type*} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) (T : ℕ) :
    trueState L δ a π owner query update initial T =
      (fun state => update state (hardGradient L δ a π owner (query state).1
        (query state).2))^[T] initial := by
  induction T with
  | zero => rfl
  | succ T ih => rw [trueState, ih, Function.iterate_succ_apply']

open LongTails.Setups.FiniteSumNondualSmoothConvex OracleTemplate

lemma execute_hard {p : Params} {k : ℕ} (δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin p.d) (owner : Fin (k + 1) → Fin p.n)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (T : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) :
    execute (hardOracle p δ a π owner) A (fun _ => T) seed ξ =
      A.output (trueState p.L δ a π owner
        (fun s => ((A.query s).2.1, (A.query s).2.2.val)) A.update (A.initial seed) T) := by
  have hξ : ξ = fun _ => () := by funext t; exact Subsingleton.elim _ _
  subst ξ
  rw [trueState_iterate]
  simpa only [hardOracle] using
    (execute_iterate (fun q : Fin p.n × Feasible p =>
      hardGradient p.L δ a π owner q.1 q.2.val) A T seed)

end LongTails.Proofs.FiniteSumNondualLowerSimulation

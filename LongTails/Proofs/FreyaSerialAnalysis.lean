import LongTails.Template
import LongTails.Setups.FreyaPageUniform
import LongTails.Proofs.FreyaMoments
import LongTails.Proofs.RecursiveGradientStep
import LongTails.Proofs.SingleOracleCounted
import LongTails.Proofs.ExecutionHistory

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.FreyaSerialAnalysis

open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs
open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaSerial
open LongTails.Algorithms.FreyaTuning

noncomputable def canonicalize (q : SerialRaw) (seed : Seed q.K) : CanonicalSeed q :=
  (fun k => refreshAt seed k.val,
    (fun k j => labelAt (seed.1 (k.val + 1) j.val) q.m), outputIndex seed)

noncomputable def estimatorError (q : SerialRaw) (f : Fin q.m → Space q.d → ℝ)
    (z : CanonicalSeed q) (k : ℕ) : ℝ :=
  ‖(idealTrace q f z k).2 - gradient (objective f) (idealTrace q f z k).1‖ ^ 2

noncomputable def energy (q : SerialRaw) (f : Fin q.m → Space q.d → ℝ)
    (z : CanonicalSeed q) (k : ℕ) : ℝ :=
  objective f (idealTrace q f z k).1 + q.η / (2 * q.ρ) * estimatorError q f z k

theorem objective_gradient {d m : ℕ} (f : Fin m → Space d → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (x : Space d) :
    gradient (objective f) x = (m : ℝ)⁻¹ • (∑ i, gradient (f i) x) := by
  exact (OracleTemplate.FiniteSum.objective_gradient
    (oracle := fun ix => gradient (f ix.1) ix.2)
    (fun i y => (hf i y).hasGradientAt) x).gradient


theorem component_lipschitz {d m : ℕ} (hm : 0 < m)
    (f : Fin m → Space d → ℝ) (Lplus : ℝ) (hLplus : 0 ≤ Lplus)
    (hmean : ∀ x y, (m : ℝ)⁻¹ * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      Lplus ^ 2 * ‖x - y‖ ^ 2) :
    ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤
      Real.sqrt m * Lplus * ‖x - y‖ := by
  open scoped BigOperators in
    intro i x y
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hsum : ‖gradient (f i) x - gradient (f i) y‖ ^ 2 ≤
        ∑ j, ‖gradient (f j) x - gradient (f j) y‖ ^ 2 :=
      Finset.single_le_sum (f := fun j : Fin m => ‖gradient (f j) x - gradient (f j) y‖ ^ 2)
        (a := i) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hmean' := mul_le_mul_of_nonneg_left (hmean x y) hmR.le
    rw [← mul_assoc, mul_inv_cancel₀ hmR.ne', one_mul] at hmean'
    have hbound := hsum.trans hmean'
    have hsq : (Real.sqrt (m : ℝ) * Lplus * ‖x-y‖)^2 =
        (m : ℝ) * (Lplus^2 * ‖x-y‖^2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hmR.le]
      ring
    have hnonneg : 0 ≤ Real.sqrt (m : ℝ) * Lplus * ‖x-y‖ := by positivity
    nlinarith [norm_nonneg (gradient (f i) x - gradient (f i) y)]


theorem inexact_descent {d : ℕ} (f : Space d → ℝ) (hf : Differentiable ℝ f)
    (L : ℝ) (hL : 0 ≤ L)
    (hsmooth : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x v : Space d) (η : ℝ) (hη : 0 < η) :
    f (x - η • v) ≤ f x - η / 2 * ‖gradient f x‖ ^ 2 -
      (1 / (2 * η) - L / 2) * ‖η • v‖ ^ 2 + η / 2 * ‖v - gradient f x‖ ^ 2 := by
  have _ := hL
  have h := OracleTemplate.NonconvexFiniteSum.inexact_gradient_descent
    (η := η) (fun y => (hf y).hasGradientAt) hsmooth x v
  have heq : (1 / (2 * η) - L / 2) * ‖η • v‖ ^ 2 =
      η / 2 * (1 - L * η) * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [hη.ne']
  rw [heq]
  exact h


theorem zero_smoothness_stationary {d : ℕ} (f : Space d → ℝ)
    (hf : Differentiable ℝ f) (lower : ℝ) (hlower : ∀ x, lower ≤ f x)
    (hsmooth : ∀ x y, ‖gradient f x - gradient f y‖ ≤ 0 * ‖x - y‖) :
    ∀ x, gradient f x = 0 := by
  intro x
  by_contra hne
  have hg : 0 < ‖gradient f x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) _
  let η : ℝ := 2 * (f x - lower + 1) / ‖gradient f x‖ ^ 2
  have h := OracleTemplate.NonconvexFiniteSum.inexact_gradient_descent
    (η := η) (fun y => (hf y).hasGradientAt) hsmooth x (gradient f x)
  have hc : η * ‖gradient f x‖ ^ 2 = 2 * (f x - lower + 1) :=
    div_mul_cancel₀ _ hg.ne'
  have hl := hlower (x - η • gradient f x)
  have hx := hlower x
  simp only [zero_mul, sub_zero, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero, mul_one] at h
  nlinarith


theorem zero_gap_stationary {d : ℕ} (f : Space d → ℝ)
    (hf : Differentiable ℝ f) (lower : ℝ) (hlower : ∀ x, lower ≤ f x)
    (x0 : Space d) (hgap : f x0 - lower ≤ 0) : gradient f x0 = 0 := by
  have hmin : IsMinOn f Set.univ x0 := by
    intro y _
    have hy := hlower y
    exact le_trans (show f x0 ≤ lower by linarith only [hgap]) hy
  have hd := (hmin.isLocalMin (by simp)).hasFDerivAt_eq_zero (hf x0).hasFDerivAt
  apply (InnerProductSpace.toDual ℝ (Space d)).injective
  rw [toDual_gradient, hd, map_zero]


theorem serial_execution (q : SerialRaw) (hm : 0 < q.m) (hS : 0 < q.S)
    (hK : 0 < q.K) (f : Fin q.m → Space q.d → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i))
    (O : Oracle (Option (Fin q.m × Space q.d)) (Space q.d) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
    (hservice : ∀ history, O.answer history (0, none) (ω history.length) = 0 ∧
      ∀ i x, O.answer history (0, some (i, x)) (ω history.length) = gradient (f i) x)
    (N : ℕ) (hN : q.m + q.K * max q.m (2 * q.S) ≤ N) :
    execute O (algorithm q) (fun _ => N) seed ω =
      idealOutput q f (canonicalize q seed) := by
  let A : ℕ → Fin 1 × Option (Fin q.m × Space q.d) → Space q.d :=
    executeAnswerAt O (algorithm q) seed ω
  have hO : ∀ k, A k (0, none) = 0 ∧ ∀ i x, A k (0, some (i, x)) = gradient (f i) x :=
    fun k => hservice (executeIndexedState O (algorithm q) seed ω k).2
  open scoped BigOperators in
    have freyaDevelopmentSelectedStable (q : SerialRaw) (s : State q)
        (hselected : (outputIndex s.seed).val ≤ s.iteration) (reply : Space q.d) :
        (update q s reply).seed = s.seed ∧ s.iteration ≤ (update q s reply).iteration ∧
          (update q s reply).selected = s.selected := by
      have hadv (t : State q) (ht : (outputIndex t.seed).val ≤ t.iteration) :
          (advance q t).seed = t.seed ∧ t.iteration ≤ (advance q t).iteration ∧
            (advance q t).selected = t.selected := by
        delta advance
        split
        · exact ⟨rfl, le_rfl, rfl⟩
        · dsimp only
          refine ⟨rfl, Nat.le_succ _, ?_⟩
          exact ite_eq_right (by omega)
      cases hs : s.phase with
      | halted =>
        delta update
        rw [hs]
        exact ⟨rfl, le_rfl, rfl⟩
      | full =>
        delta update
        rw [hs]
        dsimp only
        split
        · exact ⟨rfl, le_rfl, rfl⟩
        · exact hadv _ hselected
      | firstDifference =>
        delta update
        rw [hs]
        exact ⟨rfl, le_rfl, rfl⟩
      | secondDifference =>
        delta update
        rw [hs]
        dsimp only
        split
        · exact ⟨rfl, le_rfl, rfl⟩
        · exact hadv _ hselected
    have freyaDevelopmentSelectedStableRun (q : SerialRaw)
        (A : ℕ → Fin 1 × Option (Fin q.m × Space q.d) → Space q.d) (N call : ℕ) (s : State q)
        (hselected : (outputIndex s.seed).val ≤ s.iteration) :
        (StochasticGradient.advance
          (fun k s => update q s (A k (query q s))) N call s).selected = s.selected := by
      induction N generalizing call s with
      | zero => rfl
      | succ N ih =>
        rw [StochasticGradient.advance]
        have h := freyaDevelopmentSelectedStable q s hselected (A call (query q s))
        rw [ih]
        · exact h.2.2
        · rw [h.1]
          exact hselected.trans h.2.1
    have freyaDevelopmentAdvanceAdd {X : Type} (step : ℕ → X → X)
        (a b call : ℕ) (s : X) :
        StochasticGradient.advance step (a+b) call s =
          StochasticGradient.advance step b (call+a) (StochasticGradient.advance step a call s) := by
      induction a generalizing call s with
      | zero => simp only [zero_add, Nat.add_zero, StochasticGradient.advance]
      | succ a ih =>
        rw [Nat.succ_add, StochasticGradient.advance, ih, StochasticGradient.advance]
        congr 1
        omega
    have freyaDevelopmentFullBlock (q : SerialRaw) (hm : 0 < q.m)
        (f : Fin q.m → Space q.d → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
        (A : ℕ → Fin 1 × Option (Fin q.m × Space q.d) → Space q.d)
        (hO : ∀ k, A k (0, none) = 0 ∧
          ∀ i x, A k (0, some (i, x)) = gradient (f i) x)
        (s : State q) (hphase : s.phase = .full) (hcomp : s.component = 0)
        (hsum : s.sum = 0) (hiter : s.iteration < q.K) (call : ℕ) :
        StochasticGradient.advance
          (fun k s => update q s (A k (query q s))) q.m call s =
          advance q { s with g := gradient (objective f) s.x } := by
      classical
      let G (j : ℕ) : Space q.d := if h : j < q.m then gradient (f ⟨j,h⟩) s.x else 0
      let F (c : ℕ) : State q := {s with sum := ∑ j ∈ Finset.range c, G j, component := c}
      let step := fun k t => update q t (A k (query q t))
      have hquery (c : ℕ) (hc : c < q.m) :
          query q (F c) = (0, some (⟨c,hc⟩,s.x)) := by
        delta query
        dsimp only [F]
        rw [hphase]
        dsimp only
        rw [dite_eq_left hc]
      have hprefix (c : ℕ) (hc : c < q.m) :
          StochasticGradient.advance step c call s = F c := by
        induction c with
        | zero =>
          change s = { s with sum := ∑ j ∈ Finset.range 0, G j, component := 0 }
          simp only [Finset.sum_range_zero]
          rw [← hsum, ← hcomp]
        | succ c ih =>
          have hc' : c < q.m := by omega
          rw [freyaDevelopmentAdvanceAdd step c 1, ih hc']
          change step (call+c) (F c) = F (c+1)
          dsimp only [step]
          rw [hquery c hc', (hO (call+c)).2]
          delta update
          dsimp only [F]
          rw [hphase]
          dsimp only
          rw [ite_eq_left hc]
          rw [Finset.sum_range_succ]
          have hg : G c = gradient (f ⟨c,hc'⟩) s.x := dite_eq_left hc'
          rw [hg]
      have hm' : q.m = (q.m-1)+1 := by omega
      have hc : q.m-1 < q.m := by omega
      have hsplit := freyaDevelopmentAdvanceAdd step (q.m-1) 1 call s
      rw [← hm'] at hsplit
      change StochasticGradient.advance step q.m call s = _
      rw [hsplit, hprefix (q.m-1) hc]
      change step (call+(q.m-1)) (F (q.m-1)) = _
      dsimp only [step]
      rw [hquery (q.m-1) hc, (hO (call+(q.m-1))).2]
      delta update
      dsimp only [F]
      rw [hphase]
      dsimp only
      rw [ite_eq_right (by omega)]
      have hg : G (q.m-1) = gradient (f ⟨q.m-1,hc⟩) s.x := dite_eq_left hc
      rw [← hg, ← Finset.sum_range_succ, ← hm']
      have htotal : (∑ j ∈ Finset.range q.m, G j) = ∑ i : Fin q.m, gradient (f i) s.x := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i _
        exact dite_eq_left i.isLt
      rw [htotal, ← objective_gradient f hf s.x]
      delta advance
      dsimp only
      simp only [Nat.not_le.mpr hiter, ite_false]
    have freyaDevelopmentOptionAnswer (q : SerialRaw)
        (f : Fin q.m → Space q.d → ℝ)
        (A : ℕ → Fin 1 × Option (Fin q.m × Space q.d) → Space q.d)
        (hO : ∀ k, A k (0, none) = 0 ∧
          ∀ i x, A k (0, some (i, x)) = gradient (f i) x)
        (k : ℕ) (l : Option (Fin q.m)) (x : Space q.d) :
        A k (0,l.map fun i => (i,x)) = l.elim 0 (fun i => gradient (f i) x) := by
      cases l with
      | none => exact (hO k).1
      | some i => exact (hO k).2 i x
    have freyaDevelopmentDifferenceBlock (q : SerialRaw) (hS : 0 < q.S)
        (f : Fin q.m → Space q.d → ℝ)
        (A : ℕ → Fin 1 × Option (Fin q.m × Space q.d) → Space q.d)
        (hO : ∀ k, A k (0, none) = 0 ∧
          ∀ i x, A k (0, some (i, x)) = gradient (f i) x)
        (s : State q) (hphase : s.phase = .firstDifference) (hsample : s.sample = 0)
        (hsum : s.sum = 0) (hiter : s.iteration < q.K) (call : ℕ) :
        StochasticGradient.advance
          (fun k s => update q s (A k (query q s))) (2*q.S) call s =
          advance q { s with g := s.g + (q.S : ℝ)⁻¹ •
            (∑ j : Fin q.S, (labelAt (s.seed.1 s.iteration j.val) q.m).elim 0
              (fun i => gradient (f i) s.x - gradient (f i) s.previous)) } := by
      classical
      let New (j : ℕ) := (labelAt (s.seed.1 s.iteration j) q.m).elim 0 (fun i => gradient (f i) s.x)
      let Old (j : ℕ) := (labelAt (s.seed.1 s.iteration j) q.m).elim 0 (fun i => gradient (f i) s.previous)
      let D (j : ℕ) := New j - Old j
      let F (c : ℕ) : State q :=
        {s with
          sum := ∑ j ∈ Finset.range c, D j
          sample := c
          first := if c=0 then s.first else New (c-1)}
      let step := fun k t => update q t (A k (query q t))
      have hfirst (c k : ℕ) : step k (F c) = {F c with first := New c, phase := .secondDifference} := by
        have hquery : query q (F c) = (0,(labelAt (s.seed.1 s.iteration c) q.m).map fun i => (i,s.x)) := by
          delta query
          dsimp only [F]
          rw [hphase]
        dsimp only [step]
        rw [hquery, freyaDevelopmentOptionAnswer q f A hO]
        delta update
        dsimp only [F]
        rw [hphase]
      have hsecond (c k : ℕ) :
          step k {F c with first := New c, phase := .secondDifference} =
            if c+1 < q.S then
              {F c with
                first := New c
                sum := (F c).sum + D c
                sample := c+1
                phase := .firstDifference}
            else advance q
              {F c with
                first := New c
                phase := .secondDifference
                g := s.g + (q.S : ℝ)⁻¹ • ((F c).sum + D c)} := by
        dsimp only [step]
        have hquery : query q {F c with first := New c, phase := .secondDifference} =
            (0,(labelAt (s.seed.1 s.iteration c) q.m).map fun i => (i,s.previous)) := rfl
        rw [hquery, freyaDevelopmentOptionAnswer q f A hO]
        rfl
      have hprefix (c : ℕ) (hc : c < q.S) :
          StochasticGradient.advance step (2*c) call s = F c := by
        induction c with
        | zero =>
          change s = F 0
          dsimp only [F]
          simp only [Finset.sum_range_zero, ite_true]
          rw [← hsum, ← hsample]
        | succ c ih =>
          have hc' : c < q.S := by omega
          rw [Nat.mul_succ, freyaDevelopmentAdvanceAdd step (2*c) 2, ih hc']
          change step (call+2*c+1) (step (call+2*c) (F c)) = _
          rw [hfirst, hsecond, ite_eq_left hc]
          dsimp only [F]
          rw [Finset.sum_range_succ, hphase]
          simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
      have hSc : q.S = q.S-1+1 := by omega
      have hc : q.S-1 < q.S := by omega
      have hsplit := freyaDevelopmentAdvanceAdd step (2*(q.S-1)) 2 call s
      have hcount : 2*(q.S-1)+2 = 2*q.S := by omega
      rw [hcount] at hsplit
      change StochasticGradient.advance step (2*q.S) call s = _
      rw [hsplit, hprefix (q.S-1) hc]
      change step (call+2*(q.S-1)+1) (step (call+2*(q.S-1)) (F (q.S-1))) = _
      rw [hfirst,hsecond,ite_eq_right (by omega)]
      dsimp only [F]
      rw [← Finset.sum_range_succ, ← hSc]
      have htotal : (∑ j ∈ Finset.range q.S, D j) =
          ∑ j : Fin q.S, (labelAt (s.seed.1 s.iteration j.val) q.m).elim 0
            (fun i => gradient (f i) s.x - gradient (f i) s.previous) := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [D,New,Old]
        cases labelAt (s.seed.1 s.iteration j.val) q.m
        · exact sub_self 0
        · rfl
      rw [htotal]
      delta advance
      dsimp only
      simp only [Nat.not_le.mpr hiter,ite_false]
    classical
    let z := canonicalize q seed
    let st : ℕ → State q := fun k => Nat.rec (initial q seed)
      (fun a s => advance q {s with g := (idealTrace q f z a).2}) k
    let step := fun k s => update q s (A k (query q s))
    have hrec (a : ℕ) : idealTrace q f z (a+1) = idealTrace._sunfold q f z (a+1) := by
      conv_lhs => delta idealTrace
      refine (Nat.brecOn.eq (motive := fun _ => Space q.d × Space q.d) (a+1)
        (idealTrace._f q f z)).trans ?_
      delta idealTrace._sunfold idealTrace._f idealTrace
      rfl
    have hposition (k : ℕ) (hk : k < q.K) :
        (idealTrace q f z (k+1)).1 = (idealTrace q f z k).1 - q.η • (idealTrace q f z k).2 := by
      rw [hrec]
      delta idealTrace._sunfold
      dsimp only
      rw [dite_eq_left hk]
    have hfields (k : ℕ) (hk : k ≤ q.K) :
        (st k).seed = seed ∧ (st k).iteration = k ∧ (st k).x = (idealTrace q f z k).1 ∧
        (st k).sum = 0 ∧ (st k).first = 0 ∧ (st k).component = 0 ∧ (st k).sample = 0 ∧
        ((outputIndex seed).val = k → (st k).selected = (idealTrace q f z k).1) ∧
        (0 < k → (st k).previous = (idealTrace q f z (k-1)).1 ∧
          (st k).g = (idealTrace q f z (k-1)).2 ∧
          (st k).phase = if refreshAt seed (k-1) then .full else .firstDifference) := by
      induction k with
      | zero =>
        refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
        · intro _
          rfl
        · intro h
          omega
      | succ k ih =>
        have hk' : k < q.K := by omega
        obtain ⟨hs,hi,hx,_,_,_,_,_,_⟩ := ih (by omega)
        have hst : st (k+1) = advance q {st k with g := (idealTrace q f z k).2} := rfl
        rw [hst]
        delta advance
        dsimp only
        rw [hi, ite_eq_right (Nat.not_le.mpr hk')]
        dsimp only
        rw [hs,hx]
        refine ⟨rfl,rfl,(hposition k hk').symm,rfl,rfl,rfl,rfl,?_,?_⟩
        · intro hselect
          rw [ite_eq_left hselect]
          exact (hposition k hk').symm
        · intro _
          simpa only [Nat.add_sub_cancel] using
            (And.intro rfl (And.intro rfl rfl) :
              (idealTrace q f z k).1 = (idealTrace q f z k).1 ∧
              (idealTrace q f z k).2 = (idealTrace q f z k).2 ∧
              (if refreshAt seed k then Phase.full else .firstDifference) =
                (if refreshAt seed k then Phase.full else .firstDifference))
    have hblock (k : ℕ) (hk : k < q.K) (call : ℕ) :
        ∃ C ≤ max q.m (2*q.S), StochasticGradient.advance step C call (st k) = st (k+1) := by
      obtain ⟨hs,hi,hx,hsum,hfirst,hcomp,hsample,_,hpast⟩ := hfields k hk.le
      by_cases hz : k = 0
      · subst k
        refine ⟨q.m,le_max_left _ _,?_⟩
        have hphase : (st 0).phase = .full := by
          change (if q.m=0 ∨ q.K=0 then Phase.halted else .full) = .full
          exact ite_eq_right (by omega)
        have hb := freyaDevelopmentFullBlock q hm f hf A hO (st 0) hphase hcomp hsum
          (by rw [hi]; exact hK) call
        exact hb
      · obtain ⟨hprevious,hg,hphase⟩ := hpast (by omega)
        have hkprev : k-1 < q.K := by omega
        have hksucc : k-1+1 = k := by omega
        have hgformula := hrec (k-1)
        change idealTrace q f z (k-1+1) = idealTrace._sunfold q f z (k-1+1) at hgformula
        delta idealTrace._sunfold at hgformula
        dsimp only at hgformula
        rw [dite_eq_left hkprev] at hgformula
        rw [hksucc] at hgformula
        have hxk : (idealTrace q f z k).1 =
            (idealTrace q f z (k-1)).1-q.η • (idealTrace q f z (k-1)).2 := by
          rw [← hksucc]
          exact hposition (k-1) hkprev
        have hgk := congrArg Prod.snd hgformula
        dsimp only at hgk
        rw [← hxk] at hgk
        by_cases hb : refreshAt seed (k-1) = true
        · rw [ite_eq_left hb] at hphase
          rw [ite_eq_left (show z.1 ⟨k-1,hkprev⟩ = true from hb)] at hgk
          refine ⟨q.m,le_max_left _ _,?_⟩
          rw [freyaDevelopmentFullBlock q hm f hf A hO (st k) hphase hcomp hsum
            (by rw [hi]; exact hk) call]
          change advance q {st k with g := gradient (objective f) (st k).x} =
            advance q {st k with g := (idealTrace q f z k).2}
          rw [hx,hgk]
        · rw [ite_eq_right hb] at hphase
          rw [ite_eq_right (show ¬ z.1 ⟨k-1,hkprev⟩ = true from hb)] at hgk
          have hrows : z.2.1 ⟨k-1,hkprev⟩ = fun j : Fin q.S => labelAt (seed.1 k j.val) q.m := by
            change (fun j : Fin q.S => labelAt (seed.1 (k-1+1) j.val) q.m) = _
            rw [hksucc]
          rw [hrows] at hgk
          dsimp only at hgk
          refine ⟨2*q.S,le_max_right _ _,?_⟩
          rw [freyaDevelopmentDifferenceBlock q hS f A hO (st k) hphase hsample hsum
            (by rw [hi]; exact hk) call]
          change advance q {st k with g := _} = advance q {st k with g := (idealTrace q f z k).2}
          apply congrArg (fun g => advance q {st k with g := g})
          rw [hs,hi,hx,hprevious,hg,hgk]
          congr 2
          apply Finset.sum_congr rfl
          intro j _
          cases labelAt (seed.1 k j.val) q.m <;> rfl
    have hreach (k : ℕ) (hk : k ≤ q.K) :
        ∃ t ≤ k*max q.m (2*q.S), StochasticGradient.advance step t 0 (initial q seed) = st k := by
      induction k with
      | zero => exact ⟨0,Nat.zero_le _,rfl⟩
      | succ k ih =>
        obtain ⟨t,ht,heq⟩ := ih (by omega)
        obtain ⟨C,hC,hblock⟩ := hblock k (by omega) t
        refine ⟨t+C,?_,?_⟩
        · simpa only [Nat.succ_mul] using Nat.add_le_add ht hC
        · rw [freyaDevelopmentAdvanceAdd,heq]
          simpa only [Nat.zero_add] using hblock
    let i := (outputIndex seed).val
    have hi : i < q.K := by
      have hi := (outputIndex seed).isLt
      simpa only [i,max_eq_right (show 1 ≤ q.K by omega)] using hi
    obtain ⟨t,ht,hreach⟩ := hreach i hi.le
    have htN : t ≤ N := ht.trans ((Nat.mul_le_mul_right _ hi.le).trans (by omega))
    have hsplit := freyaDevelopmentAdvanceAdd step t (N-t) 0 (initial q seed)
    rw [Nat.add_sub_of_le htN] at hsplit
    erw [execute_advance_history]
    change (StochasticGradient.advance step N 0 (initial q seed)).selected = _
    rw [hsplit,hreach]
    have hfields := hfields i hi.le
    rw [freyaDevelopmentSelectedStableRun q A (N-t) (0+t) (st i)
      (by rw [hfields.1,hfields.2.1])]
    exact hfields.2.2.2.2.2.2.2.1 rfl


theorem serial_law (q : SerialRaw) :
    HasLaw (canonicalize q) (canonicalLaw q : Measure (CanonicalSeed q))
      (seedLaw q.ρ q.K : Measure (Seed q.K)) := by
  classical
  have singleton (m : ℕ) : MeasurableSingletonClass (Option (Fin m)) := by
    constructor
    intro a
    cases a with
    | none =>
      refine ⟨{Sum.inl ()}, by rw [measurableSet_sum_iff]; constructor <;> simp, ?_⟩
      apply Set.ext
      intro b
      cases b with
      | none => exact iff_of_true rfl rfl
      | some b => exact iff_of_false Sum.inr_ne_inl (Option.some_ne_none b)
    | some i =>
      refine ⟨{Sum.inr i}, by rw [measurableSet_sum_iff]; constructor <;> simp, ?_⟩
      apply Set.ext
      intro b
      cases b with
      | none => exact iff_of_false Sum.inl_ne_inr (Ne.symm (Option.some_ne_none i))
      | some b =>
        exact ⟨fun h => congrArg some (Sum.inr.inj h),
          fun h => congrArg Sum.inr (Option.some.inj h)⟩
  have select {ι α β : Type} [Fintype ι] [MeasurableSpace α] [MeasurableSpace β]
      (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      (X : α → β) (hX : MeasurePreserving X μ ν) (n : ι → ℕ) (hn : Function.Injective n) :
      MeasurePreserving (fun z : ℕ → α => fun i => X (z (n i)))
        (Measure.infinitePi fun _ : ℕ => μ) (Measure.pi fun _ : ι => ν) := by
    have hind := (iIndepFun_infinitePi (P := fun _ : ℕ => μ) (fun _ => hX.measurable)).precomp hn
    have hlaw (i : ι) : HasLaw (fun z : ℕ → α => X (z (n i))) ν
        (Measure.infinitePi fun _ : ℕ => μ) := by
      have h := hX.comp (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) (n i))
      exact ⟨h.measurable.aemeasurable, h.map_eq⟩
    exact ⟨Measurable.of_eval (fun i => hX.measurable.comp (measurable_pi_apply (n i))),
      (iIndepFun.hasLaw_pi hlaw hind).map_eq⟩
  have hlabel (m : ℕ) : MeasurePreserving (fun row : ChoiceRow => labelAt row m)
      (rowLaw : Measure ChoiceRow) (componentLaw m : Measure (Option (Fin m))) := by
    cases m with
    | zero =>
      change MeasurePreserving (fun _ : ChoiceRow => (none : Option (Fin 0)))
        (rowLaw : Measure ChoiceRow) (Measure.dirac none)
      exact ⟨measurable_const, by simp⟩
    | succ m =>
      have : MeasurableSingletonClass (Option (Fin (m+1))) := singleton (m+1)
      have hfun : (fun row : ChoiceRow => labelAt row (m+1)) = (fun row => some (row m)) := by
        funext row
        delta labelAt
        rw [dite_eq_left (Nat.succ_pos m)]
        apply congrArg some
        apply Fin.ext
        exact congrArg (fun j : ℕ => (row j).val) (Nat.add_sub_cancel m 1)
      rw [hfun]
      have hmapped : MeasurePreserving (some : Fin (m+1) → Option (Fin (m+1)))
          (PMF.uniformOfFintype (Fin (m+1))).toMeasure (componentLaw (m+1)) := by
        refine ⟨measurable_of_countable _, ?_⟩
        delta componentLaw
        erw [dite_eq_left (Nat.succ_pos m)]
        exact PMF.toMeasure_map (some : Fin (m+1) → Option (Fin (m+1)))
          (PMF.uniformOfFintype (Fin (m+1))) (measurable_of_countable _)
      exact hmapped.comp (measurePreserving_eval_infinitePi
        (fun j : ℕ => (PMF.uniformOfFintype (Fin (j+1))).toMeasure) m)
  have : NeZero (max 1 q.K) := ⟨by omega⟩
  let μ := (rowLaw : Measure ChoiceRow)
  let ν := (componentLaw q.m : Measure (Option (Fin q.m)))
  let β := bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one q.ρ)
  let ξ := (PMF.uniformOfFintype (Fin (max 1 q.K))).toMeasure
  have hrow := select μ ν (fun row => labelAt row q.m) (hlabel q.m)
    (fun j : Fin q.S => j.val) Fin.val_injective
  have hrows := select (Measure.infinitePi fun _ : ℕ => μ) (Measure.pi fun _ : Fin q.S => ν)
    (fun r : ℕ → ChoiceRow => fun j : Fin q.S => labelAt (r j.val) q.m) hrow
    (fun k : Fin q.K => k.val+1) (by
      intro a b h
      change a.val+1=b.val+1 at h
      apply Fin.val_injective
      omega)
  have hbits := select β β id (MeasurePreserving.id β)
    (fun k : Fin q.K => k.val) Fin.val_injective
  let R := Measure.pi (fun _ : Fin q.K => Measure.pi (fun _ : Fin q.S => ν))
  let B := Measure.pi (fun _ : Fin q.K => β)
  have hmap := hrows.prod (hbits.prod (MeasurePreserving.id ξ))
  have hassoc := (measurePreserving_prodAssoc R B ξ).symm MeasurableEquiv.prodAssoc
  have hswap := (Measure.measurePreserving_swap (μ := R) (ν := B)).prod (MeasurePreserving.id ξ)
  have hfinal := (measurePreserving_prodAssoc B R ξ).comp (hswap.comp (hassoc.comp hmap))
  exact ⟨hfinal.measurable.aemeasurable, hfinal.map_eq⟩


theorem estimator_recursion (q : SerialRaw) (hm : 0 < q.m) (hS : 0 < q.S)
    (hρ : 0 < q.ρ) (hρone : q.ρ ≤ 1)
    (f : Fin q.m → Space q.d → ℝ) (lower Lminus Lplus Lpm Δ : ℝ)
    (hreg : RegularObjective f q.x0 lower Lminus Lplus Lpm Δ)
    (k : ℕ) (hk : k < q.K) :
    (∫ z, estimatorError q f z (k + 1) ∂(canonicalLaw q : Measure (CanonicalSeed q))) ≤
      (1 - q.ρ) * (∫ z, estimatorError q f z k ∂(canonicalLaw q : Measure (CanonicalSeed q))) +
      (1 - q.ρ) * Lpm ^ 2 / q.S *
        (∫ z, ‖(idealTrace q f z (k + 1)).1 - (idealTrace q f z k).1‖ ^ 2
          ∂(canonicalLaw q : Measure (CanonicalSeed q))) := by
  open scoped BigOperators ENNReal in
    classical
    have freyaDevelopmentResample {ι α : Type} [Fintype ι] [DecidableEq ι]
        [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) :
        MeasurePreserving (fun z : (ι → α) × α => Function.update z.1 i z.2)
          ((Measure.pi fun _ : ι => μ).prod μ) (Measure.pi fun _ : ι => μ) := by
      classical
      have hm : Measurable (fun z : (ι → α) × α => Function.update z.1 i z.2) := by
        apply Measurable.of_eval
        intro j
        by_cases hj : j = i
        · subst j
          simpa (config := { iota := false }) only [Function.update_self] using
            (measurable_snd : Measurable (fun z : (ι → α) × α => z.2))
        · simpa (config := { iota := false }) only [Function.update_of_ne hj, Function.comp_def] using
            ((measurable_pi_apply j).comp (measurable_fst : Measurable (fun z : (ι → α) × α => z.1)))
      refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
      rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
      have he : (fun z : (ι → α) × α => Function.update z.1 i z.2) ⁻¹' Set.pi Set.univ s =
          (Set.pi (↑(Finset.univ.erase i) : Set ι) s) ×ˢ s i := by
        ext z
        simp (config := { iota := false }) only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
          Set.mem_prod, Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro h
          constructor
          · intro j hj
            simpa (config := { iota := false }) only [Function.update_of_ne hj] using h j
          · simpa (config := { iota := false }) only [Function.update_self] using h i
        · rintro ⟨h, hi⟩ j
          by_cases hj : j = i
          · subst j
            simpa (config := { iota := false }) only [Function.update_self] using hi
          · simpa (config := { iota := false }) only [Function.update_of_ne hj] using h j hj
      rw [he, Measure.prod_prod, Measure.pi_pi_finset]
      exact Finset.prod_erase_mul (Finset.univ : Finset ι) (fun j => μ (s j)) (Finset.mem_univ i)
    have freyaDevelopmentResampleIntegral {ι α : Type} [Fintype ι] [DecidableEq ι]
        [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
        (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) (F : (ι → α) → ℝ) :
        (∫ z, F z ∂(Measure.pi fun _ : ι => μ)) =
          ∫ z, ∫ a, F (Function.update z i a) ∂μ ∂(Measure.pi fun _ : ι => μ) := by
      have h := freyaDevelopmentResample μ i
      have law : HasLaw (fun z : (ι → α) × α => Function.update z.1 i z.2)
          (Measure.pi fun _ : ι => μ) ((Measure.pi fun _ : ι => μ).prod μ) :=
        ⟨h.measurable.aemeasurable, h.map_eq⟩
      rw [← law.integral_comp (show AEStronglyMeasurable F (Measure.pi fun _ : ι => μ) from
        Integrable.of_finite.aestronglyMeasurable)]
      exact integral_prod _ Integrable.of_finite
    have freyaDevelopmentBatchMoment {d m S : ℕ} (hm : 0 < m) (hS : 0 < S)
        (f : Fin m → Space d → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
        (D : ℝ) (x y g : Space d)
        (hvar : (m : ℝ)⁻¹ * (∑ i, ‖gradient (f i) x-gradient (f i) y‖^2) -
          ‖gradient (objective f) x-gradient (objective f) y‖^2 ≤ D^2*‖x-y‖^2)
        [MeasurableSingletonClass (Option (Fin m))] :
        (∫ r, ‖g+(S : ℝ)⁻¹ • (∑ j : Fin S,
          Option.elim' (0 : Space d) (fun i => gradient (f i) x-gradient (f i) y) (r j))-
            gradient (objective f) x‖^2
          ∂(Measure.pi fun _ : Fin S => (componentLaw m : Measure (Option (Fin m))))) ≤
          ‖g-gradient (objective f) y‖^2+D^2/(S : ℝ)*‖x-y‖^2 := by
      classical
      have : NeZero m := ⟨hm.ne'⟩
      let μ := (PMF.uniformOfFintype (Fin m)).toMeasure
      let ν := Measure.pi (fun _ : Fin S => μ)
      let P : ProbabilityMeasure (Fin S → Fin m) := ⟨ν, inferInstance⟩
      let v (i : Fin m) := gradient (f i) x-gradient (f i) y
      let u := gradient (objective f) x-gradient (objective f) y
      let avg (r : Fin S → Fin m) := (S : ℝ)⁻¹ • (∑ j : Fin S, v (r j))
      have hu : (m : ℝ)⁻¹ • (∑ i, v i) = u := by
        dsimp only [u, v]
        rw [objective_gradient f hf x, objective_gradient f hf y, Finset.sum_sub_distrib,
          smul_sub]
      have hmoment := LongTails.Proofs.FreyaMoments.uniform_centered_second_moment P hS v
        (fun j r => r j) (fun j => measurable_pi_apply j)
        (fun j => ⟨(measurable_pi_apply j).aemeasurable, (measurePreserving_eval (fun _ : Fin S => μ) j).map_eq⟩)
        (iIndepFun_pi (fun _ : Fin S => (measurable_id : Measurable (id : Fin m → Fin m)).aemeasurable))
      rw [hu] at hmoment
      have hzero : (∫ r, avg r-u ∂ν) = 0 := by
        rw [integral_sub Integrable.of_finite Integrable.of_finite]
        simpa (config := { iota := false }) [P, avg] using
          congrArg (fun a : Space d => a-u) hmoment.2.1
      have hcross : (∫ r, inner ℝ (g-gradient (objective f) y) (avg r-u) ∂ν) = 0 := by
        have hc := congrArg (fun a : Space d => inner ℝ (g-gradient (objective f) y) a) hzero
        rw [integral_fintype (show Integrable (fun r => avg r-u) ν from Integrable.of_finite)] at hc
        rw [integral_fintype (show Integrable (fun r => inner ℝ (g-gradient (objective f) y) (avg r-u)) ν from Integrable.of_finite)]
        simpa (config := { iota := false }) only [inner_sum, inner_smul_right, inner_zero_right, smul_eq_mul] using hc
      have hsplit (r : Fin S → Fin m) : g+avg r-gradient (objective f) x =
          (g-gradient (objective f) y)+(avg r-u) := by
        dsimp only [u]
        rw [sub_eq_add_neg (avg r) _, neg_sub, ← add_sub_assoc,
          add_comm (avg r) (gradient (objective f) y), ← add_sub_assoc,
          ← add_assoc, sub_add_cancel]
      have hbound : (∫ r, ‖g+avg r-gradient (objective f) x‖^2 ∂ν) ≤
          ‖g-gradient (objective f) y‖^2+D^2/(S : ℝ)*‖x-y‖^2 := by
        simp_rw [hsplit, norm_add_sq_real]
        rw [integral_add Integrable.of_finite Integrable.of_finite,
          integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul, hcross]
        simp (config := { iota := false }) only [integral_const, probReal_univ, one_smul, mul_zero, add_zero]
        have hv := hmoment.2.2.2
        change (∫ r, ‖avg r-u‖^2 ∂ν) = _ at hv
        rw [hv]
        have hh := mul_le_mul_of_nonneg_left hvar (inv_nonneg.mpr (Nat.cast_nonneg S : (0 : ℝ) ≤ S))
        simpa (config := { iota := false }) only [v, u, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          add_le_add le_rfl hh
      have hmapped : MeasurePreserving (some : Fin m → Option (Fin m)) μ (componentLaw m) := by
        refine ⟨measurable_of_countable _, ?_⟩
        delta componentLaw
        erw [dite_eq_left hm]
        exact PMF.toMeasure_map (some : Fin m → Option (Fin m))
          (PMF.uniformOfFintype (Fin m)) (measurable_of_countable _)
      have hp := measurePreserving_pi (fun _ : Fin S => μ)
        (fun _ : Fin S => (componentLaw m : Measure (Option (Fin m)))) (fun _ => hmapped)
      have hlaw : HasLaw (fun r : Fin S → Fin m => fun j => some (r j))
          (Measure.pi fun _ : Fin S => (componentLaw m : Measure (Option (Fin m)))) ν :=
        ⟨hp.measurable.aemeasurable, hp.map_eq⟩
      rw [← hlaw.integral_comp (show AEStronglyMeasurable
        (fun r => ‖g+(S : ℝ)⁻¹ • (∑ j : Fin S,
          Option.elim' (0 : Space d) (fun i => gradient (f i) x-gradient (f i) y) (r j))-
            gradient (objective f) x‖^2) _ from Integrable.of_finite.aestronglyMeasurable)]
      exact hbound
    have freyaDevelopmentDoubleResample {ι α β γ : Type} [Fintype ι] [DecidableEq ι]
        [Fintype α] [Fintype β] [Fintype γ]
        [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
        [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
        (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
        [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
        (i : ι) (F : (ι → α) → (ι → β) → γ → ℝ) :
        (∫ b, ∫ r, ∫ j, F b r j ∂ξ ∂(Measure.pi fun _ : ι => ν) ∂(Measure.pi fun _ : ι => μ)) =
          ∫ b, ∫ r, ∫ j, ∫ a, ∫ t, F (Function.update b i a) (Function.update r i t) j
            ∂ν ∂μ ∂ξ ∂(Measure.pi fun _ : ι => ν) ∂(Measure.pi fun _ : ι => μ) := by
      rw [freyaDevelopmentResampleIntegral μ i]
      apply integral_congr_ae
      filter_upwards [] with b
      calc
        (∫ a, ∫ r, ∫ j, F (Function.update b i a) r j ∂ξ ∂(Measure.pi fun _ : ι => ν) ∂μ) =
            ∫ a, ∫ r, ∫ t, ∫ j, F (Function.update b i a) (Function.update r i t) j
              ∂ξ ∂ν ∂(Measure.pi fun _ : ι => ν) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with a
          exact freyaDevelopmentResampleIntegral ν i _
        _ = ∫ r, ∫ a, ∫ t, ∫ j, F (Function.update b i a) (Function.update r i t) j
              ∂ξ ∂ν ∂μ ∂(Measure.pi fun _ : ι => ν) :=
          integral_integral_swap Integrable.of_finite
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with r
          calc
            (∫ a, ∫ t, ∫ j, F (Function.update b i a) (Function.update r i t) j ∂ξ ∂ν ∂μ) =
                ∫ a, ∫ j, ∫ t, F (Function.update b i a) (Function.update r i t) j ∂ν ∂ξ ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with a
              exact integral_integral_swap Integrable.of_finite
            _ = _ := integral_integral_swap Integrable.of_finite
    have freyaDevelopmentPastInvariant (q : SerialRaw) (f : Fin q.m → Space q.d → ℝ)
        (k : Fin q.K) (z : CanonicalSeed q) (b : Bool) (r : Fin q.S → Option (Fin q.m))
        (a : ℕ) (ha : a ≤ k.val) :
        idealTrace q f (Function.update z.1 k b, Function.update z.2.1 k r, z.2.2) a =
          idealTrace q f z a := by
      have hrec (z : CanonicalSeed q) (a : ℕ) : idealTrace q f z (a+1) =
          idealTrace._sunfold q f z (a+1) := by
        conv_lhs => delta idealTrace
        refine (Nat.brecOn.eq (motive := fun _ => Space q.d × Space q.d) (a+1)
          (idealTrace._f q f z)).trans ?_
        delta idealTrace._sunfold idealTrace._f idealTrace
        rfl
      induction a with
      | zero => rfl
      | succ a ih =>
        rw [hrec, hrec]
        delta idealTrace._sunfold
        dsimp only
        rw [ih (by omega)]
        have hak : a < q.K := by omega
        rw [dite_eq_left hak, dite_eq_left hak]
        have hne : (⟨a, hak⟩ : Fin q.K) ≠ k := by
          intro he
          have := congrArg Fin.val he
          dsimp only at this
          omega
        simp (config := { iota := false }) only [Function.update_of_ne hne]
    have : MeasurableSingletonClass (Option (Fin q.m)) := by
      constructor
      intro a
      cases a with
      | none =>
        refine ⟨{Sum.inl ()}, by rw [measurableSet_sum_iff]; constructor <;> simp, ?_⟩
        apply Set.ext
        intro b
        cases b with
        | none => exact iff_of_true rfl rfl
        | some b => exact iff_of_false Sum.inr_ne_inl (Option.some_ne_none b)
      | some i =>
        refine ⟨{Sum.inr i}, by rw [measurableSet_sum_iff]; constructor <;> simp, ?_⟩
        apply Set.ext
        intro b
        cases b with
        | none => exact iff_of_false Sum.inl_ne_inr (Ne.symm (Option.some_ne_none i))
        | some b =>
          exact ⟨fun h => congrArg some (Sum.inr.inj h),
            fun h => congrArg Sum.inr (Option.some.inj h)⟩
    have : NeZero (max 1 q.K) := ⟨by omega⟩
    let μ := bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one q.ρ)
    let ν := Measure.pi (fun _ : Fin q.S => (componentLaw q.m : Measure (Option (Fin q.m))))
    let ξ := (PMF.uniformOfFintype (Fin (max 1 q.K))).toMeasure
    let κ : Fin q.K := ⟨k,hk⟩
    let fresh (z : CanonicalSeed q) (b : Bool) (r : Fin q.S → Option (Fin q.m)) : CanonicalSeed q :=
      (Function.update z.1 κ b, Function.update z.2.1 κ r, z.2.2)
    let x (z : CanonicalSeed q) := (idealTrace q f z k).1-q.η • (idealTrace q f z k).2
    have hpast (z : CanonicalSeed q) (b : Bool) (r : Fin q.S → Option (Fin q.m)) :
        idealTrace q f (fresh z b r) k = idealTrace q f z k :=
      freyaDevelopmentPastInvariant q f κ z b r k (le_refl k)
    have hrec (z : CanonicalSeed q) (a : ℕ) : idealTrace q f z (a+1) =
        idealTrace._sunfold q f z (a+1) := by
      conv_lhs => delta idealTrace
      refine (Nat.brecOn.eq (motive := fun _ => Space q.d × Space q.d) (a+1)
        (idealTrace._f q f z)).trans ?_
      delta idealTrace._sunfold idealTrace._f idealTrace
      rfl
    have hx (z : CanonicalSeed q) : (idealTrace q f z (k+1)).1 = x z := by
      rw [hrec]
      delta idealTrace._sunfold
      dsimp only
      rw [dite_eq_left hk]
    have heval (z : CanonicalSeed q) (b : Bool) (r : Fin q.S → Option (Fin q.m)) :
        estimatorError q f (fresh z b r) (k+1) =
          if b then 0 else ‖(idealTrace q f z k).2+(q.S : ℝ)⁻¹ •
            (∑ j : Fin q.S, Option.elim' (0 : Space q.d)
              (fun i => gradient (f i) (x z)-gradient (f i) (idealTrace q f z k).1) (r j))-
                gradient (objective f) (x z)‖^2 := by
      change ‖(idealTrace q f (fresh z b r) (k+1)).2-
        gradient (objective f) (idealTrace q f (fresh z b r) (k+1)).1‖^2 = _
      rw [hrec]
      delta idealTrace._sunfold
      dsimp only
      rw [dite_eq_left hk, hpast]
      dsimp only [fresh, κ]
      simp (config := { iota := false }) only [Function.update_self]
      cases b
      · rw [ite_eq_right Bool.false_ne_true]
        congr 5
        apply Finset.sum_congr rfl
        intro j _
        cases r j <;> rfl
      · rw [ite_eq_left rfl]
        simp (config := { iota := false }) only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), ite_true]
    have hp : ((Set.projIcc 0 1 zero_le_one q.ρ : unitInterval) : ℝ) = q.ρ := by
      exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hρ.le,hρone⟩)
    have hstep (z : CanonicalSeed q) :
        (∫ b, ∫ r, estimatorError q f (fresh z b r) (k+1) ∂ν ∂μ) ≤
          (1-q.ρ)*estimatorError q f z k+
            (1-q.ρ)*Lpm^2/q.S*‖(idealTrace q f z (k+1)).1-(idealTrace q f z k).1‖^2 := by
      simp_rw [heval]
      change (∫ b, _ ∂bernoulliMeasure true false _) ≤ _
      rw [integral_bernoulliMeasure]
      simp (config := { iota := false }) only [Bool.false_eq_true, ite_false, ite_true, integral_zero, smul_eq_mul, hp]
      have hb := freyaDevelopmentBatchMoment hm hS f hreg.differentiable Lpm
        (x z) (idealTrace q f z k).1 (idealTrace q f z k).2
        (hreg.centered (x z) (idealTrace q f z k).1)
      have hh := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hρone)
      rw [hx]
      change _ ≤ (1-q.ρ)*‖(idealTrace q f z k).2-gradient (objective f) (idealTrace q f z k).1‖^2+_
      convert hh using 1 <;> ring
    have hprod (F : CanonicalSeed q → ℝ) :
        (∫ z, F z ∂(canonicalLaw q : Measure (CanonicalSeed q))) =
          ∫ b, ∫ r, ∫ j, F (b,r,j) ∂ξ ∂(Measure.pi fun _ : Fin q.K => ν)
            ∂(Measure.pi fun _ : Fin q.K => μ) := by
      change (∫ z, F z ∂(Measure.pi fun _ : Fin q.K => μ).prod
        ((Measure.pi fun _ : Fin q.K => ν).prod ξ)) = _
      rw [integral_prod _ Integrable.of_finite]
      apply integral_congr_ae
      filter_upwards [] with b
      exact integral_prod _ Integrable.of_finite
    have hres : (∫ z, estimatorError q f z (k+1) ∂(canonicalLaw q : Measure (CanonicalSeed q))) =
        ∫ z, ∫ b, ∫ r, estimatorError q f (fresh z b r) (k+1) ∂ν ∂μ
          ∂(canonicalLaw q : Measure (CanonicalSeed q)) := by
      rw [hprod, hprod]
      exact freyaDevelopmentDoubleResample μ ν ξ κ (fun b r j => estimatorError q f (b,r,j) (k+1))
    rw [hres]
    have hh := integral_mono (μ := (canonicalLaw q : Measure (CanonicalSeed q)))
      Integrable.of_finite Integrable.of_finite hstep
    simpa (config := { iota := false }) only [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul] using hh


theorem energy_descent (q : SerialRaw) (hm : 0 < q.m) (hS : 0 < q.S)
    (hρ : 0 < q.ρ) (hρone : q.ρ ≤ 1) (hη : 0 < q.η)
    (f : Fin q.m → Space q.d → ℝ) (lower Lminus Lplus Lpm Δ : ℝ)
    (hL : 0 ≤ Lminus) (hD : 0 ≤ Lpm)
    (hreg : RegularObjective f q.x0 lower Lminus Lplus Lpm Δ)
    (htune : q.η ≤ 1 / (Lminus + Lpm * Real.sqrt ((1 - q.ρ) / (q.ρ * q.S))))
    (k : ℕ) (hk : k < q.K) :
    (∫ z, energy q f z (k + 1) ∂(canonicalLaw q : Measure (CanonicalSeed q))) ≤
      (∫ z, energy q f z k ∂(canonicalLaw q : Measure (CanonicalSeed q))) -
      q.η / 2 * (∫ z, ‖gradient (objective f) (idealTrace q f z k).1‖ ^ 2
        ∂(canonicalLaw q : Measure (CanonicalSeed q))) := by
  open scoped BigOperators in
    classical
    have : MeasurableSingletonClass (Option (Fin q.m)) := by
      constructor
      intro a
      cases a with
      | none =>
        refine ⟨{Sum.inl ()}, by rw [measurableSet_sum_iff]; constructor <;> simp, ?_⟩
        apply Set.ext
        intro b
        cases b with
        | none => exact iff_of_true rfl rfl
        | some b => exact iff_of_false Sum.inr_ne_inl (Option.some_ne_none b)
      | some i =>
        refine ⟨{Sum.inr i}, by rw [measurableSet_sum_iff]; constructor <;> simp, ?_⟩
        apply Set.ext
        intro b
        cases b with
        | none => exact iff_of_false Sum.inl_ne_inr (Ne.symm (Option.some_ne_none i))
        | some b =>
          exact ⟨fun h => congrArg some (Sum.inr.inj h),
            fun h => congrArg Sum.inr (Option.some.inj h)⟩
    let μ := (canonicalLaw q : Measure (CanonicalSeed q))
    let B := Lpm*Real.sqrt ((1-q.ρ)/(q.ρ*q.S))
    have hSr : (0 : ℝ) < q.S := by exact_mod_cast hS
    have hB : 0 ≤ B := mul_nonneg hD (Real.sqrt_nonneg _)
    have hA : 0 < Lminus+B := by
      have hnonneg : 0 ≤ Lminus+B := add_nonneg hL hB
      apply lt_of_le_of_ne hnonneg
      intro he
      have hz : Lminus+B = 0 := he.symm
      change q.η ≤ 1/(Lminus+B) at htune
      rw [hz, div_zero] at htune
      exact (not_le_of_gt hη) htune
    have hηA : q.η*(Lminus+B) ≤ 1 := (le_div_iff₀ hA).mp htune
    have htB : 0 ≤ q.η*B := mul_nonneg hη.le hB
    have htL : 0 ≤ q.η*Lminus := mul_nonneg hη.le hL
    have hηB : q.η*B ≤ 1 := by nlinarith only [hηA, htL]
    have hsq : (q.η*B)^2 ≤ q.η*B := by nlinarith only [htB, hηB]
    have hBsq : B^2 = Lpm^2*((1-q.ρ)/(q.ρ*q.S)) := by
      dsimp only [B]
      rw [mul_pow, Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hρone) (mul_pos hρ hSr).le)]
    let c := q.η/(2*q.ρ)
    have hc : 0 ≤ c := by dsimp only [c]; positivity
    have hcoef : c*((1-q.ρ)*Lpm^2/q.S) ≤ 1/(2*q.η)-Lminus/2 := by
      have hh : q.η*Lminus+q.η^2*B^2 ≤ 1 := by
        nlinarith only [hηA, hsq]
      apply (mul_le_mul_iff_left₀ (show 0 < 2*q.η by positivity)).mp
      have hleft : (2*q.η)*(c*((1-q.ρ)*Lpm^2/q.S)) = q.η^2*B^2 := by
        rw [hBsq]
        dsimp only [c]
        field_simp [hρ.ne', hSr.ne']
      have hright : (2*q.η)*(1/(2*q.η)-Lminus/2) = 1-q.η*Lminus := by
        field_simp [hη.ne']
      rw [mul_comm _ (2*q.η), mul_comm _ (2*q.η), hleft, hright]
      linarith only [hh]
    have hobjective : Differentiable ℝ (objective f) := by
      intro y
      exact (OracleTemplate.FiniteSum.objective_gradient
        (oracle := fun ix => gradient (f ix.1) ix.2)
        (fun i y => (hreg.differentiable i y).hasGradientAt) y).differentiableAt
    have hrec (z : CanonicalSeed q) (a : ℕ) : idealTrace q f z (a+1) =
        idealTrace._sunfold q f z (a+1) := by
      conv_lhs => delta idealTrace
      refine (Nat.brecOn.eq (motive := fun _ => Space q.d × Space q.d) (a+1)
        (idealTrace._f q f z)).trans ?_
      delta idealTrace._sunfold idealTrace._f idealTrace
      rfl
    have hx (z : CanonicalSeed q) :
        (idealTrace q f z (k+1)).1 = (idealTrace q f z k).1-q.η • (idealTrace q f z k).2 := by
      rw [hrec]
      delta idealTrace._sunfold
      dsimp only
      rw [dite_eq_left hk]
    let F (a : ℕ) := ∫ z, objective f (idealTrace q f z a).1 ∂μ
    let E (a : ℕ) := ∫ z, estimatorError q f z a ∂μ
    let G := ∫ z, ‖gradient (objective f) (idealTrace q f z k).1‖^2 ∂μ
    let D := ∫ z, ‖(idealTrace q f z (k+1)).1-(idealTrace q f z k).1‖^2 ∂μ
    have hDnonneg : 0 ≤ D := integral_nonneg fun z => sq_nonneg _
    have hpoint (z : CanonicalSeed q) :
        objective f (idealTrace q f z (k+1)).1 ≤ objective f (idealTrace q f z k).1-
          q.η/2*‖gradient (objective f) (idealTrace q f z k).1‖^2-
          (1/(2*q.η)-Lminus/2)*‖(idealTrace q f z (k+1)).1-(idealTrace q f z k).1‖^2+
          q.η/2*estimatorError q f z k := by
      have h := inexact_descent (objective f) hobjective Lminus hL hreg.smooth
        (idealTrace q f z k).1 (idealTrace q f z k).2 q.η hη
      rw [hx]
      have he : (idealTrace q f z k).1-q.η • (idealTrace q f z k).2-
          (idealTrace q f z k).1 = -(q.η • (idealTrace q f z k).2) := by
        apply sub_eq_iff_eq_add.mpr
        rw [sub_eq_add_neg]
        exact add_comm _ _
      rw [he, norm_neg]
      exact h
    have hf : F (k+1) ≤ F k-q.η/2*G-(1/(2*q.η)-Lminus/2)*D+q.η/2*E k := by
      have h := integral_mono (μ := μ) (Integrable.of_finite) (Integrable.of_finite) hpoint
      simpa only [integral_add (Integrable.of_finite) (Integrable.of_finite),
        integral_sub (Integrable.of_finite) (Integrable.of_finite), integral_const_mul] using h
    have he : E (k+1) ≤ (1-q.ρ)*E k+(1-q.ρ)*Lpm^2/q.S*D :=
      estimator_recursion q hm hS hρ hρone f lower Lminus Lplus Lpm Δ hreg k hk
    have henergy (a : ℕ) : (∫ z, energy q f z a ∂μ) = F a+c*E a := by
      change (∫ z, objective f (idealTrace q f z a).1+c*estimatorError q f z a ∂μ) = _
      rw [integral_add (Integrable.of_finite) (Integrable.of_finite), integral_const_mul]
    change (∫ z, energy q f z (k+1) ∂μ) ≤ (∫ z, energy q f z k ∂μ)-q.η/2*G
    rw [henergy, henergy]
    have he' := mul_le_mul_of_nonneg_left he hc
    have hd := mul_le_mul_of_nonneg_right hcoef hDnonneg
    have hid : q.η/2+c*(1-q.ρ)=c := by dsimp only [c]; field_simp; ring
    have hidE := congrArg (fun t : ℝ => t*E k) hid
    nlinarith only [hf, he', hd, hidE]


theorem energy_telescope (q : SerialRaw) (hm : 0 < q.m) (hS : 0 < q.S)
    (hρ : 0 < q.ρ) (hρone : q.ρ ≤ 1) (hη : 0 < q.η)
    (f : Fin q.m → Space q.d → ℝ) (lower Lminus Lplus Lpm Δ : ℝ)
    (hL : 0 ≤ Lminus) (hD : 0 ≤ Lpm)
    (hreg : RegularObjective f q.x0 lower Lminus Lplus Lpm Δ)
    (htune : q.η ≤ 1 / (Lminus + Lpm * Real.sqrt ((1 - q.ρ) / (q.ρ * q.S)))) :
    q.η / 2 * (∑ k : Fin q.K,
      ∫ z, ‖gradient (objective f) (idealTrace q f z k.val).1‖ ^ 2
        ∂(canonicalLaw q : Measure (CanonicalSeed q))) ≤ objective f q.x0 - lower := by
  open scoped BigOperators in
    classical
    have : MeasurableSingletonClass (Option (Fin q.m)) := by
      constructor
      intro a
      cases a with
      | none =>
        refine ⟨{Sum.inl ()}, by rw [measurableSet_sum_iff]; constructor <;> simp, ?_⟩
        apply Set.ext
        intro b
        cases b with
        | none => exact iff_of_true rfl rfl
        | some b => exact iff_of_false Sum.inr_ne_inl (Option.some_ne_none b)
      | some i =>
        refine ⟨{Sum.inr i}, by rw [measurableSet_sum_iff]; constructor <;> simp, ?_⟩
        apply Set.ext
        intro b
        cases b with
        | none => exact iff_of_false Sum.inl_ne_inr (Ne.symm (Option.some_ne_none i))
        | some b =>
          exact ⟨fun h => congrArg some (Sum.inr.inj h),
            fun h => congrArg Sum.inr (Option.some.inj h)⟩
    let μ := (canonicalLaw q : Measure (CanonicalSeed q))
    let E (k : ℕ) := ∫ z, energy q f z k ∂μ
    let G (k : ℕ) := ∫ z, ‖gradient (objective f) (idealTrace q f z k).1‖^2 ∂μ
    have hstep (k : ℕ) (hk : k < q.K) : E (k+1) ≤ E k-q.η/2*G k :=
      energy_descent q hm hS hρ hρone hη f lower Lminus Lplus Lpm Δ hL hD hreg htune k hk
    have hsum : ∀ j, j ≤ q.K → q.η/2*(∑ k ∈ Finset.range j, G k) ≤ E 0-E j := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro hj
        have hi := ih (by omega)
        have hd := hstep j (by omega)
        rw [Finset.sum_range_succ, mul_add]
        linarith only [hi, hd]
    have hE0 : E 0 = objective f q.x0 := by
      have hpoint : ∀ z : CanonicalSeed q, energy q f z 0 = objective f q.x0 := by
        intro z
        change objective f q.x0 + q.η/(2*q.ρ)*
          ‖gradient (objective f) q.x0-gradient (objective f) q.x0‖^2 = _
        simp
      change (∫ z, energy q f z 0 ∂μ) = _
      simp only [hpoint, integral_const, MeasureTheory.probReal_univ, one_smul]
    have hlower : lower ≤ E q.K := by
      have hi : Integrable (fun z => energy q f z q.K) μ := Integrable.of_finite
      have hp : (fun _ : CanonicalSeed q => lower) ≤ fun z => energy q f z q.K := by
        intro z
        change lower ≤ objective f (idealTrace q f z q.K).1+
          q.η/(2*q.ρ)*estimatorError q f z q.K
        have hn : 0 ≤ estimatorError q f z q.K := sq_nonneg _
        exact (hreg.lower_bound _).trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hn))
      have h := integral_mono (integrable_const lower) hi hp
      simpa only [integral_const, MeasureTheory.probReal_univ, one_smul] using h
    have h := hsum q.K le_rfl
    rw [hE0] at h
    change q.η/2*(∑ k : Fin q.K, G k.val) ≤ _
    rw [Fin.sum_univ_eq_sum_range]
    exact h.trans (sub_le_sub_left hlower _)


theorem uniform_selector (q : SerialRaw) (hK : 0 < q.K)
    (f : Fin q.m → Space q.d → ℝ) :
    Integrable (fun z => ‖gradient (objective f) (idealOutput q f z)‖ ^ 2)
        (canonicalLaw q : Measure (CanonicalSeed q)) ∧
      (∫ z, ‖gradient (objective f) (idealOutput q f z)‖ ^ 2
        ∂(canonicalLaw q : Measure (CanonicalSeed q))) =
        (q.K : ℝ)⁻¹ * (∑ k : Fin q.K,
          ∫ z, ‖gradient (objective f) (idealTrace q f z k.val).1‖ ^ 2
            ∂(canonicalLaw q : Measure (CanonicalSeed q))) := by
  open scoped BigOperators in
    classical
    have : MeasurableSingletonClass (Option (Fin q.m)) := by
      constructor
      intro a
      cases a with
      | none =>
        refine ⟨{Sum.inl ()}, by rw [measurableSet_sum_iff]; constructor <;> simp, ?_⟩
        apply Set.ext
        intro b
        cases b with
        | none => exact iff_of_true rfl rfl
        | some b => exact iff_of_false Sum.inr_ne_inl (Option.some_ne_none b)
      | some i =>
        refine ⟨{Sum.inr i}, by rw [measurableSet_sum_iff]; constructor <;> simp, ?_⟩
        apply Set.ext
        intro b
        cases b with
        | none => exact iff_of_false Sum.inl_ne_inr (Ne.symm (Option.some_ne_none i))
        | some b =>
          exact ⟨fun h => congrArg some (Sum.inr.inj h),
            fun h => congrArg Sum.inr (Option.some.inj h)⟩
    have : NeZero (max 1 q.K) := ⟨by omega⟩
    let j0 : Fin (max 1 q.K) := ⟨0, by omega⟩
    let μb := Measure.pi (fun _ : Fin q.K =>
      bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one q.ρ))
    let μr := Measure.pi (fun _ : Fin q.K =>
      Measure.pi (fun _ : Fin q.S => (componentLaw q.m : Measure (Option (Fin q.m)))))
    let μj := (PMF.uniformOfFintype (Fin (max 1 q.K))).toMeasure
    have hrec (z : CanonicalSeed q) (k : ℕ) : idealTrace q f z (k+1) =
        idealTrace._sunfold q f z (k+1) := by
      conv_lhs => delta idealTrace
      refine (Nat.brecOn.eq (motive := fun _ => Space q.d × Space q.d) (k+1)
        (idealTrace._f q f z)).trans ?_
      delta idealTrace._sunfold idealTrace._f idealTrace
      rfl
    have htrace (b : Fin q.K → Bool) (r : Fin q.K → Fin q.S → Option (Fin q.m))
        (j : Fin (max 1 q.K)) (k : ℕ) :
        idealTrace q f (b,r,j) k = idealTrace q f (b,r,j0) k := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [hrec, hrec]
        delta idealTrace._sunfold
        dsimp only
        rw [ih]
    let F (b : Fin q.K → Bool) (r : Fin q.K → Fin q.S → Option (Fin q.m)) (k : ℕ) :=
      ‖gradient (objective f) (idealTrace q f (b,r,j0) k).1‖^2
    have hfout (z : CanonicalSeed q) :
        ‖gradient (objective f) (idealOutput q f z)‖^2 = F z.1 z.2.1 z.2.2.val := by
      change ‖gradient (objective f) (idealTrace q f z z.2.2.val).1‖^2 = _
      rw [htrace z.1 z.2.1 z.2.2]
    have hfk (z : CanonicalSeed q) (k : ℕ) :
        ‖gradient (objective f) (idealTrace q f z k).1‖^2 = F z.1 z.2.1 k := by
      rw [htrace z.1 z.2.1 z.2.2]
    refine ⟨Integrable.of_finite, ?_⟩
    simp_rw [hfout, hfk]
    have hsum (b : Fin q.K → Bool) (r : Fin q.K → Fin q.S → Option (Fin q.m)) :
        (∫ j, F b r j.val ∂μj) = (q.K : ℝ)⁻¹*(∑ k : Fin q.K, F b r k.val) := by
      rw [integral_fintype (show Integrable (fun j : Fin (max 1 q.K) => F b r j.val) μj from Integrable.of_finite)]
      have hmass (j : Fin (max 1 q.K)) : μj.real {j} = ((max 1 q.K : ℕ) : ℝ)⁻¹ := by
        simp [μj, Measure.real, PMF.uniformOfFintype_apply]
      simp_rw [hmass, smul_eq_mul]
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range, max_eq_right hK]
      rw [Fin.sum_univ_eq_sum_range]
    have hprod (g : CanonicalSeed q → ℝ) :
        (∫ z, g z ∂(canonicalLaw q : Measure (CanonicalSeed q))) =
          ∫ b, ∫ r, ∫ j, g (b,r,j) ∂μj ∂μr ∂μb := by
      change (∫ z, g z ∂μb.prod (μr.prod μj)) = _
      rw [integral_prod _ (show Integrable g (μb.prod (μr.prod μj)) from Integrable.of_finite)]
      apply integral_congr_ae
      filter_upwards [] with b
      exact integral_prod _ (show Integrable (fun z => g (b,z)) (μr.prod μj) from Integrable.of_finite)
    rw [hprod]
    simp_rw [hsum, integral_const_mul,
      integral_finsetSum Finset.univ (fun k _ => Integrable.of_finite)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hprod]
    simp


theorem page_rate (q : SerialRaw) (hm : 0 < q.m) (hS : 0 < q.S) (hK : 0 < q.K)
    (hρ : 0 < q.ρ) (hρone : q.ρ ≤ 1) (hη : 0 < q.η)
    (f : Fin q.m → Space q.d → ℝ) (lower Lminus Lplus Lpm Δ : ℝ)
    (hL : 0 ≤ Lminus) (hD : 0 ≤ Lpm)
    (hreg : RegularObjective f q.x0 lower Lminus Lplus Lpm Δ)
    (htune : q.η ≤ 1 / (Lminus + Lpm * Real.sqrt ((1 - q.ρ) / (q.ρ * q.S)))) :
    Integrable (fun z => ‖gradient (objective f) (idealOutput q f z)‖ ^ 2)
        (canonicalLaw q : Measure (CanonicalSeed q)) ∧
      (∫ z, ‖gradient (objective f) (idealOutput q f z)‖ ^ 2
        ∂(canonicalLaw q : Measure (CanonicalSeed q))) ≤
        2 * (objective f q.x0 - lower) / (q.η * q.K) := by
  open scoped BigOperators in
    obtain ⟨hint, heq⟩ := uniform_selector q hK f
    refine ⟨hint, ?_⟩
    rw [heq]
    have ht := energy_telescope q hm hS hρ hρone hη f lower Lminus Lplus Lpm Δ hL hD hreg htune
    have hKr : (0 : ℝ) < q.K := by exact_mod_cast hK
    apply (le_div_iff₀ (mul_pos hη hKr)).mpr
    have hid : (q.K : ℝ)⁻¹ *
        (∑ k : Fin q.K, ∫ z, ‖gradient (objective f) (idealTrace q f z k.val).1‖^2
          ∂(canonicalLaw q : Measure (CanonicalSeed q))) * (q.η*q.K) =
        2*(q.η/2*(∑ k : Fin q.K, ∫ z, ‖gradient (objective f) (idealTrace q f z k.val).1‖^2
          ∂(canonicalLaw q : Measure (CanonicalSeed q)))) := by
      field_simp [hKr.ne']
    rw [hid]
    exact mul_le_mul_of_nonneg_left ht (by norm_num)


theorem serial_tuning_legal (p : Serial) (hm : 0 < p.m) (hS : 0 < p.S)
    (hρ : 0 < p.ρ) (hρone : p.ρ ≤ 1) (hL : 0 < p.Lminus)
    (hD : 0 ≤ p.Lpm) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    0 < familyStep p.toBase p.S p.ρ ∧ 1 ≤ familyHorizon p.toBase p.S p.ρ ∧
      2 * p.Δ / (familyStep p.toBase p.S p.ρ * familyHorizon p.toBase p.S p.ρ) ≤ p.ε := by
  have _ := hm
  have _ := hS
  have _ := hρ
  have _ := hρone
  have _ := hΔ
  let A := familyCoefficient p.toBase p.S p.ρ
  have hA : 0 < A := by
    change 0 < p.Lminus + p.Lpm * Real.sqrt ((1 - p.ρ) / (p.ρ * p.S))
    exact add_pos_of_pos_of_nonneg hL (mul_nonneg hD (Real.sqrt_nonneg _))
  have hη : 0 < familyStep p.toBase p.S p.ρ := by change 0 < 1 / A; positivity
  have hK : 1 ≤ familyHorizon p.toBase p.S p.ρ := le_max_left _ _
  have hKreal : (0 : ℝ) < familyHorizon p.toBase p.S p.ρ := by exact_mod_cast hK
  refine ⟨hη, hK, ?_⟩
  have hceil : 2 * p.Δ * A / p.ε ≤ (familyHorizon p.toBase p.S p.ρ : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈2 * p.Δ * A / p.ε⌉₊))
  have hnum : 2 * p.Δ * A ≤ (familyHorizon p.toBase p.S p.ρ : ℝ) * p.ε :=
    (div_le_iff₀ hε).mp hceil
  apply (div_le_iff₀ (mul_pos hη hKreal)).mpr
  change 2 * p.Δ ≤ p.ε * ((1 / A) * (familyHorizon p.toBase p.S p.ρ : ℝ))
  calc
    2 * p.Δ = (2 * p.Δ * A) * (1 / A) := by field_simp [hA.ne']
    _ ≤ ((familyHorizon p.toBase p.S p.ρ : ℝ) * p.ε) * (1 / A) :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = p.ε * ((1 / A) * (familyHorizon p.toBase p.S p.ρ : ℝ)) := by ring


theorem serial_execution_accuracy (p : LongTails.Setups.FreyaPageUniform.Params)
    (hp : LongTails.Setups.FreyaPageUniform.spec.valid p)
    (f : Fin p.m → Space p.d → ℝ)
    (O : Oracle (Option (Fin p.m × Space p.d)) (Space p.d) 1)
    (hO : LongTails.Setups.FreyaPageUniform.spec.admissible p f O) :
    LongTails.Setups.FreyaPageUniform.spec.successful p f
      (fun z : (serial (LongTails.Setups.FreyaPageUniform.publicInput p)).Seed × ((k : ℕ) → O.Seed k) => execute O (serial (LongTails.Setups.FreyaPageUniform.publicInput p))
        (fun _ => p.m + (p.m + 2 * p.S) *
          (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt ((1 - p.ρ) / (p.ρ * p.S))) / p.ε⌉₊ + 1))
        z.1 z.2)
      ⟨((serial (LongTails.Setups.FreyaPageUniform.publicInput p)).law : Measure (serial (LongTails.Setups.FreyaPageUniform.publicInput p)).Seed).prod
        (O.law : Measure ((k : ℕ) → O.Seed k)), inferInstance⟩ := by
  open scoped BigOperators in
    classical
    dsimp only [LongTails.Setups.FreyaPageUniform.spec, LongTails.Setups.FreyaPageUniform.publicInput] at hp hO ⊢
    obtain ⟨hm,hL,hLplus,hD,hΔ,hε,hS,hρ,hρone⟩ := hp
    obtain ⟨hf,hlower,hgap,hsmooth,hmean,hcentered,hmeas,hservice⟩ := hO
    let B := p.m+(p.m+2*p.S)*(⌈2*p.Δ*(p.Lminus+p.Lpm*Real.sqrt ((1-p.ρ)/(p.ρ*p.S)))/p.ε⌉₊+1)
    let success (A : Algorithm (Option (Fin p.m × Space p.d)) (Space p.d) (Space p.d) 1) : Prop :=
      Integrable (fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
        ‖gradient (objective f) (execute O A (fun _ => B) z.1 z.2)‖^2)
        ((A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k))) ∧
      (∫ z : A.Seed × ((k : ℕ) → O.Seed k),
        ‖gradient (objective f) (execute O A (fun _ => B) z.1 z.2)‖^2
        ∂((A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k)))) ≤ p.ε
    change success (serial (LongTails.Setups.FreyaPageUniform.publicInput p))
    have hfobj : Differentiable ℝ (objective f) := by
      intro x
      delta objective
      simpa only [Finset.sum_apply] using ((HasFDerivAt.sum (u := Finset.univ)
        (fun i _ => (hf i x).hasGradientAt.hasFDerivAt)).const_mul (p.m : ℝ)⁻¹).differentiableAt
    by_cases hzero : p.Δ = 0 ∨ p.Lminus = 0
    · have hz : gradient (objective f) p.x0 = 0 := by
        rcases hzero with h | h
        · exact zero_gap_stationary (objective f) hfobj p.lower hlower p.x0 (by simpa only [h] using hgap)
        · exact zero_smoothness_stationary (objective f) hfobj p.lower hlower
            (by
              intro x y
              have hh := hsmooth x y
              rw [h] at hh
              exact hh) p.x0
      have halg : serial (LongTails.Setups.FreyaPageUniform.publicInput p) =
          (constantPoint none p.x0 : Algorithm (Option (Fin p.m × Space p.d)) (Space p.d) (Space p.d) 1) := by
        delta serial
        exact ite_eq_left hzero
      rw [halg]
      dsimp only [success]
      have hout (z : (constantPoint (none : Option (Fin p.m × Space p.d)) p.x0).Seed × ((k : ℕ) → O.Seed k)) :
          execute O (constantPoint none p.x0) (fun _ => B) z.1 z.2 = p.x0 := by
        erw [execute_advance_history]
        rfl
      simp only [hout,hz,norm_zero,zero_pow (by decide : 2 ≠ 0)]
      exact ⟨integrable_const (0 : ℝ),by simpa only [integral_zero] using hε.le⟩
    · have hLpos : 0 < p.Lminus := lt_of_le_of_ne hL (fun h => hzero (Or.inr h.symm))
      let q : SerialRaw :=
        {d := p.d, m := p.m, x0 := p.x0,
          η := familyStep (LongTails.Setups.FreyaPageUniform.publicInput p).toBase p.S p.ρ,
          S := p.S, ρ := p.ρ,
          K := familyHorizon (LongTails.Setups.FreyaPageUniform.publicInput p).toBase p.S p.ρ}
      have htune := serial_tuning_legal (LongTails.Setups.FreyaPageUniform.publicInput p)
        hm hS hρ hρone hLpos hD hΔ hε
      have hη : 0 < q.η := htune.1
      have hK : 0 < q.K := htune.2.1
      have hbudget : q.m+q.K*max q.m (2*q.S) ≤ B := by
        let C : ℕ := ⌈2*p.Δ*(p.Lminus+p.Lpm*Real.sqrt ((1-p.ρ)/(p.ρ*p.S)))/p.ε⌉₊
        change p.m+max 1 C*max p.m (2*p.S) ≤ p.m+(p.m+2*p.S)*(C+1)
        have hK : max 1 C ≤ C+1 := by omega
        have hmax : max p.m (2*p.S) ≤ p.m+2*p.S := by omega
        have h := Nat.mul_le_mul hK hmax
        rw [Nat.mul_comm (C+1)] at h
        exact Nat.add_le_add_left h p.m
      have halg : serial (LongTails.Setups.FreyaPageUniform.publicInput p) = algorithm q := by
        delta serial
        exact ite_eq_right hzero
      rw [halg]
      let μ := (seedLaw q.ρ q.K : Measure (Seed q.K))
      let ν := (O.law : Measure ((k : ℕ) → O.Seed k))
      have hreg : RegularObjective f q.x0 p.lower p.Lminus p.Lplus p.Lpm p.Δ :=
        ⟨hf,hlower,hsmooth,hmean,hcentered,hgap⟩
      have hrate := page_rate q hm hS hK hρ hρone hη f p.lower p.Lminus p.Lplus p.Lpm p.Δ
        hL hD hreg (by exact le_rfl)
      have hfst : HasLaw (Prod.fst : Seed q.K × ((k : ℕ) → O.Seed k) → Seed q.K) μ (μ.prod ν) :=
        ⟨measurable_fst.aemeasurable,measurePreserving_fst.map_eq⟩
      have hlaw := (serial_law q).comp hfst
      have hserv : ∀ᵐ z : Seed q.K × ((k : ℕ) → O.Seed k) ∂μ.prod ν,
          ∀ history, O.answer history (0,none) (z.2 history.length) = 0 ∧
            ∀ i x, O.answer history (0,some (i,x)) (z.2 history.length) = gradient (f i) x :=
        measurePreserving_snd.quasiMeasurePreserving.ae hservice
      have heq : (fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
          ‖gradient (objective f) (execute O (algorithm q) (fun _ => B) z.1 z.2)‖^2) =ᵐ[μ.prod ν]
          (fun z => ‖gradient (objective f) (idealOutput q f (canonicalize q z.1))‖^2) := by
        filter_upwards [hserv] with z hz
        rw [serial_execution q hm hS hK f hf O z.1 z.2 hz B hbudget]
      change Integrable _ (μ.prod ν) ∧ _ ≤ p.ε
      refine ⟨(hlaw.integrable_comp hrate.1).congr heq.symm,?_⟩
      calc
        _ = (∫ z, ‖gradient (objective f) (idealOutput q f (canonicalize q z.1))‖^2 ∂μ.prod ν) :=
          integral_congr_ae heq
        _ = (∫ z, ‖gradient (objective f) (idealOutput q f z)‖^2 ∂(canonicalLaw q : Measure (CanonicalSeed q))) :=
          hlaw.integral_comp hrate.1.aestronglyMeasurable
        _ ≤ 2*(objective f q.x0-p.lower)/(q.η*q.K) := hrate.2
        _ ≤ 2*p.Δ/(q.η*q.K) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hgap (by norm_num)) (mul_nonneg hη.le (Nat.cast_nonneg _))
        _ ≤ p.ε := htune.2.2


theorem serial_cost (p : LongTails.Setups.FreyaPageUniform.Params)
    (hp : LongTails.Setups.FreyaPageUniform.spec.valid p) :
    p.Δ = 0 ∨ p.Lminus = 0 ∨
      p.m + familyHorizon (LongTails.Setups.FreyaPageUniform.publicInput p).toBase p.S p.ρ * max p.m (2 * p.S) ≤
        p.m + (p.m + 2 * p.S) *
          (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt ((1 - p.ρ) / (p.ρ * p.S))) / p.ε⌉₊ + 1) := by
  have _ := hp
  right
  right
  let C : ℕ := ⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt ((1-p.ρ)/(p.ρ*p.S))) / p.ε⌉₊
  change p.m + max 1 C * max p.m (2*p.S) ≤ p.m + (p.m + 2*p.S)*(C+1)
  have hK : max 1 C ≤ C+1 := by omega
  have hmax : max p.m (2*p.S) ≤ p.m + 2*p.S := by omega
  have h := Nat.mul_le_mul hK hmax
  rw [Nat.mul_comm (C+1)] at h
  exact Nat.add_le_add_left h p.m


end LongTails.Proofs.FreyaSerialAnalysis

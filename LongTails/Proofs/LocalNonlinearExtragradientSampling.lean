import LongTails.Algorithms.LocalNonlinearExtragradient
import LongTails.Proofs.AdaptiveIID
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic

open MeasureTheory
open ProbabilityTheory

namespace LongTails.Proofs.LocalNonlinearExtragradientSampling

open LongTails.Algorithms.LocalNonlinearExtragradient

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma measurable_run (η : ℝ) (g : E → Ω → E) (x : E)
    (hg : Measurable (Function.uncurry g)) (k : ℕ) :
    Measurable (fun ξ : ℕ → Ω => run η g x ξ k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      have hfirst := hg.comp (ih.prodMk (measurable_pi_apply (2 * k)))
      have hhalf := ih.sub (hfirst.const_smul η)
      have hsecond := hg.comp (hhalf.prodMk (measurable_pi_apply (2 * k + 1)))
      exact ih.sub (hsecond.const_smul η)

lemma measurable_warmRun (η : ℝ) (g : E → Ω → E) (x : E)
    (hg : Measurable (Function.uncurry g)) (k : ℕ) :
    Measurable (fun ξ : ℕ → Ω => warmRun η g x ξ k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      have hquery := hg.comp (ih.prodMk (measurable_pi_apply k))
      exact ih.sub (hquery.const_smul η)

lemma measurable_run_joint (η : ℝ) (g : E → Ω → E)
    (hg : Measurable (Function.uncurry g)) (k : ℕ) :
    Measurable (fun w : E × (ℕ → Ω) => run η g w.1 w.2 k) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
      have hfirst := hg.comp (ih.prodMk ((measurable_pi_apply (2 * k)).comp measurable_snd))
      have hhalf := ih.sub (hfirst.const_smul η)
      have hsecond := hg.comp
        (hhalf.prodMk ((measurable_pi_apply (2 * k + 1)).comp measurable_snd))
      exact ih.sub (hsecond.const_smul η)

lemma measurable_warmRun_joint (η : ℝ) (g : E → Ω → E)
    (hg : Measurable (Function.uncurry g)) (k : ℕ) :
    Measurable (fun w : E × (ℕ → Ω) => warmRun η g w.1 w.2 k) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
      have hquery := hg.comp (ih.prodMk ((measurable_pi_apply k).comp measurable_snd))
      exact ih.sub (hquery.const_smul η)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma run_prefix (η : ℝ) (g : E → Ω → E) (x : E) (k : ℕ)
    {ξ ζ : ℕ → Ω} (h : ∀ j < 2 * k, ξ j = ζ j) : run η g x ξ k = run η g x ζ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [run]
      rw [ih (fun j hj => h j (by omega)), h (2 * k) (by omega), h (2 * k + 1) (by omega)]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma warmRun_prefix (η : ℝ) (g : E → Ω → E) (x : E) (k : ℕ)
    {ξ ζ : ℕ → Ω} (h : ∀ j < k, ξ j = ζ j) : warmRun η g x ξ k = warmRun η g x ζ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [warmRun]
      rw [ih (fun j hj => h j (by omega)), h k (by omega)]

lemma prefix_independent {Ξ Z : Type*} [MeasurableSpace Ξ] [MeasurableSpace Z]
    (ξ : ℕ → Ξ → Ω) (P : Measure Ξ) (default : Ω) (N j : ℕ) (hj : N ≤ j)
    (hind : iIndepFun ξ P) (hξ : ∀ k, Measurable (ξ k))
    (H : (ℕ → Ω) → Z) (hH : Measurable H)
    (hprefix : ∀ u v, (∀ k < N, u k = v k) → H u = H v) :
    IndepFun (fun ω => H (fun k => ξ k ω)) (ξ j) P := by
  classical
  let S := Finset.range N
  let extend : (S → Ω) → ℕ → Ω := fun u k => if hk : k ∈ S then u ⟨k, hk⟩ else default
  have hext : Measurable extend := by
    apply Measurable.of_eval
    intro k
    by_cases hk : k ∈ S
    · simpa only [extend, dite_eq_left hk] using (measurable_pi_apply (⟨k, hk⟩ : S))
    · simpa only [extend, dite_eq_right hk] using (measurable_const : Measurable (fun _ : S → Ω => default))
  have hdis : Disjoint S ({j} : Finset ℕ) := by
    apply Finset.disjoint_left.mpr
    intro k hk hkj
    have hkj' : k = j := Finset.mem_singleton.mp hkj
    have hk' : k < N := Finset.mem_range.mp hk
    omega
  have hh := (hind.indepFun_finset S {j} hdis hξ).comp (hH.comp hext)
    (measurable_pi_apply (⟨j, Finset.mem_singleton_self j⟩ : ({j} : Finset ℕ)))
  change IndepFun (fun ω => H (extend (fun i : S => ξ i ω))) (ξ j) P at hh
  have he : (fun ω => H (extend (fun i : S => ξ i ω))) =
      (fun ω => H (fun k => ξ k ω)) := by
    funext ω
    apply hprefix
    intro k hk
    have hks : k ∈ S := Finset.mem_range.mpr hk
    simp only [extend, dite_eq_left hks]
  rw [he] at hh
  exact hh

lemma run_independent_fresh {Ξ : Type*} [MeasurableSpace Ξ]
    (η : ℝ) (g : E → Ω → E) (x : E) (default : Ω)
    (hg : Measurable (Function.uncurry g)) (ξ : ℕ → Ξ → Ω) (P : Measure Ξ)
    (hind : iIndepFun ξ P) (hξ : ∀ k, Measurable (ξ k)) (k j : ℕ) (hj : 2 * k ≤ j) :
    IndepFun (fun ω => run η g x (fun i => ξ i ω) k) (ξ j) P :=
  prefix_independent ξ P default (2 * k) j hj hind hξ
    (fun u => run η g x u k) (measurable_run η g x hg k)
    (fun _ _ h => run_prefix η g x k h)

lemma half_independent_fresh {Ξ : Type*} [MeasurableSpace Ξ]
    (η : ℝ) (g : E → Ω → E) (x : E) (default : Ω)
    (hg : Measurable (Function.uncurry g)) (ξ : ℕ → Ξ → Ω) (P : Measure Ξ)
    (hind : iIndepFun ξ P) (hξ : ∀ k, Measurable (ξ k)) (k j : ℕ) (hj : 2 * k + 1 ≤ j) :
    IndepFun (fun ω => run η g x (fun i => ξ i ω) k -
      η • g (run η g x (fun i => ξ i ω) k) (ξ (2 * k) ω)) (ξ j) P := by
  have hm := measurable_run η g x hg k
  have hh := hm.sub ((hg.comp (hm.prodMk (measurable_pi_apply (2 * k)))).const_smul η)
  apply prefix_independent ξ P default (2 * k + 1) j hj hind hξ _ hh
  intro u v h
  have hr := run_prefix η g x k (fun l hl => h l (by omega))
  dsimp
  rw [hr, h (2 * k) (by omega)]

lemma warmRun_independent_fresh {Ξ : Type*} [MeasurableSpace Ξ]
    (η : ℝ) (g : E → Ω → E) (x : E) (default : Ω)
    (hg : Measurable (Function.uncurry g)) (ξ : ℕ → Ξ → Ω) (P : Measure Ξ)
    (hind : iIndepFun ξ P) (hξ : ∀ k, Measurable (ξ k)) (k j : ℕ) (hj : k ≤ j) :
    IndepFun (fun ω => warmRun η g x (fun i => ξ i ω) k) (ξ j) P :=
  prefix_independent ξ P default k j hj hind hξ
    (fun u => warmRun η g x u k) (measurable_warmRun η g x hg k)
    (fun _ _ h => warmRun_prefix η g x k h)

lemma fresh_pair_law {Ξ Z : Type*} [MeasurableSpace Ξ] [MeasurableSpace Z]
    (P : Measure Ξ) [IsProbabilityMeasure P] (p : Measure Ω)
    (X : Ξ → Z) (ξ : Ξ → Ω) (hX : Measurable X) (hξ : Measurable ξ)
    (hind : IndepFun X ξ P) (hmarg : P.map ξ = p) :
    MeasurePreserving (fun ω => (X ω, ξ ω)) P ((P.map X).prod p) := by
  refine ⟨hX.prodMk hξ, ?_⟩
  rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hξ.aemeasurable, hmarg]

lemma interleaved_index_injective {n b : ℕ} (hn : 0 < n) (N : ℕ) :
    Function.Injective (fun ij : Fin n × Fin b => N + (n * ij.2.val + ij.1.val)) := by
  intro a d h
  have he : n * a.2.val + a.1.val = n * d.2.val + d.1.val := Nat.add_left_cancel h
  have hi := congrArg (fun k => k % n) he
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
    Nat.mod_eq_of_lt a.1.isLt, Nat.mod_eq_of_lt d.1.isLt] at hi
  have hfirst : a.1 = d.1 := Fin.ext hi
  have hj : n * a.2.val = n * d.2.val := by rw [hfirst] at he; omega
  have hsecond : a.2 = d.2 := Fin.ext ((Nat.mul_left_cancel_iff hn).mp hj)
  exact Prod.ext hfirst hsecond

lemma interleaved_block_law {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ξ : ℕ → Ξ → Ω)
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ Q P)
    {n b : ℕ} (hn : 0 < n) (N : ℕ) :
    MeasurePreserving (fun ω (i : Fin n) (j : Fin b) => ξ (N + (n * j.val + i.val)) ω)
      P (Measure.infinitePi fun _ : Fin n => Measure.infinitePi fun _ : Fin b => Q) := by
  let index : Fin n × Fin b → ℕ := fun ij => N + (n * ij.2.val + ij.1.val)
  let Z : Ξ → (Fin n × Fin b → Ω) := fun ω ij => ξ (index ij) ω
  have hZ : Measurable Z := Measurable.of_eval fun ij => hIID.measurable (index ij)
  have hind := hIID.independent.precomp (interleaved_index_injective (b := b) hn N)
  have hmap : P.map Z = Measure.infinitePi (fun _ : Fin n × Fin b => Q) := by
    simpa only [hIID.marginal] using
      hind.map_fun_eq_infinitePi_map (fun ij => hIID.measurable (index ij))
  refine ⟨Measurable.of_eval (fun i => Measurable.of_eval (fun j => hIID.measurable _)), ?_⟩
  change P.map ((MeasurableEquiv.curry (Fin n) (Fin b) Ω) ∘ Z) = _
  rw [← Measure.map_map (MeasurableEquiv.curry (Fin n) (Fin b) Ω).measurable hZ, hmap]
  exact Measure.infinitePi_map_curry (fun (_ : Fin n) (_ : Fin b) => Q)

lemma interleaved_blocks_independent {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) (Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ξ : ℕ → Ξ → Ω)
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ Q P)
    {n b : ℕ} (hn : 0 < n) (N : ℕ) :
    iIndepFun (fun (i : Fin n) ω (j : Fin b) => ξ (N + (n * j.val + i.val)) ω) P := by
  have hblock := interleaved_block_law P Q ξ hIID (b := b) hn N
  have hm (i : Fin n) := (measurePreserving_eval_infinitePi
    (fun _ : Fin n => Measure.infinitePi fun _ : Fin b => Q) i).comp hblock
  exact (iIndepFun_iff_hasLaw_Pi_infinitePi
    (fun i => ⟨(hm i).measurable.aemeasurable, (hm i).map_eq⟩)
    hblock.measurable.aemeasurable).mpr ⟨hblock.measurable.aemeasurable, hblock.map_eq⟩

lemma prefix_interleaved_block_law {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) (Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ξ : ℕ → Ξ → Ω)
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ Q P)
    {n b : ℕ} (hn : 0 < n) (N : ℕ) :
    MeasurePreserving
      (fun ω => ((fun i : Fin N => ξ i.val ω),
        (fun (i : Fin n) (j : Fin b) => ξ (N + (n * j.val + i.val)) ω)))
      P ((Measure.pi fun _ : Fin N => Q).prod
        (Measure.infinitePi fun _ : Fin n => Measure.infinitePi fun _ : Fin b => Q)) := by
  have hblock := interleaved_block_law (Measure.infinitePi fun _ : ℕ => Q) Q
    (fun k ω => ω k) (OracleTemplate.StochasticGeneralized.infinitePi_iid Q)
    (b := b) hn 0
  have hp := (MeasurePreserving.id (Measure.pi fun _ : Fin N => Q)).prod hblock
  simpa only [Function.comp_def, Prod.map_apply, id_eq, Nat.zero_add] using
    hp.comp (hIID.prefix_tail_law N)

lemma interleaved_worker_iid {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) (Q : Measure Ω) (ξ : ℕ → Ξ → Ω)
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ Q P)
    {n : ℕ} (hn : 0 < n) (N : ℕ) (i : Fin n) :
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k => ξ (N + (n * k + i.val))) Q P where
  measurable k := hIID.measurable _
  independent := hIID.independent.precomp (by
    intro a b h
    exact (Nat.mul_left_cancel_iff hn).mp (Nat.add_right_cancel (Nat.add_left_cancel h)))
  marginal k := hIID.marginal _

lemma interleaved_runs_independent {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) (Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ξ : ℕ → Ξ → Ω)
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ Q P)
    {n : ℕ} (hn : 0 < n) (N T : ℕ) (η : ℝ) (g : Fin n → E → Ω → E) (x : E)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) :
    iIndepFun (fun (i : Fin n) ω =>
      run η (g i) x (fun k => ξ (N + (n * k + i.val)) ω) T) P := by
  classical
  let default : Ω := Classical.choice (nonempty_of_isProbabilityMeasure Q)
  let extend : (Fin (2 * T) → Ω) → ℕ → Ω :=
    fun u k => if hk : k < 2 * T then u ⟨k, hk⟩ else default
  have hExt : Measurable extend := by
    apply Measurable.of_eval
    intro k
    by_cases hk : k < 2 * T
    · simpa only [extend, dite_eq_left hk] using
        (measurable_pi_apply (⟨k, hk⟩ : Fin (2 * T)))
    · simpa only [extend, dite_eq_right hk] using
        (measurable_const : Measurable (fun _ : Fin (2 * T) → Ω => default))
  have hh := (interleaved_blocks_independent P Q ξ hIID (b := 2 * T) hn N).comp
    (fun i u => run η (g i) x (extend u) T)
    (fun i => (measurable_run η (g i) x (hg i) T).comp hExt)
  change iIndepFun (fun (i : Fin n) ω => run η (g i) x
    (extend (fun j : Fin (2 * T) => ξ (N + (n * j.val + i.val)) ω)) T) P at hh
  have he : (fun (i : Fin n) ω => run η (g i) x
      (extend (fun j : Fin (2 * T) => ξ (N + (n * j.val + i.val)) ω)) T) =
      (fun (i : Fin n) ω => run η (g i) x
        (fun k => ξ (N + (n * k + i.val)) ω) T) := by
    funext i ω
    apply run_prefix
    intro k hk
    simp only [extend, dite_eq_left hk]
  rw [he] at hh
  exact hh

lemma interleaved_warmRuns_independent {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) (Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ξ : ℕ → Ξ → Ω)
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ Q P)
    {n : ℕ} (hn : 0 < n) (N T : ℕ) (η : ℝ) (g : Fin n → E → Ω → E) (x : E)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) :
    iIndepFun (fun (i : Fin n) ω =>
      warmRun η (g i) x (fun k => ξ (N + (n * k + i.val)) ω) T) P := by
  classical
  let default : Ω := Classical.choice (nonempty_of_isProbabilityMeasure Q)
  let extend : (Fin (T) → Ω) → ℕ → Ω :=
    fun u k => if hk : k < T then u ⟨k, hk⟩ else default
  have hExt : Measurable extend := by
    apply Measurable.of_eval
    intro k
    by_cases hk : k < T
    · simpa only [extend, dite_eq_left hk] using
        (measurable_pi_apply (⟨k, hk⟩ : Fin (T)))
    · simpa only [extend, dite_eq_right hk] using
        (measurable_const : Measurable (fun _ : Fin (T) → Ω => default))
  have hh := (interleaved_blocks_independent P Q ξ hIID (b := T) hn N).comp
    (fun i u => warmRun η (g i) x (extend u) T)
    (fun i => (measurable_warmRun η (g i) x (hg i) T).comp hExt)
  change iIndepFun (fun (i : Fin n) ω => warmRun η (g i) x
    (extend (fun j : Fin (T) => ξ (N + (n * j.val + i.val)) ω)) T) P at hh
  have he : (fun (i : Fin n) ω => warmRun η (g i) x
      (extend (fun j : Fin (T) => ξ (N + (n * j.val + i.val)) ω)) T) =
      (fun (i : Fin n) ω => warmRun η (g i) x
        (fun k => ξ (N + (n * k + i.val)) ω) T) := by
    funext i ω
    apply warmRun_prefix
    intro k hk
    simp only [extend, dite_eq_left hk]
  rw [he] at hh
  exact hh

end LongTails.Proofs.LocalNonlinearExtragradientSampling

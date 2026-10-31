import LongTails.Proofs.StochasticEnvelopeApproximation
import LongTails.Proofs.StochasticEnvelopeFreshness
import LongTails.Proofs.StochasticEnvelopeExecution
import LongTails.Proofs.AcceleratedMarkovRun
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Data.Finset.Sum

open MeasureTheory
namespace LongTails.Proofs.StochasticEnvelopeTransport

variable {Ω I A B : Type*} [MeasurableSpace Ω]

noncomputable def completeIndex [Encodable I] (used : I → Prop) (flat : I → ℕ) (C : ℕ) : I → ℕ := by
  classical
  exact fun i => if used i then flat i else C + Encodable.encode i

lemma completeIndex_injective [Encodable I] (used : I → Prop) (flat : I → ℕ) (C : ℕ)
    (hbound : ∀ i, used i → flat i < C)
    (hinj : Set.InjOn flat {i | used i}) :
    Function.Injective (completeIndex used flat C) := by
  classical
  intro i j he
  dsimp [completeIndex] at he
  split_ifs at he with hi hj hj
  · exact hinj hi hj he
  · have := hbound i hi; omega
  · have := hbound j hj; omega
  · exact Encodable.encode_injective (by omega)

lemma completeIndex_preserving [Encodable I] (p : Measure Ω) [IsProbabilityMeasure p]
    (used : I → Prop) (flat : I → ℕ) (C : ℕ)
    (hbound : ∀ i, used i → flat i < C) (hinj : Set.InjOn flat {i | used i}) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun i => ξ (completeIndex used flat C i))
      (Measure.infinitePi fun _ : ℕ => p) (Measure.infinitePi fun _ : I => p) := by
  exact ⟨by fun_prop, Measure.map_infinitePi_infinitePi_of_inj
    (completeIndex_injective used flat C hbound hinj)⟩

lemma completeIndex_used [Encodable I] (used : I → Prop) (flat : I → ℕ) (C : ℕ)
    (i : I) (hi : used i) : completeIndex used flat C i = flat i := by
  classical
  simp [completeIndex, hi]

lemma infinitePi_sum_preserving (p : Measure Ω) [IsProbabilityMeasure p] :
    MeasurePreserving (fun ξ : A ⊕ B → Ω => ((fun a => ξ (.inl a)), fun b => ξ (.inr b)))
      (Measure.infinitePi fun _ : A ⊕ B => p)
      ((Measure.infinitePi fun _ : A => p).prod (Measure.infinitePi fun _ : B => p)) := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ B => Ω)
  have hinv : MeasurePreserving e.symm
      ((Measure.infinitePi fun _ : A => p).prod (Measure.infinitePi fun _ : B => p))
      (Measure.infinitePi fun _ : A ⊕ B => p) := by
    refine ⟨e.symm.measurable, ?_⟩
    apply Measure.eq_infinitePi
    intro s t ht
    classical
    rw [Measure.map_apply e.symm.measurable (MeasurableSet.pi (Finset.countable_toSet _) (by simp_all))]
    have he : e.symm ⁻¹' Set.pi (s : Set (A ⊕ B)) t =
        Set.pi (s.toLeft : Set A) (fun a => t (.inl a)) ×ˢ
        Set.pi (s.toRight : Set B) (fun b => t (.inr b)) := by
      ext w
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe,
        Finset.mem_toLeft, Finset.mem_toRight]
      constructor
      · intro hw; exact ⟨fun a ha => hw (.inl a) ha, fun b hb => hw (.inr b) hb⟩
      · rintro ⟨ha, hb⟩ (a | b) h
        · exact ha a h
        · exact hb b h
    rw [he, Measure.prod_prod, Measure.infinitePi_pi, Measure.infinitePi_pi,
      Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
    all_goals simp_all
  exact hinv.symm

lemma infinitePi_curry_preserving (p : Measure Ω) [IsProbabilityMeasure p] :
    MeasurePreserving (fun ξ : A × B → Ω => fun a b => ξ (a, b))
      (Measure.infinitePi fun _ : A × B => p)
      (Measure.infinitePi fun _ : A => Measure.infinitePi fun _ : B => p) :=
  ⟨by fun_prop, Measure.infinitePi_map_curry (fun _ : A => fun _ : B => p)⟩

lemma infinitePi_apply_preserving {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ]
    {f : X → Y} (hf : MeasurePreserving f μ ν) :
    MeasurePreserving (fun x : I → X => fun i => f (x i))
      (Measure.infinitePi fun _ : I => μ) (Measure.infinitePi fun _ : I => ν) := by
  refine ⟨Measurable.of_eval (fun i => hf.measurable.comp (measurable_pi_apply i)), ?_⟩
  rw [Measure.infinitePi_map_pi (fun _ : I => μ) (fun _ => hf.measurable)]
  simp only [hf.map_eq]

lemma infinitePi_curry_three_preserving {D : Type*} (p : Measure Ω) [IsProbabilityMeasure p] :
    MeasurePreserving (fun ξ : A × B × D → Ω => fun a b d => ξ (a, b, d))
      (Measure.infinitePi fun _ : A × B × D => p)
      (Measure.infinitePi fun _ : A => Measure.infinitePi fun _ : B =>
        Measure.infinitePi fun _ : D => p) :=
  (infinitePi_apply_preserving (I := A) (infinitePi_curry_preserving (A := B) (B := D) p)).comp
    (infinitePi_curry_preserving (A := A) (B := B × D) p)

abbrev ApproximationIndex (b h v : ℕ) :=
  ((Fin (h + 1) × Fin 8 × Fin (b + 1)) ⊕
    (ℕ × (Fin (h + 1) × Fin 8 × Fin (b + 1)))) ⊕
    (ℕ × Fin (v + 1) × ℕ)

instance (b h v : ℕ) : Encodable (ApproximationIndex b h v) :=
  inferInstanceAs (Encodable (((Fin (h + 1) × Fin 8 × Fin (b + 1)) ⊕
    (ℕ × (Fin (h + 1) × Fin 8 × Fin (b + 1)))) ⊕ (ℕ × Fin (v + 1) × ℕ)))

def groupApproximation (b h v : ℕ) (ξ : ApproximationIndex b h v → Ω) :=
  (((fun i j k => ξ (.inl (.inl (i, j, k)))),
    (fun z i j k => ξ (.inl (.inr (z, i, j, k))))),
    (fun z i k => ξ (.inr (z, i, k))))

lemma groupApproximation_preserving (p : Measure Ω) [IsProbabilityMeasure p] (b h v : ℕ) :
    let Q := Measure.pi fun _ : Fin (h + 1) => Measure.pi fun _ : Fin 8 =>
      Measure.pi fun _ : Fin (b + 1) => p
    MeasurePreserving (groupApproximation (Ω := Ω) b h v)
      (Measure.infinitePi fun _ : ApproximationIndex b h v => p)
      ((Q.prod (Measure.infinitePi fun _ : ℕ => Q)).prod
        (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (v + 1) =>
          Measure.infinitePi fun _ : ℕ => p)) := by
  let T := Fin (h + 1) × Fin 8 × Fin (b + 1)
  have hb := infinitePi_curry_three_preserving (A := Fin (h + 1)) (B := Fin 8)
    (D := Fin (b + 1)) p
  have hp := (infinitePi_apply_preserving (I := ℕ) hb).comp
    (infinitePi_curry_preserving (A := ℕ) (B := T) p)
  have hi := infinitePi_curry_three_preserving (A := ℕ) (B := Fin (v + 1)) (D := ℕ) p
  have hpair := (hb.prod hp).comp (infinitePi_sum_preserving (A := T) (B := ℕ × T) p)
  have hall := (hpair.prod hi).comp
    (infinitePi_sum_preserving (A := T ⊕ (ℕ × T)) (B := ℕ × Fin (v + 1) × ℕ) p)
  simp only [Measure.infinitePi_eq_pi, Function.comp_def, Prod.map] at hall
  convert hall using 1
  rfl

lemma radix_lt {B d i n : ℕ} (hd : d < B) (hi : i < n) : B * i + d < B * n := by
  have hh := Nat.mul_le_mul_left B (Nat.succ_le_of_lt hi)
  nlinarith only [hd, hh]

lemma radix_inj {B d e i j : ℕ} (hd : d < B) (he : e < B)
    (h : B * i + d = B * j + e) : i = j ∧ d = e := by
  have hmod := congrArg (fun z => z % B) h
  have hde : d = e := by simpa [Nat.add_mod, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] using hmod
  have hB : 0 < B := by omega
  have hij : i = j := by
    have hh : B * i = B * j := by omega
    exact (Nat.mul_left_cancel_iff hB).mp hh
  exact ⟨hij, hde⟩

def blockAddress (b h : ℕ) (i : Fin (h + 1) × Fin 8 × Fin (b + 1)) : ℕ :=
  (b + 1) * (8 * i.1.val + i.2.1.val) + i.2.2.val

lemma blockAddress_lt (b h : ℕ) (i : Fin (h + 1) × Fin 8 × Fin (b + 1)) :
    blockAddress b h i < (b + 1) * 8 * (h + 1) := by
  have hh := radix_lt i.2.2.isLt (radix_lt i.2.1.isLt i.1.isLt)
  simpa [blockAddress, Nat.mul_assoc] using hh

lemma blockAddress_injective (b h : ℕ) : Function.Injective (blockAddress b h) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ he
  obtain ⟨hij, hk⟩ := radix_inj k.isLt k'.isLt he
  obtain ⟨hi, hj⟩ := radix_inj j.isLt j'.isLt hij
  have : i = i' := Fin.ext hi
  have : j = j' := Fin.ext hj
  have : k = k' := Fin.ext hk
  simp_all

def pilotCoordinate {T : Type*} : T ⊕ (ℕ × T) → ℕ × T
  | .inl i => (0, i)
  | .inr (j, i) => (j + 1, i)

lemma pilotCoordinate_injective {T : Type*} : Function.Injective (pilotCoordinate (T := T)) := by
  rintro (i | ⟨j,i⟩) (i' | ⟨j',i'⟩) he <;> simp_all [pilotCoordinate]

def usedApproximation (b h v N K J : ℕ) : ApproximationIndex b h v → Prop
  | .inl x => (pilotCoordinate x).1 < N + 1
  | .inr (j,_i,k) => j < J ∧ k < K

def flatApproximation (b h v N K : ℕ) : ApproximationIndex b h v → ℕ
  | .inl x => (b + 1) * 8 * (h + 1) * (pilotCoordinate x).1 +
      blockAddress b h (pilotCoordinate x).2
  | .inr (j,i,k) => (b + 1) * 8 * (h + 1) * (N + 1) + K * ((v + 1) * j + i.val) + k

lemma flatApproximation_bound (b h v N K J : ℕ) (i : ApproximationIndex b h v)
    (hi : usedApproximation b h v N K J i) :
    flatApproximation b h v N K i <
      (b + 1) * 8 * (h + 1) * (N + 1) + K * (v + 1) * J := by
  cases i with
  | inl x =>
      have hh := radix_lt (blockAddress_lt b h (pilotCoordinate x).2) hi
      change _ < _ + _
      dsimp [flatApproximation]
      omega
  | inr x =>
      have hh := radix_lt hi.2 (radix_lt x.2.1.isLt hi.1)
      dsimp [flatApproximation]
      nlinarith only [hh]

lemma flatApproximation_injOn (b h v N K J : ℕ) :
    Set.InjOn (flatApproximation b h v N K) {i | usedApproximation b h v N K J i} := by
  rintro (x | ⟨j,i,k⟩) hx (y | ⟨j',i',k'⟩) hy he
  · have hh := radix_inj (blockAddress_lt b h (pilotCoordinate x).2)
        (blockAddress_lt b h (pilotCoordinate y).2) he
    apply congrArg Sum.inl
    apply pilotCoordinate_injective
    exact Prod.ext hh.1 (blockAddress_injective b h hh.2)
  · have hh := radix_lt (blockAddress_lt b h (pilotCoordinate x).2) hx
    dsimp [flatApproximation] at he
    omega
  · have hh := radix_lt (blockAddress_lt b h (pilotCoordinate y).2) hy
    dsimp [flatApproximation] at he
    omega
  · have he' : K * ((v + 1) * j + i.val) + k = K * ((v + 1) * j' + i'.val) + k' := by
      dsimp [flatApproximation] at he
      omega
    obtain ⟨hji, hk⟩ := radix_inj hx.2 hy.2 he'
    obtain ⟨hj, hi⟩ := radix_inj i.isLt i'.isLt hji
    have : i = i' := Fin.ext hi
    simp_all

noncomputable def coupledApproximation (b h v N K J : ℕ) (ξ : ℕ → Ω) :=
  groupApproximation b h v (fun i => ξ (completeIndex (usedApproximation b h v N K J)
    (flatApproximation b h v N K)
    ((b + 1) * 8 * (h + 1) * (N + 1) + K * (v + 1) * J) i))

lemma coupledApproximation_preserving (p : Measure Ω) [IsProbabilityMeasure p]
    (b h v N K J : ℕ) :
    let Q := Measure.pi fun _ : Fin (h + 1) => Measure.pi fun _ : Fin 8 =>
      Measure.pi fun _ : Fin (b + 1) => p
    MeasurePreserving (coupledApproximation (Ω := Ω) b h v N K J)
      (Measure.infinitePi fun _ : ℕ => p)
      ((Q.prod (Measure.infinitePi fun _ : ℕ => Q)).prod
        (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (v + 1) =>
          Measure.infinitePi fun _ : ℕ => p)) :=
  (groupApproximation_preserving p b h v).comp
    (completeIndex_preserving p _ _ _ (flatApproximation_bound b h v N K J)
      (flatApproximation_injOn b h v N K J))

omit [MeasurableSpace Ω] in
lemma coupledApproximation_rough (b h v N K J : ℕ) (ξ : ℕ → Ω)
    (i : Fin (h + 1)) (j : Fin 8) (k : Fin (b + 1)) :
    (coupledApproximation b h v N K J ξ).1.1 i j k =
      ξ ((b + 1) * 8 * i.val + (b + 1) * j.val + k.val) := by
  dsimp only [coupledApproximation, groupApproximation]
  rw [completeIndex_used _ _ _ _ (show usedApproximation b h v N K J (.inl (.inl (i,j,k))) by
    simp [usedApproximation, pilotCoordinate])]
  congr 1
  simp only [flatApproximation, pilotCoordinate, blockAddress, Nat.mul_zero, Nat.zero_add]
  ring

omit [MeasurableSpace Ω] in
lemma coupledApproximation_pilot (b h v N K J : ℕ) (ξ : ℕ → Ω)
    (z : ℕ) (hz : z < N) (i : Fin (h + 1)) (j : Fin 8) (k : Fin (b + 1)) :
    (coupledApproximation b h v N K J ξ).1.2 z i j k =
      ξ ((b + 1) * 8 * (h + 1) + (b + 1) * 8 * (h + 1) * z +
        (b + 1) * 8 * i.val + (b + 1) * j.val + k.val) := by
  dsimp only [coupledApproximation, groupApproximation]
  rw [completeIndex_used _ _ _ _ (show usedApproximation b h v N K J (.inl (.inr (z,i,j,k))) by
    simpa [usedApproximation, pilotCoordinate] using hz)]
  congr 1
  simp only [flatApproximation, pilotCoordinate, blockAddress]
  ring

omit [MeasurableSpace Ω] in
lemma coupledApproximation_inner (b h v N K J : ℕ) (ξ : ℕ → Ω)
    (z : ℕ) (hz : z < J) (i : Fin (v + 1)) (k : ℕ) (hk : k < K) :
    (coupledApproximation b h v N K J ξ).2 z i k =
      ξ ((b + 1) * 8 * (h + 1) * (N + 1) + K * (v + 1) * z + K * i.val + k) := by
  dsimp only [coupledApproximation, groupApproximation]
  rw [completeIndex_used _ _ _ _ (show usedApproximation b h v N K J (.inr (z,i,k)) from ⟨hz,hk⟩)]
  congr 1
  simp only [flatApproximation]
  ring

lemma advance_samples_congr {S T : Type*} (F : S → T → S) (s : S)
    (ξ ζ : ℕ → T) (N call : ℕ) (h : ∀ j < N, ξ (call + j) = ζ (call + j)) :
    OracleTemplate.StochasticGradient.advance (fun k state => F state (ξ k)) N call s =
      OracleTemplate.StochasticGradient.advance (fun k state => F state (ζ k)) N call s := by
  induction N generalizing call s with
  | zero => rfl
  | succ N ih =>
      have h0 := h 0 (by omega)
      simp only [Nat.add_zero] at h0
      simp only [OracleTemplate.StochasticGradient.advance, h0]
      apply ih
      intro j hj
      have hh := h (j + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

open OracleTemplate
open LongTails.Algorithms.StochasticEnvelopeLocalization
open LongTails.Algorithms.StochasticEnvelopePilot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [MeasurableSpace Ω] in
lemma stage_samples_congr (g : E → Ω → E) (L μ p s a U D : ℝ) (center anchor : E)
    (K v : ℕ) (ξ ζ : Fin (v + 1) → ℕ → Ω) (h : ∀ i k, k < K → ξ i k = ζ i k) :
    stage g L μ p s a U D center anchor K v ξ = stage g L μ p s a U D center anchor K v ζ := by
  unfold stage
  apply congrArg MultiplicativeRobustEstimator.medoid
  funext i
  apply congrArg (fun state : ℕ × E × E => state.2.1)
  apply HeavyTailedMarkovGradient.clippedRun_congr
  intro j hj
  simpa only [Nat.mul_one] using h i j hj

omit [MeasurableSpace Ω] in
lemma refineRun_samples_congr (g : E → Ω → E) (L μ p s a U n : ℝ) (center start : E)
    (K v J : ℕ) (ξ ζ : ℕ → Fin (v + 1) → ℕ → Ω)
    (h : ∀ j, j < J → ∀ i k, k < K → ξ j i k = ζ j i k) :
    refineRun g L μ p s a U n center start K v ξ J =
      refineRun g L μ p s a U n center start K v ζ J := by
  induction J with
  | zero => rfl
  | succ J ih =>
      simp only [refineRun, ih (fun j hj => h j (by omega))]
      split_ifs
      · rfl
      · exact stage_samples_congr g L μ p s a U _ center _ K v _ _ (h J (by omega))

omit [MeasurableSpace Ω] in
lemma approximate_samples_congr (g : E → Ω → E) (L μ p s a n β : ℝ) (center : E)
    (b h v N K J : ℕ)
    (rough rough' : Fin (h + 1) → Fin 8 → Fin (b + 1) → Ω)
    (pilot pilot' : ℕ → Fin (h + 1) → Fin 8 → Fin (b + 1) → Ω)
    (inner inner' : ℕ → Fin (v + 1) → ℕ → Ω)
    (hr : rough = rough') (hp : ∀ j, j < N → pilot j = pilot' j)
    (hi : ∀ j, j < J → ∀ i k, k < K → inner j i k = inner' j i k) :
    approximate g L μ p s a n β center b h v N K J rough pilot inner =
      approximate g L μ p s a n β center b h v N K J rough' pilot' inner' := by
  subst rough'
  have hU : localizedRadius g L μ s β center rough pilot N =
      localizedRadius g L μ s β center rough pilot' N := by
    have hrun (radius : ℝ) : sampledRun g L μ β radius center pilot N =
        sampledRun g L μ β radius center pilot' N := by
      unfold sampledRun
      apply advance_samples_congr
      simpa only [Nat.zero_add] using hp
    simp only [localizedRadius, hrun]
  unfold approximate
  rw [hU]
  exact refineRun_samples_congr g L μ p s a _ n center center K v J inner inner' hi

omit [MeasurableSpace Ω] in
lemma evalAt_approximatePlan_coupled (g : E → Ω → E) (L μ p s a n β : ℝ) (center : E)
    (b h v N K J : ℕ) (ξ : ℕ → Ω) :
    LongTails.Proofs.RecursiveEnvelopeExecution.evalAt (fun k x => g x (ξ k))
      (LongTails.Algorithms.StochasticEnvelopeProgram.approximatePlan L μ p s a n β center b h v N K J) 0 =
      let w := coupledApproximation b h v N K J ξ
      approximate g L μ p s a n β center b h v N K J w.1.1 w.1.2 w.2 := by
  rw [LongTails.Proofs.StochasticEnvelopeExecution.evalAt_approximatePlan]
  simp only [Nat.zero_add]
  symm
  apply approximate_samples_congr
  · funext i j k
    exact coupledApproximation_rough b h v N K J ξ i j k
  · intro z hz
    funext i j k
    exact coupledApproximation_pilot b h v N K J ξ z hz i j k
  · intro z hz i k hk
    exact coupledApproximation_inner b h v N K J ξ z hz i k hk

lemma approximatePlan_map_eq [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : E → Ω → E) (L μ p s a n β : ℝ) (center : E) (b h v N K J : ℕ)
    (hX : Measurable (fun w :
      ((Fin (h + 1) → Fin 8 → Fin (b + 1) → Ω) ×
        (ℕ → Fin (h + 1) → Fin 8 → Fin (b + 1) → Ω)) × (ℕ → Fin (v + 1) → ℕ → Ω) =>
      approximate g L μ p s a n β center b h v N K J w.1.1 w.1.2 w.2)) :
    let Q := Measure.pi fun _ : Fin (h + 1) => Measure.pi fun _ : Fin 8 =>
      Measure.pi fun _ : Fin (b + 1) => P
    let R := (Q.prod (Measure.infinitePi fun _ : ℕ => Q)).prod
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (v + 1) =>
        Measure.infinitePi fun _ : ℕ => P)
    (Measure.infinitePi fun _ : ℕ => P).map (fun ξ =>
      LongTails.Proofs.RecursiveEnvelopeExecution.evalAt (fun k x => g x (ξ k))
        (LongTails.Algorithms.StochasticEnvelopeProgram.approximatePlan L μ p s a n β center b h v N K J) 0) =
      R.map (fun w => approximate g L μ p s a n β center b h v N K J w.1.1 w.1.2 w.2) := by
  have hc := coupledApproximation_preserving P b h v N K J
  simp_rw [evalAt_approximatePlan_coupled]
  calc
    _ = ((Measure.infinitePi fun _ : ℕ => P).map (coupledApproximation b h v N K J)).map
        (fun w => approximate g L μ p s a n β center b h v N K J w.1.1 w.1.2 w.2) :=
      (Measure.map_map hX hc.measurable).symm
    _ = _ := by rw [hc.map_eq]

section Moment
variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
open RecursiveEnvelopeGeometry in
lemma approximatePlan_moment {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {field : E → E}
    {f : E → ℝ} {L μ p s a n : ℝ} (h : Model L f field)
    (hμ : 0 < μ) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 < a) (hn : 1 ≤ n)
    (hκ : 2 ≤ (L + μ) / μ) (haκ : a ≤ ((L + μ) / μ) ^ (-2 : ℝ))
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (center : E) :
    let κ := (L + μ) / μ
    let η₀ := (2 : ℝ) ^ (-128 : ℝ) * κ ^ (-12 : ℝ) * a ^ (2 * p) * n ^ (-2 * (p - 1))
    let η₁ := (2 : ℝ) ^ (-32 : ℝ) * a ^ p * n ^ (-(p - 1))
    let β := 1 / (1024 * κ)
    let N := ⌈17 * Real.sqrt κ * Real.log (1 + 1024 * κ)⌉₊
    let pilotReplicas := 7 + ⌈2 * Real.log (1 + (N + 1 : ℝ) / η₀)⌉₊
    let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
    let J := ⌈2 * Real.log (1 + n / a)⌉₊
    let innerReplicas := 7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η₁)⌉₊
    let K := ⌈(268435456 : ℝ) ^ (p / (p - 1)) * (Real.sqrt κ + n + 1)⌉₊
    let R := Measure.infinitePi fun _ : ℕ => P
    let X := fun ξ : ℕ → Ω => LongTails.Proofs.RecursiveEnvelopeExecution.evalAt
      (fun k x => g x (ξ k)) (LongTails.Algorithms.StochasticEnvelopeProgram.approximatePlan
        L μ p s a n β center b pilotReplicas innerReplicas N K J) 0
    let r := ‖center - prox field μ center‖
    let t := s / μ
    Integrable (fun w => ‖X w - prox field μ center‖ ^ p) R ∧
      (∫ w, ‖X w - prox field μ center‖ ^ p ∂R) ≤
        (2 : ℝ) ^ (18 : ℝ) * (t + a * r) ^ p * n ^ (-(p - 1)) := by
  let κ := (L + μ) / μ
  let η₀ := (2 : ℝ) ^ (-128 : ℝ) * κ ^ (-12 : ℝ) * a ^ (2 * p) * n ^ (-2 * (p - 1))
  let η₁ := (2 : ℝ) ^ (-32 : ℝ) * a ^ p * n ^ (-(p - 1))
  let β := 1 / (1024 * κ)
  let N := ⌈17 * Real.sqrt κ * Real.log (1 + 1024 * κ)⌉₊
  let pilotReplicas := 7 + ⌈2 * Real.log (1 + (N + 1 : ℝ) / η₀)⌉₊
  let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
  let J := ⌈2 * Real.log (1 + n / a)⌉₊
  let innerReplicas := 7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η₁)⌉₊
  let K := ⌈(268435456 : ℝ) ^ (p / (p - 1)) * (Real.sqrt κ + n + 1)⌉₊
  have hh := StochasticEnvelopeApproximation.approximate_moment P h hμ hp hp2 hs ha hn hκ haκ
    hg hi hmean hpi hm center
  have hc := coupledApproximation_preserving P b pilotReplicas innerReplicas N K J
  dsimp only
  simp_rw [evalAt_approximatePlan_coupled]
  refine ⟨hc.integrable_comp_of_integrable hh.1, ?_⟩
  have he := (show ProbabilityTheory.HasLaw (coupledApproximation (Ω := Ω) b pilotReplicas innerReplicas N K J)
    _ _ from ⟨hc.measurable.aemeasurable, hc.map_eq⟩).integral_comp hh.1.aestronglyMeasurable
  exact he.trans_le hh.2


end Moment

end LongTails.Proofs.StochasticEnvelopeTransport

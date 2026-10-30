import LongTails.Algorithms.GeneralizedLipschitzConvex
import LongTails.Proofs.GeneralizedLipschitzWarmStartSampling
import LongTails.Proofs.GeneralizedLipschitzBurnin
import LongTails.Proofs.MultiplicativeAccelerationExecution
import LongTails.Proofs.QuantileOracleLowerBound
import LongTails.Proofs.TwoSidedPLExecution
import LongTails.Proofs.CoarseGeneralizedBatchExecution
open MeasureTheory
namespace LongTails.Proofs.GeneralizedLipschitzComposition
open OracleTemplate OracleTemplate.StochasticGradient
open LongTails.Algorithms.GeneralizedLipschitzConvex
variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma advance_twoPhase_warm (A : Algorithm E E E) (seed : A.Seed) (B : ℕ) (D G0 α : ℝ)
    (oracle : E → Ω → E) (ξ : ℕ → Ω) (N call : ℕ) (center : E)
    (state : LongTails.Algorithms.GeneralizedLipschitzWarmStart.State E) :
    advance (fun k s => (twoPhase A seed B D G0 α).update s
      (oracle ((twoPhase A seed B D G0 α).query s).2 (ξ k))) N call (.inr (center, state)) =
    .inr (center, advance (fun k s => LongTails.Algorithms.GeneralizedLipschitzWarmStart.update center D α s
      (oracle (LongTails.Algorithms.GeneralizedLipschitzWarmStart.point α s) (ξ k))) N call state) := by
  induction N generalizing call state with
  | zero => rfl
  | succ N ih =>
    simp only [advance, twoPhase]
    exact ih (call + 1) _
lemma advance_twoPhase_burn (A : Algorithm E E E) (seed : A.Seed) (B : ℕ) (D G0 α : ℝ)
    (oracle : E → Ω → E) (ξ : ℕ → Ω) (N call counter : ℕ) (state : A.State)
    (hN : 0 < N) (hB : counter + N = B) :
    advance (fun k s => (twoPhase A seed B D G0 α).update s
      (oracle ((twoPhase A seed B D G0 α).query s).2 (ξ k))) N call (.inl (counter, state)) =
    let next := advance (fun k s => A.update s (oracle (A.query s).2 (ξ k))) N call state
    .inr (A.output next, LongTails.Algorithms.GeneralizedLipschitzWarmStart.initial (A.output next) G0) := by
  induction N generalizing call counter state with
  | zero => omega
  | succ N ih =>
    by_cases hn : N = 0
    · subst N
      simp only [advance, twoPhase]
      rw [ite_eq_right (by omega : ¬ counter + 1 < B)]
    · have hlt : counter + 1 < B := by omega
      simp only [advance, twoPhase, ite_eq_left hlt]
      exact ih (call + 1) (counter + 1) _ (by omega) (by omega)

lemma advance_twoPhase_warm_initial (A : Algorithm E E E) (seed : A.Seed) (B : ℕ) (D G0 α : ℝ)
    (oracle : E → Ω → E) (ξ : ℕ → Ω) (K : ℕ) (center : E) :
    advance (fun k s => (twoPhase A seed B D G0 α).update s
      (oracle ((twoPhase A seed B D G0 α).query s).2 (ξ k))) K B
        (.inr (center, LongTails.Algorithms.GeneralizedLipschitzWarmStart.initial center G0)) =
    .inr (center, LongTails.Algorithms.GeneralizedLipschitzWarmStart.trajectory center D G0 α oracle (fun k => ξ (B + k)) K) := by
  rw [advance_twoPhase_warm]
  apply congrArg (fun st => Sum.inr (center, st))
  have hs := OracleTemplate.CoarseGeneralized.advance_shift
    (fun k st => LongTails.Algorithms.GeneralizedLipschitzWarmStart.update center D α st
      (oracle (LongTails.Algorithms.GeneralizedLipschitzWarmStart.point α st) (ξ k))) K B 0
      (LongTails.Algorithms.GeneralizedLipschitzWarmStart.initial center G0)
  simp only [Nat.add_zero] at hs
  rw [hs]
  have ht := LongTails.Proofs.GeneralizedLipschitzWarmStart.advance_trajectory center D G0 α oracle (fun k => ξ (B + k)) K 0
  simpa only [LongTails.Algorithms.GeneralizedLipschitzWarmStart.trajectory, Nat.zero_add] using ht
lemma execute_twoPhase [MeasurableSpace Ω]
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (oracle : E → Ω → E)
    (A : Algorithm E E E) (seed : A.Seed) (B K : ℕ) (hB : 0 < B) (D G0 α : ℝ) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω }
      (twoPhase A seed B D G0 α) (fun _ => B + K) () ξ =
    let center := execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } A (fun _ => B) seed ξ
    (LongTails.Algorithms.GeneralizedLipschitzWarmStart.trajectory center D G0 α oracle (fun k => ξ (B + k)) K).2.1 := by
  erw [execute_advance P oracle (twoPhase A seed B D G0 α) (B + K) () ξ]
  have hi : (twoPhase A seed B D G0 α).initial () = Sum.inl (0, A.initial seed) := by
    simp only [twoPhase, ite_eq_right hB.ne']
  erw [hi, OracleTemplate.TwoSidedPL.advance_add]
  simp only [Nat.zero_add]
  erw [advance_twoPhase_burn A seed B D G0 α oracle ξ B 0 0 (A.initial seed) hB (by omega)]
  erw [advance_twoPhase_warm_initial]
  have hx := execute_advance P oracle A B seed ξ
  erw [hx]
  rfl


lemma output_eq_burnin_warm [MeasurableSpace Ω]
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (oracle : E → Ω → E)
    (c : LongTails.Algorithms.GeneralizedLipschitzPilot.Config) (hc : 0 < c.calls)
    (center : E) (R G G0 κ α : ℝ) (T K budget : ℕ) (hT : 0 < T)
    (hbudget : T * c.calls + K ≤ budget) (ξ : ℕ → Ω) :
    LongTails.Algorithms.GeneralizedLipschitzConvex.output c hc center R G G0 κ α T K budget
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ =
    let x := LongTails.Algorithms.GeneralizedLipschitzPilot.burninOutput c hc center R G G0 κ T
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, y) ω => oracle y ω } ξ
    (LongTails.Algorithms.GeneralizedLipschitzWarmStart.trajectory x (2 * R) G0 α oracle
      (fun k => ξ (T * c.calls + k)) K).2.1 := by
  let A := LongTails.Algorithms.GeneralizedLipschitzPilot.burninAlgorithm c hc center R G G0 κ
  apply (OracleTemplate.SplitRobustAcceleration.execute_capped P oracle
    (twoPhase A () (T * c.calls) (2 * R) G0 α) (T * c.calls + K) budget hbudget () ξ).trans
  exact execute_twoPhase P oracle A () (T * c.calls) K (Nat.mul_pos hT hc) (2 * R) G0 α ξ

section PrefixStream
variable {Ω : Type}
def prefixStream {B : ℕ} (hB : 0 < B) (ξ : Fin B → Ω) (k : ℕ) : Ω :=
  if h : k < B then ξ ⟨k, h⟩ else ξ ⟨0, hB⟩
lemma prefixStream_agrees {B : ℕ} (hB : 0 < B) (ξ : ℕ → Ω) (k : ℕ) (hk : k < B) :
    prefixStream hB (fun i => ξ i) k = ξ k := by
  simp only [prefixStream, dite_eq_left hk]
lemma measurable_prefixStream [MeasurableSpace Ω] {B : ℕ} (hB : 0 < B) :
    Measurable (prefixStream (Ω := Ω) hB) := by
  apply Measurable.of_eval
  intro k
  by_cases hk : k < B
  · simpa only [prefixStream, dite_eq_left hk] using measurable_pi_apply (⟨k, hk⟩ : Fin B)
  · simpa only [prefixStream, dite_eq_right hk] using measurable_pi_apply (⟨0, hB⟩ : Fin B)
lemma execute_prefixStream {Q R U : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (oracle : Q → Ω → R) (A : OracleTemplate.Algorithm Q R U)
    (B : ℕ) (hB : 0 < B) (seed : A.Seed) (ξ : ℕ → Ω) :
    OracleTemplate.execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω }
      A (fun _ => B) seed (prefixStream hB (fun i => ξ i)) =
    OracleTemplate.execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω }
      A (fun _ => B) seed ξ := by
  apply LongTails.Proofs.QuantileOracleLowerBound.execute_prefix_congr
  intro k hk
  exact prefixStream_agrees hB ξ k hk

end PrefixStream
lemma product_failure_bound {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    (P : Measure A) (Q : Measure W) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {S : Set (A × W)} {B : Set A} (hS : MeasurableSet S) (hB : MeasurableSet B)
    {δA δB : ENNReal} (hbad : P B ≤ δA)
    (hsection : ∀ a, a ∉ B → Q (Prod.mk a ⁻¹' S) ≤ δB) :
    (P.prod Q) S ≤ δA + δB := by
  have hgood : (P.prod Q) (S \ (B ×ˢ Set.univ)) ≤ δB := by
    rw [Measure.prod_apply (hS.diff (hB.prod MeasurableSet.univ))]
    calc (∫⁻ a, Q (Prod.mk a ⁻¹' (S \ (B ×ˢ Set.univ))) ∂P) ≤ ∫⁻ _, δB ∂P := by
          apply lintegral_mono
          intro a
          change Q (Prod.mk a ⁻¹' (S \ (B ×ˢ Set.univ))) ≤ δB
          by_cases ha : a ∈ B
          · have he : Prod.mk a ⁻¹' (S \ (B ×ˢ Set.univ)) = ∅ := by ext w; simp [ha]
            simp only [he, measure_empty, zero_le]
          · have he : Prod.mk a ⁻¹' (S \ (B ×ˢ Set.univ)) = Prod.mk a ⁻¹' S := by ext w; simp [ha]
            rw [he]
            exact hsection a ha
         _ = δB := by simp
  have hcover : S ⊆ (B ×ˢ Set.univ) ∪ (S \ (B ×ˢ Set.univ)) := by
    intro z hz
    by_cases hb : z ∈ B ×ˢ Set.univ
    · exact Or.inl hb
    · exact Or.inr ⟨hz, hb⟩
  calc (P.prod Q) S ≤ (P.prod Q) ((B ×ˢ Set.univ) ∪ (S \ (B ×ˢ Set.univ))) := measure_mono hcover
       _ ≤ (P.prod Q) (B ×ˢ Set.univ) + (P.prod Q) (S \ (B ×ˢ Set.univ)) := measure_union_le _ _
       _ ≤ δA + δB := by
          simpa only [Measure.prod_prod, measure_univ, mul_one] using add_le_add hbad hgood

lemma prefix_event_bound {Ω : Type} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] {B : ℕ} (hB : 0 < B)
    {X : (ℕ → Ω) → ℝ} (hX : Measurable X)
    (hprefix : ∀ ξ, X (prefixStream hB (fun i => ξ i)) = X ξ)
    {c : ℝ} {δ : ENNReal}
    (hb : (Measure.infinitePi fun _ : ℕ => p) {ξ | c < X ξ} ≤ δ) :
    (Measure.pi fun _ : Fin B => p) {η | c < X (prefixStream hB η)} ≤ δ := by
  have hm : MeasurableSet {η | c < X (prefixStream hB η)} :=
    measurableSet_lt measurable_const (hX.comp (measurable_prefixStream hB))
  have hp := OracleTemplate.StochasticGeneralized.prefix_preserving p B
  have hs : (fun ξ : ℕ → Ω => fun i : Fin B => ξ i) ⁻¹' {η | c < X (prefixStream hB η)} =
      {ξ | c < X ξ} := by
    ext ξ
    change (c < X (prefixStream hB (fun i => ξ i))) ↔ c < X ξ
    rw [hprefix ξ]
  have he := hp.measure_preimage hm.nullMeasurableSet
  rw [hs] at he
  rw [← he]
  exact hb
lemma burninOutput_law_irrel {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : LongTails.Algorithms.GeneralizedLipschitzPilot.Config) (hc : 0 < c.calls)
    (center : E) (R G G0 κ : ℝ) (T : ℕ) (oracle : E → Ω → E)
    (P Q : ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω) :
    LongTails.Algorithms.GeneralizedLipschitzPilot.burninOutput c hc center R G G0 κ T
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ =
    LongTails.Algorithms.GeneralizedLipschitzPilot.burninOutput c hc center R G G0 κ T
      { Seed := fun _ => Ω, law := Q, answer := fun _ (_, x) ω => oracle x ω } ξ := by
  rw [LongTails.Proofs.GeneralizedLipschitzExecution.execute_burnin,
    LongTails.Proofs.GeneralizedLipschitzExecution.execute_burnin]

section Confidence
open LongTails.Setups.StochasticGeneralizedLipschitzConvex
open LongTails.Algorithms.GeneralizedLipschitzPilot
open LongTails.Proofs.GeneralizedLipschitzPilot
open LongTails.Proofs.GeneralizedLipschitzExecution
open LongTails.Proofs.GeneralizedLipschitzBurnin
open LongTails.Proofs.GeneralizedLipschitzWarmStart
open LongTails.Proofs.GeneralizedLipschitzWarmStartSampling
variable {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
lemma combined_confidence (p : Measure Ω) [IsProbabilityMeasure p]
    (P : ProbabilityMeasure (ℕ → Ω))
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) p (P : Measure _))
    {f : E → ℝ} (hf : Measurable f) {xstar : E} {oracle : E → Ω → E} {R G G0 G1 ε δ : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hR : 0 < R) (hG0 : 0 < G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hκ : 1 ≤ R * G) (hmin : ∀ x, f xstar ≤ f x)
    (center : E) (hstar : ‖xstar - center‖ ≤ R) (hε : 0 < ε) (hδ : 0 < δ)
    (T : ℕ) (hT : 0 < T) :
    let c := tuning (R * G) δ
    let hc := tuning_calls_pos (R * G) δ
    let D := 2 * R
    let e := ε / 20
    let τ := ⌈(96 * D * G) ^ 2⌉₊
    let α := min (1 / (16 * τ * (D * G))) (min ((e / (24 * D * G0)) ^ 2) (e / (1536 * τ * D * G0)))
    let K := ⌈(2 / α) * Real.log (max 2 (1024 * D * G0 / e))⌉₊
    ∀ budget, T * c.calls + K ≤ budget →
      let out := LongTails.Algorithms.GeneralizedLipschitzConvex.output c hc center R G G0 (R * G) α T K budget
        { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω }
      Measurable out ∧ (P : Measure _) {ξ | ε < f (out ξ) - f xstar} ≤
        ENNReal.ofReal (2048 * (R * G) ^ 2 / T + T * δ) + ENNReal.ofReal (1 / 20 : ℝ) := by
  let c := tuning (R * G) δ
  have hc : 0 < c.calls := tuning_calls_pos (R * G) δ
  let D := 2 * R
  let e := ε / 20
  let τ := ⌈(96 * D * G) ^ 2⌉₊
  let α := min (1 / (16 * τ * (D * G))) (min ((e / (24 * D * G0)) ^ 2) (e / (1536 * τ * D * G0)))
  let K := ⌈(2 / α) * Real.log (max 2 (1024 * D * G0 / e))⌉₊
  dsimp only
  intro budget hbudget
  let B := T * c.calls
  have hB : 0 < B := Nat.mul_pos hT hc
  let Q : ProbabilityMeasure (ℕ → Ω) := ⟨Measure.infinitePi (fun _ : ℕ => p), inferInstance⟩
  have hQ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) p (Q : Measure _) :=
    OracleTemplate.StochasticGeneralized.infinitePi_iid p
  let μ := Measure.pi (fun _ : Fin B => p)
  let burn := fun ξ => burninOutput c hc center R G G0 (R * G) T
    { Seed := fun _ => Ω, law := Q, answer := fun _ (_, x) ω => oracle x ω } ξ
  let Z := fun a : Fin B → Ω => burn (prefixStream hB a)
  have hburn : Measurable burn := measurable_burninOutput c hc center R G G0 (R * G) Q ho.measurable T
  have hZ : Measurable Z := hburn.comp (measurable_prefixStream hB)
  have hprefix (ξ : ℕ → Ω) : burn (prefixStream hB (fun i => ξ i)) = burn ξ :=
    execute_prefixStream Q oracle (burninAlgorithm c hc center R G G0 (R * G)) B hB () ξ
  have hbad : μ {a | 128 * R * G0 < f (Z a) - f xstar} ≤ ENNReal.ofReal (2048 * (R * G) ^ 2 / T + T * δ) := by
    apply prefix_event_bound p hB ((hf.comp hburn).sub measurable_const)
    · intro ξ
      change f (burn (prefixStream hB (fun i => ξ i))) - f xstar = f (burn ξ) - f xstar
      rw [hprefix ξ]
    · exact burninOutput_confidence p hf ho hR.le hG0 hδ hG1 hG hGG hκ hmin hstar T hT Q
        (OracleTemplate.StochasticGeneralized.infinitePi_iid p) hc
  let Y := fun z : (Fin B → Ω) × (ℕ → Ω) =>
    (LongTails.Algorithms.GeneralizedLipschitzWarmStart.trajectory (Z z.1) D G0 α oracle z.2 K).2.1
  have hY : Measurable Y := ((measurable_trajectory_family D G0 α ho.measurable K).comp
    ((hZ.comp measurable_fst).prodMk measurable_snd)).snd.fst
  have hS : MeasurableSet {z | ε < f (Y z) - f xstar} :=
    measurableSet_lt measurable_const ((hf.comp hY).sub measurable_const)
  have hBad : MeasurableSet {a | 128 * R * G0 < f (Z a) - f xstar} :=
    measurableSet_lt measurable_const ((hf.comp hZ).sub measurable_const)
  have hprod : (μ.prod (Q : Measure _)) {z | ε < f (Y z) - f xstar} ≤
      ENNReal.ofReal (2048 * (R * G) ^ 2 / T + T * δ) + ENNReal.ofReal (1 / 20 : ℝ) := by
    apply product_failure_bound μ (Q : Measure _) hS hBad hbad
    intro a ha
    have hzball : ‖Z a - center‖ ≤ R := burninOutput_mem_ball c hc center R G G0 (R * G) hR.le Q oracle (prefixStream hB a) T
    have hzstar : ‖xstar - Z a‖ ≤ D := by
      have hh := dist_triangle xstar center (Z a)
      simp only [dist_eq_norm] at hh
      have hr : ‖center - Z a‖ ≤ R := by simpa only [norm_sub_rev] using hzball
      dsimp [D]
      linarith
    have hinit : f (Z a) - f xstar ≤ 64 * D * G0 := by
      have hh : f (Z a) - f xstar ≤ 128 * R * G0 := le_of_not_gt ha
      dsimp [D]
      nlinarith
    have h := trajectory_tuned_confidence (W := ℕ → Ω) (ξ := fun k (ξ : ℕ → Ω) => ξ k) (Q : Measure _) p hQ
      hf ho hG0 hG1 hG hGG hmin (Z a) (show 0 < D by dsimp [D]; positivity) hzstar
      (show 1 ≤ D * G by dsimp [D]; nlinarith) hinit (show 0 < e by dsimp [e]; positivity)
    have he : 20 * e = ε := by dsimp [e]; ring
    change (Q : Measure _) {ω | ε < f ((LongTails.Algorithms.GeneralizedLipschitzWarmStart.trajectory (Z a) D G0 α oracle ω K).2.1) - f xstar} ≤ ENNReal.ofReal (1 / 20 : ℝ)
    simpa only [he] using h
  let split := fun ξ : ℕ → Ω => ((fun i : Fin B => ξ i), (fun k => ξ (B + k)))
  have hp : MeasurePreserving split (P : Measure _) (μ.prod (Q : Measure _)) := hξ.prefix_tail_law B
  have he (ξ : ℕ → Ω) : LongTails.Algorithms.GeneralizedLipschitzConvex.output c hc center R G G0 (R * G) α T K budget
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ = Y (split ξ) := by
    rw [output_eq_burnin_warm P oracle c hc center R G G0 (R * G) α T K budget hT hbudget ξ]
    have hx : burninOutput c hc center R G G0 (R * G) T
        { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ = Z (fun i => ξ i) := by
      exact (burninOutput_law_irrel c hc center R G G0 (R * G) T oracle P Q ξ).trans (hprefix ξ).symm
    rw [hx]
  refine ⟨?_, ?_⟩
  · convert hY.comp hp.measurable using 1
    funext ξ
    exact he ξ
  · have hs : {ξ | ε < f (LongTails.Algorithms.GeneralizedLipschitzConvex.output c hc center R G G0 (R * G) α T K budget
        { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ) - f xstar} =
        split ⁻¹' {z | ε < f (Y z) - f xstar} := by
      ext ξ
      change (ε < f _ - f xstar) ↔ ε < f _ - f xstar
      rw [he ξ]
    rw [hs, hp.measure_preimage hS.nullMeasurableSet]
    exact hprod

end Confidence
end LongTails.Proofs.GeneralizedLipschitzComposition

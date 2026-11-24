import LongTails.Algorithms.StagewiseSarah
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.Execution

open MeasureTheory
open scoped ENNReal

namespace OracleTemplate.StagewiseSarah

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

section Generic

variable {C Z Ω : Type*}

def zrun (cn : C → C) (zn : C → Z → Ω → Z) : ℕ → C → Z → (ℕ → Ω) → Z
  | 0, _, z, _ => z
  | K + 1, c, z, ξ => zrun cn zn K (cn c) (zn c z (ξ 0)) (fun i => ξ (1 + i))

variable [MeasurableSpace Z] [MeasurableSpace Ω]

lemma zrun_measurable (cn : C → C) (zn : C → Z → Ω → Z)
    (hzn : ∀ c, Measurable (Function.uncurry (zn c))) (K : ℕ) (c : C) :
    Measurable (fun w : Z × (ℕ → Ω) => zrun cn zn K c w.1 w.2) := by
  induction K generalizing c with
  | zero => exact measurable_fst
  | succ K ih =>
    have h1 : Measurable (fun w : Z × (ℕ → Ω) => zn c w.1 (w.2 0)) :=
      (hzn c).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    have h2 : Measurable (fun w : Z × (ℕ → Ω) => fun i : ℕ => w.2 (1 + i)) :=
      Measurable.of_eval (fun i => (measurable_pi_apply (1 + i)).comp measurable_snd)
    exact (ih (cn c)).comp (h1.prodMk h2)

lemma headTail_preserving (p : Measure Ω) [IsProbabilityMeasure p] :
    MeasurePreserving (fun ξ : ℕ → Ω => (ξ 0, fun i : ℕ => ξ (1 + i)))
      (Measure.infinitePi fun _ : ℕ => p) (p.prod (Measure.infinitePi fun _ : ℕ => p)) := by
  have h1 := OracleTemplate.StochasticGeneralized.splitStream_preserving p 1
  have h2 := (measurePreserving_funUnique p (Fin 1)).prod
    (MeasurePreserving.id (Measure.infinitePi fun _ : ℕ => p))
  exact h2.comp h1

lemma zrun_lintegral (p : Measure Ω) [IsProbabilityMeasure p] (cn : C → C)
    (zn : C → Z → Ω → Z) (hzn : ∀ c, Measurable (Function.uncurry (zn c)))
    (Inv : C → Prop) (hInv : ∀ c, Inv c → Inv (cn c))
    (Φ : C → Z → ℝ≥0∞) (hΦ : ∀ c, Measurable (Φ c))
    (hstep : ∀ c z, Inv c → ∫⁻ ω, Φ (cn c) (zn c z ω) ∂p ≤ Φ c z)
    (K : ℕ) (c : C) (z : Z) (hc : Inv c) :
    ∫⁻ ξ, Φ (cn^[K] c) (zrun cn zn K c z ξ) ∂(Measure.infinitePi fun _ : ℕ => p) ≤ Φ c z := by
  induction K generalizing c z with
  | zero => simp [zrun]
  | succ K ih =>
    have hm : Measurable (fun w : Ω × (ℕ → Ω) =>
        Φ (cn^[K] (cn c)) (zrun cn zn K (cn c) (zn c z w.1) w.2)) := by
      have h1 : Measurable (fun w : Ω × (ℕ → Ω) => (zn c z w.1, w.2)) :=
        (((hzn c).comp (measurable_const.prodMk measurable_id)).comp measurable_fst).prodMk
          measurable_snd
      exact (hΦ _).comp ((zrun_measurable cn zn hzn K (cn c)).comp h1)
    have key : ∫⁻ ξ, Φ (cn^[K + 1] c) (zrun cn zn (K + 1) c z ξ)
        ∂(Measure.infinitePi fun _ : ℕ => p) =
        ∫⁻ w, Φ (cn^[K] (cn c)) (zrun cn zn K (cn c) (zn c z w.1) w.2)
          ∂(p.prod (Measure.infinitePi fun _ : ℕ => p)) := by
      rw [← (headTail_preserving p).lintegral_comp hm]
      rfl
    rw [key, lintegral_prod _ hm.aemeasurable]
    exact (lintegral_mono (fun ω => ih (cn c) (zn c z ω) (hInv c hc))).trans (hstep c z hc)

end Generic

section Machine

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ω : Type}

noncomputable def sampleNext (g : E → Ω → E) (c : Ctl) (z : E × E) (ω : Ω) : E × E :=
  zNext c z (g (pairQuery c z).1 ω, g (pairQuery c z).2 ω)

lemma machine_iterate (g : E → Ω → E) (ξ : ℕ → Ω) (K : ℕ) (c : Ctl) (z : E × E) (t : ℕ) :
    ((fun sc : (Ctl × (E × E)) × ℕ =>
        ((ctlNext sc.1.1, zNext sc.1.1 sc.1.2
          (g (pairQuery sc.1.1 sc.1.2).1 (ξ sc.2), g (pairQuery sc.1.1 sc.1.2).2 (ξ sc.2))),
          sc.2 + 1))^[K] ((c, z), t)) =
      ((ctlNext^[K] c, zrun ctlNext (sampleNext g) K c z (fun i => ξ (t + i))), t + K) := by
  induction K generalizing c z t with
  | zero => rfl
  | succ K ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    simp only [zrun, sampleNext, Nat.add_zero]
    have he : (fun i => ξ (t + 1 + i)) = fun i => ξ (t + (1 + i)) := by
      funext i
      rw [Nat.add_assoc]
    rw [he, Nat.add_assoc, Nat.add_comm 1 K]

lemma execute_sarah (g : E → Ω → E) [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (sched : List Epoch) (x0 : E) (K : ℕ) (seed : (sarah sched x0).Seed) (ξ : ℕ → Ω) :
    execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (E × E) (E × E)) (sarah sched x0) (fun _ => K) seed ξ =
      (zrun ctlNext (sampleNext g) K ⟨sched, 0⟩ (x0, 0) ξ).1 := by
  have h1 := execute_indexed_of_answer
    ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (E × E) (E × E)) (sarah sched x0) K seed ξ
    (fun t query => (g query.2.1 (ξ t), g query.2.2 (ξ t))) (fun _ query => by cases query; rfl)
  refine h1.trans ?_
  have h := machine_iterate g ξ K ⟨sched, 0⟩ (x0, (0 : E)) 0
  simp only [Nat.zero_add] at h
  change ((fun sc : (Ctl × (E × E)) × ℕ =>
        ((ctlNext sc.1.1, zNext sc.1.1 sc.1.2
          (g (pairQuery sc.1.1 sc.1.2).1 (ξ sc.2), g (pairQuery sc.1.1 sc.1.2).2 (ξ sc.2))),
          sc.2 + 1))^[K] ((⟨sched, 0⟩, (x0, 0)), 0)).1.2.1 = _
  rw [h]

lemma ctlNext_iterate_nil (K : ℕ) (i : ℕ) : ctlNext^[K] ⟨[], i⟩ = ⟨[], i⟩ := by
  induction K with
  | zero => rfl
  | succ K ih => rw [Function.iterate_succ_apply]; exact ih

lemma ctlNext_iterate_cost (sched : List Epoch) (hB : ∀ e ∈ sched, 1 ≤ e.B) (K : ℕ)
    (hK : cost sched ≤ K) : ctlNext^[K] ⟨sched, 0⟩ = ⟨[], 0⟩ := by
  have gen : ∀ (n : ℕ) (l : List Epoch) (i K : ℕ), (∀ e ∈ l, 1 ≤ e.B) →
      (∀ e rest, l = e :: rest → i < e.B + e.m) → (l = [] → i = 0) →
      cost l ≤ K + i → cost l ≤ n + i → ctlNext^[K] ⟨l, i⟩ = ⟨[], 0⟩ := by
    intro n
    induction n with
    | zero =>
      intro l i K hB hi h0 hK hn
      cases l with
      | nil => rw [h0 rfl]; exact ctlNext_iterate_nil K 0
      | cons e rest =>
        have := hi e rest rfl
        simp only [cost] at hn
        omega
    | succ n ih =>
      intro l i K hB hi h0 hK hn
      cases l with
      | nil => rw [h0 rfl]; exact ctlNext_iterate_nil K 0
      | cons e rest =>
        have hlt := hi e rest rfl
        simp only [cost] at hK hn
        cases K with
        | zero => omega
        | succ K =>
          rw [Function.iterate_succ_apply]
          by_cases h1 : i + 1 < e.B + e.m
          · have hstep : ctlNext ⟨e :: rest, i⟩ = ⟨e :: rest, i + 1⟩ := by
              simp only [ctlNext, h1, ↓reduceIte]
            rw [hstep]
            exact ih (e :: rest) (i + 1) K hB (fun e' rest' h => by cases h; exact h1)
              (fun h => absurd h (List.cons_ne_nil _ _))
              (by simp only [cost]; omega) (by simp only [cost]; omega)
          · have hstep : ctlNext ⟨e :: rest, i⟩ = ⟨rest, 0⟩ := by
              simp only [ctlNext, h1, ↓reduceIte]
            rw [hstep]
            exact ih rest 0 K (fun e' he' => hB e' (List.mem_cons_of_mem _ he'))
              (fun e' rest' h => by
                have := hB e' (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
                omega)
              (fun _ => rfl) (by omega) (by omega)
  exact gen (cost sched) sched 0 K hB
    (fun e' rest' h => by
      have := hB e' (by rw [h]; exact List.mem_cons_self)
      omega)
    (fun _ => rfl) (by omega) (by omega)

end Machine

end OracleTemplate.StagewiseSarah

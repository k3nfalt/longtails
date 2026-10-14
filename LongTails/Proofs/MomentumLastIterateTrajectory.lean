import LongTails.Proofs.MomentumLastIterateSample
import LongTails.Proofs.LinearDecaySgdExpectation

open MeasureTheory Set InnerProductSpace ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.MomentumConvex

open LongTails.Setups.MomentumLipschitzConvex

open OracleTemplate.SampledConvex (map_prefix_pair extend measurable_extend extend_agree)

section Prefix

variable {Ξ : Type*} [MeasurableSpace Ξ] {Y : Type*} [MeasurableSpace Y]

lemma integrable_prefix_of_bdd (p : Measure Ξ) [IsProbabilityMeasure p] (k : ℕ)
    (X : (Fin k → Ξ) → Y) (hX : Measurable X) (Φ : Y → Ξ → ℝ)
    (hΦ : Measurable (Function.uncurry Φ)) (hpos : ∀ y ω, 0 ≤ Φ y ω) (C : ℝ)
    (hb : ∀ y, Integrable (Φ y) p ∧ ∫ ω, Φ y ω ∂p ≤ C) :
    Integrable (fun ξ : ℕ → Ξ => Φ (X (fun i : Fin k => ξ i)) (ξ k))
      (Measure.infinitePi fun _ : ℕ => p) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  set π : (ℕ → Ξ) → (Fin k → Ξ) := fun ξ i => ξ i
  have hπ : Measurable π := by fun_prop
  set Q := P.map π
  have hQ : IsProbabilityMeasure Q := (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).mpr inferInstance
  have hpair : Measurable (fun ξ : ℕ → Ξ => (π ξ, ξ k)) := by fun_prop
  let H : (Fin k → Ξ) × Ξ → ℝ := fun z => Φ (X z.1) z.2
  have hH : Measurable H := hΦ.comp ((hX.comp measurable_fst).prodMk measurable_snd)
  have hHi : Integrable H (Q.prod p) := by
    rw [integrable_prod_iff hH.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun u => (hb (X u)).1), ?_⟩
    have hsm : StronglyMeasurable (fun u : Fin k → Ξ => ∫ ω, ‖H (u, ω)‖ ∂p) :=
      (hH.norm.stronglyMeasurable).integral_prod_right'
    refine Integrable.mono' (integrable_const C) hsm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun u => ?_))
    have h0 : 0 ≤ ∫ ω, ‖H (u, ω)‖ ∂p := integral_nonneg (fun ω => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have hfun : (fun ω => ‖H (u, ω)‖) = Φ (X u) := by
      funext ω
      simp only [H, Real.norm_eq_abs, abs_of_nonneg (hpos _ _)]
    rw [hfun]
    exact (hb (X u)).2
  have hmap := map_prefix_pair p k
  rw [← hmap] at hHi
  exact (integrable_map_measure hH.aestronglyMeasurable hpair.aemeasurable).mp hHi

end Prefix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]

noncomputable def traj (Gr : Ξ → E → E) (β γ : ℝ) (N : ℕ) (x0 : E) (ξ : ℕ → Ξ) : ℕ → E × E
  | 0 => (x0, 0)
  | k + 1 =>
    ((traj Gr β γ N x0 ξ k).1 - stepSize β γ N k •
        (β • (traj Gr β γ N x0 ξ k).2 + (1 - β) • Gr (ξ k) (traj Gr β γ N x0 ξ k).1),
      β • (traj Gr β γ N x0 ξ k).2 + (1 - β) • Gr (ξ k) (traj Gr β γ N x0 ξ k).1)

noncomputable def tau (N k : ℕ) : ℝ := (N : ℝ) + 1 - k

noncomputable def cw (γ κ : ℝ) (N k : ℕ) : ℝ := wt γ κ (tau N k + 1) / wt γ κ (tau N k)

noncomputable def refp (Gr : Ξ → E → E) (β γ : ℝ) (N : ℕ) (x0 xstar : E) (ξ : ℕ → Ξ) : ℕ → E
  | 0 => xstar
  | k + 1 => cw γ (β / (1 - β)) N k • refp Gr β γ N x0 xstar ξ k +
      (1 - cw γ (β / (1 - β)) N k) • (traj Gr β γ N x0 ξ k).1

noncomputable def zed (Gr : Ξ → E → E) (β γ : ℝ) (N : ℕ) (x0 : E) (ξ : ℕ → Ξ) (k : ℕ) : E :=
  (traj Gr β γ N x0 ξ k).1 - (β / (1 - β) * γ * tau N k) • (traj Gr β γ N x0 ξ k).2

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ξ] in
lemma tau_succ (N k : ℕ) : tau N (k + 1) = tau N k - 1 := by
  unfold tau; push_cast; ring

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ξ] in
lemma zed_succ (Gr : Ξ → E → E) {β : ℝ} (hβ : β < 1) (γ : ℝ) (N : ℕ) (x0 : E) (ξ : ℕ → Ξ)
    (k : ℕ) :
    zed Gr β γ N x0 ξ (k + 1) =
      zed Gr β γ N x0 ξ k - (γ * tau N k) • Gr (ξ k) (traj Gr β γ N x0 ξ k).1 := by
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  unfold zed
  simp only [traj]
  set x := (traj Gr β γ N x0 ξ k).1
  set m := (traj Gr β γ N x0 ξ k).2
  set g := Gr (ξ k) x
  rw [tau_succ]
  have ha : (stepSize β γ N k + β / (1 - β) * γ * (tau N k - 1)) * β =
      β / (1 - β) * γ * tau N k := by
    unfold stepSize tau; field_simp; ring
  have hb : (stepSize β γ N k + β / (1 - β) * γ * (tau N k - 1)) * (1 - β) = γ * tau N k := by
    unfold stepSize tau; field_simp; ring
  rw [← ha, ← hb]
  module

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ξ] in
lemma traj_prev (Gr : Ξ → E → E) (β γ : ℝ) (N : ℕ) (x0 : E) (ξ : ℕ → Ξ) (k : ℕ) :
    (traj Gr β γ N x0 ξ k).1 + (γ * (tau N k + 1 + β / (1 - β))) • (traj Gr β γ N x0 ξ k).2 =
      (traj Gr β γ N x0 ξ (k - 1)).1 := by
  cases k with
  | zero => simp [traj]
  | succ k =>
    simp only [traj, Nat.add_sub_cancel]
    have e : γ * (tau N (k + 1) + 1 + β / (1 - β)) = stepSize β γ N k := by
      rw [tau_succ]; unfold stepSize tau; ring
    rw [e]
    abel

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ξ] in
lemma traj_congr (Gr : Ξ → E → E) (β γ : ℝ) (N : ℕ) (x0 : E) {ξ ξ' : ℕ → Ξ} :
    ∀ k, (∀ i, i < k → ξ i = ξ' i) → traj Gr β γ N x0 ξ k = traj Gr β γ N x0 ξ' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hξ
    simp only [traj]
    rw [ih (fun i hi => hξ i (Nat.lt_succ_of_lt hi)), hξ k (Nat.lt_succ_self k)]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ξ] in
lemma refp_congr (Gr : Ξ → E → E) (β γ : ℝ) (N : ℕ) (x0 xstar : E) {ξ ξ' : ℕ → Ξ} :
    ∀ k, (∀ i, i < k → ξ i = ξ' i) →
      refp Gr β γ N x0 xstar ξ (k + 1) = refp Gr β γ N x0 xstar ξ' (k + 1) ∧
      refp Gr β γ N x0 xstar ξ k = refp Gr β γ N x0 xstar ξ' k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [refp, traj]
  | succ k ih =>
    intro hξ
    have h := ih (fun i hi => hξ i (Nat.lt_succ_of_lt hi))
    refine ⟨?_, h.1⟩
    simp only [refp] at h ⊢
    rw [h.1, traj_congr Gr β γ N x0 (k + 1) hξ]

omit [CompleteSpace E] in
lemma measurable_traj {Gr : Ξ → E → E} (hG : Measurable (Function.uncurry Gr)) (β γ : ℝ) (N : ℕ)
    (x0 : E) : ∀ k, Measurable (fun ξ : ℕ → Ξ => (traj Gr β γ N x0 ξ k).1) ∧
      Measurable (fun ξ : ℕ → Ξ => (traj Gr β γ N x0 ξ k).2) := by
  intro k
  induction k with
  | zero => exact ⟨measurable_const, measurable_const⟩
  | succ k ih =>
    have hg : Measurable (fun ξ : ℕ → Ξ => Gr (ξ k) (traj Gr β γ N x0 ξ k).1) :=
      hG.comp ((measurable_pi_apply k).prodMk ih.1)
    have hm : Measurable (fun ξ : ℕ → Ξ =>
        β • (traj Gr β γ N x0 ξ k).2 + (1 - β) • Gr (ξ k) (traj Gr β γ N x0 ξ k).1) :=
      (ih.2.const_smul _).add (hg.const_smul _)
    simp only [traj]
    exact ⟨ih.1.sub (hm.const_smul _), hm⟩

omit [CompleteSpace E] in
lemma measurable_refp {Gr : Ξ → E → E} (hG : Measurable (Function.uncurry Gr)) (β γ : ℝ) (N : ℕ)
    (x0 xstar : E) : ∀ k, Measurable (fun ξ : ℕ → Ξ => refp Gr β γ N x0 xstar ξ k) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    simp only [refp]
    exact (ih.const_smul _).add (((measurable_traj hG β γ N x0 k).1).const_smul _)

end OracleTemplate.MomentumConvex

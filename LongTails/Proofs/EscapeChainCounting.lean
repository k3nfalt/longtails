import LongTails.Proofs.EscapeChainInvariance
import LongTails.Proofs.EscapeChainRun
import LongTails.Proofs.EscapeChainGaps

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.EscapeChainCounting

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus EscapeChainFunction
open EscapeChainCoordinates EscapeChainCount EscapeChainOracle EscapeChainSimulator EscapeChainSmooth
open EscapeChainCertificate EscapeChainGeometry EscapeChainReveal EscapeChainHiding EscapeChainFamily
open EscapeChainInvariance EscapeChainRun EscapeChainGaps

variable {d : ℕ}

abbrev Sp (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Ctx (d : ℕ) where
  n : ℕ
  b : ℕ
  K : ℕ
  N : ℕ
  m : ℕ
  hnb : n * b ≤ d
  hb : 0 < b
  hK : 2 * K + 2 ≤ n
  A : ℝ
  r0 : ℝ
  δ0 : ℝ
  hA : 45 * 2 ^ 102 ≤ A
  hr0 : 0 < r0
  hδ0 : 0 < δ0

variable (c : Ctx d) (alg : Algorithm (Sp d) (Sp d) (Sp d))

noncomputable def U (θ : Hid c.n c.b) : ℕ → Sp d := uOf c.hnb θ
noncomputable def V (θ : Hid c.n c.b) : ℕ → Sp d := vOf c.hnb θ

lemma frameθ (θ : Hid c.n c.b) : Frame c.K (U c θ) (V c θ) :=
  frame c.hnb c.hb θ (by have := c.hK; omega)

noncomputable def ans (θ : Hid c.n c.b) (j : ℕ) (x : Sp d) (w : ℝ) : Sp d :=
  (c.δ0 / c.r0) • answerS c.K j c.A (U c θ) (V c θ) (c.r0⁻¹ • x) w

noncomputable def runJ (θ : Hid c.n c.b) (j : ℕ) (z : alg.Seed × (ℕ → ℝ)) (t : ℕ) : alg.State :=
  run alg (ans c θ j) z.1 z.2 t

noncomputable def yq (θ : Hid c.n c.b) (j : ℕ) (z : alg.Seed × (ℕ → ℝ)) (t : ℕ) : Sp d :=
  c.r0⁻¹ • (alg.query (runJ c alg θ j z t)).2

noncomputable def yo (θ : Hid c.n c.b) (j : ℕ) (z : alg.Seed × (ℕ → ℝ)) : Sp d :=
  c.r0⁻¹ • alg.output (runJ c alg θ j z c.N)

def rev (θ : Hid c.n c.b) (j l : ℕ) (z : alg.Seed × (ℕ → ℝ)) (t : ℕ) : Prop :=
  reveals c.K c.A (U c θ) (V c θ) l (yq c alg θ j z t) (z.2 t)

def Bad (θ : Hid c.n c.b) (z : alg.Seed × (ℕ → ℝ)) : Prop :=
  ∃ j ≤ c.K, (∃ t < c.N, ‖yq c alg θ j z t‖ ≤ 2 * radius c.K ∧
      ¬ Clean c.K (U c θ) (V c θ) j (yq c alg θ j z t)) ∨
    (‖yo c alg θ j z‖ ≤ radius c.K ∧ ¬ Clean c.K (U c θ) (V c θ) j (yo c alg θ j z))

def Win (θ : Hid c.n c.b) (j : ℕ) (z : alg.Seed × (ℕ → ℝ)) (t : ℕ) : Prop :=
  (j = 0 ∧ t ≤ c.m) ∨ (j ≠ 0 ∧ ∃ s < t, t ≤ s + c.m ∧ rev c alg θ j (j - 1) z s ∧
    ∀ s' < s, ¬ rev c alg θ j (j - 1) z s')

def Fast (θ : Hid c.n c.b) (j : ℕ) (z : alg.Seed × (ℕ → ℝ)) : Prop :=
  ∃ t < c.N, rev c alg θ j j z t ∧ Win c alg θ j z t

def Calm' (θ : Hid c.n c.b) (y : Sp d) (g : ℝ) : Prop :=
  ¬ ((∃ e : Sp d, ‖e‖ = 1 ∧ g < |D (objective c.K (radius c.K) (U c θ) (V c θ)) y e|) ∨
    (∃ e : Sp d, ‖e‖ = 1 ∧ Q (objective c.K (radius c.K) (U c θ) (V c θ)) y e < -(1 / 10)))

lemma scale_eq (θ : Hid c.n c.b) {j j' : ℕ} (x : Sp d) (w : ℝ)
    (h : answerS c.K j c.A (U c θ) (V c θ) (c.r0⁻¹ • x) w =
      answerS c.K j' c.A (U c θ) (V c θ) (c.r0⁻¹ • x) w) : ans c θ j x w = ans c θ j' x w := by
  unfold ans; rw [h]

lemma query_scaled (θ : Hid c.n c.b) (j : ℕ) (z : alg.Seed × (ℕ → ℝ)) (t : ℕ) :
    c.r0⁻¹ • (alg.query (run alg (ans c θ j) z.1 z.2 t)).2 = yq c alg θ j z t := rfl

lemma couple_truth (θ : Hid c.n c.b) (z : alg.Seed × (ℕ → ℝ)) (hbad : ¬ Bad c alg θ z) {j : ℕ}
    (hj : j < c.K) (hno : ∀ t < c.N, ¬ rev c alg θ j j z t) :
    ∀ t ≤ c.N, runJ c alg θ c.K z t = runJ c alg θ j z t := by
  apply run_couple
  intro t ht
  apply scale_eq
  rw [query_scaled, answerS_full]
  by_cases hy : 2 * radius c.K ≤ ‖yq c alg θ j z t‖
  · rw [← answerS_full, answerS_outside _ _ _ _ _ _ _ hy, answerS_outside _ _ _ _ _ _ _ hy]
  · push Not at hy
    have hc : Clean c.K (U c θ) (V c θ) j (yq c alg θ j z t) := by
      by_contra hc
      exact hbad ⟨j, hj.le, Or.inl ⟨t, ht, hy.le, hc⟩⟩
    exact answer_eq_sim c.A (U c θ) (V c θ) hj.le _ _ hc (fun _ => hno t ht)

lemma couple_next (θ : Hid c.n c.b) (z : alg.Seed × (ℕ → ℝ)) (hbad : ¬ Bad c alg θ z) {j T : ℕ}
    (hj : j < c.K) (hT : T ≤ c.N) (hno : ∀ t < T, ¬ rev c alg θ j j z t) :
    ∀ t ≤ T, runJ c alg θ (j + 1) z t = runJ c alg θ j z t := by
  apply run_couple
  intro t ht
  apply scale_eq
  rw [query_scaled]
  by_cases hy : 2 * radius c.K ≤ ‖yq c alg θ j z t‖
  · rw [answerS_outside _ _ _ _ _ _ _ hy, answerS_outside _ _ _ _ _ _ _ hy]
  · push Not at hy
    have hc : Clean c.K (U c θ) (V c θ) j (yq c alg θ j z t) := by
      by_contra hc
      exact hbad ⟨j, hj.le, Or.inl ⟨t, by omega, hy.le, hc⟩⟩
    apply answerS_step
    left
    refine ⟨?_, hno t ht⟩
    have := (hc j le_rfl hj).2
    linarith [clean_sq this]

lemma clean_dead {K : ℕ} {u v : ℕ → Sp d} {j : ℕ} {y : Sp d} (h : Clean K u v j y) :
    ∀ l, j ≤ l → l < K → dead u v l y := by
  intro l hl hlK
  obtain ⟨ha, hc⟩ := h l hl hlK
  exact ⟨by linarith [le_abs_self ⟪u l, y⟫], by nlinarith [clean_sq hc]⟩

lemma not_calm (θ : Hid c.n c.b) {g : ℝ} (hg0 : 0 < g) (hg : g ≤ 1 / 2 ^ 30) {j : ℕ} (hj : j < c.K)
    (y : Sp d) (hy : ‖y‖ ≤ radius c.K → Clean c.K (U c θ) (V c θ) j y) : ¬ Calm' c θ y g := by
  intro hcalm
  apply hcalm
  by_cases hr : ‖y‖ ≤ radius c.K
  · exact certificate (frameθ c θ) hg0 hg y hj (clean_dead (hy hr))
  · push Not at hr
    left
    have hxp : 0 < ‖y‖ := (radius_pos c.K).trans hr
    refine ⟨(‖y‖⁻¹) • y, ?_, radial (frameθ c θ) (hg.trans (by norm_num)) y hr⟩
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hxp.ne']

open Classical in
theorem many_fast (θ : Hid c.n c.b) (z : alg.Seed × (ℕ → ℝ)) (hbad : ¬ Bad c alg θ z) {g : ℝ}
    (hg0 : 0 < g) (hg : g ≤ 1 / 2 ^ 30) (hcalm : Calm' c θ (yo c alg θ c.K z) g) (hK : 0 < c.K)
    (hm : 2 * c.N ≤ (c.m + 1) * c.K) :
    c.K < 2 * ((Finset.range c.K).filter (fun j => Fast c alg θ j z)).card := by
  classical
  have hall : ∀ j < c.K, ∃ t, t < c.N ∧ rev c alg θ j j z t := by
    intro j hj
    by_contra hno
    push Not at hno
    have hrun := couple_truth c alg θ z hbad hj (fun t ht h => hno t ht h)
    have hyo : yo c alg θ c.K z = yo c alg θ j z := by unfold yo; rw [hrun c.N le_rfl]
    rw [hyo] at hcalm
    refine not_calm c θ hg0 hg hj _ (fun hr => ?_) hcalm
    by_contra hc
    exact hbad ⟨j, hj.le, Or.inr ⟨hr, hc⟩⟩
  let τ : ℕ → ℕ := fun j => if h : j < c.K then Nat.find (hall j h) else 0
  have hspec : ∀ j (hj : j < c.K), τ j < c.N ∧ rev c alg θ j j z (τ j) ∧
      ∀ t < τ j, ¬ rev c alg θ j j z t := by
    intro j hj
    have h1 := Nat.find_spec (hall j hj)
    have hτ : τ j = Nat.find (hall j hj) := by simp [τ, hj]
    refine ⟨hτ ▸ h1.1, hτ ▸ h1.2, fun t ht hrt => ?_⟩
    rw [hτ] at ht
    exact Nat.find_min (hall j hj) ht ⟨lt_trans ht h1.1, hrt⟩
  have hcouple : ∀ j (hj : j < c.K), ∀ t ≤ τ j, runJ c alg θ (j + 1) z t = runJ c alg θ j z t :=
    fun j hj => couple_next c alg θ z hbad hj (hspec j hj).1.le (hspec j hj).2.2
  have hyq : ∀ j (hj : j < c.K), ∀ t ≤ τ j, yq c alg θ (j + 1) z t = yq c alg θ j z t := by
    intro j hj t ht; unfold yq; rw [hcouple j hj t ht]
  have hsame : ∀ j (hj : j < c.K), ∀ t ≤ τ j, rev c alg θ (j + 1) j z t ↔ rev c alg θ j j z t := by
    intro j hj t ht; unfold rev; rw [hyq j hj t ht]
  have hnorev : ∀ j (hj : j + 1 < c.K), ∀ t ≤ τ j, ¬ rev c alg θ (j + 1) (j + 1) z t := by
    intro j hj t ht
    unfold rev
    rw [hyq j (by omega) t ht]
    by_cases hy : 2 * radius c.K ≤ ‖yq c alg θ j z t‖
    · intro h
      unfold reveals at h
      rw [prob_outside c.A (U c θ) (V c θ) (j + 1) _ hy, add_zero] at h
      linarith [h.1, h.2]
    · push Not at hy
      have hc : Clean c.K (U c θ) (V c θ) j (yq c alg θ j z t) := by
        by_contra hc
        exact hbad ⟨j, by omega, Or.inl ⟨t, lt_of_le_of_lt ht (hspec j (by omega)).1, hy.le, hc⟩⟩
      exact no_reveal_of_clean c.A (U c θ) (V c θ) _ _ hc hj
  have hinc : ∀ j, j + 1 < c.K → τ j < τ (j + 1) := by
    intro j hj
    by_contra h
    push Not at h
    exact hnorev j hj (τ (j + 1)) h (hspec (j + 1) hj).2.1
  have hlast : τ (c.K - 1) < c.N := (hspec (c.K - 1) (by omega)).1
  have hgaps := many_small_gaps τ hK hinc hlast hm
  refine lt_of_lt_of_le hgaps (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
  intro j hj
  obtain ⟨hjK, hgap⟩ := Finset.mem_filter.1 hj
  have hjK' := Finset.mem_range.1 hjK
  refine Finset.mem_filter.2 ⟨hjK, τ j, (hspec j hjK').1, (hspec j hjK').2.1, ?_⟩
  cases j with
  | zero => exact Or.inl ⟨rfl, by simpa [gap] using hgap⟩
  | succ j' =>
    right
    have hj' : j' < c.K := by omega
    refine ⟨Nat.succ_ne_zero _, τ j', hinc j' hjK', ?_, ?_, ?_⟩
    · simp only [gap] at hgap; omega
    · simpa using (hsame j' hj' (τ j') le_rfl).2 (hspec j' hj').2.1
    · intro s' hs' hr
      simp only [Nat.add_sub_cancel] at hr
      exact (hspec j' hj').2.2 s' hs' ((hsame j' hj' s' hs'.le).1 hr)

end LongTails.Proofs.EscapeChainCounting

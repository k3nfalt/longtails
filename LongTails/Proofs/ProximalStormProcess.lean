import LongTails.Proofs.ProximalStormBlock

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.ProximalStorm

lemma sum_update_eq {K W : ℕ} (k : Fin K) (h : (Fin K → Fin W) → ℝ≥0∞) :
    ∑ σ : Fin K → Fin W, ∑ j : Fin W, h (Function.update σ k j) = W * ∑ σ, h σ := by
  set e := Equiv.funSplitAt k (Fin W)
  have he : ∀ σ j, Function.update σ k j = e.symm (j, (e σ).2) := by
    intro σ j
    apply e.injective
    rw [Equiv.apply_symm_apply]
    simp only [e, Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_mk, Function.update_self,
      Prod.mk.injEq, true_and]
    funext i
    exact Function.update_of_ne i.2 _ _
  simp_rw [he]
  rw [← e.symm.sum_comp (fun σ => ∑ j, h (e.symm (j, (e σ).2)))]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← e.symm.sum_comp h, Fintype.sum_prod_type, Finset.sum_comm]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]

noncomputable def outerRun (g : E → Ω → E) (lam eta a : ℝ) (T0 W B : ℕ) (x0 : E) (τ : ℕ → ℕ)
    (ξ : ℕ → Ω) : ℕ → ℝ × E × E
  | 0 => (0, x0, x0)
  | k + 1 => blockStep g lam eta a T0 W B (τ k) (k * (B + (T0 + W)))
      (outerRun g lam eta a T0 W B x0 τ ξ k) ξ

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma outerRun_fst (g : E → Ω → E) (lam eta a : ℝ) (T0 W B : ℕ) (x0 : E) (τ : ℕ → ℕ)
    (ξ : ℕ → Ω) : ∀ k, (outerRun g lam eta a T0 W B x0 τ ξ k).1 = accA lam k
  | 0 => rfl
  | k + 1 => by
      simp only [outerRun, blockStep, accA]
      rw [outerRun_fst g lam eta a T0 W B x0 τ ξ k]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma outerRun_congr_tau (g : E → Ω → E) (lam eta a : ℝ) (T0 W B : ℕ) (x0 : E) {τ τ' : ℕ → ℕ}
    (ξ : ℕ → Ω) : ∀ k, (∀ i, i < k → τ i = τ' i) →
      outerRun g lam eta a T0 W B x0 τ ξ k = outerRun g lam eta a T0 W B x0 τ' ξ k
  | 0, _ => rfl
  | k + 1, h => by
      simp only [outerRun]
      rw [outerRun_congr_tau g lam eta a T0 W B x0 ξ k fun i hi => h i (by omega),
        h k (by omega)]

omit [CompleteSpace E] in
lemma measurable_outerRun {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (lam eta a : ℝ) (T0 W B : ℕ) (x0 : E) (τ : ℕ → ℕ) :
    ∀ k, Measurable fun ξ => outerRun g lam eta a T0 W B x0 τ ξ k
  | 0 => measurable_const
  | k + 1 => by
      have hO := measurable_outerRun hg lam eta a T0 W B x0 τ k
      simp only [outerRun]
      unfold blockStep
      have hfst : Measurable fun ξ => (outerRun g lam eta a T0 W B x0 τ ξ k).1 := hO.fst
      have hA : (fun ξ => (outerRun g lam eta a T0 W B x0 τ ξ k).1) = fun _ => accA lam k := by
        funext ξ; exact outerRun_fst g lam eta a T0 W B x0 τ ξ k
      simp only [outerRun_fst]
      have hmx : Measurable fun ξ => mixPt lam (accA lam k) (outerRun g lam eta a T0 W B x0 τ ξ k).2.1
          (outerRun g lam eta a T0 W B x0 τ ξ k).2.2 := by
        unfold mixPt
        exact ((hO.snd.fst).const_smul _).add ((hO.snd.snd).const_smul _)
      have hy := (measurable_innerRun hg lam eta a hmx (k * (B + (T0 + W))) (T0 + τ k)).fst
      exact measurable_const.prodMk (hy.prodMk (hO.snd.snd.sub
        ((measurable_batchSum hg hy _ _).const_smul _)))

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma outerRun_dep (g : E → Ω → E) (lam eta a : ℝ) (T0 W B : ℕ) (x0 : E) {τ : ℕ → ℕ}
    (hτ : ∀ i, τ i < W) : ∀ k, ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k * (B + (T0 + W)) → ξ i = ξ' i) →
      outerRun g lam eta a T0 W B x0 τ ξ k = outerRun g lam eta a T0 W B x0 τ ξ' k
  | 0, _, _, _ => rfl
  | k + 1, ξ, ξ', h => by
      have hk := outerRun_dep g lam eta a T0 W B x0 hτ k ξ ξ' fun i hi => h i (by nlinarith)
      have hτk := hτ k
      simp only [outerRun, blockStep]
      rw [hk]
      set o := outerRun g lam eta a T0 W B x0 τ ξ' k
      set n := k * (B + (T0 + W))
      have hlen : (k + 1) * (B + (T0 + W)) = n + (B + (T0 + W)) := by
        simp only [n]; ring
      rw [hlen] at h
      have hXdep : ∀ ζ ζ' : ℕ → Ω, (∀ i, i < n → ζ i = ζ' i) →
          (fun _ : ℕ → Ω => mixPt lam o.1 o.2.1 o.2.2) ζ =
            (fun _ : ℕ → Ω => mixPt lam o.1 o.2.1 o.2.2) ζ' := fun _ _ _ => rfl
      have hin := innerRun_congr g lam eta a hXdep (T0 + τ k) ξ ξ' fun i hi => h i (by omega)
      have hbs : batchSum g (innerRun g lam eta a (mixPt lam o.1 o.2.1 o.2.2) ξ n (T0 + τ k)).1 ξ
          (n + T0 + W) B = batchSum g (innerRun g lam eta a (mixPt lam o.1 o.2.1 o.2.2) ξ' n
            (T0 + τ k)).1 ξ' (n + T0 + W) B := by
        rw [hin]
        unfold batchSum
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.mp hi
        rw [h (n + T0 + W + i) (by omega)]
      rw [hbs, hin]

lemma seedIndex_lt {K W : ℕ} (σ : Fin K → Fin W) (hW : 0 < W) (i : ℕ) : seedIndex σ i < W := by
  unfold seedIndex; split_ifs
  · exact (σ _).isLt
  · exact hW

lemma seedIndex_update {K W : ℕ} (σ : Fin K → Fin W) (κ : Fin K) (j : Fin W) (i : ℕ)
    (hi : i < κ.val) : seedIndex (Function.update σ κ j) i = seedIndex σ i := by
  unfold seedIndex
  have hiK : i < K := hi.trans κ.isLt
  simp only [hiK, dite_true]
  rw [Function.update_of_ne]
  intro h
  have := congrArg Fin.val h
  simp at this; omega

lemma seedIndex_update_self {K W : ℕ} (σ : Fin K → Fin W) (κ : Fin K) (j : Fin W) :
    seedIndex (Function.update σ κ j) κ.val = j.val := by
  unfold seedIndex
  simp only [κ.isLt, dite_true, Fin.eta, Function.update_self]

section Bound

variable {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E}
  {Lbar Γ : ℝ} {xstar : E}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

theorem Hyp.process_bound (H : Hyp p f g Lbar Γ xstar) {Γh : ℝ} (hΓ : 1 ≤ Γh) (hΓΓ : Γ ≤ Γh)
    {B : ℕ} (hB1 : 1 ≤ B) (hB : 6 * Γ ^ 2 ≤ B) {Wm : ℕ} (hW : 800 * Γh ^ 2 ≤ ((Wm + 1 : ℕ) : ℝ))
    (x0 : E)
    (K : ℕ) : ∀ k, k ≤ K →
    ∑ σ : Fin K → Fin (Wm + 1), ∫⁻ ξ, ENNReal.ofReal (outerPot f xstar
        (outerRun g (pLam Lbar Γh) (pEta Lbar Γh) (pA Γh) (pT0 Γh) (Wm + 1) B x0 (seedIndex σ) ξ k)) ∂P ≤
      (Fintype.card (Fin K → Fin (Wm + 1)) : ℝ≥0∞) * ENNReal.ofReal (outerPot f xstar (0, x0, x0))
  | 0, _ => by
      simp only [outerRun, lintegral_const, measure_univ, mul_one, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      exact le_rfl
  | k + 1, hk => by
      have ih := H.process_bound hΓ hΓΓ hB1 hB hW x0 K k (by omega)
      set κ : Fin K := ⟨k, by omega⟩
      set lam := pLam Lbar Γh
      set eta := pEta Lbar Γh
      set a := pA Γh
      set T0 := pT0 Γh
      set W := Wm + 1
      have hlam : 0 < lam := (tune_inner H.Lbar_pos hΓ).lam_pos
      set h : (Fin K → Fin (Wm + 1)) → ℝ≥0∞ := fun σ => ∫⁻ ξ, ENNReal.ofReal (outerPot f xstar
        (outerRun g lam eta a T0 W B x0 (seedIndex σ) ξ (k + 1))) ∂P
      have hsu := sum_update_eq κ h
      have hWpos : 0 < W := by omega
      have hblk : ∀ σ : Fin K → Fin (Wm + 1), ∑ j : Fin (Wm + 1), h (Function.update σ κ j) ≤
          (W : ℝ≥0∞) * ∫⁻ ξ, ENNReal.ofReal (outerPot f xstar
            (outerRun g lam eta a T0 W B x0 (seedIndex σ) ξ k)) ∂P := by
        intro σ
        have heq : ∀ j : Fin (Wm + 1), h (Function.update σ κ j) =
            ∫⁻ ξ, ENNReal.ofReal (outerPot f xstar (blockStep g lam eta a T0 W B j.val
              (k * (B + (T0 + W))) (outerRun g lam eta a T0 W B x0 (seedIndex σ) ξ k) ξ)) ∂P := by
          intro j
          have hc : ∀ ξ, outerRun g lam eta a T0 W B x0 (seedIndex (Function.update σ κ j)) ξ k =
              outerRun g lam eta a T0 W B x0 (seedIndex σ) ξ k := fun ξ =>
            outerRun_congr_tau g lam eta a T0 W B x0 _ k (fun i hi => seedIndex_update σ κ j i hi)
          have hs : seedIndex (Function.update σ κ j) k = j.val := seedIndex_update_self σ κ j
          simp only [h, outerRun, hs]
          simp_rw [hc]
        simp_rw [heq]
        rw [Fin.sum_univ_eq_sum_range (fun j => ∫⁻ ξ, ENNReal.ofReal (outerPot f xstar
          (blockStep g lam eta a T0 W B j (k * (B + (T0 + W)))
            (outerRun g lam eta a T0 W B x0 (seedIndex σ) ξ k) ξ)) ∂P)]
        have hτ : ∀ i, seedIndex σ i < W := fun i => seedIndex_lt σ (by omega) i
        exact H.block_le hΓ hΓΓ hW hB1 hB (measurable_outerRun H.meas lam eta a T0 W B x0 _ k)
          (outerRun_dep g lam eta a T0 W B x0 hτ k) (accA_nonneg hlam k)
          (fun ξ => outerRun_fst g lam eta a T0 W B x0 _ ξ k)
      have hcard : ((Wm + 1 : ℕ) : ℝ≥0∞) = W := rfl
      have hle : (W : ℝ≥0∞) * ∑ σ, h σ ≤ (W : ℝ≥0∞) *
          ((Fintype.card (Fin K → Fin (Wm + 1)) : ℝ≥0∞) *
            ENNReal.ofReal (outerPot f xstar (0, x0, x0))) := by
        rw [← hcard, ← hsu, hcard]
        calc ∑ σ, ∑ j : Fin (Wm + 1), h (Function.update σ κ j)
            ≤ ∑ σ : Fin K → Fin (Wm + 1), (W : ℝ≥0∞) * ∫⁻ ξ, ENNReal.ofReal (outerPot f xstar
                (outerRun g lam eta a T0 W B x0 (seedIndex σ) ξ k)) ∂P :=
              Finset.sum_le_sum fun σ _ => hblk σ
          _ = (W : ℝ≥0∞) * ∑ σ : Fin K → Fin (Wm + 1), ∫⁻ ξ, ENNReal.ofReal (outerPot f xstar
                (outerRun g lam eta a T0 W B x0 (seedIndex σ) ξ k)) ∂P := by rw [Finset.mul_sum]
          _ ≤ _ := by gcongr
      exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).mp hle

end Bound

end OracleTemplate.ProximalStorm

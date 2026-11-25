import LongTails.Proofs.NcConcaveStage
import LongTails.Proofs.AbcLowerMeasure

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveReply

open LongTails.Proofs.NcConcaveInstance LongTails.Proofs.NcConcaveModel
open LongTails.Proofs.NcConcaveLocality LongTails.Proofs.NcConcaveChainGrad
open LongTails.Proofs.NcConcaveEmbed LongTails.Proofs.NcConcaveStage
open LongTails.Proofs.AbcHardOracle (coin unif coin_integrable coin_integral coin_sq_integral setOf_le_measurable coin_measurable)

variable {n m : ℕ}

noncomputable def knownC (θ τ : ℝ) (r : ℕ) (c : CS n m) : CS n m := prC r (gradC θ τ (prC r c))

lemma prC_eU (r : ℕ) (j : Fin (n + 1)) : prC r (eU (m := m) j) = if pU m j < r then eU j else 0 := by
  rw [prC_apply]
  split_ifs with h
  · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only [eU]
    · funext j'; simp only [prU]; split_ifs with h' <;> simp [Pi.single_apply]
      intro hj; subst hj; exact absurd h h'
    · funext i; simp [prA]
    · funext i; simp [prB]
    · funext i k; simp [prY]
  · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only [eU, Prod.fst_zero, Prod.snd_zero]
    · funext j'; simp only [prU, Pi.zero_apply]; split_ifs with h' <;> simp [Pi.single_apply]
      intro hj; subst hj; exact absurd h' h
    · funext i; simp [prA]
    · funext i; simp [prB]
    · funext i k; simp [prY]

lemma prC_eA (r : ℕ) (i : Fin n) : prC r (eA (m := m) i) = if pA m i < r then eA i else 0 := by
  rw [prC_apply]
  split_ifs with h
  · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only [eA]
    · funext j; simp [prU]
    · funext i'; simp only [prA]; split_ifs with h' <;> simp [Pi.single_apply]
      intro hi; subst hi; exact absurd h h'
    · funext i; simp [prB]
    · funext i k; simp [prY]
  · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only [eA, Prod.fst_zero, Prod.snd_zero]
    · funext j; simp [prU]
    · funext i'; simp only [prA, Pi.zero_apply]; split_ifs with h' <;> simp [Pi.single_apply]
      intro hi; subst hi; exact absurd h' h
    · funext i; simp [prB]
    · funext i k; simp [prY]

lemma prC_eB (r : ℕ) (i : Fin n) : prC r (eB (m := m) i) = if pB m i < r then eB i else 0 := by
  rw [prC_apply]
  split_ifs with h
  · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only [eB]
    · funext j; simp [prU]
    · funext i; simp [prA]
    · funext i'; simp only [prB]; split_ifs with h' <;> simp [Pi.single_apply]
      intro hi; subst hi; exact absurd h h'
    · funext i k; simp [prY]
  · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only [eB, Prod.fst_zero, Prod.snd_zero]
    · funext j; simp [prU]
    · funext i; simp [prA]
    · funext i'; simp only [prB, Pi.zero_apply]; split_ifs with h' <;> simp [Pi.single_apply]
      intro hi; subst hi; exact absurd h' h
    · funext i k; simp [prY]

lemma prC_eY (r : ℕ) (i : Fin n) (k : Fin (m + 1)) :
    prC r (eY i k) = if pY m i k < r then eY i k else 0 := by
  rw [prC_apply]
  split_ifs with h
  · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only [eY]
    · funext j; simp [prU]
    · funext i; simp [prA]
    · funext i; simp [prB]
    · funext i' k'; simp only [prY]; split_ifs with h'
      · rfl
      · by_cases hi : i' = i
        · subst hi
          by_cases hk : k' = k
          · subst hk; exact absurd h h'
          · simp [hk]
        · simp [hi]
  · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only [eY, Prod.fst_zero, Prod.snd_zero]
    · funext j; simp [prU]
    · funext i; simp [prA]
    · funext i; simp [prB]
    · funext i' k'; simp only [prY, Pi.zero_apply]; split_ifs with h'
      · by_cases hi : i' = i
        · subst hi
          by_cases hk : k' = k
          · subst hk; exact absurd h' h
          · simp [hk]
        · simp [hi]
      · rfl

theorem gradC_local {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) {s : ℕ} (c : CS n m)
    (hc : SmallFrom (θ / 2) s c) : gradC θ τ c = knownC θ τ (s + 1) c := by
  have h := DFc_local (τ := τ) hθ hθ1 hτ c hc
  unfold knownC gradC
  rw [prC_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext j; simp only [prU]
    rw [h, ContinuousLinearMap.comp_apply, prC_eU]
    split_ifs <;> simp
  · funext i; simp only [prA]
    rw [h, ContinuousLinearMap.comp_apply, prC_eA]
    split_ifs <;> simp
  · funext i; simp only [prB]
    rw [h, ContinuousLinearMap.comp_apply, prC_eB]
    split_ifs <;> simp
  · funext i k; simp only [prY]
    rw [h, ContinuousLinearMap.comp_apply, prC_eY]
    split_ifs <;> simp

lemma prC_K (c : CS n m) : prC (K n m) c = c := by
  rw [prC_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext j; simp [prU, pU_lt j]
  · funext i; simp [prA, pA_lt i]
  · funext i; simp [prB, pB_lt i]
  · funext i k; simp [prY, pY_lt i k]

lemma known_full (θ τ : ℝ) (c : CS n m) : knownC θ τ (K n m) c = gradC θ τ c := by
  simp only [knownC, prC_K]

lemma stage_le_of_small {θ : ℝ} (c : CS n m) (s : ℕ) (h : SmallFrom θ s c) : stage θ c ≤ s := by
  unfold stage stageUpTo
  simp only [max_le_iff]
  have key : ∀ {ι : Type} [Fintype ι] (pos : ι → ℕ) (val : ι → ℝ),
      (∀ i, s ≤ pos i → |val i| ≤ θ) → famSup θ (K n m) pos val ≤ s := by
    intro ι _ pos val hv
    apply Finset.sup_le; intro i _
    split_ifs with hi
    · by_contra hc; push Not at hc
      have := hv i (by omega); linarith [hi.2]
    · exact Nat.zero_le _
  exact ⟨⟨key _ _ h.hu, key _ _ h.ha⟩, key _ _ h.hb,
    key (fun p : Fin n × Fin (m + 1) => pY m p.1 p.2) (fun p => c.2.2.2 p.1 p.2)
      (fun (p : Fin n × Fin (m + 1)) hp => h.hy p.1 p.2 hp)⟩

lemma smallFrom_mono {θ : ℝ} {s s' : ℕ} (c : CS n m) (h : SmallFrom θ s c) (hs : s ≤ s') :
    SmallFrom θ s' c :=
  ⟨fun j hj => h.hu j (by omega), fun i hi => h.ha i (by omega), fun i hi => h.hb i (by omega),
    fun i k hk => h.hy i k (by omega)⟩

noncomputable def replyC (θ τ p : ℝ) (c : CS n m) (ξ : ℝ) : CS n m :=
  if maskedPos m n (stage (θ / 2) c) then
    knownC θ τ (stage (θ / 2) c) c + coin p ξ • (gradC θ τ c - knownC θ τ (stage (θ / 2) c) c)
  else gradC θ τ c

noncomputable def simReplyC (θ τ p : ℝ) (r : ℕ) (c : CS n m) (ξ : ℝ) : CS n m :=
  if stageUpTo (θ / 2) r c < r then
    (if maskedPos m n (stageUpTo (θ / 2) r c) then
      knownC θ τ (stageUpTo (θ / 2) r c) c + coin p ξ •
        (knownC θ τ (stageUpTo (θ / 2) r c + 1) c - knownC θ τ (stageUpTo (θ / 2) r c) c)
    else knownC θ τ (stageUpTo (θ / 2) r c + 1) c)
  else knownC θ τ (stageUpTo (θ / 2) r c) c

noncomputable def levelStep (n m : ℕ) (p : ℝ) (lev : ℕ) (ξ : ℝ) : ℕ :=
  if lev < K n m then (if maskedPos m n lev then (if ξ ≤ p then lev + 1 else lev) else lev + 1)
  else lev

lemma levelStep_ge (p : ℝ) (lev : ℕ) (ξ : ℝ) : lev ≤ levelStep n m p lev ξ := by
  unfold levelStep; split_ifs <;> omega

lemma levelStep_le (p : ℝ) (lev : ℕ) (ξ : ℝ) (h : lev ≤ K n m) : levelStep n m p lev ξ ≤ K n m := by
  unfold levelStep; split_ifs <;> omega

theorem reply_eq_sim {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (p : ℝ) (lev : ℕ)
    (hlev : lev ≤ K n m) (c : CS n m) (hsmall : SmallFrom (θ / 2) lev c) (ξ : ℝ) :
    replyC θ τ p c ξ = simReplyC θ τ p (levelStep n m p lev ξ) c ξ := by
  set st := stage (θ / 2) c with hstdef
  set r := levelStep n m p lev ξ with hr
  have hst : st ≤ lev := stage_le_of_small c lev hsmall
  have hlr : lev ≤ r := levelStep_ge p lev ξ
  have hrK : r ≤ K n m := levelStep_le p lev ξ hlev
  have hsu : stageUpTo (θ / 2) r c = st :=
    stageUpTo_eq_stage r c hrK (smallFrom_mono c hsmall hlr)
  have hfull : gradC θ τ c = knownC θ τ (st + 1) c :=
    gradC_local hθ hθ1 hτ c (smallFrom_stage c st le_rfl)
  unfold replyC simReplyC
  rw [hsu, ← hstdef]
  by_cases hlt : st < r
  · rw [ite_eq_left hlt]
    by_cases hm : maskedPos m n st
    · rw [ite_eq_left hm, ite_eq_left hm, hfull]
    · rw [ite_eq_right hm, ite_eq_right hm, hfull]
  · rw [ite_eq_right hlt]
    have hst' : st = lev := by omega
    have hr' : r = lev := by omega
    by_cases hK : lev < K n m
    · have hr2 := hr'
      simp only [hr, levelStep, ite_eq_left hK] at hr2
      by_cases hm : maskedPos m n lev
      · rw [ite_eq_left hm] at hr2
        by_cases hξ : ξ ≤ p
        · rw [ite_eq_left hξ] at hr2; omega
        · rw [← hst'] at hm
          rw [ite_eq_left hm]
          have : coin p ξ = 0 := by simp [coin, hξ]
          rw [this, zero_smul, add_zero]
      · rw [ite_eq_right hm] at hr2; omega
    · have hl : lev = K n m := by omega
      have hm : ¬ maskedPos m n st := by rw [hst', hl]; exact not_masked_K
      rw [ite_eq_right hm, hst', hl, known_full]

end LongTails.Proofs.NcConcaveReply

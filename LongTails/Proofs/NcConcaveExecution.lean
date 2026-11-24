import LongTails.Proofs.NcConcaveSecret

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveExecution

open LongTails.Proofs.NcConcaveInstance LongTails.Proofs.NcConcaveModel
open LongTails.Proofs.NcConcaveLocality LongTails.Proofs.NcConcaveChainGrad
open LongTails.Proofs.NcConcavePartThree LongTails.Proofs.NcConcaveEmbed
open LongTails.Proofs.NcConcaveStage LongTails.Proofs.NcConcaveReply LongTails.Proofs.NcConcaveValue
open LongTails.Proofs.NcConcaveOracle LongTails.Proofs.NcConcaveSecret
open LongTails.Proofs.AbcHardOracle (coin unif coin_integrable coin_integral coin_sq_integral setOf_le_measurable coin_measurable)
open LongTails.Proofs.AbcHardExecution (coinCount)
open LongTails.Setups.StochasticNonconvexConcaveMinimax

variable {d n m : ℕ}

structure SuppBelow (r : ℕ) (v : CS n m) : Prop where
  hu : ∀ j : Fin (n + 1), r ≤ pU m j → v.1 j = 0
  ha : ∀ i : Fin n, r ≤ pA m i → v.2.1 i = 0
  hb : ∀ i : Fin n, r ≤ pB m i → v.2.2.1 i = 0
  hy : ∀ (i : Fin n) (k : Fin (m + 1)), r ≤ pY m i k → v.2.2.2 i k = 0

lemma suppBelow_prC (r : ℕ) (v : CS n m) : SuppBelow r (prC r v) := by
  rw [prC_apply]
  exact ⟨fun j h => by simp only [prU]; rw [ite_eq_right (by omega)],
    fun i h => by simp only [prA]; rw [ite_eq_right (by omega)],
    fun i h => by simp only [prB]; rw [ite_eq_right (by omega)],
    fun i k h => by simp only [prY]; rw [ite_eq_right (by omega)]⟩

lemma suppBelow_mono {r r' : ℕ} {v : CS n m} (h : SuppBelow r v) (hr : r ≤ r') : SuppBelow r' v :=
  ⟨fun j hj => h.hu j (by omega), fun i hi => h.ha i (by omega), fun i hi => h.hb i (by omega),
    fun i k hk => h.hy i k (by omega)⟩

lemma suppBelow_add {r : ℕ} {v w : CS n m} (hv : SuppBelow r v) (hw : SuppBelow r w) :
    SuppBelow r (v + w) :=
  ⟨fun j h => by simp [hv.hu j h, hw.hu j h], fun i h => by simp [hv.ha i h, hw.ha i h],
    fun i h => by simp [hv.hb i h, hw.hb i h], fun i k h => by simp [hv.hy i k h, hw.hy i k h]⟩

lemma suppBelow_smul {r : ℕ} {v : CS n m} (a : ℝ) (hv : SuppBelow r v) : SuppBelow r (a • v) :=
  ⟨fun j h => by simp [hv.hu j h], fun i h => by simp [hv.ha i h], fun i h => by simp [hv.hb i h],
    fun i k h => by simp [hv.hy i k h]⟩

lemma suppBelow_sub {r : ℕ} {v w : CS n m} (hv : SuppBelow r v) (hw : SuppBelow r w) :
    SuppBelow r (v - w) := by
  rw [sub_eq_add_neg, show -w = (-1 : ℝ) • w by simp]
  exact suppBelow_add hv (suppBelow_smul _ hw)

lemma suppBelow_known (θ τ : ℝ) (r : ℕ) (c : CS n m) : SuppBelow r (knownC θ τ r c) :=
  suppBelow_prC r _

lemma simReplyC_supp (θ τ p : ℝ) (r : ℕ) (c : CS n m) (ξ : ℝ) :
    SuppBelow r (simReplyC θ τ p r c ξ) := by
  unfold simReplyC
  set st := stageUpTo (θ / 2) r c
  have hst : st ≤ r := stageUpTo_le _ r c
  split_ifs with hlt hm
  · exact suppBelow_add (suppBelow_mono (suppBelow_known θ τ st c) hst)
      (suppBelow_smul _ (suppBelow_sub (suppBelow_mono (suppBelow_known θ τ (st + 1) c) (by omega))
        (suppBelow_mono (suppBelow_known θ τ st c) hst)))
  · exact suppBelow_mono (suppBelow_known θ τ (st + 1) c) (by omega)
  · exact suppBelow_mono (suppBelow_known θ τ st c) hst

structure AgreeBelow (r : ℕ) (c c' : CS n m) : Prop where
  hu : ∀ j : Fin (n + 1), pU m j < r → c.1 j = c'.1 j
  ha : ∀ i : Fin n, pA m i < r → c.2.1 i = c'.2.1 i
  hb : ∀ i : Fin n, pB m i < r → c.2.2.1 i = c'.2.2.1 i
  hy : ∀ (i : Fin n) (k : Fin (m + 1)), pY m i k < r → c.2.2.2 i k = c'.2.2.2 i k

lemma prC_congr {r : ℕ} {c c' : CS n m} (h : AgreeBelow r c c') : prC r c = prC r c' := by
  rw [prC_apply, prC_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext j; simp only [prU]; split_ifs with hj
    · exact h.hu j hj
    · rfl
  · funext i; simp only [prA]; split_ifs with hi
    · exact h.ha i hi
    · rfl
  · funext i; simp only [prB]; split_ifs with hi
    · exact h.hb i hi
    · rfl
  · funext i k; simp only [prY]; split_ifs with hk
    · exact h.hy i k hk
    · rfl

lemma agreeBelow_mono {r r' : ℕ} {c c' : CS n m} (h : AgreeBelow r c c') (hr : r' ≤ r) :
    AgreeBelow r' c c' :=
  ⟨fun j hj => h.hu j (by omega), fun i hi => h.ha i (by omega), fun i hi => h.hb i (by omega),
    fun i k hk => h.hy i k (by omega)⟩

lemma knownC_congr (θ τ : ℝ) {r : ℕ} {c c' : CS n m} (h : AgreeBelow r c c') :
    knownC θ τ r c = knownC θ τ r c' := by
  unfold knownC; rw [prC_congr h]

lemma simReplyC_congr (θ τ p : ℝ) {r : ℕ} {c c' : CS n m} (h : AgreeBelow r c c') (ξ : ℝ) :
    simReplyC θ τ p r c ξ = simReplyC θ τ p r c' ξ := by
  have hs : stageUpTo (θ / 2) r c = stageUpTo (θ / 2) r c' :=
    stageUpTo_congr r c c' h.hu h.ha h.hb h.hy
  have hst := stageUpTo_le (θ / 2) r c
  unfold simReplyC
  rw [hs]
  set st := stageUpTo (θ / 2) r c'
  split_ifs with hlt hm
  · rw [knownC_congr θ τ (agreeBelow_mono h (by omega)), knownC_congr θ τ (agreeBelow_mono h (by omega))]
  · rw [knownC_congr θ τ (agreeBelow_mono h (by omega))]
  · rw [knownC_congr θ τ (agreeBelow_mono h (by omega))]

def WordAgree (r : ℕ) (W W' : Word d n m) : Prop := ∀ k : Fin (K n m), k.val < r → W.w k = W'.w k

lemma selC_agree {r : ℕ} {W W' : Word d n m} (h : WordAgree r W W') (s : ℝ) (x : Prim d) (y : Dual d) :
    AgreeBelow r (selC W s x y) (selC W' s x y) :=
  ⟨fun j hj => by simp only [selC, Word.πU]; rw [h (posU j) hj],
    fun i hi => by simp only [selC, Word.πA]; rw [h (posA i) hi],
    fun i hi => by simp only [selC, Word.πB]; rw [h (posB i) hi],
    fun i k hk => by simp only [selC, Word.πY]; rw [h (posY i k) hk]⟩

lemma emb_agree {k : ℕ} (π π' : Fin k → Fin d) (g : Fin k → ℝ) (hg : ∀ j, π j ≠ π' j → g j = 0)
    (i : Fin d) : emb π g i = emb π' g i := by
  simp only [emb]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : π j = π' j
  · rw [h]
  · simp [hg j h]

lemma embX_agree {r : ℕ} {W W' : Word d n m} (h : WordAgree r W W') (v : CS n m)
    (hv : SuppBelow r v) : embX W v = embX W' v := by
  ext c
  simp only [embX, PiLp.toLp_apply]
  have hU : ∀ i, emb W.πU v.1 i = emb W'.πU v.1 i := emb_agree _ _ _ (fun j hj => by
    by_contra hne
    exact hj (h (posU j) (by by_contra hc; push Not at hc; exact hne (hv.hu j hc))))
  have hA : ∀ i, emb W.πA v.2.1 i = emb W'.πA v.2.1 i := emb_agree _ _ _ (fun j hj => by
    by_contra hne
    exact hj (h (posA j) (by by_contra hc; push Not at hc; exact hne (hv.ha j hc))))
  have hB : ∀ i, emb W.πB v.2.2.1 i = emb W'.πB v.2.2.1 i := emb_agree _ _ _ (fun j hj => by
    by_contra hne
    exact hj (h (posB j) (by by_contra hc; push Not at hc; exact hne (hv.hb j hc))))
  rw [hU, hA, hB]

lemma embY_agree {r : ℕ} {W W' : Word d n m} (h : WordAgree r W W') (v : CS n m)
    (hv : SuppBelow r v) : embY W v = embY W' v := by
  ext i
  simp only [embY, PiLp.toLp_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : pY m a k < r
  · have e := h (posY a k) hk
    by_cases hw : W'.w (posY a k) = i
    · simp [Word.πY, e, hw]
    · simp [Word.πY, e, hw]
  · push Not at hk; simp [hv.hy a k hk]

noncomputable def simG (θ τ p : ℝ) (W : Word d n m) (s ℓ : ℝ) (r : ℕ) (z : Prim d × Dual d) (ξ : ℝ) :
    Prim d × Dual d :=
  ((ℓ * s) • embX W (simReplyC θ τ p r (selC W s z.1 z.2) ξ),
    (ℓ * s) • embY W (simReplyC θ τ p r (selC W s z.1 z.2) ξ))

lemma simG_prefix (θ τ p : ℝ) {r : ℕ} {W W' : Word d n m} (h : WordAgree r W W') (s ℓ : ℝ)
    (z : Prim d × Dual d) (ξ : ℝ) : simG θ τ p W s ℓ r z ξ = simG θ τ p W' s ℓ r z ξ := by
  unfold simG
  rw [simReplyC_congr θ τ p (selC_agree h s z.1 z.2) ξ,
    embX_agree h _ (simReplyC_supp θ τ p r _ ξ), embY_agree h _ (simReplyC_supp θ τ p r _ ξ)]

lemma oracle_eq_sim {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (p : ℝ) (W : Word d n m)
    (s ℓ : ℝ) (lev : ℕ) (hlev : lev ≤ K n m) (z : Prim d × Dual d)
    (hsmall : SmallFrom (θ / 2) lev (selC W s z.1 z.2)) (ξ : ℝ) :
    oracleG θ τ p W s ℓ z.1 z.2 ξ = simG θ τ p W s ℓ (levelStep n m p lev ξ) z ξ := by
  unfold oracleG simG
  rw [reply_eq_sim hθ hθ1 hτ p lev hlev _ hsmall ξ]

noncomputable def levelSeq (n m : ℕ) (p : ℝ) (ω : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => levelStep n m p (levelSeq n m p ω t) (ω t)

lemma levelSeq_le (p : ℝ) (ω : ℕ → ℝ) (t : ℕ) : levelSeq n m p ω t ≤ K n m := by
  induction t with
  | zero => simp [levelSeq]
  | succ t ih => exact levelStep_le p _ _ ih

lemma levelSeq_mono (p : ℝ) (ω : ℕ → ℝ) {s t : ℕ} (h : s ≤ t) :
    levelSeq n m p ω s ≤ levelSeq n m p ω t := by
  induction t with
  | zero => simp [Nat.le_zero.mp h]
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hs | hs
    · exact (ih (by omega)).trans (levelStep_ge p _ _)
    · rw [show s = t + 1 by omega]

variable {St : Type*}

noncomputable def trueState (G : Prim d × Dual d → ℝ → Prim d × Dual d) (qry : St → Prim d × Dual d)
    (upd : St → Prim d × Dual d → St) (init : St) (ω : ℕ → ℝ) : ℕ → St
  | 0 => init
  | t + 1 => upd (trueState G qry upd init ω t) (G (qry (trueState G qry upd init ω t)) (ω t))

noncomputable def simState (θ τ p : ℝ) (W : Word d n m) (s ℓ : ℝ) (qry : St → Prim d × Dual d)
    (upd : St → Prim d × Dual d → St) (init : St) (ω : ℕ → ℝ) : ℕ → St
  | 0 => init
  | t + 1 => upd (simState θ τ p W s ℓ qry upd init ω t)
      (simG θ τ p W s ℓ (levelSeq n m p ω (t + 1)) (qry (simState θ τ p W s ℓ qry upd init ω t)) (ω t))

lemma simState_prefix (θ τ p : ℝ) {W W' : Word d n m} (s ℓ : ℝ) (qry : St → Prim d × Dual d)
    (upd : St → Prim d × Dual d → St) (init : St) (ω : ℕ → ℝ) (t : ℕ)
    (h : WordAgree (levelSeq n m p ω t) W W') :
    simState θ τ p W s ℓ qry upd init ω t = simState θ τ p W' s ℓ qry upd init ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm := levelSeq_mono (n := n) (m := m) p ω (Nat.le_add_right t 1)
    have he := ih (fun k hk => h k (by omega))
    simp only [simState]
    rw [he, simG_prefix θ τ p h]

lemma coupling {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (p : ℝ) (W : Word d n m)
    (s ℓ : ℝ) (qry : St → Prim d × Dual d) (upd : St → Prim d × Dual d → St) (init : St)
    (ω : ℕ → ℝ) (N : ℕ)
    (hhit : ∀ t < N, SmallFrom (θ / 2) (levelSeq n m p ω t)
      (selC W s (qry (simState θ τ p W s ℓ qry upd init ω t)).1
        (qry (simState θ τ p W s ℓ qry upd init ω t)).2)) :
    simState θ τ p W s ℓ qry upd init ω N =
      trueState (fun z ξ => oracleG θ τ p W s ℓ z.1 z.2 ξ) qry upd init ω N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have he := ih (fun t ht => hhit t (by omega))
    simp only [simState, trueState]
    rw [← he, oracle_eq_sim hθ hθ1 hτ p W s ℓ _ (levelSeq_le p ω N) _ (hhit N (by omega))]
    rfl

noncomputable def maskedBelow (n m r : ℕ) : ℕ := ((Finset.range r).filter (maskedPos m n)).card

lemma maskedBelow_succ (r : ℕ) :
    maskedBelow n m (r + 1) = maskedBelow n m r + if maskedPos m n r then 1 else 0 := by
  unfold maskedBelow
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rw [add_zero]

lemma maskedBelow_step (p : ℝ) (lev : ℕ) (ξ : ℝ) :
    maskedBelow n m (levelStep n m p lev ξ) ≤ maskedBelow n m lev + if ξ ≤ p then 1 else 0 := by
  have hs := maskedBelow_succ (n := n) (m := m) lev
  unfold levelStep
  by_cases h1 : lev < K n m
  · by_cases h2 : maskedPos m n lev
    · by_cases hξ : ξ ≤ p
      · simp only [h1, h2, hξ, ↓reduceIte]; rw [hs]; simp [h2]
      · simp only [h1, h2, hξ, ↓reduceIte]; omega
    · simp only [h1, h2, ↓reduceIte]; rw [hs]; simp only [h2, ↓reduceIte, add_zero]
      exact Nat.le_add_right _ _
  · simp only [h1, ↓reduceIte]; exact Nat.le_add_right _ _

lemma maskedBelow_le_coin (p : ℝ) (ω : ℕ → ℝ) (t : ℕ) :
    maskedBelow n m (levelSeq n m p ω t) ≤ coinCount p ω t := by
  induction t with
  | zero => simp [levelSeq, maskedBelow, coinCount]
  | succ t ih =>
    have := maskedBelow_step (n := n) (m := m) p (levelSeq n m p ω t) (ω t)
    simp only [levelSeq, coinCount]
    split_ifs at this ⊢ <;> omega

lemma maskedBelow_K : n * (m + 1) ≤ maskedBelow n m (K n m) := by
  classical
  unfold maskedBelow
  have hsub : (Finset.univ : Finset (Fin n × Fin (m + 1))).image (fun q => pY m q.1 q.2) ⊆
      (Finset.range (K n m)).filter (maskedPos m n) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨q, rfl⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨pY_lt q.1 q.2, q.1, q.2, rfl⟩
  have hinj : Function.Injective (fun q : Fin n × Fin (m + 1) => pY m q.1 q.2) := by
    intro q q' h
    exact posY_inj (n := n) (m := m) (Fin.ext h)
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at this
  simpa using this

lemma level_lt_K (p : ℝ) (ω : ℕ → ℝ) (N : ℕ) (h : coinCount p ω N < n * (m + 1)) :
    levelSeq n m p ω N < K n m := by
  have h1 := levelSeq_le (n := n) (m := m) p ω N
  rcases h1.lt_or_eq with h2 | h2
  · exact h2
  · exfalso
    have h3 := maskedBelow_le_coin (n := n) (m := m) p ω N
    rw [h2] at h3
    have h4 := maskedBelow_K (n := n) (m := m)
    omega

end LongTails.Proofs.NcConcaveExecution

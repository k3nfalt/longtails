import LongTails.Proofs.FiniteSumNondualCuts
import LongTails.Proofs.FiniteSumNondualDomain
import LongTails.Proofs.FiniteSumNondualExecution
import LongTails.Proofs.NondualSelectorMovement
import LongTails.Proofs.KnownValueNondualCounting

open Set Classical
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.FiniteSumNondualHistory

open LongTails.Setups.FiniteSumNondualSmoothConvex
open LongTails.Algorithms.FiniteSumNondual
open FiniteSumNondualDomain FiniteSumNondualExecution FiniteSumNondualCuts
open RecursiveEnvelopeGeometry (Model)

lemma cutBody_subset (p : Params) (δ : ℝ) (history : List (Trial p)) : cutBody p δ history ⊆ domain p :=
  fun _ h => h.1

lemma cutBody_nil (p : Params) (δ : ℝ) : cutBody p δ [] = domain p := by
  ext u
  simp [cutBody]

lemma cutBody_antitone (p : Params) (δ : ℝ) {history history' : List (Trial p)}
    (hh : history ⊆ history') : cutBody p δ history' ⊆ cutBody p δ history :=
  fun _ hu => ⟨hu.1, fun trial ht => hu.2 trial (hh ht)⟩

lemma cutBody_append (p : Params) (δ : ℝ) (history : List (Trial p)) (trial : Trial p) :
    cutBody p δ (history ++ [trial]) = cutBody p δ history ∩
      {u | δ ≤ ⟪trial.certificate.gradient, (trialPoint p trial).val - u⟫} := by
  ext u
  simp only [cutBody, mem_inter_iff, mem_ofPred_eq, List.mem_append, List.mem_singleton ]
  aesop

lemma cutBody_closed (p : Params) (δ : ℝ) (history : List (Trial p)) : IsClosed (cutBody p δ history) := by
  have he : cutBody p δ history = domain p ∩
      ⋂ trial ∈ history, {u | δ ≤ ⟪trial.certificate.gradient, (trialPoint p trial).val - u⟫} := by
    ext u
    simp [cutBody]
  rw [he]
  apply (domain_compact p).isClosed.inter
  apply isClosed_biInter
  intro trial _
  apply isClosed_le continuous_const
  fun_prop

lemma cutBody_compact (p : Params) (δ : ℝ) (history : List (Trial p)) : IsCompact (cutBody p δ history) :=
  (domain_compact p).of_isClosed_subset (cutBody_closed p δ history) (cutBody_subset p δ history)

lemma cutBody_convex (p : Params) (δ : ℝ) (history : List (Trial p)) : Convex ℝ (cutBody p δ history) := by
  intro x hx y hy a b ha hb hab
  refine ⟨domain_convex p hx.1 hy.1 ha hb hab, ?_⟩
  intro trial ht
  have h₁ := mul_le_mul_of_nonneg_left (hx.2 trial ht) ha
  have h₂ := mul_le_mul_of_nonneg_left (hy.2 trial ht) hb
  simp only [inner_sub_right, inner_add_right, inner_smul_right] at h₁ h₂ ⊢
  nlinarith [congrArg (fun t : ℝ => t * δ) hab,
    congrArg (fun t : ℝ => t * ⟪trial.certificate.gradient, (trialPoint p trial).val⟫) hab]

lemma empty_body_constraints (p : Params) (δ : ℝ) (history : List (Trial p))
    (hempty : ¬(cutBody p δ history).Nonempty) :
    ¬∃ u ∈ domain p, ∀ i : Fin history.length,
      δ ≤ ⟪(history.get i).certificate.gradient, (trialPoint p (history.get i)).val - u⟫ := by
  rintro ⟨u, hu, hall⟩
  apply hempty
  refine ⟨u, hu, ?_⟩
  intro trial ht
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ht
  exact hall i

lemma historyOutput_gap (p : Params) {δ L : ℝ} {f : Point p → ℝ} {g : Point p → Point p}
    (hf : Model L f g) (history : List (Trial p))
    (hg : ∀ trial ∈ history, trial.certificate.gradient = g (trialPoint p trial).val)
    (hempty : ¬(cutBody p δ history).Nonempty) (u : Point p) (hu : u ∈ domain p) :
    f (historyOutput p δ history).val - f u < δ := by
  have hs := cutOutput_spec (domain_nonempty p) (domain_compact p) (domain_convex p) hf
    (fun i => (trialPoint p (history.get i)).val) (fun i => (history.get i).certificate.gradient)
    (fun i => (trialPoint p (history.get i)).property) (fun i => hg _ (history.get_mem i)) δ
    (empty_body_constraints p δ history hempty)
  rw [historyOutput, feasiblePoint_val p _ hs.1]
  exact hs.2 u hu

lemma selector_val (p : Params) [NeZero p.d] {C : Set (Point p)}
    (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C) (hsub : C ⊆ domain p) :
    (selector p C).val = LongTails.Algorithms.NondualSelector.center C (selectorRadius p) := by
  have hm := NondualProjection.center_mem hne hco hcv (selectorRadius p)
  simp only [selector, dite_eq_right (NeZero.ne p.d)]
  exact feasiblePoint_val p _ (hsub hm)

lemma selector_mem (p : Params) [NeZero p.d] {C : Set (Point p)}
    (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C) (hsub : C ⊆ domain p) :
    (selector p C).val ∈ C := by
  rw [selector_val p hne hco hcv hsub]
  exact NondualProjection.center_mem hne hco hcv _

lemma radius_properties (p : Params) [NeZero p.d] (hR : 0 < p.R) :
    0 < selectorRadius p ∧ selectorRadius p ^ 2 * ((1 + Nat.log 2 p.d : ℕ) : ℝ) = p.R ^ 2 * p.d :=
  KnownValueNondualCounting.selectorRadius_properties ⟨p.d, p.L, 0, p.R, p.ε, 0, 0⟩ (NeZero.pos p.d) hR

lemma selector_movement (p : Params) [NeZero p.d] (hR : 0 < p.R)
    (K : ℕ → Set (Point p)) (T : ℕ)
    (hne : ∀ t ≤ T, (K t).Nonempty) (hco : ∀ t ≤ T, IsCompact (K t))
    (hcv : ∀ t ≤ T, Convex ℝ (K t)) (hsub : ∀ t ≤ T, K t ⊆ domain p)
    (hnest : ∀ t < T, K (t + 1) ⊆ K t) :
    (∑ t ∈ Finset.range T, ‖(selector p (K t)).val - (selector p (K (t + 1))).val‖) ≤
      12 * p.R * Real.sqrt (((1 + Nat.log 2 p.d : ℕ) : ℝ) * (1 + Nat.log 2 T : ℕ)) := by
  have hpow (t : ℕ) : t ≤ 2 ^ (1 + Nat.log 2 t) := by
    simpa only [Nat.add_comm 1, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) t).le
  have hh := NondualSelectorMovement.nested_movement_bound K T hne hco hcv hnest hR.le
    (radius_properties p hR).1 (fun t ht u hu => hsub t ht hu)
    (1 + Nat.log 2 p.d) (1 + Nat.log 2 T) (by omega) (by omega) (hpow p.d) (hpow T)
    (radius_properties p hR).2
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  rw [selector_val p (hne t (by omega)) (hco t (by omega)) (hcv t (by omega)) (hsub t (by omega)),
    selector_val p (hne (t + 1) (by omega)) (hco (t + 1) (by omega))
      (hcv (t + 1) (by omega)) (hsub (t + 1) (by omega)), norm_sub_rev]

lemma prefix_body_nested (p : Params) (δ : ℝ) (history : List (Trial p)) (t : ℕ) :
    cutBody p δ (history.take (t + 1)) ⊆ cutBody p δ (history.take t) := by
  apply cutBody_antitone
  have he : history.take t = (history.take (t + 1)).take t := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_succ t)]
  rw [he]
  exact List.take_subset t _

lemma history_movement (p : Params) [NeZero p.d] (hR : 0 < p.R) (δ : ℝ)
    (history : List (Trial p)) (T : ℕ)
    (hne : ∀ t ≤ T, (cutBody p δ (history.take t)).Nonempty) :
    (∑ t ∈ Finset.range T,
      ‖(selector p (cutBody p δ (history.take t))).val -
        (selector p (cutBody p δ (history.take (t + 1)))).val‖) ≤
      12 * p.R * Real.sqrt (((1 + Nat.log 2 p.d : ℕ) : ℝ) * (1 + Nat.log 2 T : ℕ)) :=
  selector_movement p hR _ T hne (fun t _ => cutBody_compact p δ (history.take t))
    (fun t _ => cutBody_convex p δ (history.take t)) (fun t _ => cutBody_subset p δ (history.take t))
    (fun t _ => prefix_body_nested p δ history t)

end LongTails.Proofs.FiniteSumNondualHistory

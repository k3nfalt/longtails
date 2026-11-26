import LongTails.Proofs.EscapeChainCoordinates
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

namespace LongTails.Proofs.EscapeChainHiding

open scoped RealInnerProductSpace BigOperators
open EscapeChainCoordinates

variable {d n b : ℕ}

noncomputable def sgn (s : Bool) : ℝ := if s then 1 else -1

lemma sgn_mul_self (s : Bool) : sgn s * sgn s = 1 := by cases s <;> simp [sgn]

lemma sgn_sum : ∑ s : Bool, sgn s = 0 := by simp [sgn]

def emb (hnb : n * b ≤ d) (B : Fin n) (k : Fin b) : Fin d := Fin.castLE hnb (finProdFinEquiv (B, k))

lemma emb_inj (hnb : n * b ≤ d) {B B' : Fin n} {k k' : Fin b} :
    emb hnb B k = emb hnb B' k' ↔ B = B' ∧ k = k' := by
  constructor
  · intro h
    have h1 : finProdFinEquiv (B, k) = finProdFinEquiv (B', k') := Fin.castLE_injective hnb h
    have h2 := finProdFinEquiv.injective h1
    exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

noncomputable def blockVec (hnb : n * b ≤ d) (B : Fin n) (σs : Fin b → Bool) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ k, (sgn (σs k) / Real.sqrt b) • EuclideanSpace.single (emb hnb B k) (1 : ℝ)

lemma inner_blockVec (hnb : n * b ≤ d) (B : Fin n) (σs : Fin b → Bool) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪blockVec hnb B σs, x⟫ = ∑ k, sgn (σs k) / Real.sqrt b * x (emb hnb B k) := by
  unfold blockVec
  rw [sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_left, EuclideanSpace.inner_single_left]
  simp

lemma blockVec_apply (hnb : n * b ≤ d) (B : Fin n) (σs : Fin b → Bool) (k : Fin b) :
    blockVec hnb B σs (emb hnb B k) = sgn (σs k) / Real.sqrt b := by
  classical
  unfold blockVec
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    rw [ite_eq_right]
    intro h
    exact hk' ((emb_inj hnb).1 h.symm).2
  · simp

lemma blockVec_inner_self (hnb : n * b ≤ d) (hb : 0 < b) (B : Fin n) (σs : Fin b → Bool) :
    ⟪blockVec hnb B σs, blockVec hnb B σs⟫ = 1 := by
  rw [inner_blockVec]
  simp only [blockVec_apply]
  have : ∀ k : Fin b, sgn (σs k) / Real.sqrt b * (sgn (σs k) / Real.sqrt b) = 1 / b := by
    intro k
    rw [div_mul_div_comm, sgn_mul_self, Real.mul_self_sqrt (Nat.cast_nonneg b)]
  rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

lemma blockVec_inner_ne (hnb : n * b ≤ d) {B B' : Fin n} (h : B ≠ B') (σs σs' : Fin b → Bool) :
    ⟪blockVec hnb B σs, blockVec hnb B' σs'⟫ = 0 := by
  classical
  rw [inner_blockVec]
  refine Finset.sum_eq_zero fun k _ => ?_
  unfold blockVec
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_zero]
  · ring
  · intro k' _
    rw [ite_eq_right]
    intro he
    exact h ((emb_inj hnb).1 he).1

lemma block_mass (hnb : n * b ≤ d) (B : Fin n) (x : EuclideanSpace ℝ (Fin d)) :
    ∑ k, x (emb hnb B k) ^ 2 ≤ ‖x‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  have hinj : Function.Injective (emb hnb B) := fun k k' h => ((emb_inj hnb).1 h).2
  calc ∑ k, x (emb hnb B k) ^ 2 = ∑ c ∈ (Finset.univ.image (emb hnb B)), x c ^ 2 := by
        rw [Finset.sum_image (fun k _ k' _ h => hinj h)]
    _ ≤ ∑ c, x c ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)

lemma blocks_mass (hnb : n * b ≤ d) (S : Finset (Fin n)) (x : EuclideanSpace ℝ (Fin d)) :
    ∑ B ∈ S, ∑ k, x (emb hnb B k) ^ 2 ≤ ‖x‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  have hinj : Function.Injective (fun p : Fin n × Fin b => emb hnb p.1 p.2) := by
    intro p p' h
    obtain ⟨h1, h2⟩ := (emb_inj hnb).1 h
    exact Prod.ext h1 h2
  calc ∑ B ∈ S, ∑ k, x (emb hnb B k) ^ 2 = ∑ p ∈ S ×ˢ Finset.univ, x (emb hnb p.1 p.2) ^ 2 := by
        rw [Finset.sum_product]
    _ = ∑ c ∈ (S ×ˢ Finset.univ).image (fun p : Fin n × Fin b => emb hnb p.1 p.2), x c ^ 2 := by
        rw [Finset.sum_image (fun p _ p' _ h => hinj h)]
    _ ≤ ∑ c, x c ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)

lemma sign_pair (k k' : Fin b) :
    ∑ σs : Fin b → Bool, sgn (σs k) * sgn (σs k') = if k = k' then (2 : ℝ) ^ b else 0 := by
  classical
  by_cases h : k = k'
  · subst h
    simp only [sgn_mul_self, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ite_true]
    push_cast; ring
  · rw [ite_eq_right h]
    let f : Fin b → Bool → ℝ := fun j β => if j = k then sgn β else if j = k' then sgn β else 1
    have hprod : ∀ σs : Fin b → Bool, sgn (σs k) * sgn (σs k') = ∏ j, f j (σs j) := by
      intro σs
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
        ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm h, Finset.mem_univ k'⟩)]
      simp only [f, ite_eq_left rfl, ite_eq_right (Ne.symm h), ite_true]
      rw [Finset.prod_eq_one]
      · ring
      · intro j hj
        have hj1 := Finset.ne_of_mem_erase hj
        have hj2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
        simp [hj1, hj2]
    rw [Finset.sum_congr rfl fun σs _ => hprod σs]
    rw [← Fintype.prod_sum]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [f, sgn]

lemma sign_second_moment (hnb : n * b ≤ d) (hb : 0 < b) (B : Fin n) (x : EuclideanSpace ℝ (Fin d)) :
    ∑ σs : Fin b → Bool, ⟪blockVec hnb B σs, x⟫ ^ 2 =
      (2 : ℝ) ^ b * ((1 / b) * ∑ k, x (emb hnb B k) ^ 2) := by
  classical
  have hexp : ∀ σs : Fin b → Bool, ⟪blockVec hnb B σs, x⟫ ^ 2 =
      ∑ k, ∑ k', (x (emb hnb B k) * x (emb hnb B k') / b) * (sgn (σs k) * sgn (σs k')) := by
    intro σs
    rw [inner_blockVec, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have hs : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb'.le
    field_simp
    rw [show Real.sqrt b ^ 2 = b by rw [sq]; exact hs]
    ring
  rw [Finset.sum_congr rfl fun σs _ => hexp σs, Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := Fin b → Bool) (s := Finset.univ), ← Finset.mul_sum, sign_pair]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma cosh_mgf (hnb : n * b ≤ d) (B : Fin n) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ∑ σs : Fin b → Bool, Real.exp (t * ⟪blockVec hnb B σs, x⟫) ≤
      (2 : ℝ) ^ b * Real.exp (t ^ 2 * (∑ k, x (emb hnb B k) ^ 2) / (2 * b)) := by
  classical
  have hprod : ∀ σs : Fin b → Bool, Real.exp (t * ⟪blockVec hnb B σs, x⟫) =
      ∏ k, Real.exp (t * (sgn (σs k) / Real.sqrt b * x (emb hnb B k))) := by
    intro σs
    rw [inner_blockVec, Finset.mul_sum, Real.exp_sum]
  rw [Finset.sum_congr rfl fun σs _ => hprod σs]
  rw [← Fintype.prod_sum (fun k (β : Bool) => Real.exp (t * (sgn β / Real.sqrt b * x (emb hnb B k))))]
  have hk : ∀ k : Fin b, ∑ β : Bool, Real.exp (t * (sgn β / Real.sqrt b * x (emb hnb B k))) ≤
      2 * Real.exp (t ^ 2 * x (emb hnb B k) ^ 2 / (2 * b)) := by
    intro k
    set a := t * x (emb hnb B k) / Real.sqrt b
    have hs : ∑ β : Bool, Real.exp (t * (sgn β / Real.sqrt b * x (emb hnb B k))) = 2 * Real.cosh a := by
      simp only [Fintype.sum_bool, sgn, ite_true, Bool.false_eq_true, ite_false, Real.cosh_eq]
      rw [show t * (1 / Real.sqrt b * x (emb hnb B k)) = a by simp only [a]; ring,
        show t * (-1 / Real.sqrt b * x (emb hnb B k)) = -a by simp only [a]; ring]
      ring
    rw [hs]
    have hc := Real.cosh_le_exp_half_sq a
    have ha : a ^ 2 / 2 = t ^ 2 * x (emb hnb B k) ^ 2 / (2 * b) := by
      simp only [a]
      rcases Nat.eq_zero_or_pos b with h0 | hpos
      · simp [h0]
      · have hb' : (0 : ℝ) < b := by exact_mod_cast hpos
        rw [div_pow, Real.sq_sqrt hb'.le]; field_simp
    rw [ha] at hc
    linarith
  calc ∏ k, ∑ β : Bool, Real.exp (t * (sgn β / Real.sqrt b * x (emb hnb B k)))
      ≤ ∏ k, (2 * Real.exp (t ^ 2 * x (emb hnb B k) ^ 2 / (2 * b))) :=
        Finset.prod_le_prod₀ (fun k _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
          fun k _ => hk k
    _ = (2 : ℝ) ^ b * Real.exp (t ^ 2 * (∑ k, x (emb hnb B k) ^ 2) / (2 * b)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← Real.exp_sum, Finset.mul_sum, Finset.sum_div]

lemma update_split {α β : Type*} [DecidableEq α] (i : α) (x a : β) (r : {j // j ≠ i} → β) :
    Function.update ((Equiv.funSplitAt i β).symm (x, r)) i a = (Equiv.funSplitAt i β).symm (a, r) := by
  funext j
  by_cases h : j = i
  · subst h; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · rw [Function.update_of_ne h]
    simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

lemma sum_update {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] (i : α)
    (G : (α → β) → ℝ) :
    ∑ s : α → β, ∑ a : β, G (Function.update s i a) = Fintype.card β * ∑ s : α → β, G s := by
  classical
  let e := (Equiv.funSplitAt i β).symm
  calc ∑ s : α → β, ∑ a : β, G (Function.update s i a)
      = ∑ p : β × ({j // j ≠ i} → β), ∑ a : β, G (Function.update (e p) i a) :=
        (Equiv.sum_comp e (fun s => ∑ a : β, G (Function.update s i a))).symm
    _ = ∑ p : β × ({j // j ≠ i} → β), ∑ a : β, G (e (a, p.2)) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun a _ => ?_
        rw [show p = (p.1, p.2) from rfl, update_split]
    _ = ∑ x : β, ∑ r : {j // j ≠ i} → β, ∑ a : β, G (e (a, r)) := Fintype.sum_prod_type _
    _ = Fintype.card β * ∑ r : {j // j ≠ i} → β, ∑ a : β, G (e (a, r)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = Fintype.card β * ∑ p : β × ({j // j ≠ i} → β), G (e p) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = Fintype.card β * ∑ s : α → β, G s := by rw [Equiv.sum_comp e G]

lemma tail_count (hnb : n * b ≤ d) (hb : 0 < b) (B : Fin n) (x : EuclideanSpace ℝ (Fin d))
    {t ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ) (hx : ‖x‖ ≤ ρ) :
    ∑ σs : Fin b → Bool, (if t ≤ ⟪blockVec hnb B σs, x⟫ then (1 : ℝ) else 0) ≤
      (2 : ℝ) ^ b * Real.exp (-(t ^ 2 * b / (2 * ρ ^ 2))) := by
  classical
  set M := ∑ k, x (emb hnb B k) ^ 2 with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hMρ : M ≤ ρ ^ 2 := (block_mass hnb B x).trans (pow_le_pow_left₀ (norm_nonneg _) hx 2)
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  set lam := t * b / ρ ^ 2 with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hpt : ∀ σs : Fin b → Bool, (if t ≤ ⟪blockVec hnb B σs, x⟫ then (1 : ℝ) else 0) ≤
      Real.exp (lam * ⟪blockVec hnb B σs, x⟫ - lam * t) := by
    intro σs
    split_ifs with h
    · rw [Real.one_le_exp_iff]; nlinarith
    · exact (Real.exp_pos _).le
  have hsum := Finset.sum_le_sum fun σs (_ : σs ∈ (Finset.univ : Finset (Fin b → Bool))) => hpt σs
  refine hsum.trans ?_
  have hsplit : ∑ σs : Fin b → Bool, Real.exp (lam * ⟪blockVec hnb B σs, x⟫ - lam * t) =
      Real.exp (-(lam * t)) * ∑ σs : Fin b → Bool, Real.exp (lam * ⟪blockVec hnb B σs, x⟫) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σs _ => ?_
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have hmgf := cosh_mgf hnb B x lam
  calc Real.exp (-(lam * t)) * ∑ σs : Fin b → Bool, Real.exp (lam * ⟪blockVec hnb B σs, x⟫)
      ≤ Real.exp (-(lam * t)) * ((2 : ℝ) ^ b * Real.exp (lam ^ 2 * M / (2 * b))) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ ≤ Real.exp (-(lam * t)) * ((2 : ℝ) ^ b * Real.exp (lam ^ 2 * ρ ^ 2 / (2 * b))) := by
        gcongr
    _ = (2 : ℝ) ^ b * Real.exp (-(t ^ 2 * b / (2 * ρ ^ 2))) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        rw [hlam]
        field_simp
        ring

lemma tail_count_abs (hnb : n * b ≤ d) (hb : 0 < b) (B : Fin n) (x : EuclideanSpace ℝ (Fin d))
    {t ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ) (hx : ‖x‖ ≤ ρ) :
    ∑ σs : Fin b → Bool, (if t ≤ |⟪blockVec hnb B σs, x⟫| then (1 : ℝ) else 0) ≤
      2 * ((2 : ℝ) ^ b * Real.exp (-(t ^ 2 * b / (2 * ρ ^ 2)))) := by
  classical
  have h1 := tail_count hnb hb B x ht hρ hx
  have h2 := tail_count hnb hb B (-x) ht hρ (by rw [norm_neg]; exact hx)
  have hpt : ∀ σs : Fin b → Bool, (if t ≤ |⟪blockVec hnb B σs, x⟫| then (1 : ℝ) else 0) ≤
      (if t ≤ ⟪blockVec hnb B σs, x⟫ then (1 : ℝ) else 0) +
        (if t ≤ ⟪blockVec hnb B σs, -x⟫ then (1 : ℝ) else 0) := by
    intro σs
    rw [inner_neg_right]
    by_cases h : t ≤ |⟪blockVec hnb B σs, x⟫|
    · rw [ite_eq_left h]
      rcases le_abs'.1 h with h' | h'
      · rw [ite_eq_left (by linarith : t ≤ -⟪blockVec hnb B σs, x⟫)]; split_ifs <;> norm_num
      · rw [ite_eq_left h']; split_ifs <;> norm_num
    · rw [ite_eq_right h]; split_ifs <;> norm_num
  calc _ ≤ ∑ σs : Fin b → Bool, ((if t ≤ ⟪blockVec hnb B σs, x⟫ then (1 : ℝ) else 0) +
        (if t ≤ ⟪blockVec hnb B σs, -x⟫ then (1 : ℝ) else 0)) := Finset.sum_le_sum fun σs _ => hpt σs
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith

end LongTails.Proofs.EscapeChainHiding

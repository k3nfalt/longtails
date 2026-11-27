import LongTails.Proofs.SlidingWireLocal
import LongTails.Proofs.SlidingLowerChain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SlidingWireSplit

open LongTails.Proofs.SlidingLowerChain (Point)

open SlidingWireChain SlidingWireGeometry SlidingWireLocal FrontierChainProfiles FrontierChain
open Classical

variable {d : ℕ}

def gpos (r T : ℕ) (j : Fin (2 * T + 1)) : Fin (T * (r ^ 2 + 2) + 1) :=
  ⟨if j.val % 2 = 0 then j.val / 2 * (r ^ 2 + 2) else j.val / 2 * (r ^ 2 + 2) + r ^ 2 + 1, by
    have hj := j.isLt
    split_ifs
    · have : j.val / 2 ≤ T := by omega
      have := Nat.mul_le_mul_right (r ^ 2 + 2) this
      omega
    · have : j.val / 2 < T := by omega
      have := SlidingWireGeometry.mul_facts r (j.val / 2) T this
      omega⟩

lemma gpos_mod (r T : ℕ) (j : Fin (2 * T + 1)) :
    (gpos r T j).val % (r ^ 2 + 2) = if j.val % 2 = 0 then 0 else r ^ 2 + 1 := by
  simp only [gpos]
  split_ifs
  · simp
  · rw [show j.val / 2 * (r ^ 2 + 2) + r ^ 2 + 1 = (r ^ 2 + 1) + j.val / 2 * (r ^ 2 + 2) by ring,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

lemma gpos_div (r T : ℕ) (j : Fin (2 * T + 1)) :
    (gpos r T j).val / (r ^ 2 + 2) = j.val / 2 := by
  have hm : 0 < r ^ 2 + 2 := by positivity
  simp only [gpos]
  split_ifs
  · exact Nat.mul_div_cancel _ hm
  · rw [show j.val / 2 * (r ^ 2 + 2) + r ^ 2 + 1 = (r ^ 2 + 1) + j.val / 2 * (r ^ 2 + 2) by ring,
      Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt (by omega), zero_add]

lemma gpos_injective (r T : ℕ) : Function.Injective (gpos r T) := by
  intro a b h
  have hpar : a.val % 2 = b.val % 2 := by
    have hm : (gpos r T a).val % (r ^ 2 + 2) = (gpos r T b).val % (r ^ 2 + 2) := by rw [h]
    rw [gpos_mod, gpos_mod] at hm
    rcases Nat.mod_two_eq_zero_or_one a.val with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b.val with hb | hb <;>
      simp only [ha, hb, ite_true, ite_false, show (1 : ℕ) ≠ 0 by omega] at hm ⊢ <;> omega
  have hdiv : a.val / 2 = b.val / 2 := by
    rw [← gpos_div r T a, ← gpos_div r T b, h]
  apply Fin.ext
  omega

def gEmb (r T : ℕ) : Fin (2 * T + 1) ↪ Fin (T * (r ^ 2 + 2) + 1) :=
  ⟨gpos r T, gpos_injective r T⟩

def gateLink (r T : ℕ) (i : Fin T) : Fin (T * (r ^ 2 + 2)) :=
  ⟨i.val * (r ^ 2 + 2) + r ^ 2 + 1, by have := SlidingWireGeometry.mul_facts r i.val T i.isLt; omega⟩

lemma gate_sum {M : Type*} [AddCommMonoid M] (r T : ℕ) (G : Fin (T * (r ^ 2 + 2)) → M) :
    ∑ l : Fin (T * (r ^ 2 + 2)), (if phase r l.val = r ^ 2 + 1 then G l else 0) =
      ∑ i : Fin T, G (gateLink r T i) := by
  have hm : 0 < r ^ 2 + 2 := by positivity
  let e : Fin T ↪ Fin (T * (r ^ 2 + 2)) :=
    ⟨gateLink r T, fun a b h => by
      have h' := congrArg Fin.val h
      simp only [gateLink] at h'
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right hm (by omega))⟩
  rw [← Finset.sum_filter]
  have hs : (Finset.univ.filter fun l : Fin (T * (r ^ 2 + 2)) => phase r l.val = r ^ 2 + 1) =
      Finset.univ.map e := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hl
      refine ⟨⟨l.val / (r ^ 2 + 2), ?_⟩, ?_⟩
      · exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq l.isLt (Nat.mul_comm _ _))
      · apply Fin.ext
        simp only [e, gateLink, Function.Embedding.coeFn_mk, Fin.val_mk]
        have := Nat.div_add_mod l.val (r ^ 2 + 2)
        unfold phase at hl
        rw [Nat.mul_comm, hl] at this
        linarith
    · rintro ⟨i, rfl⟩
      show phase r (i.val * (r ^ 2 + 2) + r ^ 2 + 1) = r ^ 2 + 1
      rw [show i.val * (r ^ 2 + 2) + r ^ 2 + 1 = i.val * (r ^ 2 + 2) + (r ^ 2 + 1) from
        Nat.add_assoc _ _ _]
      exact SlidingWireGeometry.phase_eq r i.val (r ^ 2 + 1) (by omega)
  rw [hs, Finset.sum_map]
  rfl

lemma gate_pos_z (r T : ℕ) (i : Fin T) :
    (gEmb r T) (SlidingLowerChain.zi i) = (gateLink r T i).castSucc := by
  apply Fin.ext
  simp only [gEmb, gpos, gateLink, SlidingLowerChain.zi, Function.Embedding.coeFn_mk,
    Fin.val_castSucc]
  rw [ite_eq_right (by omega), show (2 * i.val + 1) / 2 = i.val by omega]

lemma gate_pos_x (r T : ℕ) (i : Fin T) :
    (gEmb r T) (SlidingLowerChain.xi i.succ) = (gateLink r T i).succ := by
  apply Fin.ext
  simp only [gEmb, gpos, gateLink, SlidingLowerChain.xi, Function.Embedding.coeFn_mk,
    Fin.val_succ]
  rw [ite_eq_left (by omega)]
  rw [show 2 * (i.val + 1) / 2 = i.val + 1 by omega]
  ring

lemma gate_pos_0 (r T : ℕ) : (gEmb r T) (SlidingLowerChain.xi 0) = 0 := by
  apply Fin.ext
  simp [gEmb, gpos, SlidingLowerChain.xi]

noncomputable def springObj (r : ℕ) (δ : ℝ) {T : ℕ} (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d)
    (u : Point d) : ℝ :=
  ∑ l : Fin (T * (r ^ 2 + 2)), if phase r l.val = r ^ 2 + 1 then 0 else
    sp δ (stretch r l.val (u (π l.castSucc)) (u (π l.succ)))

lemma link_split (r : ℕ) (δ : ℝ) (l : ℕ) (s t : ℝ) :
    link r δ l s t = (if phase r l = r ^ 2 + 1 then edge s t else 0) +
      (if phase r l = r ^ 2 + 1 then 0 else sp δ (stretch r l s t)) := by
  unfold link; split_ifs <;> simp

lemma obj_split (r : ℕ) (δ : ℝ) {T : ℕ} (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d) (u : Point d) :
    obj r δ π u = SlidingLowerChain.gateObj ((gEmb r T).trans π) u + springObj r δ π u := by
  unfold obj springObj SlidingLowerChain.gateObj
  simp_rw [link_split]
  rw [Finset.sum_add_distrib, gate_sum (M := ℝ) r T
    (fun l => edge (u (π l.castSucc)) (u (π l.succ)))]
  simp only [Function.Embedding.trans_apply, gate_pos_z, gate_pos_x, gate_pos_0]
  ring

end LongTails.Proofs.SlidingWireSplit

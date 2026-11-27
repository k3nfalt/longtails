import LongTails.Proofs.SlidingLowerRun
import LongTails.Proofs.SlidingLowerChain
import LongTails.Proofs.FiniteSumNondualLowerAveraging
import LongTails.Proofs.SmoothConvexFiniteHiding

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace LongTails.Proofs.SlidingLowerSim

open SlidingLowerChain (Point)
open OracleTemplate SlidingLowerRun FiniteSumNondualLowerAveraging FiniteSumNondualLowerExposure
open FiniteSumNondualLowerHiding SmoothConvexFiniteHiding

variable {d k : ℕ} {S : Type*}

structure Run (S : Type*) (d : ℕ) where
  query : S → Fin 2 × Point d
  update : S → Point d → S
  output : S → Point d
  init : S

structure Config (S : Type*) (d : ℕ) where
  state : S
  exposure : ℕ
  rem : Fin 2 → ℕ

noncomputable def simStep (H : Run S d) (rv : Fin 2 → Bool → ℕ)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (b : Bool) (x : Config S d) : Config S d :=
  if x.rem (H.query x.state).1 = 0 then x
  else ⟨H.update x.state (pr π x.exposure b (H.query x.state)),
    x.exposure + rv (H.query x.state).1 b,
    Function.update x.rem (H.query x.state).1 (x.rem (H.query x.state).1 - 1)⟩

noncomputable def simSeq (H : Run S d) (rv : Fin 2 → Bool → ℕ)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (β : ℕ → Bool) (budget : Fin 2 → ℕ) : ℕ → Config S d
  | 0 => ⟨H.init, 0, budget⟩
  | t + 1 => simStep H rv pr π (β t) (simSeq H rv pr π β budget t)

noncomputable def trueStep (H : Run S d)
    (tr : (Fin (k + 1) ↪ Fin d) → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (b : Bool) (x : S × (Fin 2 → ℕ)) : S × (Fin 2 → ℕ) :=
  if x.2 (H.query x.1).1 = 0 then x
  else (H.update x.1 (tr π b (H.query x.1)),
    Function.update x.2 (H.query x.1).1 (x.2 (H.query x.1).1 - 1))

noncomputable def trueSeq (H : Run S d)
    (tr : (Fin (k + 1) ↪ Fin d) → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (β : ℕ → Bool) (budget : Fin 2 → ℕ) : ℕ → S × (Fin 2 → ℕ)
  | 0 => (H.init, budget)
  | t + 1 => trueStep H tr π (β t) (trueSeq H tr π β budget t)

lemma simSeq_exposure_mono (H : Run S d) (rv : Fin 2 → Bool → ℕ)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (β : ℕ → Bool) (budget : Fin 2 → ℕ) {s t : ℕ} (h : s ≤ t) :
    (simSeq H rv pr π β budget s).exposure ≤ (simSeq H rv pr π β budget t).exposure := by
  induction t with
  | zero => have : s = 0 := by omega
            subst this; rfl
  | succ t ih =>
      rcases Nat.lt_or_ge s (t + 1) with hs | hs
      · have := ih (by omega)
        refine this.trans ?_
        simp only [simSeq, simStep]
        split_ifs <;> simp
      · have : s = t + 1 := by omega
        subst this; rfl

lemma simSeq_prefix (H : Run S d) (rv : Fin 2 → Bool → ℕ) (lev : ℕ → ℕ) (hlev : Monotone lev)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (hp : ∀ π ρ e b q, (∀ j : Fin (k + 1), j.val < lev (e + rv q.1 b) → π j = ρ j) →
      pr π e b q = pr ρ e b q)
    (π ρ : Fin (k + 1) ↪ Fin d) (β : ℕ → Bool) (budget : Fin 2 → ℕ) (t : ℕ)
    (h : ∀ j : Fin (k + 1), j.val < lev (simSeq H rv pr π β budget t).exposure → π j = ρ j) :
    simSeq H rv pr π β budget t = simSeq H rv pr ρ β budget t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hmono := simSeq_exposure_mono H rv pr π β budget (Nat.le_succ t)
      have he := ih (fun j hj => h j (lt_of_lt_of_le hj (hlev hmono)))
      simp only [simSeq] at h ⊢
      rw [← he]
      unfold simStep at h ⊢
      split_ifs with hz
      · rfl
      · rw [ite_eq_right hz] at h
        congr 1
        congr 1
        apply hp
        intro j hj
        exact h j hj

lemma coupling (H : Run S d) (rv : Fin 2 → Bool → ℕ) (lev : ℕ → ℕ)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (tr : (Fin (k + 1) ↪ Fin d) → Bool → Fin 2 × Point d → Point d)
    (good : (Fin (k + 1) ↪ Fin d) → ℕ → Point d → Prop)
    (heq : ∀ π e b q, good π (lev e) q.2 → pr π e b q = tr π b q)
    (π : Fin (k + 1) ↪ Fin d) (β : ℕ → Bool) (budget : Fin 2 → ℕ) (N : ℕ)
    (hgood : ∀ t < N, good π (lev (simSeq H rv pr π β budget t).exposure)
      (H.query (simSeq H rv pr π β budget t).state).2) :
    ((simSeq H rv pr π β budget N).state, (simSeq H rv pr π β budget N).rem) =
      trueSeq H tr π β budget N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have he := ih (fun t ht => hgood t (by omega))
      simp only [simSeq, trueSeq, ← he]
      unfold simStep trueStep
      split_ifs with hz
      · rfl
      · simp only [Prod.mk.injEq]
        exact ⟨by rw [heq π _ _ _ (hgood N (by omega))], trivial⟩

lemma simSeq_coin_dep (H : Run S d) (rv : Fin 2 → Bool → ℕ)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (β β' : ℕ → Bool) (budget : Fin 2 → ℕ) (t : ℕ)
    (h : ∀ s < t, β s = β' s) :
    simSeq H rv pr π β budget t = simSeq H rv pr π β' budget t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [simSeq]
      rw [ih (fun s hs => h s (by omega)), h t (by omega)]

noncomputable def active (H : Run S d) (rv : Fin 2 → Bool → ℕ)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (β : ℕ → Bool) (budget : Fin 2 → ℕ) (i : Fin 2) (t : ℕ) : ℝ :=
  if (simSeq H rv pr π β budget t).rem (H.query (simSeq H rv pr π β budget t).state).1 ≠ 0 ∧
    (H.query (simSeq H rv pr π β budget t).state).1 = i then 1 else 0

lemma exposure_eq (H : Run S d) (rv : Fin 2 → Bool → ℕ)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (β : ℕ → Bool) (budget : Fin 2 → ℕ) (N : ℕ) :
    ((simSeq H rv pr π β budget N).exposure : ℝ) =
      ∑ t ∈ Finset.range N, ∑ i : Fin 2,
        active H rv pr π β budget i t * (rv i (β t) : ℝ) := by
  induction N with
  | zero => simp [simSeq]
  | succ N ih =>
      rw [Finset.sum_range_succ, ← ih]
      have key : ((simSeq H rv pr π β budget (N + 1)).exposure : ℝ) =
          (simSeq H rv pr π β budget N).exposure +
            ∑ i : Fin 2, active H rv pr π β budget i N * (rv i (β N) : ℝ) := by
        rw [Fin.sum_univ_two]
        simp only [simSeq, simStep, active]
        by_cases hz : (simSeq H rv pr π β budget N).rem
            (H.query (simSeq H rv pr π β budget N).state).1 = 0
        · rw [ite_eq_left hz]
          simp [hz]
        · rw [ite_eq_right hz]
          rcases (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1)
            (H.query (simSeq H rv pr π β budget N).state).1 with he | he
          · rw [he] at hz ⊢
            simp [hz]
          · rw [he] at hz ⊢
            simp [hz]
      exact key

lemma rem_le (H : Run S d) (rv : Fin 2 → Bool → ℕ)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (β : ℕ → Bool) (budget : Fin 2 → ℕ) (i : Fin 2) (N : ℕ) :
    ((∑ t ∈ Finset.range N, active H rv pr π β budget i t) : ℝ) +
      (simSeq H rv pr π β budget N).rem i = budget i := by
  induction N with
  | zero => simp [simSeq]
  | succ N ih =>
      have key : ((simSeq H rv pr π β budget (N + 1)).rem i : ℝ) +
          active H rv pr π β budget i N = (simSeq H rv pr π β budget N).rem i := by
        simp only [simSeq, simStep, active]
        set R := (simSeq H rv pr π β budget N).rem
        set q := (H.query (simSeq H rv pr π β budget N).state).1
        by_cases hz : R q = 0
        · rw [ite_eq_left hz]
          have : ¬ (R q ≠ 0 ∧ q = i) := fun h => h.1 hz
          rw [ite_eq_right this]
          simp; rfl
        · rw [ite_eq_right hz]
          by_cases hi : q = i
          · rw [ite_eq_left ⟨hz, hi⟩]
            have hu : Function.update R q (R q - 1) i = R q - 1 := by
              rw [← hi]; exact Function.update_self _ _ _
            simp only
            rw [hu, ← hi]
            have h1 : 1 ≤ R q := Nat.one_le_iff_ne_zero.mpr hz
            push_cast [Nat.cast_sub h1]
            ring
          · rw [ite_eq_right (fun h => hi h.2)]
            simp only
            rw [Function.update_of_ne (fun h => hi h.symm)]
            ring
      rw [Finset.sum_range_succ]
      linarith

lemma active_sum_le (H : Run S d) (rv : Fin 2 → Bool → ℕ)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (β : ℕ → Bool) (budget : Fin 2 → ℕ) (i : Fin 2) (N : ℕ) :
    ((∑ t ∈ Finset.range N, active H rv pr π β budget i t) : ℝ) ≤ budget i := by
  have := rem_le H rv pr π β budget i N
  have h0 : (0 : ℝ) ≤ (simSeq H rv pr π β budget N).rem i := Nat.cast_nonneg _
  linarith

end LongTails.Proofs.SlidingLowerSim

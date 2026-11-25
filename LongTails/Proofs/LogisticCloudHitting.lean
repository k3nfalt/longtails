import LongTails.Proofs.LogisticCloudDrift

open LongTails.Proofs.LogisticCloudCone
open LongTails.Proofs.LogisticCloudDrift

namespace LongTails.Proofs.LogisticCloudHitting

structure Progress (s : Scales) (x y : Point) where
  cone : Cone s.a y
  growth : (1+s.η*s.μ/80)*mass x ≤ mass y
  slow : x.v ≤ y.v
  monotone : amplitude x ≤ amplitude y
  bounded : amplitude y ≤ (1+s.η*s.μ)*amplitude x
  drift : 64*Real.sqrt s.a ≤ amplitude x → x.q+6*s.η*s.μ*s.a*x.p ≤ y.q

def Safe (s : Scales) (z : ℕ → Point) (ok : ℕ → Prop) (n : ℕ) : Prop :=
  Cone s.a (z n) ∧ (z n).q ≤ 0 ∧ ok n ∧ mass (z 0) ≤ mass (z n) ∧ (z 0).v ≤ (z n).v

lemma until_crossing (s : Scales) (z : ℕ → Point) (ok hit : ℕ → Prop)
    (h₀ : Safe s z ok 0) (hsmall : amplitude (z 0) ≤ 64*Real.sqrt s.a)
    (step : ∀ n, Safe s z ok n → amplitude (z n) ≤ 2^16*Real.sqrt s.a →
      Progress s (z n) (z (n+1)) ∧ ok (n+1) ∧ (0 < (z (n+1)).q → hit (n+1)))
    (K J : ℕ) (hwarm : 640*Real.sqrt s.a ≤ (1+s.η*s.μ/80)^K*mass (z 0))
    (hspan : 4 ≤ (J:ℝ)*s.η*s.μ) (hmax : (1+s.η*s.μ)^J ≤ 512) :
    ∃ n ≤ K+J, hit n := by
  let δ := s.η*s.μ
  let b := Real.sqrt s.a
  have hb : 0 < b := Real.sqrt_pos.mpr s.ha
  have hδ : 0 < δ := mul_pos s.hη s.hμ
  have hδ' : δ ≤ 1 := by
    dsimp [δ]
    linarith [s.tune,mul_nonneg s.hη.le s.ha.le]
  by_contra! hno
  have next (n : ℕ) (hn : n < K+J) (h : Safe s z ok n) (Ht : amplitude (z n) ≤ 2^16*b) :
      Safe s z ok (n+1) ∧ Progress s (z n) (z (n+1)) := by
    obtain ⟨P,hgood,hh⟩ := step n h Ht
    have hp := (geometry s.ha' h.1 h.2.1).2.2.1
    have hp₀ := h.1.1
    have hm : mass (z n) ≤ mass (z (n+1)) := by
      nlinarith [P.growth,mul_nonneg hδ.le (show 0 ≤ mass (z n) by linarith)]
    exact ⟨⟨P.cone,le_of_not_gt (fun H => hno _ (by omega) (hh H)),hgood,
      h.2.2.2.1.trans hm,h.2.2.2.2.trans P.slow⟩,P⟩
  have low (k : ℕ) (hk : k ≤ K) :
      (∃ n ≤ k, Safe s z ok n ∧ 64*b ≤ amplitude (z n) ∧ amplitude (z n) ≤ 128*b) ∨
      (Safe s z ok k ∧ amplitude (z k) < 64*b ∧ (1+δ/80)^k*mass (z 0) ≤ mass (z k)) := by
    induction k with
    | zero =>
      by_cases h : 64*b ≤ amplitude (z 0)
      · left; exact ⟨0,le_rfl,h₀,h,by linarith⟩
      · right; exact ⟨h₀,lt_of_not_ge h,by simp⟩
    | succ k ih =>
      obtain H | ⟨hS,ht,hm⟩ := ih (by omega)
      · obtain ⟨n,hn,he⟩ := H
        exact Or.inl ⟨n,by omega,he⟩
      obtain ⟨hS',P⟩ := next k (by omega) hS (by linarith)
      by_cases hHigh : 64*b ≤ amplitude (z (k+1))
      · have hh := mul_le_mul (show 1+δ ≤ 2 by linarith) ht.le
          (amplitude_bounds hS.1).1.le (by norm_num : (0:ℝ) ≤ 2)
        exact Or.inl ⟨k+1,le_rfl,hS',hHigh,by linarith [P.bounded]⟩
      · right
        refine ⟨hS',lt_of_not_ge hHigh,?_⟩
        rw [pow_succ]
        have he := mul_le_mul_of_nonneg_left hm (show 0 ≤ 1+δ/80 by linarith)
        nlinarith only [he,P.growth]
  obtain H | ⟨hs,ht,hm⟩ := low K le_rfl
  case inr =>
    obtain ⟨_,_,_,h₁⟩ := geometry s.ha' hs.1 hs.2.1
    have h₂ := (amplitude_bounds hs.1).2.1
    linarith
  obtain ⟨n,hn,hS,hHigh,hBound⟩ := H
  let m := mass (z n)
  have hmass (k : ℕ) (hk : k ≤ J) :
      Safe s z ok (n+k) ∧ m ≤ mass (z (n+k)) ∧
      amplitude (z n) ≤ amplitude (z (n+k)) ∧
      amplitude (z (n+k)) ≤ (1+δ)^k*amplitude (z n) ∧
      (z n).q+(k:ℝ)*(6*δ*s.a*m/5) ≤ (z (n+k)).q := by
    induction k with
    | zero => simpa [m] using hS
    | succ k ih =>
      obtain ⟨hs,hm,hl,hu,hq⟩ := ih (by omega)
      have hpow := pow_le_pow_right₀ (show 1 ≤ 1+δ by linarith) (show k ≤ J by omega)
      have hh := mul_le_mul (hpow.trans hmax) hBound (amplitude_bounds hS.1).1.le
        (by norm_num : (0:ℝ) ≤ 512)
      obtain ⟨hs',P⟩ := next (n+k) (by omega) hs (by linarith)
      have hp := (geometry s.ha' hs.1 hs.2.1).2.2.2
      have hm₀ : 0 ≤ mass (z (n+k)) := by linarith [(geometry s.ha' hs.1 hs.2.1).2.2.1,hs.1.1]
      refine ⟨hs',?_,hl.trans P.monotone,?_,?_⟩
      · rw [← Nat.add_assoc]
        have hg := P.growth
        dsimp [δ] at hδ
        nlinarith only [hm,hg,mul_nonneg hδ.le hm₀]
      · rw [← Nat.add_assoc,pow_succ]
        dsimp [δ] at *
        nlinarith only [P.bounded,mul_le_mul_of_nonneg_left hu (show 0 ≤ 1+δ by linarith)]
      · rw [← Nat.add_assoc,Nat.cast_succ]
        have HH := P.drift (hHigh.trans hl)
        have Hz := mul_le_mul_of_nonneg_left (hm.trans hp) (mul_nonneg hδ.le s.ha.le)
        dsimp [δ] at *
        nlinarith only [hq,HH,Hz]
  obtain ⟨hs,_,_,_,hq⟩ := hmass J le_rfl
  have hp := (geometry s.ha' hS.1 hS.2.1).2.2.1
  have hp₀ := hS.1.1
  have hm : 0 < m := hp₀.trans_le hp
  have h1 := mul_le_mul_of_nonneg_right hspan (mul_nonneg s.ha.le hm.le)
  have h2 := mul_le_mul_of_nonneg_left hp s.ha.le
  change (z n).p ≤ m at hp
  have hangle := hS.1.2.1
  change 4 ≤ (J:ℝ)*s.η*s.μ at hspan
  dsimp [δ,m] at *
  nlinarith only [hq,hs.2.1,h1,h2,hangle,mul_pos s.ha hm]

end LongTails.Proofs.LogisticCloudHitting

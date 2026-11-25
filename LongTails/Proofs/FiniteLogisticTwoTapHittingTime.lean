import LongTails.Proofs.FiniteLogisticTwoTapPhase
import LongTails.Proofs.FiniteLogisticPerceptronWarmup

open LongTails.Proofs.FiniteLogisticTwoTapCoordinates
open LongTails.Proofs.FiniteLogisticPerceptronCrossing
open LongTails.Proofs.FiniteLogisticTwoTapPhase

namespace LongTails.Proofs.FiniteLogisticTwoTapHittingTime

def mass (z : Coords) := z.p+z.q+z.u

noncomputable def barrier (s : Scales) (z : Coords) := 7*s.k*(z.p+z.u)-z.q

lemma prefix_control (s : Scales) (z : ℕ → Coords) (hstep : ∀ n, z (n+1) = advance s (z n))
    (hcone : Cone s (z 0)) (hinit : mass (z 0) ≤ 4096*s.k) (n : ℕ)
    (hq : ∀ k ≤ n, (z k).q ≤ 0) :
    Cone s (z n) ∧ barrier s (z n) ≤ 270336*s.k^2 ∧
    (1+s.η*s.μ/336)^n * mass (z 0) ≤ mass (z n) := by
  induction n with
  | zero =>
    obtain ⟨hp,hu,_,hW,ha,_⟩ := cone_geometry s _ hcone (hq 0 le_rfl)
    refine ⟨hcone,?_,by simp⟩
    change _ ≤ _ at hinit
    change 7*s.k*((z 0).p+(z 0).u)-(z 0).q ≤ _
    dsimp only [mass] at hinit
    nlinarith [mul_le_mul_of_nonneg_left hW s.hk.le,
      mul_le_mul_of_nonneg_left hinit s.hk.le,mul_nonneg s.hk.le hu,sq_nonneg s.k]
  | succ n ih =>
    obtain ⟨hc,hK,hg⟩ := ih (fun k hk => hq k (by omega))
    have hn := hq n (by omega)
    obtain ⟨_,_,_,hW,_,_⟩ := cone_geometry s _ hc hn
    obtain ⟨HC,hP,hU,HG,HW,_,HB⟩ := cone_step s _ hc hn
    rw [← hstep] at HC hP hU HG HW HB
    refine ⟨HC,?_,?_⟩
    · by_cases h : 4096*s.k ≤ mass (z n)
      · exact (HB h).2.trans hK
      · obtain ⟨_,_,_,_,hQ,_⟩ := cone_geometry s _ HC (hq _ le_rfl)
        exact size_barrier s.hk hU hQ HW hW (le_of_not_ge h)
    · rw [pow_succ']
      change _ ≤ mass (z (n+1)) at HG
      have hr : 0 ≤ 1+s.η*s.μ/336 := by nlinarith [mul_pos s.hη s.hμ]
      calc
        _ = (1+s.η*s.μ/336)*((1+s.η*s.μ/336)^n*mass (z 0)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hg hr
        _ ≤ _ := HG

lemma high_prefix (s : Scales) (z : ℕ → Coords) (hstep : ∀ n, z (n+1) = advance s (z n))
    (m n : ℕ) (hc : Cone s (z m)) (hm : 4096*s.k ≤ mass (z m))
    (hq : ∀ t ≤ n, (z (m+t)).q ≤ 0) :
    Cone s (z (m+n)) ∧ mass (z m) ≤ mass (z (m+n)) ∧
    (z m).q + n*(8*s.η*s.μ*s.k*(mass (z m)/51)) ≤ (z (m+n)).q := by
  induction n with
  | zero => simpa using hc
  | succ n ih =>
    obtain ⟨Hc,HG,Hq⟩ := ih (fun t ht => hq t (by omega))
    have hn := hq n (by omega)
    obtain ⟨_,_,hP,_,_,_⟩ := cone_geometry s _ Hc hn
    obtain ⟨HC,_,_,Hg,_,_,HB⟩ := cone_step s _ Hc hn
    have HH := (HB (hm.trans HG)).1
    rw [← hstep] at HC Hg HH
    have h₁ : 0 ≤ mass (z (m+n)) := le_trans (by linarith [s.hk]) (hm.trans HG)
    have hr : 0 ≤ s.η*s.μ/336 := by exact div_nonneg (mul_nonneg s.hη.le s.hμ.le) (by norm_num)
    have H : mass (z (m+n)) ≤ mass (z (m+n+1)) := by
      change (1+s.η*s.μ/336)*mass _ ≤ mass _ at Hg
      nlinarith only [Hg,mul_nonneg hr h₁]
    refine ⟨HC,HG.trans H,?_⟩
    have hP' : mass (z m)/51 ≤ (z (m+n)).p := by change mass _ ≤ _ at hP; linarith
    have hδ : 0 ≤ 8*s.η*s.μ*s.k := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) s.hη.le) s.hμ.le) s.hk.le
    rw [← Nat.add_assoc]
    push_cast
    nlinarith only [HH,Hq,mul_le_mul_of_nonneg_left hP' hδ]

lemma exists_crossing (s : Scales) (z : ℕ → Coords) (hstep : ∀ n, z (n+1) = advance s (z n))
    (hcone : Cone s (z 0)) (hq₀ : (z 0).q ≤ 0) (hinit : mass (z 0) ≤ 4096*s.k)
    (m n : ℕ) (hm : 4096*s.k ≤ (1+s.η*s.μ/336)^m * mass (z 0))
    (hn : 52 ≤ (n:ℝ)*s.η*s.μ) :
    ∃ t < m+n, (∀ i ≤ t, (z i).q ≤ 0) ∧ 0 < (z (t+1)).q := by
  classical
  have H : ∃ i ≤ m+n, 0 < (z i).q := by
    by_contra! h
    have hm' : ∀ i ≤ m, (z i).q ≤ 0 := fun i hi => h i (by omega)
    obtain ⟨hc,_,hG⟩ := prefix_control s z hstep hcone hinit m hm'
    obtain ⟨_,hu,_,hw,ha,_⟩ := cone_geometry s _ hc (hm' m le_rfl)
    have hqg : -8*s.k*mass (z m) ≤ (z m).q := by
      obtain ⟨H,_,hU,_,_⟩ := hc
      have hp : (z m).p ≤ 2*mass (z m) := by dsimp [mass]; linarith
      nlinarith only [ha,mul_le_mul_of_nonneg_left hp s.hk.le]
    obtain ⟨_,_,Hq⟩ := high_prefix s z hstep m n hc (hm.trans hG)
      (fun i hi => h (m+i) (by omega))
    have Hpos : 0 < mass (z m) := lt_of_lt_of_le (by linarith [s.hk]) (hm.trans hG)
    have Hmul := mul_le_mul_of_nonneg_right hn (mul_nonneg s.hk.le Hpos.le)
    nlinarith only [Hq,hqg,Hmul,h (m+n) le_rfl,mul_pos s.hk Hpos]
  let i := Nat.find H
  have hi : i ≤ m+n ∧ 0 < (z i).q := Nat.find_spec H
  have hne : i ≠ 0 := by rintro hi'; rw [hi'] at hi; linarith
  refine ⟨i-1,by omega,?_,by simpa [Nat.sub_add_cancel (by omega : 1 ≤ i)] using hi.2⟩
  intro j hj
  have Hsmall := Nat.find_min H (show j < i by omega)
  exact le_of_not_gt (fun hpos => Hsmall ⟨by omega,hpos⟩)

lemma crossing_separates (s : Scales) (z : ℕ → Coords) (hstep : ∀ n, z (n+1) = advance s (z n))
    (hcone : Cone s (z 0)) (hinit : mass (z 0) ≤ 4096*s.k) (t : ℕ)
    (hq : ∀ i ≤ t, (z i).q ≤ 0) (hit : 0 < (z (t+1)).q) :
    0 < s.L*(z (t+1)).p*(z (t+1)).q ∧
      0 < defect s (z (t+1)) - ((1+s.μ*s.k^2)*s.L)*(z (t+1)).p*(z (t+1)).q := by
  let x := z t
  let y := z (t+1)
  let L₂ := (1+s.μ*s.k^2)*s.L
  obtain ⟨hc,hK,_⟩ := prefix_control s z hstep hcone hinit t hq
  have hn := hq t le_rfl
  obtain ⟨hp,hu,_,_,_,hD⟩ := cone_geometry s x hc hn
  obtain ⟨_,hP,hU,_,hw,hD',_⟩ := cone_step s x hc hn
  have hstep_t : y = advance s x := hstep t
  rw [← hstep_t] at hP hU hw hD'
  change 7*s.k*(x.p+x.u)-x.q ≤ _ at hK
  have hk := s.hk
  have hk' : s.k ≤ 1 := by nlinarith [s.hk₂]
  have hW : x.p+x.u ≤ 40000*s.k := by
    change x.q ≤ 0 at hn
    by_contra! H
    nlinarith only [hK,hn,mul_pos hk (sub_pos.mpr H),sq_nonneg s.k]
  have hX : x.p ≤ 40000*s.k := by linarith
  have hY : y.p ≤ 80000*s.k := by linarith
  obtain ⟨hL,_,_,_,_,hμ⟩ := scale_bounds s
  have hL₂ : s.L ≤ L₂ := by
    dsimp [L₂]
    nlinarith [mul_nonneg (mul_nonneg s.hμ.le (sq_nonneg s.k)) hL.le]
  have hL₁ : s.L*s.k ≤ 2 := by rw [s.hL]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  have hLk : L₂*s.k ≤ 3 := by
    dsimp [L₂]
    nlinarith [mul_le_mul_of_nonneg_left hL₁ (mul_nonneg s.hμ.le (sq_nonneg s.k))]
  have hscale : s.η/2 ≤ 1/(2^40:ℝ) := by linarith [s.hη']
  have hLX : s.L*x.p ≤ 80000 := by nlinarith [mul_le_mul_of_nonneg_left hX hL.le]
  have hLX₂ : (s.L+L₂)*x.p ≤ 200000 := by
    nlinarith [mul_le_mul_of_nonneg_left hX (show 0 ≤ L₂ by linarith)]
  have hLY : L₂*y.p ≤ 240000 := by nlinarith [mul_le_mul_of_nonneg_left hY (show 0 ≤ L₂ by linarith)]
  apply first_crossing_separates hL hL₂ (by linarith [s.hη] : 0 ≤ s.η/2) hp hP hn hit hD hD'
  · rw [hstep t]
    dsimp [advance,L₂]
    ring
  · have H := mul_le_mul hLX hLX₂ (mul_nonneg (by linarith) hp.le) (by norm_num)
    nlinarith only [mul_le_mul hscale H (mul_nonneg (mul_nonneg hL.le hp.le)
      (mul_nonneg (by linarith) hp.le)) (by norm_num)]
  · have H := mul_le_mul hLX hLY (mul_nonneg (by linarith) hP.le) (by norm_num)
    nlinarith only [mul_le_mul hscale H (mul_nonneg (mul_nonneg hL.le hp.le)
      (mul_nonneg (by linarith) hP.le)) (by norm_num)]

end LongTails.Proofs.FiniteLogisticTwoTapHittingTime

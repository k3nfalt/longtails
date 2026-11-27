import LongTails.Setups.RidgeClockTwoTapLogistic
import LongTails.Proofs.TwoTapRadialClock
import LongTails.Proofs.RadialWorkPotential
import LongTails.Proofs.FirstFitGradientExecution
import LongTails.Proofs.ExponentialMarginWork

namespace LongTails.Proofs.RidgeClockTwoTapConvergence

open LongTails.Setups.RidgeClockTwoTapLogistic
open LongTails.Setups.TwoSampleQuadraticPerceptron (margin)

lemma source_error {u : Input} (s : Source u) (X : Rows u) (T : ℕ) (h : s.encloses X T) :
    ∀ t ≤ T, size ((step X)^[t] u.x₀-s.point t) ≤ s.r t := by
  let z := fun t => (step X)^[t] u.x₀
  let e := fun t => z t-s.point t
  let err := fun t => step X (z t)-step X (s.point t)-s.linear t (e t)
  have ht (a k : ℕ) : s.response X a (e a) err k = e (a+k) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Source.response, ih]
      dsimp only [err, e, z]
      simp only [Nat.add_succ, Nat.add_zero, Function.iterate_succ_apply']
      abel
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro hT
    cases t with
    | zero => exact h.1
    | succ j =>
      rcases h.2 j (by omega) with hn | ⟨a,ha,hl,hr⟩
      · simpa only [Function.iterate_succ_apply', add_sub_cancel] using
          hn (_-s.point j) (ih j (by omega) (by omega))
      have hv := ih a (by omega) (by omega)
      have hb (l : ℕ) (hh : l ∈ Finset.Icc a j) : size (err l) ≤ s.error l := by
        have hj := (Finset.mem_Icc.mp hh).2
        have hb := hl l hh (e l) (ih l (by omega) (by omega))
        simpa only [err,e,add_sub_cancel] using hb
      have hh := hr (e a) hv err hb
      rw [ht,Nat.add_sub_of_le (by omega : a ≤ j+1)] at hh
      exact hh

lemma radial_gain {u : Input} (X : Rows u) (z : LongTails.Setups.TwoSampleQuadraticPerceptron.Space .conv u.d) :
    radius (step X z)-radius z = 2*u.η*work X z + u.η^2*radius (descent X z) := by
  exact TwoTapRadialClock.full_gradient_radius X z u.η

lemma epoch_radius {p : Params} (X : Rows p.input) (s : Source p.input) (T : ℕ)
    (hη : 0 < p.input.η) (he : s.encloses X T) (hb : s.dataBounds X T) (a B : ℕ) (ha : a+B ≤ T) :
    s.gain a B ≤ radius ((step X)^[a+B] p.input.x₀)-radius ((step X)^[a] p.input.x₀) := by
  induction B with
  | zero => simp [Source.gain]
  | succ B ih =>
    have hj : a+B ≤ T := by omega
    have hz := hb (a+B) hj _ (source_error s X T he _ hj)
    have h1 := mul_le_mul_of_nonneg_left hz.2.2.1 (show 0 ≤ 2*p.input.η by positivity)
    have h2 := mul_le_mul_of_nonneg_left hz.2.2.2.1 (sq_nonneg p.input.η)
    have hh := radial_gain X ((step X)^[a+B] p.input.x₀)
    rw [← Function.iterate_succ_apply' (step X) (a+B) p.input.x₀] at hh
    change (∑ j ∈ Finset.range (B+1), _) ≤ _
    rw [Finset.sum_range_succ]
    have h_old := ih hj
    dsimp only [Source.gain] at h_old
    rw [Nat.add_succ]
    linarith

lemma score_step {u : Input} (X : Rows u) (i : Fin u.n)
    (z : LongTails.Setups.TwoSampleQuadraticPerceptron.Space .conv u.d) :
    margin .conv u.d (X i) (step X z)-margin .conv u.d (X i) z = scoreDrift X i z := by
  simp only [step,scoreDrift,margin,LongTails.Setups.TwoSampleQuadraticPerceptron.direction,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,inner_add_right,
    real_inner_smul_right,inner_add_left,real_inner_smul_left]
  ring

lemma work_gate {p : Params} (X : Rows p.input) (s : Source p.input) (q : RidgeProfile p)
    (g : ScoreWork p.input) (L : ℕ) (hc : g.checked s q X L)
    (he : s.encloses X (p.burn+p.block*L)) (hb : s.dataBounds X (p.burn+p.block*L)) :
    let t := fun k : ℕ => p.burn+p.block*k
    ∀ k ≤ L, p.edge p.bins ≤ s.hi (t k) → separates X ((step X)^[t k] p.input.x₀) := by
  intro t
  let m := fun j i => margin .conv p.input.d (X i) ((step X)^[j] p.input.x₀)
  let C := g.ceiling q X s
  have ht (a b : ℕ) (h : a ≤ b) : t a ≤ t b := by dsimp [t]; gcongr
  obtain ⟨hβ,hstart,_,_,ho,hlo,hw,hend⟩ := hc
  have bounds (j : ℕ) (hj : j ≤ t L) (i : Fin p.input.n) :
      g.lowerMass s X j i ≤ Real.exp (-g.β*m j i) ∧
      Real.exp (-g.β*m j i) ≤ g.upper s X j i := by
    have h := abs_le.mp ((hb j hj _ (source_error s X _ he j hj)).2.2.2.2 i)
    dsimp only [ScoreWork.lowerMass, ScoreWork.upper, m]
    constructor <;> apply Real.exp_le_exp.mpr <;> nlinarith [hβ.le]
  have mass (k : ℕ) (hk : g.start ≤ k) (hK : k ≤ L) :
      ExponentialMarginWork.mass g.β (m (t k)) ≤ C k := by
    induction k, hk using Nat.le_induction with
    | base =>
      exact (Finset.sum_le_sum fun i _ => (bounds _ (ht _ _ hstart) i).2).trans ho
    | succ k hk ih =>
      have hmem : k ∈ Finset.Ico g.start L := Finset.mem_Ico.mpr ⟨hk,by omega⟩
      have hd (i : Fin p.input.n) :
          ∑ j ∈ Finset.range p.block, g.lower (t k+j) i ≤ m (t (k+1)) i-m (t k) i := by
        have hn (N : ℕ) (hN : N ≤ p.block) :
            ∑ j ∈ Finset.range N, g.lower (t k+j) i ≤ m (t k+N) i-m (t k) i := by
          induction N with
          | zero => simp
          | succ j ih =>
            have hj : t k+j ∈ Finset.Ico (t g.start) (t L) := by
              apply Finset.mem_Ico.mpr
              refine ⟨(ht _ _ hk).trans (Nat.le_add_right _ _), ?_⟩
              have hh : t k + (p.block : ℕ) = t (k+1) := by simp [t,Nat.mul_succ,Nat.add_assoc]
              exact (Nat.add_lt_add_left (by omega : j < (p.block : ℕ)) (t k)).trans_le (hh ▸ ht _ _ hK)
            have H := hlo _ hj _ (source_error s X _ he _ (Finset.mem_Ico.mp hj).2.le) i
            have Hstep : m (t k+j+1) i-m (t k+j) i =
                scoreDrift X i ((step X)^[t k+j] p.input.x₀) := by
              dsimp only [m]
              rw [Function.iterate_succ_apply']
              exact score_step _ _ _
            rw [← Hstep] at H
            rw [Finset.sum_range_succ]
            have H' := ih (by omega)
            rw [← Nat.add_assoc]
            linarith
        simpa [t,Nat.mul_succ,Nat.add_assoc] using hn p.block le_rfl
      have hrat : 0 ≤ C (k+1)/C k := by dsimp [C,ScoreWork.ceiling]; positivity
      have hC : C k ≠ 0 := (Real.exp_pos _).ne'
      have ha := ExponentialMarginWork.increment hβ (fun i => (bounds _ (ht _ _ (by omega : k ≤ L)) i).1)
        (fun i => (bounds _ (ht _ _ (by omega : k ≤ L)) i).2) hd (hw _ hmem)
      exact ha.trans (by
        calc _ ≤ (C (k+1)/C k)*C k := mul_le_mul_of_nonneg_left (ih (by omega)) hrat
             _ = C (k+1) := div_mul_cancel₀ _ hC)
  intro k hk hR i
  obtain ⟨hs,_,hc⟩ := hend k hk hR
  exact ExponentialMarginWork.strictly_positive hβ ((mass k hs hk).trans_lt hc) i

lemma epochs_formula (p : Params) : epochs p =
    ⌈(∑ i : Fin p.bins, p.width i/(p.c i*p.W i))/
       (2*p.η*p.block)⌉₊ := by
  have hh (i : Fin p.bins) : p.width i/(p.c i*p.W i) =
      p.atBin p.width i.val/(p.atBin p.c i.val*p.atBin p.W i.val) := by
    simp [Params.atBin,i.isLt]
  simp_rw [hh]
  rw [Fin.sum_univ_eq_sum_range (fun i => p.atBin p.width i/(p.atBin p.c i*p.atBin p.W i))]
  unfold epochs speed Params.input
  congr 1
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Params.edge, add_sub_cancel_left, mul_inv_rev]
  ring

lemma reaches_fit {p : Params} (X : Rows p.input) (hv : valid p) (hg : geometry p X) :
    ∃ t ≤ p.burn+p.block*epochs p, fit X ((step X)^[t] p.input.x₀) = true := by
  let B : ℕ := p.block
  let K := epochs p
  let t := fun k => p.burn+B*k
  let z := fun k => (step X)^[t k] p.input.x₀
  obtain ⟨s,q,L,hLK,hend,_,_,_,he,hb,h₀,hg,hgate⟩ := hg
  have htime (i j : ℕ) (h : i ≤ j) : t i ≤ t j := by dsimp [t]; gcongr
  have H (k : ℕ) (hk : k ≤ L) := hb (t k) (htime k L hk) (z k)
    (source_error s X (t L) he _ (htime k L hk))
  have hfitGate (k : ℕ) (hk : k ≤ L) (hr : p.edge p.bins ≤ radius (z k)) :
      separates X (z k) := by
    rcases hgate with hgate | ⟨g,hg⟩
    swap
    · exact work_gate X s q g L hg he hb k hk (hr.trans (H k hk).2.1)
    intro i
    have hb' := H k hk
    have hscore := hgate k hk (hr.trans hb'.2.1) i
    have ha := (abs_le.mp (hb'.2.2.2.2 i)).1
    linarith
  rcases hend with hEq | hr
  swap
  · have htime₀ := htime 0 L (Nat.zero_le _)
    have heq : t 0 + (t L - t 0) = t L := Nat.add_sub_of_le htime₀
    have hwork := epoch_radius X s (t L) hv.1 he hb (t 0) (t L - t 0) heq.le
    rw [heq] at hwork
    have hstart := h₀.trans (H 0 (Nat.zero_le _)).1
    have hclose : p.edge p.bins ≤ radius (z L) := by
      change _ ≤ radius (z L) - radius (z 0) at hwork
      linarith
    exact ⟨t L,htime L K hLK,by simpa [fit] using hfitGate L le_rfl hclose⟩
  subst L
  have hv' (i : ℕ) (hi : i < p.bins) : 0 < speed p i := by
    have hi' := hv.2.2.2.2 i hi
    dsimp [speed]
    positivity [hv.1, hi'.1, hi'.2]
  have hf := RadialWorkPotential.first_fit (fun k => radius (z k))
    (fun k => separates X (z k)) p.edge (speed p) p.bins hv.2.2.2.1 hv' (h₀.trans (H 0 (Nat.zero_le _)).1)
  obtain ⟨k,hk,hfit⟩ := hf hfitGate (by
    intro k hk _
    have hdata := H k hk.le
    obtain ⟨hpos,hcover⟩ := hg k hk
    refine ⟨s.gain (t k) B,hpos,?_,hcover _ ⟨hdata.1,hdata.2.1⟩⟩
    have ht : t k+B = t (k+1) := by simp [t, Nat.mul_succ, Nat.add_assoc]
    have hh := epoch_radius X s (t K) hv.1 he hb (t k) B (ht ▸ htime _ _ hk)
    rw [ht] at hh
    change radius (z k)+_ ≤ radius (z (k+1))
    change _ ≤ radius (z (k+1))-radius (z k) at hh
    linarith)
  exact ⟨t k,htime k K hk,by simpa [fit] using hfit⟩

end LongTails.Proofs.RidgeClockTwoTapConvergence

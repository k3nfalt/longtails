import LongTails.Proofs.SpectralTwoTapResponse
import LongTails.Proofs.SpectralTwoTapGeometry

open scoped RealInnerProductSpace
open LongTails.Setups.SpectralTwoTapLogistic
open LongTails.Proofs.SpectralTwoTapResponse LongTails.Proofs.SpectralTwoTapGeometry

namespace LongTails.Proofs.SpectralTwoTapSeparation

variable {u : Input} {X : Images u}

lemma enclosure (q : Source u) (T : ℕ) (he : q.encloses X T) (z : ℕ → State u.d)
    (hz : z 0 = u.start) (step : ∀ t, z (t+1) = z t + u.η • descent X (z t)) :
    ∀ t < T, ‖z t-q.point t‖ ≤ q.width t := by
  let y (t : ℕ) := z t-q.point t
  let e (t : ℕ) := y (t+1)-q.linear t (y t)
  have rep (a k : ℕ) : q.response a (y a) e k = y (a+k) := by
    induction k with
    | zero => simp [Source.response]
    | succ k ih =>
      rw [Source.response,ih]
      dsimp only [e]
      rw [add_sub_cancel]
      rfl
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    by_cases hzero : t = 0
    · simpa [hzero,hz] using he.1
    obtain ⟨a,ha,gain⟩ := he.2.2 t (Nat.pos_of_ne_zero hzero) ht
    have bound (j : ℕ) (hj : j ∈ Finset.Ico a t) : ‖e j‖ ≤ q.defect j := by
      have jj := (Finset.mem_Ico.mp hj).2
      have h := he.2.1 j (by omega) (y j) (ih j jj (by omega))
      dsimp only [y] at h
      rw [add_sub_cancel] at h
      simpa only [e,y,step j] using h
    have hh := gain (y a) (ih a ha (by omega)) e bound
    rw [rep,Nat.add_sub_of_le ha.le] at hh
    exact hh

lemma prediction_error (s : Spectrum X) (q : Source u) {K T : ℕ} (hT : 0 < T)
    (z : ℕ → State u.d) (hz : z 0 = u.start) (step : ∀ t, z (t+1) = z t + u.η • descent X (z t))
    (he : q.encloses X (K+T)) {κ : ℝ} (δ : ℕ → ℝ) (hk : ∀ j, |s.multiplier j| ≤ κ)
    (hδ : ∀ t < T, ∀ v, ‖v‖ ≤ q.width (K+t) →
      ‖s.remainder (q.point (K+t)+v)-s.remainder (q.point (K+t))‖ ≤ δ t) :
    ‖z (K+T)-(s.center+(s.affine T+s.correction q K T))‖ ≤
      propagation κ (q.width K) δ T := by
  have mem := enclosure q (K+T) he z hz step
  have hκ := (abs_nonneg _).trans (hk (0 : Modes u))
  have hh (t : ℕ) (ht : t ≤ T) :
      ‖z (K+t)-(s.center+(s.affine t+s.correction q K t))‖ ≤
      propagation κ (q.width K) δ t := by
    induction t with
    | zero =>
      have hw := mem K (by omega)
      simpa [Spectrum.affine,Spectrum.correction,propagation] using hw
    | succ t ih =>
      have lt : t < T := by omega
      have herr := hδ t lt (z (K+t)-q.point (K+t)) (mem (K+t) (by omega))
      rw [add_sub_cancel] at herr
      let y := s.center+(s.affine t+s.correction q K t)
      have eqn : z (K+(t+1))-(s.center+(s.affine (t+1)+s.correction q K (t+1))) =
          s.move (z (K+t)-y) + (s.remainder (z (K+t))-s.remainder (q.point (K+t))) := by
        rw [← Nat.add_assoc,step,Spectrum.affine,Spectrum.correction,
          show z (K+t)-y = (z (K+t)-s.center)-(s.affine t+s.correction q K t) by dsimp [y]; abel,
          move_sub,move_add]
        unfold Spectrum.remainder
        simp only [smul_sub]
        abel
      rw [eqn]
      exact (norm_add_le _ _).trans (add_le_add
        ((move_bound s κ hk _).trans (mul_le_mul_of_nonneg_left (ih lt.le) hκ)) herr)
  exact hh T le_rfl

lemma separates (p : Params) (hp : valid p) (X : Images p.input) (hg : geometry p X)
    (z : ℕ → State p.input.d) (hz : z 0 = p.input.start)
    (step : ∀ t, z (t+1) = z t + p.input.η • descent X (z t)) :
    correct X (z (p.K + 2*⌈2*p.d/p.W⌉₊)) := by
  let N := ⌈2*p.d/p.W⌉₊
  let T := 2*N
  have hN : 2*p.d ≤ (N:ℝ)*p.W := (div_le_iff₀ hp.2.2.1).mp (Nat.le_ceil _)
  have hn : 0 < N := Nat.ceil_pos.mpr (by exact div_pos (mul_pos (by norm_num) hp.2.1) hp.2.2.1)
  have ht : 0 < T := Nat.mul_pos (by decide) hn
  obtain ⟨hard,s,q,R,σ,κ,δ,_,_,he,hδ,hk,hσ,hR,hW,hc,hd,hh,bulk⟩ := hg
  have ran := prediction_error s q ht z hz step he δ (fun j => (hk j).1) hδ
  have priced := allowance_floor s hard hp.2.1 hp.2.2.1 hp.2.2.2 hR
    (fun j => (hk j).2) (by rw [← hW]; linarith only [hp.2.2.1,hσ]) hc N hN
  let a := s.affine T
  let c := s.correction q p.K T
  let err := propagation κ (q.width p.K) δ T
  let base (i : Fin p.input.n) := score (X i) (q.point p.K)+⟪action (X i) s.center,a⟫
  let nonlinear (i : Fin p.input.n) := score (X i) s.center-score (X i) (q.point p.K) +
    ⟪action (X i) s.center,c⟫+score (X i) (a+c)
  let loss (i : Fin p.input.n) := max 0 (-nonlinear i)+scoreError (X i) (s.center+(a+c)) err
  have hrow (i : Fin p.input.n) : base i-loss i ≤ score (X i) (z (p.K+T)) := by
    have qs := quadratic (X i) s.center (s.center+(a+c))
    rw [add_sub_cancel_left,inner_add_right] at qs
    have qs' := (abs_le.mp (score_near (X i) _ _ ran)).1
    have hmin := le_max_right (0:ℝ) (-nonlinear i)
    dsimp only [base,loss,nonlinear] at *
    change -scoreError (X i) (s.center+(a+c)) err ≤
      score (X i) (z (p.K+T)) - score (X i) (s.center+(a+c)) at qs'
    linarith only [qs,qs',hmin]
  intro i
  by_cases hi : i = hard
  · subst i
    change loss hard + σ*(∑ j ∈ Finset.range N,R^j) ≤ p.d/4 at hh
    change 5*p.d/4 < σ*(∑ j ∈ Finset.range N,R^j) + ⟪action (X hard) s.center,a⟫ at priced
    have hr := hrow hard
    dsimp only [base] at hr
    linarith only [hh,priced,hd,hr]
  · obtain ⟨hb,hl⟩ := bulk i hi
    change 0 < base i at hb
    change loss i ≤ 3*base i/4 at hl
    linarith only [hrow i,hb,hl]

end LongTails.Proofs.SpectralTwoTapSeparation

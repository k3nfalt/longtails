import LongTails.Proofs.PreferenceTranscriptDistance
import LongTails.Proofs.SphericalPreferenceHypercube

open scoped BigOperators

namespace LongTails.Proofs.SphericalPreferenceTranscript

open LongTails.Proofs.PreferenceTranscriptDistance LongTails.Proofs.SphericalPreferenceHypercube

def Words : ℕ → Type
  | 0 => Unit
  | k+1 => Words k × Bool

instance wordsFinite : (k : ℕ) → Fintype (Words k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k+1 => @instFintypeProd _ _ (wordsFinite k) inferInstance

def state {S : Type*} (s : S) (step : S → Bool → S) : (k : ℕ) → Words k → S
  | 0,_ => s
  | k+1,w => step (state s step k w.1) w.2

def factor (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

noncomputable def weight {S : Type*} (s : S) (step : S → Bool → S) (p : S → ℝ) :
    (k : ℕ) → Words k → ℝ
  | 0,_ => 1
  | k+1,w => weight s step p k w.1 * factor (p (state s step k w.1)) w.2

lemma weight_nonneg {S : Type*} (s : S) (step : S → Bool → S) (p : S → ℝ)
    (hp : ∀ x, p x ∈ Set.Icc 0 1) (k : ℕ) (w : Words k) : 0 ≤ weight s step p k w := by
  induction k with
  | zero => exact zero_le_one
  | succ k ih =>
    apply mul_nonneg (ih w.1)
    cases w.2 <;> simp only [factor, Bool.false_eq_true,ite_false,ite_true]
    · exact sub_nonneg.mpr (hp _).2
    · exact (hp _).1

lemma mass_one {S : Type*} (s : S) (step : S → Bool → S) (p : S → ℝ) (k : ℕ) :
    ∑ w : Words k, weight s step p k w = 1 := by
  induction k with
  | zero => change ∑ _w : Unit, (1:ℝ) = 1
            simp
  | succ k ih =>
    change ∑ w : Words k × Bool, weight s step p k w.1 * factor (p (state s step k w.1)) w.2 = _
    rw [Fintype.sum_prod_type]
    simpa [weight,Fintype.sum_bool,factor,← mul_add] using ih

lemma cost_sum {d k : ℕ} (m : Vertex d → Words k → ℝ) (e : Fin d → Words k → ℝ)
    (hm : ∀ v w, 0 ≤ m v w) (hM : ∀ v, ∑ w, m v w = 1) {C : ℝ}
    (he : ∀ w, ∑ i, e i w ≤ C) :
    ∑ v, ∑ i, ∑ w, (m v w + m (SphericalPreferenceHypercube.flip v i) w) * e i w ≤
      2 * Fintype.card (Vertex d) * C := by
  have hinv (i : Fin d) (w : Words k) : ∑ v : Vertex d, m (SphericalPreferenceHypercube.flip v i) w = ∑ v, m v w :=
    (flipEquiv i).sum_comp (fun v => m v w)
  calc
    _ = ∑ i, ∑ w, (2 * ∑ v, m v w) * e i w := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      rw [← Finset.sum_mul,Finset.sum_add_distrib,hinv,two_mul]
    _ = ∑ w, (2 * ∑ v, m v w) * ∑ i, e i w := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ w, (2 * ∑ v, m v w) * C := Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (he w) (mul_nonneg (by norm_num) (Finset.sum_nonneg fun v _ => hm v w))
    _ = _ := by
      rw [← Finset.sum_mul,← Finset.mul_sum]
      congr 2
      rw [Finset.sum_comm]
      simp [hM]

lemma transcript_distance {d : ℕ} {S : Type*} (s : S) (step : S → Bool → S)
    (p : Vertex d → S → ℝ) (e : Fin d → S → ℝ) {C : ℝ}
    (hp : ∀ v x, p v x ∈ Set.Icc 0 1) (hC : ∀ x, ∑ i, e i x ≤ C)
    (hstep : ∀ v i x a b, 0 ≤ a → 0 ≤ b →
      ∑ c : Bool, squareDistance (a * factor (p v x) c) (b * factor (p (SphericalPreferenceHypercube.flip v i) x) c) ≤
        squareDistance a b + (a+b)*e i x) (k : ℕ) :
    ∑ v, ∑ i, ∑ w : Words k, squareDistance (weight s step (p v) k w)
      (weight s step (p (SphericalPreferenceHypercube.flip v i)) k w) ≤ k * (2*Fintype.card (Vertex d)*C) := by
  induction k with
  | zero => simp only [weight,squareDistance,sub_self,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,Finset.sum_const_zero,Nat.cast_zero,zero_mul,le_refl]
  | succ k ih =>
    let m := fun v => weight s step (p v) k
    let t := state s step k
    have hcost := cost_sum m (fun i w => e i (t w)) (fun v => weight_nonneg s step _ (hp v) k)
      (fun v => mass_one s step (p v) k) (fun w => hC (t w))
    change ∑ v, ∑ i, ∑ w : Words k × Bool, _ ≤ _
    simp_rw [Fintype.sum_prod_type]
    have hle := Finset.sum_le_sum (s := Finset.univ) (fun (v : Vertex d) _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin d) _ =>
        Finset.sum_le_sum (s := Finset.univ) (fun (w : Words k) _ =>
          hstep v i (t w) (m v w) (m (SphericalPreferenceHypercube.flip v i) w)
            (weight_nonneg s step _ (hp v) k w) (weight_nonneg s step _ (hp _) k w))))
    apply hle.trans
    simp only [Finset.sum_add_distrib]
    dsimp only [m,t] at *
    push_cast
    linarith only [ih,hcost]

lemma overlap (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    3*(a+b) ≤ 8*min a b + 16*squareDistance a b := by
  unfold squareDistance
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    nlinarith only [sq_nonneg (13*Real.sqrt b-16*Real.sqrt a),Real.sq_sqrt ha,Real.sq_sqrt hb,ha]
  · rw [min_eq_right h]
    nlinarith only [sq_nonneg (13*Real.sqrt a-16*Real.sqrt b),Real.sq_sqrt ha,Real.sq_sqrt hb,hb]

def mistake (d b : Bool) : ℝ := if d=b then 0 else 1

lemma paired_loss {d k : ℕ} (m : Vertex d → Words k → ℝ) (hm : ∀ v w, 0 ≤ m v w)
    (hmass : ∀ v, ∑ w, m v w = 1) (decoder : Words k → Vertex d) :
    6*(Fintype.card (Vertex d) : ℝ)*d ≤
      16* (∑ v, ∑ i, ∑ w, m v w * mistake (decoder w i) (v i)) +
      16* (∑ v, ∑ i, ∑ w, squareDistance (m v w) (m (SphericalPreferenceHypercube.flip v i) w)) := by
  let loss := fun v i w => m v w * mistake (decoder w i) (v i)
  have hone (v i w) : 3*(m v w + m (SphericalPreferenceHypercube.flip v i) w) ≤
      8*(loss v i w + loss (SphericalPreferenceHypercube.flip v i) i w)+16*squareDistance (m v w) (m (SphericalPreferenceHypercube.flip v i) w) := by
    apply (overlap _ _ (hm v w) (hm _ w)).trans
    have hbit : SphericalPreferenceHypercube.flip v i i = !(v i) := by simp [SphericalPreferenceHypercube.flip]
    have hle : min (m v w) (m (SphericalPreferenceHypercube.flip v i) w) ≤ loss v i w + loss (SphericalPreferenceHypercube.flip v i) i w := by
      unfold loss
      rw [hbit]
      cases decoder w i <;> cases v i <;> simp [mistake]
    linarith only [hle]
  have hswap (g : Vertex d → Fin d → Words k → ℝ) :
      ∑ v, ∑ i, ∑ w, g (SphericalPreferenceHypercube.flip v i) i w = ∑ v, ∑ i, ∑ w, g v i w := by
    rw [Finset.sum_comm,Finset.sum_comm (f := fun v i => ∑ w, g v i w)]
    exact Finset.sum_congr rfl fun i _ => (flipEquiv i).sum_comp (fun v => ∑ w, g v i w)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (v : Vertex d) _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin d) _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun (w : Words k) _ => hone v i w)))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at h
  rw [hswap loss] at h
  simp only [hmass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h
  dsimp only [loss] at h
  linarith only [h]

end LongTails.Proofs.SphericalPreferenceTranscript

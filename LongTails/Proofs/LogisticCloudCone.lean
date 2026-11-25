import Mathlib.Tactic

namespace LongTails.Proofs.LogisticCloudCone

structure Point where
  p : ℝ
  q : ℝ
  u : ℝ
  t : ℝ
  v : ℝ

def Cone (a : ℝ) (x : Point) : Prop :=
  0 < x.p ∧ -4 * a * x.p ≤ x.q ∧ x.p / 2 ≤ x.u ∧ x.u ≤ 4 * (x.p + x.q) ∧
  0 < x.v ∧ x.v / 2 ≤ x.t ∧ x.t ≤ 2 * x.v

def step (x : Point) (h j l e f : ℝ) : Point :=
  ⟨x.p + h * x.q + j * (x.u + e), x.q + h * x.p, x.u + j * x.p,
    x.t + l * (x.v + f), x.v + l * x.t⟩

def mass (x : Point) : ℝ := x.p + x.q + x.u

lemma geometry {a : ℝ} {x : Point} (ha : a ≤ 1 / 16) (hx : Cone a x) (hq : x.q ≤ 0) :
    3 / 4 * x.p ≤ x.p + x.q ∧ x.u ≤ 4 * x.p ∧
      x.p ≤ mass x ∧ mass x ≤ 5 * x.p := by
  obtain ⟨hp, hangle, hu, hu', _⟩ := hx
  have h := mul_le_mul_of_nonneg_right ha hp.le
  dsimp [mass]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma advance {a h j l e f : ℝ} {x : Point} (ha : 0 ≤ a) (ha' : a ≤ 1 / 16)
    (hx : Cone a x) (hq : x.q ≤ 0) (hh : |h| ≤ 1 / 2)
    (hlo : -(5 / 4) * a * j ≤ h) (hj : 0 ≤ j) (hj' : j ≤ 1 / 2)
    (hl : 0 ≤ l) (hl' : l ≤ 1 / 2) (he : |e| ≤ x.p / 8) (hf : |f| ≤ x.v / 8) :
    Cone a (step x h j l e f) ∧
    mass x + j * x.p ≤ mass (step x h j l e f) ∧
    x.p / 2 ≤ (step x h j l e f).p ∧ x.v ≤ (step x h j l e f).v := by
  obtain ⟨hp, hangle, hu, hu', hv, ht, ht'⟩ := hx
  obtain ⟨eh, eh'⟩ := abs_le.mp he
  obtain ⟨fh, fh'⟩ := abs_le.mp hf
  obtain ⟨hh₁, hh₂⟩ := abs_le.mp hh
  have hap := mul_le_mul_of_nonneg_right ha' hp.le
  have ht₀ : 0 ≤ x.t := by linarith
  have hsum : 0 ≤ x.p + x.q := by linarith
  have hju := mul_le_mul_of_nonneg_left (show 3/8*x.p ≤ x.u+e by linarith) hj
  have hjp := mul_nonneg hj hp.le
  have haj := mul_le_mul_of_nonneg_right ha' hj
  have hjq := mul_nonpos_of_nonneg_of_nonpos hj hq
  have hlow : -(1/8)*j ≤ h := by linarith
  have hprod := mul_le_mul_of_nonpos_right hlow hq
  have hP : x.p/2 ≤ x.p+h*x.q+j*(x.u+e) := by
    linarith [mul_le_mul_of_nonpos_right hh₂ hq]
  have hqj := mul_le_mul_of_nonneg_left (show -(1:ℝ)*x.p ≤ x.q by linarith) hj
  have hθ : -(1:ℝ)/2 ≤ h := by linarith
  have hθ' : 0 ≤ 1+4*a*h := by
    nlinarith [mul_le_mul_of_nonneg_left hθ ha]
  have hangle' : 0 ≤ (x.q+h*x.p)+4*a*(x.p+h*x.q+j*(x.u+e)) := by
    have h₁ := mul_nonneg hθ' (show 0 ≤ x.q+4*a*x.p by linarith)
    have hb : 0 ≤ 1-(4*a)^2 := by
      nlinarith [mul_nonneg (show 0 ≤ 1-4*a by linarith) (show 0 ≤ 1+4*a by linarith)]
    have h₂ := mul_le_mul_of_nonneg_right hlo (mul_nonneg hb hp.le)
    have h₃ := mul_le_mul_of_nonneg_left hju ha
    nlinarith only [h₁,h₂,h₃,mul_nonneg (mul_nonneg ha hjp) (sq_nonneg (4*a)),
      mul_nonneg ha hjp]
  have hU := mul_nonneg (show 0 ≤ 1-j/2 by linarith) (show 0 ≤ x.u-x.p/2 by linarith)
  have hU' := mul_nonneg (show 0 ≤ 1+h by linarith) (show 0 ≤ 4*(x.p+x.q)-x.u by linarith)
  have hsum' := mul_le_mul_of_nonneg_right hlow hsum
  have hv' := mul_nonneg hl ht₀
  have hT := mul_nonneg (show 0 ≤ 1-l/2 by linarith) (show 0 ≤ x.t-x.v/2 by linarith)
  have hT' := mul_nonneg (show 0 ≤ 1-2*l by linarith) (show 0 ≤ 2*x.v-x.t by linarith)
  dsimp [Cone, step, mass]
  refine ⟨⟨by linarith, by linarith, ?_, ?_, by linarith, ?_, ?_⟩, ?_, hP, by linarith⟩
  · nlinarith only [hU,hprod,hqj,mul_le_mul_of_nonneg_left eh' hj,hjp]
  · nlinarith only [hu',hju,hsum',hjq]
  · nlinarith only [hT,mul_le_mul_of_nonneg_left (show -x.v/8 ≤ f by linarith) hl,
      mul_nonneg hl hv.le]
  · nlinarith only [hT',mul_le_mul_of_nonneg_left fh' hl,mul_nonneg hl hv.le]
  · nlinarith only [hju,hsum',hjq,hjp]


def amplitude (x : Point) : ℝ := max x.u x.v

lemma amplitude_bounds {a : ℝ} {x : Point} (hx : Cone a x) :
    0 < amplitude x ∧ x.p ≤ 2 * amplitude x ∧ x.t ≤ 2 * amplitude x := by
  obtain ⟨_, _, hu, _, hv, _, ht⟩ := hx
  dsimp [amplitude]
  exact ⟨hv.trans_le (le_max_right _ _), by linarith [le_max_left x.u x.v],
    by linarith [le_max_right x.u x.v]⟩

lemma amplitude_step {a h j l e f δ : ℝ} {x : Point} (hx : Cone a x)
    (hj : 0 ≤ j) (hl : 0 ≤ l) (hj' : 2 * j ≤ δ) (hl' : 2 * l ≤ δ) :
    amplitude x ≤ amplitude (step x h j l e f) ∧
    amplitude (step x h j l e f) ≤ (1 + δ) * amplitude x := by
  obtain ⟨H, hp', ht'⟩ := amplitude_bounds hx
  obtain ⟨hp, _, _, _, hv, ht, _⟩ := hx
  have hu := le_max_left x.u x.v
  have hv' := le_max_right x.u x.v
  dsimp [amplitude,step] at *
  constructor
  · apply max_le_max <;> nlinarith [mul_nonneg hj hp.le,
      mul_nonneg hl (show 0 ≤ x.t by linarith)]
  · apply max_le <;> nlinarith [mul_le_mul_of_nonneg_left hp' hj,
      mul_le_mul_of_nonneg_left ht' hl, mul_le_mul_of_nonneg_right hj' H.le,
      mul_le_mul_of_nonneg_right hl' H.le]

lemma mass_growth {a h j l e f δ : ℝ} {x : Point} (ha : a ≤ 1/16)
    (hx : Cone a x) (hq : x.q ≤ 0) (hj : 0 ≤ j) (hδ : 0 ≤ δ)
    (he : |e| ≤ x.p/8) (hcases : δ/16 ≤ j ∨ δ ≤ h)
    (hinc : mass x + j*x.p ≤ mass (step x h j l e f)) :
    (1+δ/80)*mass x ≤ mass (step x h j l e f) := by
  obtain ⟨hs,_,_,hm⟩ := geometry ha hx hq
  obtain ⟨hp,_,hu,_,_⟩ := hx
  rcases hcases with h | h
  · nlinarith only [hinc,mul_le_mul_of_nonneg_right h hp.le,
      mul_le_mul_of_nonneg_left hm hδ]
  · have h₁ := mul_le_mul h hs (by positivity : 0 ≤ 3/4*x.p) (hδ.trans h)
    have h₂ := mul_nonneg hj (show 0 ≤ x.p+x.u+e by linarith [(abs_le.mp he).1])
    dsimp [mass,step] at *
    nlinarith only [h₁,h₂,mul_le_mul_of_nonneg_left hm hδ,mul_nonneg hδ hp.le]

def signal (β : ℝ) (x : Point) : ℝ := β*x.p*x.u+x.t*x.v

lemma signal_bounds {a β : ℝ} {x : Point} (hx : Cone a x)
    (hq : x.q ≤ 0) (hβ : 4/5 ≤ β) (hβ' : β ≤ 1) :
    (amplitude x)^2/5 ≤ signal β x ∧ signal β x ≤ 4*(amplitude x)^2 := by
  obtain ⟨H,hp',ht'⟩ := amplitude_bounds hx
  obtain ⟨hp, _, hu, hu', hv, ht, _⟩ := hx
  have hu₀ : 0 ≤ x.u := by linarith
  have ht₀ : 0 ≤ x.t := by linarith
  have hpu := mul_nonneg hp.le hu₀
  have htv := mul_nonneg ht₀ hv.le
  have h₁ := mul_le_mul_of_nonneg_right hβ hpu
  have h₂ := mul_le_mul_of_nonneg_right ht hv.le
  dsimp [signal]
  constructor
  · rcases max_cases x.u x.v with ⟨h,_⟩ | ⟨h,_⟩ <;> simp only [amplitude,h]
    · nlinarith only [h₁,htv,mul_le_mul_of_nonneg_right (show x.u ≤ 4*x.p by linarith) hu₀]
    · nlinarith only [h₁,hpu,h₂,sq_nonneg x.v]
  · have h₃ := mul_le_mul hp' (le_max_left x.u x.v) hu₀ (by positivity : 0 ≤ 2*amplitude x)
    have h₄ := mul_le_mul ht' (le_max_right x.u x.v) hv.le (by positivity : 0 ≤ 2*amplitude x)
    dsimp [amplitude] at *
    nlinarith only [h₃,h₄,mul_le_mul_of_nonneg_right hβ' hpu]

end LongTails.Proofs.LogisticCloudCone

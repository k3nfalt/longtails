import LongTails.Proofs.OptimumHeterogeneityDesign

namespace LongTails.Proofs.OptimumHeterogeneitySupport

open LongTails.Setups.DistributedOptimumHeterogeneity LongTails.Algorithms.OptimumHeterogeneityDesign

variable {p : Params}

noncomputable def score (p : Params) (w : Fin p.n → ℝ) (t : ℝ) :=
  p.n * p.μ * t - ∑ i, p.L i * max (t-w i) 0

lemma score_le (w : Fin p.n → ℝ) {a : Fin p.n → ℝ} (ha : a ∈ admissibleCurvatures p)
    {t : ℝ} (ht : 0 ≤ t) : score p w t ≤ ∑ i, w i * a i := by
  have h (i) : t*a i-p.L i*max (t-w i) 0 ≤ w i*a i := by
    have h₁ := mul_le_mul_of_nonneg_right (le_max_left (t-w i) 0) (ha.1 i).1
    have h₂ := mul_le_mul_of_nonneg_right (ha.1 i).2 (le_max_right (t-w i) 0)
    linarith only [h₁,h₂]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  unfold score
  linarith only [hs, mul_le_mul_of_nonneg_right ha.2 ht]

lemma exact_score (hp : spec.valid p) (w : Fin p.n → ℝ) :
    ∃ j, ∃ a ∈ admissibleCurvatures p, score p w (w j) = ∑ i, w i*a i := by
  classical
  let B : ℝ := p.n*p.μ
  let mass (t : ℝ) := ∑ i, if w i ≤ t then p.L i else 0
  let good := Finset.univ.filter (fun j => B ≤ mass (w j))
  obtain ⟨v,_,hv⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  have hv' (i) := hv i (Finset.mem_univ i)
  have hgood : v ∈ good := by
    simpa [good,mass,hv'] using hp.1.2.2.2.1
  obtain ⟨j,hj,hm⟩ := Finset.exists_min_image good w ⟨v,hgood⟩
  let t := w j
  let low i := if w i < t then p.L i else 0
  let tie i := if w i = t then p.L i else 0
  let A := ∑ i, low i
  let E := ∑ i, tie i
  have hhi : B ≤ A+E := by
    have hj' := (Finset.mem_filter.mp hj).2
    change B ≤ ∑ i, if w i ≤ t then p.L i else 0 at hj'
    apply hj'.trans_eq
    change _ = (∑ i, low i) + ∑ i, tie i
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases lt_trichotomy (w i) t with h|h|h
    · simp [low,tie,h,h.le,h.ne]
    · simp [low,tie,h]
    · simp [low,tie,h.not_ge,h.not_gt,h.ne']
  have hB : 0 < B := mul_pos (by exact_mod_cast p.n.pos) hp.1.2.2.1
  let below := Finset.univ.filter fun i => w i < t
  have hlo : A ≤ B := by
    by_cases hn : below.Nonempty
    · obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image below w hn
      have hk' : w k < t := (Finset.mem_filter.mp hk).2
      have hiff (i) : w i ≤ w k ↔ w i < t :=
        ⟨fun h => h.trans_lt hk',fun h => hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)⟩
      have heq : mass (w k) = A := by simp [mass,A,low,hiff]
      by_contra! h
      exact (not_le.mpr hk') (hm k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq.symm ▸ h.le⟩))
    · have hn' (i) : ¬ w i < t := fun h => hn ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
      simpa [A,low,hn'] using hB.le
  have hE : 0 ≤ E := Finset.sum_nonneg fun i _ => by dsimp [tie]; split <;> simp [hp.1.2.1]
  let r := (B-A)/E
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hlo) hE
  have hr' : r ≤ 1 := by
    rcases hE.eq_or_lt with he|he
    · simp [r,←he]
    · exact (div_le_one he).mpr (by linarith)
  have hrE : r*E = B-A := by
    rcases hE.eq_or_lt with he|he
    · rw [← he] at hhi ⊢; linarith
    · exact div_mul_cancel₀ _ he.ne'
  let a i := low i + r*tie i
  have hsum : ∑ i, a i = B := by
    simp only [a, Finset.sum_add_distrib, ← Finset.mul_sum]
    change A+r*E = B
    linarith
  refine ⟨j,a,⟨fun i => ?_, hsum.ge⟩,?_⟩
  · have hi := hp.1.2.1 i
    rcases lt_trichotomy (w i) t with h|h|h
    · simp [a,low,tie,h,h.ne,hi]
    · simpa [a,low,tie,h] using And.intro (mul_nonneg hr hi)
        (show r*p.L i ≤ p.L i by simpa using mul_le_mul_of_nonneg_right hr' hi)
    · simp [a,low,tie,h.ne',h.not_gt,hi]
  · have hid (i) : w i*a i = t*a i - p.L i*max (t-w i) 0 := by
      rcases lt_trichotomy (w i) t with h|h|h
      · simp [a,low,tie,h,h.ne,max_eq_left (sub_nonneg.mpr h.le)]; ring
      · simp [h]
      · simp [a,low,tie,h.not_gt,h.ne',max_eq_right (sub_nonpos.mpr h.le)]
    simp_rw [hid]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,hsum]
    unfold score
    dsimp [t,B]
    ring

lemma designs_eq (hp : spec.valid p) :
    designs p = {w | 0 ≤ Finset.univ.inf' Finset.univ_nonempty w ∧
      1 ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => score p w (w i)) ∧
      4096*p.n*p.ζ^2*centeredEnergy p w ≤ p.ε^2} := by
  ext w
  constructor
  · rintro ⟨hw,hs,hc⟩
    obtain ⟨j,a,ha,hj⟩ := exact_score hp w
    refine ⟨Finset.le_inf' _ _ (fun i _ => hw i), ?_, hc⟩
    exact (hs a ha).trans (hj ▸ Finset.le_sup' (f := fun i => score p w (w i)) (Finset.mem_univ j))
  · rintro ⟨hw,hs,hc⟩
    have hnn i := hw.trans (Finset.inf'_le w (Finset.mem_univ i))
    exact ⟨hnn,fun a ha => hs.trans (Finset.sup'_le _ _ (fun i _ => score_le w ha (hnn i))),hc⟩

end LongTails.Proofs.OptimumHeterogeneitySupport

import LongTails.Proofs.LaggedAlignment

namespace LongTails.Proofs.UscgSharpDescent

lemma sublevel_and_sum {f g z w : ℕ → ℝ} {η c Δ B lower : ℝ} {T : ℕ}
    (hη : 0 ≤ η) (hc : 0 ≤ c) (hg : ∀ i < T, 0 ≤ g i)
    (hw : ∀ i, 0 ≤ w i)
    (hstep : ∀ i < T, f (i + 1) ≤ f i - η * g i + η * z i + c)
    (hcap : ∀ i < T, f i ≤ f 0 + Δ → z i ≤ w i)
    (hsum : ∑ i ∈ Finset.range T, w i ≤ B)
    (hmargin : η * B + T * c ≤ Δ)
    (hlower : lower ≤ f T) (hgap : f 0 - lower ≤ Δ) :
    (∀ n ≤ T, f n ≤ f 0 + Δ) ∧
      η * ∑ i ∈ Finset.range T, g i ≤ Δ + η * B + T * c := by
  have hprefix : ∀ n ≤ T, ∑ i ∈ Finset.range n, min (z i) (w i) ≤ 0 * n + B := by
    intro n hn
    have h₁ := Finset.sum_le_sum (s := Finset.range n) (fun i _ => min_le_right (z i) (w i))
    have h₂ : ∑ i ∈ Finset.range n, w i ≤ ∑ i ∈ Finset.range T, w i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun i _ _ => hw i)
    simpa using h₁.trans (h₂.trans hsum)
  have hm : ∀ n ≤ T, η * (0 * n + B) + n * c ≤ Δ := by
    intro n hn
    have hn' : (n : ℝ) ≤ T := by exact_mod_cast hn
    have hh := mul_le_mul_of_nonneg_right hn' hc
    nlinarith
  have hsub := LaggedAlignment.stopped_sublevel hη hg hstep
    (w := fun i => min (z i) (w i))
    (fun i hi hp => (min_eq_left (hcap i hi (hp i le_rfl))).symm) hprefix hm
  refine ⟨hsub, ?_⟩
  have hh := Finset.sum_le_sum (s := Finset.range T)
    (fun i hi => hcap i (Finset.mem_range.mp hi) (hsub i (Finset.mem_range.mp hi).le))
  simpa using LaggedAlignment.average_from_descent hη hstep hlower hgap
    (μ := 0) (b := B) (by simpa using hh.trans hsum)

lemma shifted_sum_le {a : ℕ → ℝ} {G : ℝ} (hzero : 0 ≤ a 0)
    (hbound : ∀ i, a i ≤ G) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) ≤ (∑ i ∈ Finset.range n, a i) + G := by
  have he : ∀ n, (∑ i ∈ Finset.range n, a (i + 1)) + a 0 =
      (∑ i ∈ Finset.range n, a i) + a n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp only [Finset.sum_range_succ]; linarith
  have hh := he n
  have hb := hbound n
  linarith

end LongTails.Proofs.UscgSharpDescent

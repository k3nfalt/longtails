import LongTails.Proofs.GraceSteinerPruning

namespace LongTails.Proofs.GraceSteinerPrices

open GraceSteinerCuts GraceSteinerPruning

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma singleton_connector (S : Finset V) (a : Endpoints V E) (hS : S.card ≤ 1) :
    Connects a S ∅ := by
  intro C hC
  obtain ⟨⟨i, hi, hiC⟩, ⟨j, hj, hjC⟩⟩ := hC
  have he := Finset.card_le_one.mp hS i hi j hj
  exact False.elim (hjC (he ▸ hiC))

lemma price_bound (a : Endpoints V E) (S U : Finset V) (hS : S ⊆ U)
    (hU : ∀ e, a.left e ∈ U ∧ a.right e ∈ U) (b c : E → ℝ)
    (hb : ∀ e, 0 ≤ b e) (hc : ∀ e, 0 ≤ c e) (rate : ℝ) (hr : 0 < rate)
    (hcut : ∀ C, Splits S C → rate ≤ cut a b C) :
    ∃ F : Finset E, Connects a S F ∧ rate * (∑ e ∈ F, c e) ≤ 2 * ∑ e, b e * c e := by
  classical
  induction U using (measure Finset.card).wf.induction generalizing a S c with
  | h U ih =>
    by_cases hsmall : S.card ≤ 1
    · exact ⟨∅, singleton_connector _ _ hsmall, by
        simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Finset.sum_nonneg fun e _ => mul_nonneg (hb e) (hc e))⟩
    have hsize : 1 < S.card := by omega
    let n (e : E) : ℝ := incidence a S e
    have hn (e : E) : 0 ≤ n e := Nat.cast_nonneg _
    have hcap : (S.card : ℝ) * rate ≤ ∑ e, b e * n e := incidence_capacity a S b rate hsize hcut
    let active := Finset.univ.filter (fun e => 0 < n e)
    have hex : active.Nonempty := by
      by_contra! hempty
      have hz (e : E) : n e = 0 := by
        have hnot : e ∉ active := by simp [hempty]
        simp [active] at hnot
        exact le_antisymm hnot (hn e)
      simp [hz] at hcap
      have hs : 0 < (S.card : ℝ) := by exact_mod_cast (show 0 < S.card by omega)
      linarith [mul_pos hs hr]
    obtain ⟨e₀, hact, hleast⟩ := Finset.exists_min_image active (fun e => c e / n e) hex
    have : Nonempty E := ⟨e₀⟩
    let δ := c e₀ / n e₀
    have hn₀ := (Finset.mem_filter.mp hact).2
    have hδ : 0 ≤ δ := div_nonneg (hc _) (hn _)
    let residual e := c e - δ * n e
    have hres (e : E) : 0 ≤ residual e := by
      apply sub_nonneg.mpr
      by_cases hp : 0 < n e
      · exact (le_div_iff₀ hp).mp (hleast e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩))
      · have hz := le_antisymm (le_of_not_gt hp) (hn e)
        simpa [hz] using hc e
    have htight : residual e₀ = 0 := by
      simp [residual, δ, div_mul_cancel₀ _ (ne_of_gt hn₀)]
    let u := a.left e₀
    let v := a.right e₀
    have hne : u ≠ v := by
      intro he
      change a.left e₀ = a.right e₀ at he
      have hz : incidence a S e₀ = 0 := by simp [incidence, Crosses, he]
      change 0 < (incidence a S e₀ : ℝ) at hn₀
      simp [hz] at hn₀
    have maps {x : V} (hx : x ∈ U) : merge u v x ∈ U.erase u := by
      by_cases hxu : x = u
      · simpa [merge, hxu, hne.symm] using (hU e₀).2
      · simp [merge, hxu, hx]
    obtain ⟨q, hq, hcost⟩ := ih (U.erase u) (Finset.card_erase_lt_of_mem (hU e₀).1)
      (a.contract u v) (S.image (merge u v)) (Finset.image_subset_iff.mpr fun _ hs => maps (hS hs))
      (fun e => ⟨maps (hU e).1, maps (hU e).2⟩) residual hres
      (contraction_preserves_mincut a b S rate hcut u v)
    have hconn := lift_connector a S e₀ q hq
    obtain ⟨r, hrS⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    obtain ⟨F, hF, hconnect, hdegree⟩ := prune_connector hrS hconn
    have hsub : ∑ e ∈ F, residual e ≤ ∑ e ∈ q, residual e := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg hF (fun e _ _ => hres e)
      by_cases hmem : e₀ ∈ q
      · simpa [Finset.insert_eq_of_mem hmem] using h
      · simpa [Finset.sum_insert hmem, htight] using h
    have hdeg : ∑ e ∈ F, n e ≤ 2 * (S.card : ℝ) := by
      dsimp only [n]
      exact_mod_cast hdegree.trans (Nat.mul_le_mul_left 2 (Nat.sub_le ..))
    have refund : rate * δ * (∑ e ∈ F, n e) ≤ 2 * δ * (∑ e, b e * n e) := by
      calc
        _ ≤ rate * δ * (2 * S.card) := mul_le_mul_of_nonneg_left hdeg (mul_nonneg hr.le hδ)
        _ = 2 * δ * ((S.card : ℝ) * rate) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcap (by positivity)
    have hrhs : ∑ e, b e * residual e = (∑ e, b e * c e) - δ * ∑ e, b e * n e := by
      simp only [residual, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro e _
      ring
    have hlhs : ∑ e ∈ F, residual e = (∑ e ∈ F, c e) - δ * ∑ e ∈ F, n e := by
      simp [residual, Finset.sum_sub_distrib, Finset.mul_sum]
    have hpaid := (mul_le_mul_of_nonneg_left hsub hr.le).trans hcost
    rw [hlhs, hrhs] at hpaid
    exact ⟨F, hconnect, by linarith only [hpaid, refund]⟩

end LongTails.Proofs.GraceSteinerPrices

import LongTails.Proofs.FractalChebyshevWindows

namespace OracleTemplate.FractalChebyshev

open Real

def chainRel (p q : ℕ × ℝ) : Prop := p.1 < q.1 ∧ p.2 = (π - q.2) / 2 ^ (q.1 - p.1)

lemma isChain_cons_cons {R : ℕ × ℝ → ℕ × ℝ → Prop} {a b : ℕ × ℝ} {l : List (ℕ × ℝ)} :
    List.IsChain R (a :: b :: l) ↔ R a b ∧ List.IsChain R (b :: l) := by
  rw [List.isChain_cons]; simp

lemma getD_flatMap_even (l : List ℝ) {j : ℕ} (hj : j < l.length) :
    (l.flatMap split).getD (2 * j) 0 = π / 2 - l.getD j 0 / 2 := by
  induction l generalizing j with
  | nil => simp at hj
  | cons ψ l ih =>
    rcases j with _ | j
    · simp [split]
    · have hj' : j < l.length := by simpa using hj
      rw [List.flatMap_cons, show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
      simp only [split, List.cons_append, List.nil_append, List.getD_cons_succ]
      rw [ih hj']

lemma getD_flatMap_odd (l : List ℝ) {j : ℕ} (hj : j < l.length) :
    (l.flatMap split).getD (2 * j + 1) 0 = π / 2 + l.getD j 0 / 2 := by
  induction l generalizing j with
  | nil => simp at hj
  | cons ψ l ih =>
    rcases j with _ | j
    · simp [split]
    · have hj' : j < l.length := by simpa using hj
      rw [List.flatMap_cons, show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring]
      simp only [split, List.cons_append, List.nil_append, List.getD_cons_succ]
      rw [ih hj']

lemma getD_mem_angles {k j : ℕ} (hj : j < 2 ^ k) :
    0 < (angles k).getD j 0 ∧ (angles k).getD j 0 < π := by
  have hj' : j < (angles k).length := by rw [angles_length]; exact hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
  exact angles_mem (List.getElem_mem hj')

lemma mem_liftChain {c : List (ℕ × ℝ)} {p : ℕ × ℝ} (hp : p ∈ liftChain c) :
    ∃ q ∈ c, p = (q.1 + 1, q.2) := by
  simp only [liftChain, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨q, hq, rfl⟩

lemma chain'_liftChain {c : List (ℕ × ℝ)} (hc : List.IsChain chainRel c) :
    List.IsChain chainRel (liftChain c) := by
  unfold liftChain
  apply List.isChain_map_of_isChain _ _ hc
  intro p q hpq
  obtain ⟨h1, h2⟩ := hpq
  refine ⟨by simp only; omega, ?_⟩
  simp only
  rw [h2]; congr 2; omega

theorem chain_props (k : ℕ) : ∀ s ≤ 2 ^ k,
    (∀ p ∈ chain k s, 0 < p.2 ∧ p.2 < π / 2) ∧ List.IsChain chainRel (chain k s) ∧
      (1 ≤ s → ∀ h β rest, chain k s = (h, β) :: rest →
        β = π - 2 ^ h * (π - (angles k).getD (s - 1) 0)) := by
  induction k with
  | zero =>
    intro s _
    simp [chain]
  | succ k ih =>
    intro s hs
    have hlen : (angles k).length = 2 ^ k := angles_length k
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' s
    · have hj : j ≤ 2 ^ k := by rw [pow_succ] at hs; omega
      have hc : chain (k + 1) (2 * j) = liftChain (chain k j) := by
        rw [chain]
        have h1 : (2 * j) % 2 = 0 := by omega
        have h2 : (2 * j + 1) / 2 = j := by omega
        simp [h1, h2]
      obtain ⟨hA, hB, hC⟩ := ih j hj
      rw [hc]
      refine ⟨?_, chain'_liftChain hB, ?_⟩
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := mem_liftChain hp
        exact hA q hq
      · intro h1 h β rest hcons
        rcases hck : chain k j with _ | ⟨⟨h', β'⟩, rest'⟩
        · rw [hck] at hcons; simp [liftChain] at hcons
        · rw [hck] at hcons
          simp only [liftChain, List.map_cons, List.cons.injEq, Prod.mk.injEq] at hcons
          obtain ⟨⟨rfl, rfl⟩, -⟩ := hcons
          have hj1 : 1 ≤ j := by omega
          have := hC hj1 h' β' rest' hck
          rw [this]
          have hidx : 2 * j - 1 = 2 * (j - 1) + 1 := by omega
          rw [angles, hidx, getD_flatMap_odd _ (by rw [hlen]; omega)]
          rw [pow_succ]; ring
    · have hj : j < 2 ^ k := by rw [pow_succ] at hs; omega
      have h1 : (2 * j + 1) % 2 = 1 := by omega
      have h2 : (2 * j + 1) / 2 = j := by omega
      have h3 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
      have hc : chain (k + 1) (2 * j + 1) =
          (0, π / 2 - (angles k).getD j 0 / 2) :: liftChain (chain k (j + 1)) := by
        rw [chain]; simp [h1, h2, h3]
      obtain ⟨hA, hB, hC⟩ := ih (j + 1) (by omega)
      have hψ := getD_mem_angles hj
      rw [hc]
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · show 0 < π / 2 - (angles k).getD j 0 / 2 ∧ π / 2 - (angles k).getD j 0 / 2 < π / 2
          constructor <;> linarith [hψ.1, hψ.2]
        · obtain ⟨q, hq, rfl⟩ := mem_liftChain hp
          exact hA q hq
      · rw [List.isChain_cons]
        refine ⟨?_, chain'_liftChain hB⟩
        intro y hy
        rcases hck : chain k (j + 1) with _ | ⟨⟨h', β'⟩, rest'⟩
        · rw [hck] at hy; simp [liftChain] at hy
        · rw [hck] at hy
          simp only [liftChain, List.map_cons, List.head?_cons, Option.mem_def,
            Option.some.injEq] at hy
          subst hy
          have hβ := hC (by omega) h' β' rest' hck
          simp only [Nat.add_sub_cancel] at hβ
          refine ⟨by simp, ?_⟩
          simp only [Nat.sub_zero]
          rw [hβ, pow_succ]
          field_simp
          ring
      · intro _ h β rest hcons
        simp only [List.cons.injEq, Prod.mk.injEq] at hcons
        obtain ⟨⟨rfl, rfl⟩, -⟩ := hcons
        rw [Nat.add_sub_cancel, angles, getD_flatMap_even _ (by rw [hlen]; exact hj)]
        ring

lemma bad_le_two_div {τ β : ℝ} (hτ : 1 < τ) : bad τ β ≤ 2 / (τ - 1) := by
  unfold bad
  have hc := Real.cos_le_one β
  have hc' := Real.neg_one_le_cos β
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem chainBound_collapse {X : ℝ} (hX : 1 < X) : ∀ (n : ℕ) (c : List (ℕ × ℝ)),
    c.length = n → List.IsChain chainRel c → (∀ p ∈ c, 0 < p.2 ∧ p.2 < π / 2) →
      chainBound X c ≤ max 1 (2 / (X - 1)) := by
  intro n
  induction n with
  | zero =>
    intro c hc _ _
    rw [List.length_eq_zero_iff.mp hc, chainBound_nil]; exact le_max_left _ _
  | succ n ih =>
    intro c hc hR hA
    rcases c with _ | ⟨p, _ | ⟨q, rest⟩⟩
    · simp at hc
    · rw [chainBound_cons, chainBound_nil, mul_one]
      have hτ : X ≤ dbl^[p.1] X := le_dbl_iterate hX.le _
      apply max_le_max le_rfl
      calc bad (dbl^[p.1] X) p.2 ≤ 2 / (dbl^[p.1] X - 1) := bad_le_two_div (by linarith)
        _ ≤ 2 / (X - 1) := div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    · rw [isChain_cons_cons] at hR
      obtain ⟨⟨hlt, hβ⟩, hR'⟩ := hR
      obtain ⟨Δ, hΔ⟩ : ∃ Δ, q.1 = p.1 + (Δ + 1) := ⟨q.1 - p.1 - 1, by omega⟩
      have hsub : q.1 - p.1 = Δ + 1 := by omega
      set n' : ℝ := 2 ^ (Δ + 1) with hn'
      have hn2 : 2 ≤ n' := by
        rw [hn']; calc (2:ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (Δ + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hqA := hA q (by simp)
      set τ1 := dbl^[p.1] X with hτ1
      have hτ1X : X ≤ τ1 := le_dbl_iterate hX.le _
      have hτ2 : dbl^[q.1] X = dbl^[Δ + 1] τ1 := by
        rw [hΔ, add_comm, Function.iterate_add_apply]
      have hY : 1 + n' ^ 2 * (τ1 - 1) ≤ dbl^[q.1] X := by
        rw [hτ2]
        have := dbl_iterate_ge (by linarith : (1:ℝ) ≤ τ1) (Δ + 1)
        have e : n' ^ 2 = 4 ^ (Δ + 1) := by rw [hn', ← pow_mul, mul_comm, pow_mul]; norm_num
        rw [e]; exact this
      have hex := exchange_max hqA.1 hqA.2 hn2 (by linarith) hY
      rw [hsub] at hβ
      rw [← hβ] at hex
      set c' := (p.1, q.2 / n') :: rest with hc'
      have hlen' : c'.length = n := by simp [hc'] at hc ⊢; omega
      have hpos : 0 < n' := by linarith
      have hA' : ∀ r ∈ c', 0 < r.2 ∧ r.2 < π / 2 := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · refine ⟨div_pos hqA.1 hpos, ?_⟩
          rw [div_lt_iff₀ hpos]; nlinarith [hqA.2]
        · exact hA r (by simp [hr])
      have hR'' : List.IsChain chainRel c' := by
        rw [hc']
        rcases rest with _ | ⟨r, rest'⟩
        · simp
        · rw [isChain_cons_cons] at hR' ⊢
          obtain ⟨⟨hlt2, hβ2⟩, hR3⟩ := hR'
          refine ⟨⟨by simp; omega, ?_⟩, hR3⟩
          simp only
          rw [hβ2, hn', div_div, ← pow_add]
          congr 2; omega
      have hIH := ih c' hlen' hR'' hA'
      rw [chainBound_cons, chainBound_cons]
      rw [hc', chainBound_cons] at hIH
      have hrest := one_le_chainBound X rest
      calc max 1 (bad (dbl^[p.1] X) p.2) * (max 1 (bad (dbl^[q.1] X) q.2) * chainBound X rest)
          = (max 1 (bad τ1 p.2) * max 1 (bad (dbl^[q.1] X) q.2)) * chainBound X rest := by
            rw [hτ1]; ring
        _ ≤ max 1 (bad τ1 (q.2 / n')) * chainBound X rest :=
            mul_le_mul_of_nonneg_right hex (by linarith)
        _ ≤ max 1 (2 / (X - 1)) := hIH

theorem window_le_kappa (k s m : ℕ) {x x0 : ℝ} (hs : s ≤ 2 ^ k) (hx0 : 1 < x0)
    (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |prodF x x0 (((angles k).drop s).take m)| ≤ max 1 (2 / (x0 - 1)) := by
  obtain ⟨hA, hB, -⟩ := chain_props k s hs
  exact (window_le_chain k s m hx0 hx1 hx2).trans
    (chainBound_collapse hx0 _ _ rfl hB hA)

end OracleTemplate.FractalChebyshev

import LongTails.Proofs.FractalChebyshevCollapse

namespace OracleTemplate.FractalChebyshev

open Real

def liftChain (c : List (ℕ × ℝ)) : List (ℕ × ℝ) := c.map fun p => (p.1 + 1, p.2)

noncomputable def chain : ℕ → ℕ → List (ℕ × ℝ)
  | 0, _ => []
  | k + 1, s =>
      (if s % 2 = 1 then [(0, π / 2 - (angles k).getD (s / 2) 0 / 2)] else []) ++
        liftChain (chain k ((s + 1) / 2))

noncomputable def chainBound (X : ℝ) (c : List (ℕ × ℝ)) : ℝ :=
  (c.map fun p => max 1 (bad (dbl^[p.1] X) p.2)).prod

lemma chainBound_nil (X : ℝ) : chainBound X [] = 1 := by simp [chainBound]

lemma chainBound_cons (X : ℝ) (p : ℕ × ℝ) (c : List (ℕ × ℝ)) :
    chainBound X (p :: c) = max 1 (bad (dbl^[p.1] X) p.2) * chainBound X c := by
  simp [chainBound]

lemma chainBound_append (X : ℝ) (c c' : List (ℕ × ℝ)) :
    chainBound X (c ++ c') = chainBound X c * chainBound X c' := by
  simp [chainBound, List.map_append, List.prod_append]

lemma chainBound_lift (X : ℝ) (c : List (ℕ × ℝ)) :
    chainBound X (liftChain c) = chainBound (dbl X) c := by
  induction c with
  | nil => simp [chainBound, liftChain]
  | cons p c ih =>
    have : liftChain (p :: c) = (p.1 + 1, p.2) :: liftChain c := by simp [liftChain]
    rw [this, chainBound_cons, chainBound_cons, ih, Function.iterate_succ_apply]

lemma one_le_chainBound (X : ℝ) (c : List (ℕ × ℝ)) : 1 ≤ chainBound X c := by
  induction c with
  | nil => simp [chainBound]
  | cons p c ih =>
    rw [chainBound_cons]
    have := le_max_left 1 (bad (dbl^[p.1] X) p.2)
    nlinarith

lemma drop_flatMap_even (l : List ℝ) (j : ℕ) :
    (l.flatMap split).drop (2 * j) = (l.drop j).flatMap split := by
  induction l generalizing j with
  | nil => simp
  | cons ψ l ih =>
    rcases j with _ | j
    · simp
    · rw [List.flatMap_cons, show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
      simp [split, ih j]

lemma drop_flatMap_odd (l : List ℝ) (j : ℕ) :
    (l.flatMap split).drop (2 * j + 1) =
      ((l.drop j).take 1).map (fun ψ => π / 2 + ψ / 2) ++ (l.drop (j + 1)).flatMap split := by
  induction l generalizing j with
  | nil => simp
  | cons ψ l ih =>
    rcases j with _ | j
    · simp [split]
    · rw [List.flatMap_cons, show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring]
      simp [split, ih j]

lemma abs_fac_second_le {x x0 ψ : ℝ} (hx0 : 1 < x0) (hx : -1 ≤ x ∧ x ≤ 1)
    (hψ : 0 < ψ ∧ ψ < π) :
    |fac x x0 (π / 2 + ψ / 2)| ≤ bad x0 (π / 2 - ψ / 2) := by
  unfold fac bad
  rw [cos_second, cos_first]
  have hs : 0 ≤ sin (ψ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs1 : sin (ψ / 2) ≤ 1 := Real.sin_le_one _
  have hpos : 0 < x0 - sin (ψ / 2) := by linarith
  rw [show x0 + -sin (ψ / 2) = x0 - sin (ψ / 2) by ring, abs_div, abs_of_pos hpos]
  apply div_le_div_of_nonneg_right _ hpos.le
  rw [abs_le]; constructor <;> linarith

lemma abs_dbl_le {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) : -1 ≤ dbl x ∧ dbl x ≤ 1 := by
  unfold dbl; constructor <;> nlinarith

theorem window_le_chain (k : ℕ) : ∀ (s m : ℕ) {x x0 : ℝ}, 1 < x0 → -1 ≤ x → x ≤ 1 →
    |prodF x x0 (((angles k).drop s).take m)| ≤ chainBound x0 (chain k s) := by
  induction k with
  | zero =>
    intro s m x x0 hx0 hx1 hx2
    rw [chain, chainBound_nil]
    rcases s with _ | s
    · rcases m with _ | m
      · simp [prodF]
      · simp only [angles, List.drop_zero, List.take_succ_cons, List.take_nil, prodF,
          List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, fac,
          Real.cos_pi_div_two, add_zero]
        have hx0' : (0:ℝ) < x0 := by linarith
        rw [abs_div, abs_of_pos hx0', div_le_one hx0', abs_le]
        constructor <;> linarith
    · simp [angles, prodF]
  | succ k ih =>
    intro s m x x0 hx0 hx1 hx2
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' s
    ·
      have hc : chain (k + 1) (2 * j) = liftChain (chain k j) := by
        rw [chain]
        have h1 : (2 * j) % 2 = 0 := by omega
        have h2 : (2 * j + 1) / 2 = j := by omega
        simp [h1, h2]
      rw [hc, chainBound_lift, angles, drop_flatMap_even]
      obtain ⟨m', -, e, he, he'⟩ := take_flatMap_split ((angles k).drop j) m
      rw [he, prodF_append, prodF_flatMap x x0 hx0, abs_mul]
      have hd := abs_dbl_le ⟨hx1, hx2⟩
      have h1 := ih j m' (one_lt_dbl hx0) hd.1 hd.2
      have h2 : |prodF x x0 e| ≤ 1 := by
        rcases he' with rfl | ⟨ψ, hψ, rfl⟩
        · simp [prodF]
        · simp only [prodF, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          exact abs_fac_first_le hx0 ⟨hx1, by linarith⟩
            (angles_mem (List.mem_of_mem_drop hψ))
      calc _ ≤ chainBound (dbl x0) (chain k j) * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by linarith [one_le_chainBound (dbl x0) (chain k j)])
        _ = _ := mul_one _
    ·
      have h1 : (2 * j + 1) % 2 = 1 := by omega
      have h2 : (2 * j + 1) / 2 = j := by omega
      have h3 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
      have hc : chain (k + 1) (2 * j + 1) =
          [(0, π / 2 - (angles k).getD j 0 / 2)] ++ liftChain (chain k (j + 1)) := by
        rw [chain]; simp [h1, h2, h3]
      rw [hc, chainBound_append, chainBound_lift, angles, drop_flatMap_odd]
      rcases hl : (angles k).drop j with _ | ⟨ψ, l'⟩
      · have : (angles k).drop (j + 1) = [] := by
          rw [← List.drop_drop, hl]; simp
        rw [this]
        simp only [List.take_nil, List.map_nil, List.flatMap_nil, List.append_nil, prodF_nil,
          abs_one]
        have := one_le_chainBound x0 [(0, π / 2 - (angles k).getD j 0 / 2)]
        have := one_le_chainBound (dbl x0) (chain k (j + 1))
        nlinarith
      · have hl' : (angles k).drop (j + 1) = l' := by
          rw [← List.drop_drop, hl]; simp
        have hψmem : ψ ∈ angles k := List.mem_of_mem_drop (by rw [hl]; simp)
        have hgetD : (angles k).getD j 0 = ψ := by
          rw [List.getD_eq_getElem?_getD, ← List.head?_drop, hl]; simp
        rw [hl', hgetD]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.singleton_append]
        rcases m with _ | m
        · simp only [List.take_zero, prodF_nil, abs_one]
          have := one_le_chainBound x0 [(0, π / 2 - ψ / 2)]
          have := one_le_chainBound (dbl x0) (chain k (j + 1))
          nlinarith
        · rw [List.take_succ_cons, prodF_cons, abs_mul]
          obtain ⟨m', -, e, he, he'⟩ := take_flatMap_split l' m
          rw [he, prodF_append, prodF_flatMap x x0 hx0, abs_mul]
          have hd := abs_dbl_le ⟨hx1, hx2⟩
          have hIH := ih (j + 1) m' (one_lt_dbl hx0) hd.1 hd.2
          rw [hl'] at hIH
          have he2 : |prodF x x0 e| ≤ 1 := by
            rcases he' with rfl | ⟨φ, hφ, rfl⟩
            · simp [prodF]
            · simp only [prodF, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
                mul_one]
              have : φ ∈ angles k := by
                rw [← hl'] at hφ; exact List.mem_of_mem_drop hφ
              exact abs_fac_first_le hx0 ⟨hx1, by linarith⟩ (angles_mem this)
          have hfirst : |fac x x0 (π / 2 + ψ / 2)| ≤
              chainBound x0 [(0, π / 2 - ψ / 2)] := by
            rw [chainBound_cons, chainBound_nil, mul_one, Function.iterate_zero, id]
            exact (abs_fac_second_le hx0 ⟨hx1, hx2⟩ (angles_mem hψmem)).trans
              (le_max_right _ _)
          have hB := one_le_chainBound (dbl x0) (chain k (j + 1))
          calc |fac x x0 (π / 2 + ψ / 2)| *
                (|prodF (dbl x) (dbl x0) (l'.take m')| * |prodF x x0 e|)
              ≤ chainBound x0 [(0, π / 2 - ψ / 2)] *
                (chainBound (dbl x0) (chain k (j + 1)) * 1) := by
                apply mul_le_mul hfirst _ (by positivity)
                  (by linarith [one_le_chainBound x0 [(0, π / 2 - ψ / 2)]])
                exact mul_le_mul hIH he2 (abs_nonneg _) (by linarith)
            _ = _ := by ring

end OracleTemplate.FractalChebyshev

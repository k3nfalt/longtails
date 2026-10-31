import LongTails.Proofs.CoarseGeneralizedTrajectory
import LongTails.Proofs.CoarseGeneralizedExecution

open scoped RealInnerProductSpace

namespace OracleTemplate.CoarseGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure IterateValid (t : Tuning) (f : E → ℝ) (u : E) (R : ℝ) (s : Iterate E) : Prop where
  trace : Nonempty (AcceptedTrace t f u R s)
  radius : ‖s.x - u‖ ≤ R

def AnalyticValid (t : Tuning) (f : E → ℝ) (g : E → E) (u : E) (R : ℝ) : Search E → Prop
  | .done x => ‖x - u‖ ≤ R ∧ f x - f u ≤ 4097 * R * t.L / t.L1
  | .left s => IterateValid t f u R s
  | .right s => IterateValid t f u R s ∧ ⟪g s.v, s.x - s.v⟫ ≤ 0
  | .bracket s lo hi upper remaining =>
      IterateValid t f u R s ∧ 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1 ∧ 0 < remaining ∧
      hi - lo ≤ (2 : ℝ) ^ remaining / (2 : ℝ) ^ t.depth ∧
      ⟪g (s.v + lo • (s.x - s.v)), s.x - s.v⟫ ≤ 0 ∧
      0 ≤ ⟪g (s.v + hi • (s.x - s.v)), s.x - s.v⟫ ∧
      ‖upper - g (s.v + hi • (s.x - s.v))‖ ≤ t.ζ ∧
      4096 * t.L / t.L1 < ‖upper‖

lemma exhausted_gap_le_low_gap (t : Tuning) {R : ℝ}
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hR : 1 ≤ t.L1 * R) :
    t.L / t.L1 ^ 2 ≤ 4097 * R * t.L / t.L1 := by
  apply (div_le_div_iff₀ (sq_pos_of_pos hL1) hL1).mpr
  have hh := mul_le_mul_of_nonneg_right hR (mul_nonneg hL.le hL1.le)
  nlinarith only [hh, mul_pos hL hL1]

lemma resume_analytic (t : Tuning) {f : E → ℝ} {g : E → E} {u : E} {R : ℝ}
    {s : Iterate E} (hv : IterateValid t f u R s)
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hR : 1 ≤ t.L1 * R)
    (hmin : ∀ x, f u ≤ f x) (hrounds : 2050 * (t.L1 * R) < t.rounds) :
    AnalyticValid t f g u R (resume t s) := by
  unfold resume
  split_ifs with hh
  · change ‖s.x - u‖ ≤ R ∧ f s.x - f u ≤ 4097 * R * t.L / t.L1
    rcases hv.trace with ⟨tr⟩
    refine ⟨hv.radius, ?_⟩
    have hindex : 2050 * (t.L1 * R) < s.index :=
      hrounds.trans_le (by exact_mod_cast hh)
    exact (trace_gap t tr hL hL1 hR hmin hindex).trans
      (exhausted_gap_le_low_gap t hL hL1 hR)
  · exact hv

lemma initial_analytic (t : Tuning) {f : E → ℝ} {g : E → E} {u x0 : E} {R : ℝ}
    (hdist : ‖x0 - u‖ ≤ R) (hL : 0 < t.L) (hL1 : 0 < t.L1)
    (hR : 1 ≤ t.L1 * R) (hmin : ∀ x, f u ≤ f x)
    (hrounds : 2050 * (t.L1 * R) < t.rounds) :
    AnalyticValid t f g u R (resume t ⟨x0, x0, 0, 0⟩) := by
  apply resume_analytic t ⟨initial_trace t f u x0 hdist, hdist⟩ hL hL1 hR hmin hrounds

lemma analytic_query_radius (t : Tuning) {f : E → ℝ} {g : E → E} {u : E} {R : ℝ}
    {q : Search E} (hq : AnalyticValid t f g u R q)
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hR : 0 ≤ R) (hmin : ∀ x, f u ≤ f x) :
    ‖searchPoint q - u‖ ≤ R := by
  cases q with
  | done x => exact hq.1
  | left s =>
      rcases hq.trace with ⟨tr⟩
      exact trace_radius t tr hL hL1 hR hmin
  | right s => exact hq.1.radius
  | bracket s lo hi upper remaining =>
      rcases hq.1.trace with ⟨tr⟩
      apply segment_radius (by linarith [hq.2.1, hq.2.2.1])
        (by linarith [hq.2.2.1, hq.2.2.2.1]) hq.1.radius
      exact trace_radius t tr hL hL1 hR hmin

lemma finish_analytic [CompleteSpace E] (t : Tuning) {f : E → ℝ} {g : E → E}
    {u y h : E} {R : ℝ} {s : Iterate E} (hv : IterateValid t f u R s)
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hζ : 0 ≤ t.ζ)
    (hR : 1 ≤ t.L1 * R) (hinflate : t.L1 ^ 2 * R * t.ζ ≤ t.L)
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : Differentiable ℝ g) (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ t.L + t.L1 * ‖g x‖)
    (hu : g u = 0) (hmin : ∀ x, f u ≤ f x)
    (hrounds : 2050 * (t.L1 * R) < t.rounds)
    (hy : ‖y - u‖ ≤ R) (he : ‖h - g y‖ ≤ t.ζ)
    (hlarge : 4096 * t.L / t.L1 < ‖h‖)
    (hsearch : f y ≤ f s.x + decrement t h / 256)
    (halign : ⟪h, y - s.v⟫ ≤ decrement t h / 256) :
    AnalyticValid t f g u R (finish t s y h) := by
  rcases hv.trace with ⟨tr⟩
  have hs : 0 < ‖h‖ := (div_pos (by positivity) hL1).trans hlarge
  have hhigh := (div_lt_iff₀ hL1).mp hlarge
  have hP := surplus_dominates_decrement t h hL hL1 (by nlinarith)
  have hD : 0 ≤ decrement t h := by unfold decrement; positivity
  have hsupport := high_reply_support t hL hL1 hζ hR hinflate hc hf hg hH hu hy he hlarge
  have hnoise := (high_reply_noise t h hL hL1 hζ hR hinflate hlarge).1
  have henergy := advance_energy t s hL hL1.le hf hg hH hs (trace_weight_nonneg t tr hL hL1)
    (by linarith) he hnoise hsearch halign hsupport
  have htrace := extend_trace t tr y h hlarge (by
    unfold iterateEnergy
    nlinarith only [henergy])
  apply resume_analytic t ⟨htrace, ?_⟩ hL hL1 hR hmin hrounds
  exact high_advance_radius t s hL hL1 hζ hR hinflate hc hf hg hH hu hmin hy he hlarge

lemma bisection_width {lo hi : ℝ} {r depth : ℕ} (hr : 0 < r)
    (hw : hi - lo ≤ (2 : ℝ) ^ r / (2 : ℝ) ^ depth) :
    hi - (lo + hi) / 2 ≤ (2 : ℝ) ^ (r - 1) / (2 : ℝ) ^ depth ∧
      (lo + hi) / 2 - lo ≤ (2 : ℝ) ^ (r - 1) / (2 : ℝ) ^ depth := by
  have he : (2 : ℝ) ^ r = 2 * (2 : ℝ) ^ (r - 1) := by
    calc
      (2 : ℝ) ^ r = 2 ^ ((r - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (r - 1) := by rw [pow_succ]; ring
  rw [he, mul_div_assoc] at hw
  constructor <;> linarith

lemma terminal_bisection_width {lo hi : ℝ} {r depth : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hw : hi - lo ≤ (2 : ℝ) ^ r / (2 : ℝ) ^ depth) :
    hi - (lo + hi) / 2 ≤ 1 / (2 : ℝ) ^ depth ∧
      (lo + hi) / 2 - lo ≤ 1 / (2 : ℝ) ^ depth := by
  have hh := bisection_width hr hw
  have he : r - 1 = 0 := by omega
  simpa only [he, pow_zero] using hh

lemma assess_analytic_cases (t : Tuning) {f : E → ℝ} {g : E → E} {u : E} {R : ℝ}
    {s : Iterate E} {y h : E} {next : Search E}
    (hsmall : ‖h‖ ≤ 4096 * t.L / t.L1 → AnalyticValid t f g u R (.done y))
    (huncertain : 4096 * t.L / t.L1 < ‖h‖ →
      |⟪h, s.x - s.v⟫| ≤ t.ζ * ‖s.x - s.v‖ → AnalyticValid t f g u R (finish t s y h))
    (hnext : 4096 * t.L / t.L1 < ‖h‖ →
      t.ζ * ‖s.x - s.v‖ < |⟪h, s.x - s.v⟫| → AnalyticValid t f g u R next) :
    AnalyticValid t f g u R (assess t s y h next) := by
  unfold assess
  split_ifs with hs hu
  · exact hsmall hs
  · exact huncertain (lt_of_not_ge hs) hu
  · exact hnext (lt_of_not_ge hs) (lt_of_not_ge hu)

lemma search_update_analytic [CompleteSpace E] (t : Tuning) {f : E → ℝ} {g : E → E}
    {u : E} {R : ℝ} {q : Search E} (hq : AnalyticValid t f g u R q) (h : E)
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hζ : 0 ≤ t.ζ)
    (hR : 1 ≤ t.L1 * R) (hinflate : t.L1 ^ 2 * R * t.ζ ≤ t.L)
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : Differentiable ℝ g) (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ t.L + t.L1 * ‖g x‖)
    (hu : g u = 0) (hmin : ∀ x, f u ≤ f x)
    (hrounds : 2050 * (t.L1 * R) < t.rounds) (hdepth : 0 < t.depth)
    (hshort : 8 * (t.L1 * R) * (1 / (2 : ℝ) ^ t.depth) ≤ 1)
    (hwidth : 65536 * (t.L1 * R) ^ 2 * (1 / (2 : ℝ) ^ t.depth) ≤ 1)
    (he : ‖h - g (searchPoint q)‖ ≤ t.ζ) :
    AnalyticValid t f g u R (searchUpdate t q h) := by
  have hRp : 0 ≤ R := by nlinarith
  have hqr := analytic_query_radius t hq hL hL1 hRp hmin
  have hfin : ∀ (s : Iterate E) (y b : E), IterateValid t f u R s → ‖y - u‖ ≤ R →
      ‖b - g y‖ ≤ t.ζ → 4096 * t.L / t.L1 < ‖b‖ →
      f y ≤ f s.x + decrement t b / 256 → ⟪b, y - s.v⟫ ≤ decrement t b / 256 →
      AnalyticValid t f g u R (finish t s y b) := by
    intro s y b hs hyr hbe hbl hfs hal
    exact finish_analytic t hs hL hL1 hζ hR hinflate hc hf hg hH hu hmin hrounds
      hyr hbe hbl hfs hal
  have hunc : ∀ (s : Iterate E) (y b : E) (θ : ℝ), IterateValid t f u R s →
      0 ≤ θ → θ ≤ 1 → y = s.v + θ • (s.x - s.v) → ‖b - g y‖ ≤ t.ζ →
      4096 * t.L / t.L1 < ‖b‖ → |⟪b, s.x - s.v⟫| ≤ t.ζ * ‖s.x - s.v‖ →
      AnalyticValid t f g u R (finish t s y b) := by
    intro s y b θ hs hθ hθ1 hy hbe hbl hdir
    rcases hs.trace with ⟨tr⟩
    have hvr := trace_radius t tr hL hL1 hRp hmin
    have hh := uncertain_search_slack t hL hL1 hζ hR hinflate hc hf hs.radius hvr
      hθ hθ1 hy hbe hdir hbl
    apply hfin s y b hs _ hbe hbl hh.1 hh.2
    rw [hy]
    exact segment_radius hθ hθ1 hs.radius hvr
  cases q with
  | done x => exact hq
  | left s =>
      change AnalyticValid t f g u R (assess t s s.v h _)
      apply assess_analytic_cases t
      · intro hs
        exact ⟨hqr, low_reply_gap t hc hf hL1 hζ hR hinflate hqr he hs⟩
      · intro hl hd
        exact hunc s s.v h 0 hq le_rfl (by norm_num) (by simp) he hl hd
      · intro hl hd
        split_ifs with hdir
        · have htrue := (reliable_direction he hd).1 hdir
          have hb := (endpoint_search_slack t (h := h) hL hL1.le hc hf).1 htrue
          exact hfin s s.v h hq hqr he hl hb.1 hb.2
        · exact ⟨hq, (reliable_direction he hd).2 (le_of_not_ge hdir)⟩
  | right s =>
      change AnalyticValid t f g u R (assess t s s.x h _)
      apply assess_analytic_cases t
      · intro hs
        exact ⟨hqr, low_reply_gap t hc hf hL1 hζ hR hinflate hqr he hs⟩
      · intro hl hd
        exact hunc s s.x h 1 hq.1 (by norm_num) le_rfl (by simp) he hl hd
      · intro hl hd
        split_ifs with hdir hz
        · have hb := (endpoint_search_slack t (h := h) hL hL1.le hc hf).2 hdir
          exact hfin s s.x h hq.1 hqr he hl hb.1 hb.2
        · omega
        · change IterateValid t f u R s ∧ _
          refine ⟨hq.1, le_rfl, zero_le_one, le_rfl, hdepth, ?_, ?_, ?_, ?_, hl⟩
          · simp
          · simpa using hq.2
          · simpa [searchPoint] using (reliable_direction he hd).1 (le_of_not_ge hdir)
          · simpa [searchPoint] using he
  | bracket s lo hi upper r =>
      change AnalyticValid t f g u R (assess t s (s.v + ((lo + hi) / 2) • (s.x - s.v)) h _)
      apply assess_analytic_cases t
      · intro hs
        exact ⟨hqr, low_reply_gap t hc hf hL1 hζ hR hinflate hqr he hs⟩
      · intro hl hd
        exact hunc s _ h _ hq.1 (by linarith [hq.2.1, hq.2.2.1])
          (by linarith [hq.2.2.1, hq.2.2.2.1]) rfl he hl hd
      · intro hl hd
        rcases hq with ⟨hs, hlo, hle, hhi, hr, hw, hleft, hright, hupper, hupl⟩
        rcases hs.trace with ⟨tr⟩
        have hvr := trace_radius t tr hL hL1 hRp hmin
        have hmid0 : 0 ≤ (lo + hi) / 2 := by linarith
        have hmid1 : (lo + hi) / 2 ≤ 1 := by linarith
        have hmidlo : lo ≤ (lo + hi) / 2 := by linarith
        have hmidhi : (lo + hi) / 2 ≤ hi := by linarith
        have hhalf := bisection_width hr hw
        split_ifs with hdir hr1 hr1
        · have hn := (reliable_direction he hd).2 hdir.le
          have ht := (terminal_bisection_width hr hr1 hw).1
          have hdist := interval_segment_distance hs.radius hvr hmidhi ht
          rw [norm_sub_rev] at hdist
          have hb := bracket_search_slack t hL hL1 hζ hR hinflate hc hf hg hH
            hs.radius hvr (hlo.trans hle) hhi rfl hupper hn hright hupl
            (by positivity) hdist hshort hwidth
          exact hfin s _ upper hs (segment_radius (hlo.trans hle) hhi hs.radius hvr)
            hupper hupl hb.1 hb.2
        · change IterateValid t f u R s ∧ _
          exact ⟨hs, hmid0, hmidhi, hhi, by omega, hhalf.1,
            (reliable_direction he hd).2 hdir.le, hright, hupper, hupl⟩
        · have hn := (reliable_direction he hd).1 (le_of_not_gt hdir)
          have ht := (terminal_bisection_width hr hr1 hw).2
          have hdist := interval_segment_distance hs.radius hvr hmidlo ht
          rw [norm_sub_rev] at hdist
          have hb := bracket_search_slack t hL hL1 hζ hR hinflate hc hf hg hH
            hs.radius hvr hmid0 hmid1 rfl he hleft hn hl
            (by positivity) hdist hshort hwidth
          exact hfin s _ h hs hqr he hl hb.1 hb.2
        · change IterateValid t f u R s ∧ _
          exact ⟨hs, hlo, hmidlo, hmid1, by omega, hhalf.2, hleft,
            (reliable_direction he hd).1 (le_of_not_gt hdir), he, hl⟩

lemma warm_pathwise [CompleteSpace E] (t : Tuning) {f : E → ℝ} {g : E → E}
    {u x0 : E} {R : ℝ} (reply : ℕ → E → E)
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hζ : 0 ≤ t.ζ)
    (hR : 1 ≤ t.L1 * R) (hinflate : t.L1 ^ 2 * R * t.ζ ≤ t.L)
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : Differentiable ℝ g) (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ t.L + t.L1 * ‖g x‖)
    (hu : g u = 0) (hmin : ∀ x, f u ≤ f x) (hdist : ‖x0 - u‖ ≤ R)
    (hrounds : 2050 * (t.L1 * R) < t.rounds) (hdepth : 0 < t.depth)
    (hshort : 8 * (t.L1 * R) * (1 / (2 : ℝ) ^ t.depth) ≤ 1)
    (hwidth : 65536 * (t.L1 * R) ^ 2 * (1 / (2 : ℝ) ^ t.depth) ≤ 1)
    (he : ∀ k < t.rounds * (t.depth + 2),
      let q := StochasticGradient.advance (fun i s => searchUpdate t s (reply i (searchPoint s)))
        k 0 ((warmAlgorithm t x0).initial ())
      ‖reply k (searchPoint q) - g (searchPoint q)‖ ≤ t.ζ) :
    let q := StochasticGradient.advance (fun i s => searchUpdate t s (reply i (searchPoint s)))
      (t.rounds * (t.depth + 2)) 0 ((warmAlgorithm t x0).initial ())
    ‖warmOutput q - u‖ ≤ R ∧ f (warmOutput q) - f u ≤ 4097 * R * t.L / t.L1 := by
  let state := fun k => StochasticGradient.advance
    (fun i s => searchUpdate t s (reply i (searchPoint s))) k 0 (resume t ⟨x0, x0, 0, 0⟩)
  have hv : ∀ k ≤ t.rounds * (t.depth + 2), AnalyticValid t f g u R (state k) := by
    intro k
    induction k with
    | zero =>
        intro _
        exact initial_analytic t hdist hL hL1 hR hmin hrounds
    | succ k ih =>
        intro hk
        have hk' : k < t.rounds * (t.depth + 2) := by omega
        have hh := search_update_analytic t (ih (by omega)) (reply k (searchPoint (state k)))
          hL hL1 hζ hR hinflate hc hf hg hH hu hmin hrounds hdepth hshort hwidth (he k hk')
        change AnalyticValid t f g u R (StochasticGradient.advance _ (k + 1) 0
          (resume t ⟨x0, x0, 0, 0⟩))
        rw [advance_append_step]
        simpa only [zero_add] using hh
  obtain ⟨x, hx⟩ := warm_terminal t reply x0
  have hh := hv _ le_rfl
  dsimp [state] at hh
  change AnalyticValid t f g u R (StochasticGradient.advance _ _ _
    ((warmAlgorithm t x0).initial ())) at hh
  rw [hx] at hh ⊢
  exact hh

end OracleTemplate.CoarseGeneralized

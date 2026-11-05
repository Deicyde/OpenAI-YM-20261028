import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Highway
import YM.Planned.RECIPE_STARTUP_PORT.Horizon
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Raw
open Filter Function Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure Presented Oriented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side}

open PhysicalNext.Repeat.Height
-- EXTRA mark (arity-1 grading). Independent of Currency.
def extraA (c f : Side) : LogLetter c f → ℕ := Sum.elim (fun _=>1) (Sum.elim (fun _=>0) (Sum.elim (fun _=>1) (Sum.elim (fun _=>1) (Sum.elim (fun _=>2) fun _=>2))))
lemma boost_price {ι:Type*} {X:ι→Support c} {w:ι→ℝ} {e:ι→ℕ} {a b γ t : ℝ} {n:ℕ} (h : Sales n a b X w e γ) (hp:0≤t) : Sales n a b X (fun i=> t*w i) e (t*γ) := h.shift hp (fun _=>mul_nonneg hp (h.nonneg _)) (fun _=>le_rfl)
lemma store_price {ι:Type*} {X:ι→Support c} {w:ι→ℝ} {e:ι→ℕ} {a b γ t : ℝ} {n:ℕ} (k : ι→ℕ) (h : Sales n a b X (fun i=> t^k i*w i) e γ) (hp : 1≤t) : Sales n a b X w e γ := by
  have ht:0<t:=zero_lt_one.trans_le hp
  have he i:0≤w i:= nonneg_of_mul_nonneg_right (h.nonneg i) (pow_pos ht _)
  exact (one_mul γ) ▸ h.shift zero_le_one he (fun i=> by rw [one_mul]; exact le_mul_of_one_le_left (he i) (one_le_pow₀ hp))

/- Optional pre-census. Version of Raw.inherit_bills with grades. -/
theorem inherit_multi (G : Gauge) (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0<ε) (ha : 0≤a)
    (hx : 4*ε < P.top.supportExponent) (hy : 8*ε < P.top.width) (hz : 8*ε < P.below.width) :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ r : ℝ, -(1/2:ℝ) < r → ∀ r' : ℝ,
      ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f), S.patch.L=L →
      Intake P T x R →
      ∃ z : LogLetter c f → ℝ, (∀ U V i, |expo T x R U V i| ≤ z i) ∧
        Sales (radiusB x) a ε (space T l (radiusB x) R) (fun i=>grow G L x^extraA c f i*z i) (extra T R) (betaF G x L ^ r) ∧
      ∃ w : ℕ → ℝ, (∀ i U, |R.activities.K i U| ≤ w i) ∧
        Sales (radiusB x) a ε (forcedFoot S.ratio l (radiusB x) R) w (forcedExtra R) (betaF G x L ^ r') := by
  obtain ⟨n,hn⟩ := core_bills P l he ha hx
  refine ⟨n,fun L hL r hv r' => ?_⟩
  obtain ⟨s,hm,hs⟩ := exists_between hv
  have ht := (Rate.hat (L:=L) (G:=G)).mul_left 2
  have hr := Rate.const (G:=G) (L:=L) P.top.paths
  have hp : 4*ε < P.top.width := by linarith
  have H := Rate.const (G:=G) (L:=L) (1:ℝ)
  let f:= -(15/16:ℝ)
  have hx₁:= (Rate.power (G:=G) (L:=L) (a:=3/8)).mul (Rate.power (a:=f)) s (by unfold f; linarith only [hm])
  have hx₂:= ((Rate.power (G:=G) (L:=L) (a:=3/8)).pow 2).mul (Rate.power (a:=-2)) s (by push_cast; linarith only [hm])
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,hx₁,hx₂,hn L hL f r' (by dsimp [f]; linarith), atoms_meet G L 3 l he ha hp ht hr (r:=s) (by push_cast; linarith),
    atoms_meet G L 4 l he ha hp ht hr (r := f) (by unfold f; push_cast; linarith),
    atoms_meet G L 2 l he ha hp H (loopBill_rate G L) (r:=f) (by unfold f; push_cast; linarith),
    tails_meet G L L 1 l (s:=P.top.clip) (C:=P.top.paths) he (by decide) ha hy ht (-2),
    tails_meet G L scaleOne L.val l (s:=P.below.clip) (C:=P.below.paths) he L.property ha hz ht (-2),
    ((Rate.power (G:=G) (L:=L) (a:=s)).mul_left 6) r hs] with x hA hv hz hb hc hq hK hU hD h
  intro c f S T R hS hR
  let p := S.ratio
  have hl : p.count = L := hS
  obtain ⟨w,b,H1,H2,H3,H4⟩ := hb S T R hS hR
  let θ := -orientation*R.beta
  have ho : |-orientation|≤1 := by rw [abs_neg,abs_of_nonneg orientation_range.1.le]; exact orientation_range.2
  obtain ⟨hlh,hy'⟩ := hR.window
  have hθ : |θ| ≤ 2*betaF G x L := by
    rw [← hS]; unfold θ; rw [abs_mul, abs_of_nonneg hR.positive.le]
    exact le_trans (mul_le_of_le_one_left hR.positive.le ho) hy'
  have hpaths := hR.cap.paths
  have hF : R.p.threshold = fiery G x L := by rw [hR.received.temp,hS]
  obtain ⟨w₁,e₁,B₁⟩ := hc c f p hl R.path.cubic hpaths.three θ hθ R.p hF
  obtain ⟨w₂,e₂,B₂⟩ := hq c f p hl R.path.quartic hpaths.four θ hθ R.p hF
  rw [hS] at hpaths
  obtain ⟨w₀,e₀,B₀⟩ := hK c f p hl R.path.loop hpaths.two (-orientation) ho R.p hF
  have hu : R.clip = P.top.clip := hR.received.clip.trans hR.ready.high
  rw [hu] at hpaths
  obtain ⟨w₃,e₃,B₃⟩ := hU c f p hl R.path _ hpaths θ hθ
  obtain ⟨_,_,_,hk⟩ := hR.ready.feeds
  obtain ⟨w₄,e₄,B₄⟩ := hD c c (atOne _) rfl T.down _ hk (-θ) (by simpa only [abs_neg] using hθ)
  let z := Sum.elim w (Sum.elim w₁ (Sum.elim w₂ (Sum.elim w₀ (Sum.elim w₃ w₄))))
  let X:=grow G L x
  have hp:1≤ X:= Real.one_le_rpow hA (by norm_num); have hkX:=zero_le_one.trans hp
  have h1:X*betaF G x L ^ (-(15/16):ℝ) ≤ betaF G x L ^ s:= (le_abs_self _).trans hv
  have h2:X^2*betaF G x L ^ (-2:ℝ)≤betaF G x L ^ s:= (le_abs_self _).trans hz
  have hHg:= (Sales.together ((boost_price H2 hkX).raise h1) (B₁.together (((boost_price B₂ hkX).raise h1).together
    (((boost_price B₀ hkX).raise h1).together (((boost_price B₃ (pow_nonneg hkX 2)).raise h2).together ((boost_price B₄ (pow_nonneg hkX 2)).raise h2))))))
  refine ⟨z,?_,?_,b,H3,H4⟩
  · intro U V i
    rcases i with i| (i | (i | (i | (i | i))))
    · dsimp only [z,expo,Sum.elim]; rw [abs_neg]; exact H1 i U
    · exact e₁ ..
    · exact e₂ ..
    · exact e₀ ..
    · dsimp only [expo,z,Sum.elim]; rw [hu]; exact e₃ ..
    dsimp only [expo,z,Sum.elim]
    rw [hR.ready.low,hS]; exact e₄ ..
  convert hHg.raise (hg:=show _ ≤ betaF G x L^r from ?_) using 1
  · rfl
  · funext i; rcases i with i|i|i|i|i|i <;> simp [z,extraA,X]
  · rfl
  linarith only [h,le_abs_self (6*betaF G x L^s)]

end YM.ConnectedActivityE6.Raw

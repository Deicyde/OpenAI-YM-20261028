import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Paths
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Weights

/-!
# Real masked occurrence costs

PathPrices at inputs to RAdvances. Per-label exponent bills: no random
multipliers erased, path Taylor tests, stationary equality or coupling-reset
assumed. In a Mayer test also after further multiplication in the exponent by
any protective factors of magnitude ≤1, and on rotated orientations. These
are sup bounds (including measures on same sector stencils, not restricted to
average F) before occupancy choices, output-Hessian and contour comparisons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Raw
open Filter Lattice RG Pressure Pressure.Stores Wilson Finset MeasureTheory
open Push AbsoluteSums AbsoluteSums.Paths AbsoluteSums.Footprint
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side}

/-- MAY use a *different* spatial scale for projection of supports (e.g.
coarse identity scale for output-only tails). -/
def pathPay (L : Side) (r m l B : ℕ) (ε C γ a : ℝ) :=
  payment (L.val^4) (originFee l B) m ε C γ a
    (preCost l + 10*preCost l / L.val *(1+(r:ℝ)))

lemma pathPay_rate (L L' : Side) (l r m : ℕ) {a u v ε : ℝ} {C γ : ℝ → ℝ}
    (h : Rate G L u C) (k : Rate G L v γ) : Rate G L (u+v) (fun x => pathPay L' r m l (radiusB x) ε (C x) (γ x) a) :=
  h.payment k (Rate.transfers l 1) _ m ε a _

/-- `pairFoot` buys one same-level mask reach. Here allow l more halos in
output metric for decisions over the *entire* inherited footprint. -/
lemma price_foot (p : Ratio c f) (l : ℕ) (T : PathData G) (x : Cell f) (i : ℕ×ℕ) (B : ℕ) (he : 0 < B) :
    enlargement p l B (pairFoot B T x i) ⊆ enlargement p (l+2) B (bundle x.1 (duplex T x.2 i)) := by
  intro y hy
  obtain ⟨z,hz,hh⟩ := halo_spec.mp hy
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
  apply halo_spec.mpr
  rcases mem_union.mp hw with hm|hm
  · obtain ⟨x',hx',ht⟩ := halo_spec.mp hm
    rw [mem_singleton.mp hx'] at ht
    refine ⟨p.parent x.1,mem_image_of_mem _ (mem_insert_self ..), (separation_triangle _ (p.parent w) _).trans ?_⟩
    have h := Work.E04.parent_separation p x.1 w
    rw [Nat.add_mul]; omega
  exact ⟨p.parent w,mem_image_of_mem _ hm,hh.trans (Nat.mul_le_mul_right B (Nat.le_add_right l 2))⟩

/-- At the true `R = floor (B/100000)`, this is a negligible tail. -/
lemma tail_sale (p : Ratio c f) (l B d R k : ℕ) (T : PathData G) (s : Clip) (σ D Λ : ℝ) (r : PlaqAxes)
    (h : T.Bounds s σ D Λ) (hB : 0 < B) (hd : 0 < d)
    (C a ε : ℝ) (hC : 0 ≤ C) (he : 2*ε < σ/2)
    (hu : reserve (σ/2-2*ε) a (legFee p (l+2) B) ε) (z : Site f × (ℕ × ℕ) → ℝ) (hz : ∀ i : Site f × (ℕ × ℕ),
      0 ≤ z i ∧ z i ≤ C * pairPrice T R d r i.2*(1+(length (duplex T r i.2):ℝ))^k) :
    Sales B a ε (fun i => enlargement p l B (pairFoot B T (i.1,r) i.2)) z (fun i => length (duplex T r i.2))
      (pathPay p.count 2 k (l+2) B ε C (2*Real.exp (-(σ/(2*d))*R)*(D*D)) a) := by
  refine Sales.paths (l := l+2) p (duplex T r) (pairPrice_nonneg T R d r) ?_ _
    (fun i => price_foot p l T (i.1,r) i.2 B hB) (sub_pos.mpr he) hB hu k hC z hz
  have h1 : 0 ≤ 2*Real.exp (-(σ/(2*d))*R) := by positivity
  apply budget_mono (budget_scale h1 (budget_prod (h.rows r) (h.rows r)))
  · intro i; exact mul_nonneg (pairPrice_nonneg ..) (Real.exp_pos _).le
  intro i
  unfold pairPrice
  split
  next hg =>
    unfold long at hg
    let x := (T.row r i.1).2.length
    let y := (T.row r i.2).2.length
    have hx : (R:ℝ) ≤ ((x:ℝ)+(y:ℝ))*(d:ℝ) := by
      change ¬(x*d ≤ R ∧ y*d ≤ R) at hg
      have hy : R ≤ (x+y)*d := by rw [Nat.add_mul]; omega
      exact_mod_cast hy
    have hσ := h.width
    have hv : 0 < (d:ℝ) := by exact_mod_cast hd
    rw [duplex_price,Nat.cast_add]
    calc
      _ ≤ 2*mate T r i * Real.exp (-(σ/(2*d))*R+σ*x+σ*y) := by
        have he : R / (d:ℝ) ≤ (x:ℝ)+(y:ℝ) := (div_le_iff₀ hv).2 hx
        apply mul_le_mul_of_nonneg_left _ (by unfold mate; positivity)
        apply Real.exp_monotone; unfold x y at *
        field_simp; nlinarith
      _ = _ := by unfold x y mate; rw [Real.exp_add,Real.exp_add]; ring
  next hg =>
    rw [zero_mul]; exact (budget_scale h1 (budget_prod (h.rows r) (h.rows r))).1 _

lemma atom_sale {k : ℕ} (p : Ratio c f) (l B m : ℕ) (T : ℕ → Atom G k) (σ D : ℝ)
    (h : SumBudget (fun i => (T i).budget σ) D) (hB : 0 < B)
    (C a ε : ℝ) (hC : 0 ≤ C) (he : 2*ε < σ)
    (hu : reserve (σ-2*ε) a (legFee p (l+5) B) ε) (z : Site f × ℕ → ℝ)
    (hz : ∀ i : Site f × ℕ, 0 ≤ z i ∧ z i ≤ C*(T i.2).magnitude*(1+((T i.2).length:ℝ))^m) :
    Sales B a ε (fun i => enlargement p l B (inspected ((T i.2).footprint i.1))) z (fun i => (T i.2).length)
      (pathPay p.count k m (l+5) B ε C D a) := by
  refine Sales.paths (l := l+5) p (fun i => (T i).leg) (w:=fun i => (T i).magnitude)
    (fun i => by unfold Atom.magnitude; positivity) (δ:=σ) h _
    (fun i => ?_) (sub_pos.mpr he) hB hu m hC z hz
  rw [← atom_foot]; exact inspected_price p l B _ hB

/-! Keeping this flexible in k/angular order permits pricing the C-path
components of an integrated estimate, with additional marks: exact currencies.
Need put in numerical caps in this version (e.g.
`C = β*t^3`, `g i` the corresponding NO exponent-β-reset value at that
support). Test permits extra seed marks via Mixed; these output sales INCLUDE
a per-vertex degree/length charge. The support can be the FULL inspected one
*before* intersecting. Parameters θ, t, etc are not altered from readout.
-/
lemma atom_bills (G : Gauge) (L L' : Side) (k m l : ℕ) {σ a ε : ℝ} {u v : ℝ}
    (hε : 0 < ε) (hσ : 4*ε < σ) (ha : 0 ≤ a) {C γ : ℝ → ℝ}
    (hc : Rate G L u C) (hv : Rate G L v γ) {r : ℝ} (hr : u+v < r) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (p : Ratio c f), p.count=L' → ∀ T : ℕ → Atom G k,
      SumBudget (fun i => (T i).budget σ) (γ x) → ∀ z : Site f × ℕ → ℝ,
      0 ≤ C x →
      (∀ i, 0 ≤ z i ∧ z i ≤ C x * (T i.2).magnitude*(1+((T i.2).length:ℝ))^m) →
      let B := radiusB x
      Sales B a ε (fun i => enlargement p l B (inspected ((T i.2).footprint i.1))) z (fun i => (T i.2).length)
        (betaF G x L^r) := by
  filter_upwards [(pathPay_rate (a:=a) (ε:=ε) L L' (l+5) k m hc hv) r hr,
    Fees.horizons G L' (l+5) hε ha (show 2*ε < σ-2*ε by linarith)] with x hx hp
  intro c f p hP T h z hZ hg B
  have he := atom_sale p l B m T σ (γ x) h hp.1 _ a ε hZ (by linarith) (hp.2.2 _ _ _ hP) z hg
  apply he.raise
  rw [hP]; exact (le_abs_self _).trans hx

/-- Unlike unlabelled culling, no need a cutoff on paths visited by a
compulsory packet. The true length exponential (same-level) gives a
negligible hit at each output site even including the cover query halo.
L' projection parameter: fine inputs L, same-level identity for coarse
uses. r is any real loss, incl. arbitrary inverse powers. -/
lemma tail_bills (G : Gauge) (L L' : Side) (m l d : ℕ) {s : Clip} {σ C u a ε : ℝ} (hd : 0 < d)
    (hε : 0 < ε) (hσ : 8*ε < σ) (ha : 0 ≤ a) {D : ℝ → ℝ} (hg : Rate G L u D) (r : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (p : Ratio c f), p.count=L' → ∀ T : PathData G, ∀ Λ : ℝ,
      T.Bounds s σ C Λ → ∀ i : PlaqAxes, ∀ z : Site f × (ℕ×ℕ) → ℝ, 0 ≤ D x →
      (∀ j, 0 ≤ z j ∧ z j ≤ D x * pairPrice T (till x) d i j.2*(1+(length (duplex T i j.2):ℝ))^m) →
      let B := radiusB x
      Sales B a ε (fun j => enlargement p l B (pairFoot B T (j.1,i) j.2)) z (fun j => length (duplex T i j.2))
        (betaF G x L^r) := by
  have h0 : 0 < σ := by linarith
  let γ (x : ℝ) := 2*Real.exp (-(σ/(2*d))*till x) * (C*C)
  have hv : Rate G L (r-1-u) γ := ((Rate.cutoff (show 0 < σ/(2*d:ℝ) by positivity)).mul_left 2).mul_right _
  filter_upwards [(pathPay_rate (a := a) (ε := ε) L L' (l+2) 2 m hg hv) r (by linarith),
    Fees.horizons G L' (l+2) hε ha (show 2*ε<σ/2-2*ε by linarith)] with x hx hp
  intro c f p hP T Λ h i z hZ he B
  apply (tail_sale p _ _ d _ m T s σ C Λ i h hp.1 hd (D x) _ _ hZ (by linarith) (hp.2.2 c f p hP) z he).raise
  rw [hP]; exact (le_abs_self _).trans hx
end YM.ConnectedActivityE6.Raw

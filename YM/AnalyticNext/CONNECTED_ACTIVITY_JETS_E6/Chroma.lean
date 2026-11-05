import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Cryo
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pigmented
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Scroll
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tint

/-!
# Numeric zip/row envelope of PIGMENT buds

Bills not from unrelated stencils. Need some separately (guide). Use cuffs at
all γ extend. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows Mask Coat SliceRows.DataKernel Scroll Strokes
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
variable {s : ℝ} {P : Teller G} {L : Side} {o : Site c} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {k j : ℕ} {U : E→ Config G f} {V Q : E→ Config G c} {x : E} {v z a : ℝ}
open Brush

lemma screen (S : PathData G) {R : Clip} (d r : ℕ) {σ C Λ : ℝ} (h : S.Bounds R σ C Λ) (hd : 0<d)
    (u : Mode V x k v) (i : Twin c) : Brush k (Real.sqrt R.direct+C*royalty G^2) ((4+2*r)*(v*royalty G))
      (fun t=> plotted S R r d (V t) i) x := by
  unfold plotted; split_ifs; next hp => exact (shortened S _ _ _ hd h u.pos u.atLink).climb (le_add_of_nonneg_left <| Real.sqrt_nonneg _)
                                           (by have hx := u.pos; have hh : 0≤v*royalty G:=mul_nonneg hx (zero_le_one.trans <| royalty_ge _); rw [add_mul]; apply le_add_of_nonneg_left; positivity)
  next hp =>
    let W:=4*(v*royalty G); let e := i.1
    have he : Brush k 1 W (fun z=> G.curvature (faceValue (V z) e)) x := sculpt (g:=fun z=> faceValue (V z) e) (by
       convert! tour (o:=e.1) (square e.2.val.1 e.2.val.2) u.pos u.atLink using 1)
    refine (he.smul (Real.sqrt R.direct)).climb ?_ ?_
    · have hv := budget_nonneg (h.rows i.1.2); rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_one]; exact le_add_of_nonneg_right (by positivity)
    unfold W; rw [add_mul]; apply le_add_of_nonneg_right; have := royalty_ge G; have := u.pos; positivity

lemma Noise (S : StepData c f) (u : Mode V x k v) (h : Mode Q x k v) (i : Bond c) :
    Brush k (Real.sqrt S.kernel.penalty) (v*royalty G+v) (fun t=> Tube.Z S (Q t) (V t) i) x := by
  refine ((sculpt (g:=fun t=> V t i * (Q t i)⁻¹) (links (u.atLink i) (reverse (f:=fun t=>Q t i) (h.atLink i)) (royalty G) (max_le (royalty_ge G) le_rfl))).smul (Real.sqrt _)).climb ?_ le_rfl
  rw [mul_one,Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- Budget class for All sweeps in scroll. Quantitative avoids exponential
inflation from differentiating when using *kept* rows and lore. `primary`
purchases even ancestor raw data. -/
def shadowL (P : Teller G) := Real.sqrt P.below.clip.direct+P.below.paths*royalty G^2+
    (Real.sqrt P.top.clip.direct+P.top.paths*royalty G^2)+ Real.sqrt P.bind.penalty
def dimLift (P : Teller G) (r : ℕ) (v : ℝ) := ((4+2*r)*(v*royalty G))+(v*royalty G+v) + max 0 P.η

structure Primary (P : Teller G) (U : E→ Config G f) (V Q : E→ Config G c) (x : E) (h d : ℝ) (r : ℕ) (T : Tube G S) (k : ℕ) : Prop where
  cost : 0≤ h
  hill : 0≤d
  down p : Brush k h d (fun i=> T.Xn r (V i) p) x
  high p : Brush k h d (fun i=> T.Xf r (U i) p) x
  wanted p : Brush k h d (fun i=> Tube.Z S (Q i) (V i) p) x

lemma measures (p : P.Funds S T) (hV : Mode V x k v) (hU : Mode U x k v) (hQ : Mode Q x k v) (R : ℕ) :
    Primary P U V Q x (shadowL P) (dimLift P R v) R T k := by
  obtain ⟨_,_,h',h⟩ := p.feeds; rw [← p.high] at h'; rw [← p.low] at h
  let u := shadowL P
  have he := royalty_ge G; have hi := hU.pos
  have hs : 0≤ (4+2*(R:ℝ))*(v*royalty G) := by positivity
  have ht : 0≤ v*royalty G+v := by positivity
  have hX := P.below.paths_pos; have hY := P.top.paths_pos
  refine ⟨(by unfold shadowL; positivity),(by unfold dimLift; positivity),fun i=> (screen T.down _ _ h S.patch.L.property hV i).climb ?_ ?_,
    fun i=> (screen T.up _ _ h' (by norm_num : 0<(1:ℕ)) hU i).climb ?_ ?_, fun i=> (Noise S hV hQ i).climb ?_ ?_⟩
  · unfold shadowL; rw [p.low]; exact (le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · unfold dimLift; exact (le_add_of_nonneg_right ht).trans (le_add_of_nonneg_right (le_max_left 0 _))
  · unfold shadowL; rw [p.high]; exact (le_add_of_nonneg_left (by positivity)).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · unfold dimLift; exact (le_add_of_nonneg_right ht).trans (le_add_of_nonneg_right (le_max_left 0 _))
  · unfold shadowL; rw [p.knobs]; apply le_add_of_nonneg_left; positivity
  unfold dimLift; exact (le_add_of_nonneg_left hs).trans (le_add_of_nonneg_right (le_max_left 0 _))

def payZ (P : Teller G) (L : Side) (R : ℕ) (v : ℝ) := (Animals.ballCost R:ℝ) * coversMark L * (typesL P*v)
def hikeZ (G : Gauge) (u : ℝ) (R : ℕ) (v : ℝ) := 2*(R:ℝ)*u*royalty G+v

structure Canopied (U : E→ Config G f) (V Q : E → Config G c) (R k : ℕ) (T : Tube G S) (p v Y d : ℝ) (x : E) : Prop where
  p0 i : Brush k p v (fun j=> canopyF T R (V j) i) x
  p1 i : Brush k p v (fun j=> canopyI T R (V j) i) x
  p2 i : Brush k p v (fun j=> canopyN T R (V j) i) x
  warp i : Brush k p v (fun j=> unzip (T.Φ R (V j)) (T.Xf R (U j)) i) x
  wear i : Brush k p v (fun j=> unzip (T.Φ' R (V j)) (Tube.Z S (Q j) (V j)) i) x
  wo i : Brush k Y d (fun j => unzip (T.Φ R (V j)) (canopyF T R (V j)) i) x
  wq i : Brush k Y d (fun j => unzip (T.Φ' R (V j)) (canopyI T R (V j)) i) x
  wp i : Brush k Y d (fun j => unzip (T.N R (V j)) (canopyN T R (V j)) i) x
lemma enCanvas (p : P.Funds S T) {C D : ℝ} {R : ℕ} (h : Primary P U V Q x C D R T k)
    (hV : Mode V x k v) (hp : S.patch.L=L) : let q := payZ P L R C; let w:=hikeZ G v R D
    Canopied U V Q R k T q w (payZ P L R q) (hikeZ G v R w) x := by
  subst L; intro q w
  obtain ⟨ht,hv,hp⟩:= pigments P R p hV.pos hV.atLink
  have hF (i) := ht.pigment_zip (g:=fun i=> T.Xn R (V i)) i h.cost h.hill (fun j _=> h.down j)
  have hI (i) := hv.pigment_zip (g:=fun i=> T.Xn R (V i)) i h.cost h.hill (fun j _=> h.down j)
  have hN (i) := hp.pigment_zip (g:=fun i=> T.Xn R (V i)) i h.cost h.hill (fun j _=> h.down j)
  have hq : 0≤ q := (hI (0,0)).nonneg; have hw : 0≤w := (hI (0,0)).pos
  exact ⟨hF,hI,hN,fun i=> ht.pigment_unzip i h.cost h.hill fun j _=> h.high j,
    fun i=> hv.pigment_unzip i h.cost h.hill fun j _=> h.wanted j,
    fun i=> ht.pigment_unzip i hq hw fun j _=> hF j, fun i=> hv.pigment_unzip i hq hw fun j _=> hI j,
    fun i=> hp.pigment_unzip i hq hw fun j _=> hN j⟩
end YM.ConnectedActivityE6.Blaze

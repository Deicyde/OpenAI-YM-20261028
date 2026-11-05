import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Window
import YM.Push.FREE_RESOLVENT.Midpoint
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen



/-!
# Address comparison for the *two* geometries, ambient and active

Use the exact ratio of S, odd L. Prove both windows contain the same
working balls (the price needed for inverse decay) and differ by at
most a fixed-radius ENLARGEMENT in their d_L interpretation (the price
for reading, not a change to either kernel). True torus endpoints
including seam, B = radiusB x. Color blocks intact. Prove invariance
under signed readdressing and all allowed coarse translations (midpoint
relation even under fine ones); actual sector equivalences studied later.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Lattice Wilson RG Precision Exterior Tree Pressure Pressure.Stores YM.Bid Next SectorChange
  Rows Wisps Gaussian Function Set FreeResolvent Matrix
open scoped Classical BigOperators

variable {c f n : Side} {S : StepData c f} {G : Gauge} {F : Forest S.ratio} {A : Stores S} {x : ℝ}

/-- Both whole spaces are common physical *positive* links times color,
one written with Body type axes. Use this map, not `cast`. -/
abbrev RawLink (G : Gauge) (n : Side) := Bond n × G.ColorIndex

def rawEquiv (G : Gauge) (n : Side) : RawLink G n ≃ Affine.raw G n := {
  toFun t := (t.1.1,coord t.1.2,t.2)
  invFun t := ((t.1,axisEquiv.symm t.2.1),t.2.2)
  left_inv t := by rcases t with ⟨⟨i,b⟩,z⟩; change ((i,axisEquiv.symm (axisEquiv b)),z)=_; rw [axisEquiv.symm_apply_apply]
  right_inv t := by rcases t with ⟨i,b,z⟩; change (i,axisEquiv (axisEquiv.symm b),z)=_; rw [axisEquiv.apply_symm_apply] }

def originLink (A : Stores S) (F : Forest S.ratio) (x : ℝ) (G : Gauge) :
    In (G:=G) x A F ↪ RawLink G f where
  toFun i := (i.1.val.val,i.2)
  inj' _ _ h := Prod.ext (Subtype.ext (Subtype.ext (congr_arg (fun x : RawLink G f => x.1) h))) (congr_arg (fun x : RawLink G f => x.2) h)

/-- Registration in the *actual* window domain of Mid.cutView. -/
def register (A : Stores S) (F : Forest S.ratio) (x : ℝ) (G : Gauge) :
    In (G:=G) x A F ↪ Affine.raw G f := (originLink A F x G).trans (rawEquiv G f).toEmbedding







/-- Exact  comparison (Doubling implementation). Config need not
have any colors (e.g. finite gauges); state also on raw Bonds. -/
def midMeet (S : StepData c f) (B : ℕ) (e p : Bond f) : Prop :=
  20 * separation (Mid.axis e) (Mid.axis p) ≤ 2*S.patch.L.val*B

def endMeet (S : StepData c f) (B : ℕ) (e p : Bond f) : Prop :=
  ∀ y ∈ SectorChange.points S e, ∀ z ∈ SectorChange.points S p, separation y z ≤ B/20





lemma mid_mono (S : StepData c f) {e p : Bond f} {B B' : ℕ} (h : B≤B') (hp : midMeet S B e p) : midMeet S B' e p :=
  hp.trans (Nat.mul_le_mul_left _ h)










-- Direct, color-free two-sided compare to initial parents
private lemma triangles (S : StepData c f) (i j : Bond f) :
    let L := S.patch.L.val
    let a := separation (S.ratio.parent i.1) (S.ratio.parent j.1)
    let b := separation (Mid.axis i) (Mid.axis j)
    b ≤ 2*L*a+2*L+2 ∧ 2*L*a ≤ b+2*L+2 := by
  intro L a b
  let g := S.ratio; let q := Mid.double f
  let l (i : Bond f) := q.embed (g.embed (g.parent i.1))
  have he (i : Bond f) : separation (l i) (Mid.axis i) ≤ L+1 := by
    unfold l Mid.axis
    refine (separation_triangle (q.embed _) (q.embed i.1) _).trans ?_
    rw [Mid.upto,separation_comm (g.embed (g.parent i.1))]
    exact Nat.add_le_add (Corona.near g i.1) (Work.E03.sep_step ..)
  have hp : separation (l i) (l j)=2*L*a := by unfold l; rw [Mid.upto,Mid.upto]; unfold q Mid.double g; change 2*(L*a)=_; rw [mul_assoc]
  have hh := he i; have hm := he j
  have hu := separation_triangle (Mid.axis i) (l i) (l j)
  have hv := separation_triangle (Mid.axis i) (l j) (Mid.axis j)
  rw [hp,separation_comm (Mid.axis i) (l i)] at hu
  have hw := separation_triangle (l i) (Mid.axis i) (Mid.axis j)
  have ht := separation_triangle (l i) (Mid.axis j) (l j)
  rw [hp,separation_comm (Mid.axis j)] at ht
  change _ ≤ _ + b at hw
  change b ≤ _ at hv
  omega

lemma end_to_mid (S : StepData c f) {B : ℕ} {i j : Bond f} (h : endMeet S B i j) :
    midMeet S (B+40) i j := by
  let L := S.patch.L.val
  let a := separation (S.ratio.parent i.1) (S.ratio.parent j.1)
  let b := separation (Mid.axis i) (Mid.axis j)
  change 20*b ≤ _
  obtain ⟨hh,-⟩ := triangles S i j
  change b ≤ 2*L*a+2*L+2 at hh
  have hx : a ≤ B/20 := h _ (by simp [SectorChange.points]) _ (by simp [SectorChange.points])
  have he : 20*a ≤ B := by omega
  have hp := Nat.mul_le_mul_left (2*L) he
  have hk : 3 ≤ L := S.patch.coarse
  change 20*b ≤ 2*L*(B+40)
  nlinarith only [hh,hp,hk]

lemma mid_to_end (S : StepData c f) {B : ℕ} {i j : Bond f} (h : midMeet S B i j) :
    endMeet S (B+80) i j := by
  let L := S.patch.L.val
  let u := S.ratio.parent i.1; let v := S.ratio.parent j.1
  let a := separation u v; let b := separation (Mid.axis i) (Mid.axis j)
  have hk : 3 ≤ L := S.patch.coarse
  change 20*b ≤ 2*L*B at h
  obtain ⟨-,hh⟩ := triangles S i j
  change 2*L*a ≤ b+2*L+2 at hh
  have hp : 20*a ≤ B+40 := by
    have ht : 2*L*(20*a) ≤ 2*L*(B+40) := by nlinarith only [hk,h,hh]
    exact Nat.le_of_mul_le_mul_left ht (by omega)
  intro y hy z hz
  have hl : separation u y ≤ 1 := meetings _ hy
  have hv : separation v z ≤ 1 := meetings _ hz
  rw [separation_comm u] at hl
  have he := separation_triangle y u v; change _ ≤ _+a at he
  have hq := separation_triangle y v z
  omega

lemma endContains (S : StepData c f) {B : ℕ} (h : 120 ≤ B) {i j : Bond f}
    (hh : separation (S.ratio.parent i.1) (S.ratio.parent j.1) ≤ B/60) : endMeet S B i j := by
  let u := S.ratio.parent i.1; let v := S.ratio.parent j.1
  intro y hy z hz
  have he := separation_triangle y u v; have ht := separation_triangle y v z
  have hl : separation u y ≤ 1 := meetings _ hy
  have hv : separation v z ≤ 1 := meetings _ hz
  rw [separation_comm u] at hl
  change separation u v ≤ _ at hh; omega

lemma midContains (S : StepData c f) {B : ℕ} (h : 120 ≤ B) {i j : Bond f}
    (hh : separation (S.ratio.parent i.1) (S.ratio.parent j.1) ≤ B/60) : midMeet S B i j := by
  have ht : 20*(B/60) +40+40 ≤ B := by omega
  refine mid_mono S ht (end_to_mid S ?_)
  intro y hy z hz
  let u := S.ratio.parent i.1; let v := S.ratio.parent j.1
  have he := separation_triangle y u v; have ht := separation_triangle y v z
  have hl : separation u y ≤ 1 := meetings _ hy
  have hv : separation v z ≤ 1 := meetings _ hz
  rw [separation_comm u] at hl
  change separation u v ≤ _ at hh; omega

/-! ## The surveys used in the two theorem statements -/

def midSets (S : StepData c f) (B : ℕ) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (G : Gauge) (i : In x A F (G:=G)) :=
  {j : In x A F (G:=G) | midMeet S B i.1.val.val j.1.val.val}

def endSets (S : StepData c f) (B : ℕ) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (G : Gauge) (i : In x A F (G:=G)) :=
  {j : In x A F (G:=G) | endMeet S B i.1.val.val j.1.val.val}





lemma both_bars (S : StepData c f) {B : ℕ} (h : 120 ≤ B) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (G : Gauge) :
    SectorChange.Schur.Bars (midSets S B A F x G) (front A F) (B/60) ∧
      SectorChange.Schur.Bars (endSets S B A F x G) (front A F) (B/60) := by
  constructor
  · exact fun i j he => midContains S h he
  exact fun i j he => endContains S h he

lemma bars_hasCenters {V : Type} {c} {p : V → Site c} {W : V → Set V} {R : ℕ}
    (h : SectorChange.Schur.Bars W p R) (i) : i ∈ W i := h i i (by simp)

lemma bars_near {V : Type} {c} {p : V → Site c} {W : V → Set V} {R : ℕ}
    (h : SectorChange.Schur.Bars W p R) : (setSurvey W (bars_hasCenters h)).Near (native c) p R := by
  intro i j he
  have hj : j ∉ W i := fun hh => he ⟨⟨j,hh⟩,rfl⟩
  have hh : R ≤ separation (p i) (p j) := Nat.le_of_lt (lt_of_not_ge (fun h₀ => hj (h i j h₀)))
  change (R:ℝ) ≤ (separation (p i) (p j):ℝ)
  exact_mod_cast hh



/-- Covariance/mean ordering adapters on the actual active counting
basis; full-space completion in `Padded`. -/
theorem named_sector (S : StepData c f) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (T : Tube G S)
    (k : S.Choices) (V : Config G c) (q : YM.Push.SectorMeasure.Chi) (d : ℝ) :
    let Q := Rows.gram T x V k (shots S x) A F
    let H := pane (endSets S (radiusB x) A F x G) Q 0
    fog A F T x V k = mirror H ∧ ∀ y, meanLog A F T x V k q d y = -(H.transpose) *ᵥ Rows.blame T x V k (shots S x) A F q d y := by
  intro Q H
  unfold H; rw [pane_zero]
  exact ⟨rfl,fun y => rfl⟩
end YM.AnalyticBridge.LocalGaussianLaws

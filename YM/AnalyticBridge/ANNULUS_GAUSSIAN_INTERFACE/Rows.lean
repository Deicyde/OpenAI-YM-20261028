import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Geometry
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Remainder
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stencils

set_option warningAsError false

/-!
# Exact partition of the deducted rows in `SectorChange.dyed`

Pull before reading each row; anchors in a `Window` in that orientation.
No active ``thin envelope'' assumption, no accounting in a completed
space before subtraction. Classification only on geometry and the actual F, A.
Numerical alignment of the subtracted squares requires more hypotheses and
comes later. See .
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus
open Function Lattice RG RG.Patch Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree
  YM.Push.SectorMeasure Oriented Precision Exterior Bloch Next.SectorChange
open YM.SectorNext.Remainder (onWindow)
open YM.SectorNext.Remainder.Affine
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- A merged packet pays for precisely the D-dome *row* anchors. -/
def inner (O : Stores S) (D : ℕ) (x : ℝ) (s : Signed) : Window S :=
  let H := (turnStore s O).dome (D*radiusB x)
  ⟨Finset.univ.filter fun i => S.ratio.parent i.1 ∈ H, Finset.univ.filter fun i => i.1 ∈ H,
    Finset.univ.filter fun i => i.1∈ H,Finset.univ.filter fun i => i.1 ∈ H⟩

def less (U V : Window S) : Window S :=
  ⟨U.face \ V.face,U.noise \ V.noise,U.coarse \ V.coarse,U.rows \ V.rows⟩

def other (U : Window S) : Window S := ⟨U.faceᶜ,U.noiseᶜ,U.coarseᶜ,U.rowsᶜ⟩

def rim (O : Stores S) (D : ℕ) (x : ℝ) (s : Signed) := less (inner O D x s) (inner O 2 x s)

lemma rim_located (O A : Stores S) (x : ℝ) (s : Signed) {D r : ℕ} (h : Clearance O A r) (hs : (D+2)*radiusB x ≤ r) :
    (rim O D x s).annulus (turnStore s O) (turnStore s A) D (radiusB x) := by
  let B := radiusB x
  have he (i : Site c) (hi : i∈(turnStore s O).dome (D*B)) (hh : i∉(turnStore s O).dome (2*B)) :
      inSweep (turnStore s O) (turnStore s A) D B i :=
    ⟨fun hj => hh ((h.turn s).owns_dome hi (by rwa [add_mul] at hs) hj),hi⟩
  simp only [Window.annulus, rim, less,inner,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun i hi => he _ hi.1 hi.2,fun i hi => he _ hi.1 hi.2,fun i hi => he _ hi.1 hi.2⟩

/-- Copy the selected rows, exactly at curb rule on the *full initial* A
(all cores). Don't change active sets when testing O. -/
def selectFrom (U : Window S) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (s : Signed) : Window S :=
    ⟨U.face.filter fun i => curb (shots S x) A F x s (.inl i),
      U.noise.filter fun i => curb (shots S x) A F x s (.inr i),∅,∅⟩

lemma selects (U : Window S) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (s : Signed) :
    (selectFrom U A F x s).selects U := ⟨Finset.filter_subset ..,Finset.filter_subset ..⟩

lemma selects_empty_heart (O A : Stores S) (F : Forest S.ratio) (x : ℝ) (s : Signed) (hp : span S.patch x ≤ radiusB x/50)
    {r : ℕ} (ho : Clearance O A r) : selectFrom (inner O 2 x s) A F x s = ⟨∅,∅,∅,∅⟩ := by
  let B := radiusB x
  have he (i : Where S) (hf : curb (shots S x) A F x s i) : roots S i ∉ (turnStore s O).dome (2*B) := by
    intro h; apply (guarded hp hf).1
    exact expand_dome A (show 2*B ≤ 9*B+9*B/10 by omega) (ho.all _ ((turn_dome ..).mp h))
  have hh : (selectFrom (inner O 2 x s) A F x s).face=∅ := by
    apply Finset.eq_empty_of_forall_notMem; intro i ha
    simp only [selectFrom,inner,Finset.mem_filter,Finset.mem_univ,true_and] at ha
    exact he _ ha.2 ha.1
  have hl : (selectFrom (inner O 2 x s) A F x s).noise=∅ := by
    apply Finset.eq_empty_of_forall_notMem; intro i ha
    simp only [selectFrom,inner,Finset.mem_filter,Finset.mem_univ,true_and] at ha
    exact he _ ha.2 ha.1
  change Window.mk _ _ _ _= _
  congr

variable (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices)
    (A : Stores S) (F : Forest S.ratio) (q : Chi) (d : ℝ)
    (Y : LinkArray G (Frozen A x F)) (a : Prices G (Active A x F))
    (U : Config G f) (O : Stores S) (D : ℕ)

def squares (s : Signed) (X : Window S) :=
    (∑ i∈X.face, ∑ j : Bool, Rows.chargedUp T x V k (shots S x) A F q d Y a s (i,j)) +
      (∑ i∈X.noise,Rows.chargedSide T x V k (shots S x) A F q d Y a s i)

lemma squares_nonneg (s : Signed) (X : Window S) : 0 ≤ squares T x V k A F q d Y a s X := by
  refine add_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg ?_) (Finset.sum_nonneg ?_)
  · intro j _; unfold Rows.chargedUp; split <;> positivity
  intro j _; unfold Rows.chargedSide; split <;> positivity

lemma squares_select (s : Signed) (X : Window S) :
    squares T x V k A F q d Y a s X=squares T x V k A F q d Y a s (selectFrom X A F x s) := by
  unfold squares selectFrom; simp only [Finset.sum_filter]; apply congr_arg₂ (fun u v : ℝ => u+v)
  · apply Finset.sum_congr rfl
    intro i _; split
    · rfl
    rename_i hc; simp [Rows.chargedUp,hc]
  · apply Finset.sum_congr rfl; intro i _; split
    · rfl
    rename_i hc; simp [Rows.chargedSide,hc]

lemma heart_zero (s : Signed) (hp : span S.patch x ≤ radiusB x/50) {r : ℕ} (ho : Clearance O A r) :
    squares T x V k A F q d Y a s (inner O 2 x s)=0 := by
  rw [squares_select, selects_empty_heart O A F x s hp ho]; simp [squares]

private lemma corePay (s : Signed) : (inner O 2 x s).work T x U k V = (turnStore s O).assessed T x U (S.prediction U k) V := by
  unfold Window.work onWindow inner assessed tally talli tallc talln talll limit intern outs coordN
  simp only [Finset.sum_add_distrib]; abel

/-- Row residual cost on actual charge window. Includes answer for *every* row (some
zero), all cut LDross works, before additive/sign. -/
def debris (s : Signed) (X : Window S) :=
    X.work T x (pull s 0 U) (choice s k) (pull s 0 V) - squares T x V k A F q d Y a s X

private lemma subsum {ι : Type} [DecidableEq ι] (e : ι → Site c) (g : ι → ℝ) (s : Signed) (hD : 2 ≤ D)
    (w : Finset ι) :
    let H d := w.filter fun i => e i ∈ (turnStore s O).dome (d*radiusB x)
    (∑ i ∈ H D, g i) = (∑ i ∈ H 2, g i) + (∑ i ∈ H D \ H 2, g i) := by
  intro H; symm; rw [add_comm]
  have hi : H 2 ⊆ H D := fun i h => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp h).1,expand_dome _ (Nat.mul_le_mul_right _ hD) (Finset.mem_filter.mp h).2⟩
  exact Finset.sum_sdiff hi

lemma debris_core (s : Signed) (hD : 2 ≤ D) (hp : span S.patch x ≤ radiusB x/50) {r : ℕ} (ho : Clearance O A r) :
    let W := choice s k; let H := pull s 0 U; let R := pull s 0 V
    debris T x V k A F q d Y a U s (inner O D x s)=(turnStore s O).assessed T x H (S.prediction H W) R+
      debris T x V k A F q d Y a U s (rim O D x s) := by
  intro W H R
  have hi : debris T x V k A F q d Y a U s (inner O 2 x s)=(turnStore s O).assessed T x H (S.prediction H W) R := by
    unfold debris; rw [corePay,heart_zero T x V k A F q d Y a O s hp ho, sub_zero]
  rw [← hi]
  unfold debris Window.work onWindow squares rim inner less
  dsimp only
  -- use subsum individually before converting costs
  let t := till x; let u := temp x; let v := fiery G x S.patch.L; let P := S.prediction H W
  have he := subsum x O D (fun i : Cell f => S.ratio.parent i.1) (fun i => T.workF t H R v u i) s hD Finset.univ
  have hb := subsum x O D (fun i : Bond c => i.1) (fun i => T.workI t P R u i) s hD Finset.univ
  have hh := subsum x O D (fun i : Cell c => i.1) (fun i => T.workC t R u i+(T.workL t H P R u i+T.workD t R u i)) s hD Finset.univ
  have hv := subsum x O D (fun i : Co c Gain => i.1) (fun i => T.workN t R u i) s hD Finset.univ
  have hg := subsum x O D (fun i : Cell f => S.ratio.parent i.1)
    (fun i => ∑ j : Bool,Rows.chargedUp T x V k (shots S x) A F q d Y a s (i,j)) s hD Finset.univ
  have hf := subsum x O D (fun i : Bond c => i.1) (fun i => Rows.chargedSide T x V k (shots S x) A F q d Y a s i) s hD Finset.univ
  dsimp only [W,H,R,t,u,v,P] at he hb hh hv hg hf
  linarith only [he,hb,hh,hv,hg,hf]







end YM.AnalyticBridge.Annulus

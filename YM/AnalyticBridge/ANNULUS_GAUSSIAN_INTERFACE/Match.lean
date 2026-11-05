import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Rows
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.LocalJet

set_option warningAsError false

/-!
# Literal oriented affine squares

At the coordinates used in `dyed`. `Q` receives its actual rotated
directions, not a transformation by the V tangent of a canonical bond
noise! In particular this file walks the jets in both developments and
compares them; no implicit identification because of similar sizes. In
this piece the analytic branch prerequisite for blockJet is an explicit
hypothesis; addressed locally later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus
open Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree
  YM.Push.SectorMeasure Oriented Exterior Bloch Next.SectorChange Motion
open YM.SectorNext.Remainder.Affine
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (A : Stores S) (F : Forest S.ratio) (q : Chi)
    (d : ℝ) (Y : LinkArray G (Frozen A x F)) (a : Prices G (Active A x F))

def theta := Rows.input x A F (autoShell q d V Y)+Rows.fresh x (shots S x) A F (tape a)

def angle (s : Signed) := inChannel s (replica S.ratio V) (theta x V A F q d Y a)

/-- E affvd p tangent. Smooth (no branch). -/
theorem face_match (s : Signed) (p : Cell f) (u : Directions G f) :
    plaquetteJet S V s p u = faceVar (replica S.ratio (pull s 0 V)) (inChannel s (replica S.ratio V) u) p := by
  let W := pull s 0 (replica S.ratio V)
  let L := pTest W p
  let e := inChannel s (replica S.ratio V) u
  have ht : ContDiffAt ℝ ω L 0 := (LocalJet.face_smooth ..).contDiffAt
  have he := (plaquette_turn s V p ht).2 u
  unfold plaquetteJet
  rw [he]; unfold faceVar
  rw [← replica_turn]
  have hf := YM.Push.side L (ht.differentiableAt (by simp)) e
  exact hf.deriv.symm

/-- Noise tangent. Match on branch with actual normalization. -/
theorem side_match (s : Signed) (i : Bond c) (u : Directions G f)
    (hp : ContDiffAt ℝ ω (bTest (pull s 0 (replica S.ratio V)) (choice s k) i) 0) :
    blockJet V k s i u=qVar S (replica S.ratio (pull s 0 V)) i (choice s k) (inChannel s (replica S.ratio V) u) := by
  let W := pull s 0 (replica S.ratio V)
  let L := bTest W (choice s k) i
  let a := inChannel s (replica S.ratio V) u
  unfold qVar blockJet
  rw [(block_turn s V i k hp).2 u, ← replica_turn, actuate,zero_smul,Motion.increment_zero]
  exact (YM.Push.side L (hp.differentiableAt (by simp)) a).deriv.symm

private theorem first_cut (s : Signed) (p : Cell f) (u : Directions G f) {o σ C Λ} (h : T.up.Bounds o σ C Λ) :
    let W := replica S.ratio (pull s 0 V); let R := till x; let a := inChannel s (replica S.ratio V) u
    shorten T.up R 1 W p + barrel T.up R W (fun i => plaquetteJet S V s i u) p = firstCut T.up R W a p := by
  intro W R a; rw [← barrel_term,← barrel_add _ _ _ _ _ h]; simp_rw [face_match]
  rfl

/-- One *selected* p-block; both p rows included. -/
theorem twin_match (s : Signed) (p : Cell f) {o σ C Λ} (h : T.up.Bounds o σ C Λ)
    (hi : curb (shots S x) A F x s (.inl p)) :
    let w := pull s 0 V; let W := replica S.ratio w
    (∑ j : Bool, Rows.chargedUp T x V k (shots S x) A F q d Y a s (p,j)) =
        squareP T (till x) (temp x) w W (angle x V A F q d Y a s) p := by
  intro w W
  let u := theta x V A F q d Y a
  let e (i : Bool) := Rows.lands T x V k (shots S x) A F q d Y a (s,.inl (p,i))
  have he : facade S s V 0 = W := (fixed_facade ..).trans (replica_turn ..)
  let α := angle x V A F q d Y a s
  have hα : inChannel s (replica S.ratio V) u=α := rfl
  have hh0 : e false = affF0 T (till x) (temp x) w W α p := by
    change Rows.faceFixed T x s V (p,false)+Rows.faceKick T x V u s (p,false) = _
    unfold Rows.faceFixed Rows.faceKick affF0 firstFace
    simp only [Bool.false_eq_true, ↓reduceIte, Xf,shoot,plotted, he, smul_add]
    rw [face_match, hα]; unfold W w; abel
  have hh1 : e true = affF1 T (till x) (temp x) w W α p := by
    change Rows.faceFixed T x s V (p,true)+Rows.faceKick T x V u s (p,true)=_
    unfold Rows.faceFixed Rows.faceKick affF1
    simp only [↓reduceIte,Xf,plotted,he]
    have ht := first_cut T x V s p u h
    change shorten T.up _ _ W _ + barrel T.up _ W _ _ = firstCut T.up _ W α _ at ht
    rw [← ht]; unfold w; abel
  unfold squareP Rows.chargedUp
  rw [Fintype.sum_bool]; dsimp only; rw [if_pos hi, if_pos hi]
  dsimp only [e,α] at hh0 hh1
  rw [hh0,hh1]; exact add_comm ..

/-- Noise row with Q in the actual pulled orientation. -/
theorem noise_match (s : Signed) (i : Bond c)
    (hp : ContDiffAt ℝ ω (bTest (pull s 0 (replica S.ratio V)) (choice s k) i) 0)
    (hi : curb (shots S x) A F x s (.inr i)) :
    let w := pull s 0 V; let W := replica S.ratio w
    Rows.chargedSide T x V k (shots S x) A F q d Y a s i =
      squareQ T (till x) (temp x) w W (choice s k) (angle x V A F q d Y a s) i := by
  intro w W
  let u := theta x V A F q d Y a
  have he : facade S s V 0 = W := (fixed_facade ..).trans (replica_turn ..)
  unfold Rows.chargedSide squareQ; rw [if_pos hi]
  change ‖Rows.noiseFixed T x V k s i+Rows.noiseKick V k u s i‖^2/2 = _
  unfold Rows.noiseKick Rows.noiseFixed
  rw [side_match V k s i u hp,he]
  let b := Real.sqrt S.kernel.penalty • qVar S W i (choice s k) (angle x V A F q d Y a s)
  change ‖Z S _ w i-T.Mw _ _ w i + -b‖^2/2 = _
  rw [show Z S _ w i-T.Mw _ _ w i + -b = Z S (S.prediction W (choice s k)) w i-b-T.Mw (till x) (temp x) w i from ?_]
  abel

def AtBranches (s : Signed) (X : Window S) :=
    ∀ i∈(selectFrom X A F x s).noise, ContDiffAt ℝ ω (bTest (pull s 0 (replica S.ratio V)) (choice s k) i) 0

theorem cost_match (s : Signed) (X : Window S) {o σ C Λ} (h : T.up.Bounds o σ C Λ)
    (hb : AtBranches x V k A F s X) :
    squares T x V k A F q d Y a s X =
      (selectFrom X A F x s).extract T x (choice s k) (pull s 0 V) (angle x V A F q d Y a s) := by
  rw [squares_select]; unfold squares Window.extract
  apply congr_arg₂ (fun t v : ℝ => t+v)
  · exact Finset.sum_congr rfl fun i hi => twin_match T x V k A F q d Y a s i h (Finset.mem_filter.mp hi).2
  exact Finset.sum_congr rfl fun i hi => noise_match T x V k A F q d Y a s i (hb _ hi) (Finset.mem_filter.mp hi).2

theorem core_match (U : Config G f) (O : Stores S) (s : Signed) (D : ℕ) {o σ C Λ} (h : T.up.Bounds o σ C Λ)
    (hp : span S.patch x ≤ radiusB x/50) (hd : 2 ≤ D) {r : ℕ} (hc : Clearance O A r)
    (hb : AtBranches x V k A F s (rim O D x s)) :
    debris T x V k A F q d Y a U s (inner O D x s) =
      credits U V O (rim O D x) (fun s => selectFrom (rim O D x s) A F x s) T x k (angle x V A F q d Y a) s := by
  rw [debris_core T x V k A F q d Y a U O D s hd hp hc]; unfold debris credits boost
  rw [cost_match _ _ _ _ _ _ _ _ _ _ _ _ h hb]
end YM.AnalyticBridge.Annulus

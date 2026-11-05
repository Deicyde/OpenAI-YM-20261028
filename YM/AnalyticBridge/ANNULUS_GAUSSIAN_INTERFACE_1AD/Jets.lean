import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Anchors
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Author
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Remainder

/-!
# Identify 's true jets with the subtraction in dyed

Even for winding reads. All a arguments (incl shell extension on frozen) in
common orientation passed through the pull rule. No use of an assumption
about commutation of noise log with reversal. NO second channel weight here.
-/
set_option autoImplicit false
-- Only stylistic lint disabled. All holes/axioms/declaration safety audited at entry.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric Oriented Presented Exterior Bloch
open YM.Next.SectorChange YM.SectorNext.Remainder
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
open Affine

variable {G : Gauge} {c f : Side} (S : StepData c f)

/-- Use the *literal* arguments of selected Gaussian precision. -/
def basisArray {S : StepData c f} (x : ℝ) (A : Stores S) (F : Forest S.ratio) (q : Chi) (d : ℝ) (V : Config G c)
    (Y : LinkArray G (Frozen A x F)) (a : Prices G (Active A x F)) :=
  Rows.input x A F (autoShell q d V Y) + Rows.fresh x (shots S x) A F (tape a)

def signedArray {S : StepData c f} (x : ℝ) (A : Stores S) (F : Forest S.ratio) (q : Chi) (d : ℝ) (V : Config G c)
    (Y : LinkArray G (Frozen A x F)) (a : Prices G (Active A x F)) (s : Signed) :=
  Motion.inChannel s (replica S.ratio V) (basisArray x A F q d V Y a)

lemma same_facade (s : Signed) (V : Config G c) : facade S s V 0 = replica S.ratio (pull s 0 V) :=
  (fixed_facade ..).trans (replica_turn S.ratio S.patch.odd_side s V).symm

lemma jet_at_p (s : Signed) (V : Config G c) (i : Cell f) (u : Directions G f) :
    let f := Motion.inChannel s (replica S.ratio V)
    plaquetteJet S V s i u = faceVar (replica S.ratio (pull s 0 V)) (f u) i := by
  let h := pull s (0:Site f) (replica S.ratio V)
  have he := (LocalJet.face_smooth (G:=G) h i).contDiffAt (x:=0)
  intro f
  calc
    _ = fderiv ℝ (Motion.pTest h i) 0 (f u) := (Motion.plaquette_turn s V i (S:=S) he).2 u
    _ = deriv (fun a : ℝ => Motion.pTest h i (a • f u)) 0 :=
      (YM.Push.side _ (he.differentiableAt (by simp)) (f u)).deriv.symm
    _ = _ := by unfold Motion.pTest h faceVar; rw [replica_turn _ S.patch.odd_side]

variable {S}
variable (V : Config G c) (x : ℝ) (k : S.Choices)

lemma jet_at_b (A : Stores S) (F : Forest S.ratio) {B : ℝ} (s : Signed) {i : Bond c}
    (h : curb (shots S x) A F x s (.inr i)) (ha : Authorized A V F x B) (u : Directions G f) :
    let f := Motion.inChannel s (replica S.ratio V)
    blockJet V k s i u = qVar S (replica S.ratio (pull s 0 V)) i (choice s k) (f u) := by
  let hU := pull s (0:Site f) (replica S.ratio V)
  let Q := Motion.bTest hU (choice s k) i
  have he : ContDiffAt ℝ ω Q 0 := (ha.noise s k i h).2.1
  intro f
  calc
    _ = fderiv ℝ Q 0 (f u) := (Motion.block_turn s V i k he).2 u
    _ = deriv (fun a : ℝ => Q (a • f u)) 0 := (YM.Push.side Q (he.differentiableAt (by simp)) (f u)).deriv.symm
    _ = _ := by
      unfold Q Motion.bTest Motion.out hU qVar actuate; rw [replica_turn _ S.patch.odd_side,zero_smul,Motion.increment_zero]

variable (T : Tube G S) (F : Forest S.ratio) (A : Stores S) {B : ℝ} {n Λ Zr : ℝ} {o : Clip}
variable (q : Chi) (d : ℝ)



lemma labels_agree (Y : LinkArray G (Frozen A x F)) (a : Prices G (Active A x F)) (hT : T.up.Bounds o n Λ Zr) (s : Signed)
    (i : Cell f) :
    let c := Rows.lands T x V k (shots S x) A F q d Y a
    let U := pull s (0:Site _) V; let f := signedArray x A F q d V Y a s
    c (s,.inl (i,true)) = affF1 T (till x) (temp x) U (replica S.ratio U) f i ∧
    c (s,.inl (i,false)) = affF0 T (till x) (temp x) U (replica S.ratio U) f i := by
  intro c' U f'
  let W := replica S.ratio U
  let z p := G.curvature (faceValue W p)
  let C p := faceVar W f' p
  let v:=basisArray x A F q d V Y a
  let r:=till x; let l:=temp x
  have ht p : plaquetteJet S V s p v=C p := jet_at_p S s V p v
  constructor
  · change (T.Xf r (facade S s V 0) (i,true) - T.Mv r l U (i,true)) +
      barrel T.up r (facade S s V 0) (fun p => plaquetteJet S V s p v) i =
      firstCut T.up r W f' i - T.Mv r l U (i,true)
    simp_rw [show (fun p => plaquetteJet S V s p v) = C from funext ht,same_facade S s V]
    unfold Xf plotted
    simp only [↓reduceIte]; change (shorten T.up r 1 W i-_) + barrel T.up r W C i = _
    rw [← barrel_term]
    have he : firstCut T.up r W f' i = barrel T.up r W z i + barrel T.up r W C i :=
      barrel_add T.up r W z i hT C
    rw [he]; abel
  change (T.Xf r (facade S s V 0) (i,false)-_) +  (Real.sqrt T.high.direct • plaquetteJet S V s i v) = _
  rw [same_facade S s V,ht]
  unfold Xf plotted
  simp only [Bool.false_eq_true,↓reduceIte]
  unfold Pressure.shoot affF0 firstFace C W U
  rw [smul_add]; abel

lemma block_agrees (Y : LinkArray G (Frozen A x F)) (a : Prices G (Active A x F)) (s : Signed)
    (i : Bond c) (h : curb (shots S x) A F x s (.inr i)) (hT : Authorized A V F x B) :
    let c := Rows.lands T x V k (shots S x) A F q d Y a
    let U := pull s 0 V; let f := signedArray x A F q d V Y a s
    let r:= till x
    let z:=Z S (S.prediction (replica S.ratio U) (choice s k)) U i
    let e:=Real.sqrt S.kernel.penalty • qVar S (replica S.ratio U) i (choice s k) f
    c (s,.inr i) = z - e - T.Mw r (temp x) U i := by
  intro c' U f' r z e
  change (Z S (S.prediction (facade S s V 0) (choice s k)) (pull s 0 V) i-T.Mw (till x) (temp x) (pull s 0 V) i) + (-(Real.sqrt S.kernel.penalty • blockJet V k s i (basisArray x A F q d V Y a))) = z - e - _
  rw [jet_at_b V x k A F s h hT]
  unfold z U e; rw [same_facade]; unfold f' r signedArray; abel

variable (Y : LinkArray G (Frozen A x F)) (a : Prices G (Active A x F)) (s : Signed)

lemma same_square (i : Cell f) (hT : T.up.Bounds o n Λ Zr) (he : curb (shots S x) A F x s (.inl i)) :
    (∑ j : Bool, Rows.chargedUp T x V k (shots S x) A F q d Y a s (i,j)) =
      let U := pull s 0 V
      squareP T (till x) (temp x) U (replica S.ratio U) (signedArray x A F q d V Y a s) i := by
  obtain ⟨h1,h2⟩ := labels_agree V x k T F A q d Y a hT s i
  rw [Fintype.sum_bool]
  unfold Rows.chargedUp; dsimp only
  rw [if_pos he,if_pos he,h1,h2]; exact add_comm _ _

lemma same_squareQ (i : Bond c) (hT : Authorized A V F x B) (he : curb (shots S x) A F x s (.inr i)) :
    Rows.chargedSide T x V k (shots S x) A F q d Y a s i =
      let U := pull s 0 V
      squareQ T (till x) (temp x) U (replica S.ratio U) (choice s k) (signedArray x A F q d V Y a s) i := by
  unfold Rows.chargedSide; rw [if_pos he,block_agrees V x k T F A q d Y a s i he hT]; rfl

/-- Score at any anchor set (uses the genuine selected factors). -/
def columns (M : Window S) :=
  (∑ p ∈ M.face, ∑ j : Bool, Rows.chargedUp T x V k (shots S x) A F q d Y a s (p,j)) +
    (∑ p ∈ M.noise, Rows.chargedSide T x V k (shots S x) A F q d Y a s p)
lemma columns_nonneg (M : Window S) : 0 ≤ columns V x k T F A q d Y a s M := by
  unfold columns; apply add_nonneg
  · refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg (fun i _ => ?_)
    unfold Rows.chargedUp; split <;> positivity
  refine Finset.sum_nonneg fun p _ => ?_
  unfold Rows.chargedSide; split <;> positivity

open Finset

lemma extracting (O : Stores S) (D : ℕ) (h : T.up.Bounds o n Λ Zr) (he : Authorized A V F x B) :
    columns V x k T F A q d Y a s (anchorage (turnStore s O) (D*radiusB x)) =
      (harvest A O x F s D).extract T x (choice s k) (pull s 0 V) (signedArray x A F q d V Y a s) := by
  unfold columns Window.extract harvest; dsimp only
  rw [sum_filter,sum_filter]; refine congr_arg₂ (· + ·) ?_ ?_
  · refine sum_congr rfl (fun i _ => ?_)
    split <;> rename_i ht
    · exact same_square V x k T F A q d Y a s i h ht
    simp [Rows.chargedUp,ht]
  refine sum_congr rfl (fun i _ => ?_)
  split <;> rename_i ht
  · exact same_squareQ V x k T F A q d Y a s i he ht
  simp [Rows.chargedSide, ht]

end YM.AnalyticBridge.Annulus1AD

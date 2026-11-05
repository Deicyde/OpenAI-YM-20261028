import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Turn
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Author
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Remainder
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Collar


/-!
# Metering exactly the affvd rows of `dyed`

No estimates yet, just the exact adaptor & sums,
conditional on the same (noise) jet authorization needed to read D as an
actual derivative.

No condition on where using the frozen coordinates
on-shell needed to *write* this formula.

No confusion of Kernel choices,
colors, wraps, or Clip constants between the two realizations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented
open SectorNext.Remainder SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

lemma sq_face (s : Signed) (V : Config G c) (u : Directions G f) (p : Cell f) :
    faceVar (replica S.ratio (pull s 0 V)) (inChannel s (replica S.ratio V) u) p =
      plaquetteJet S V s p u := by
  rw [← turn_replica]
  let P := pTest (pull s 0 (replica S.ratio V)) p
  have h := (LocalJet.face_smooth (pull s 0 (replica S.ratio V)) p).contDiffAt (x:=0)
  rw [plaquetteJet,(plaquette_turn s V p h).2]
  exact (YM.Push.side P (h.differentiableAt (by simp)) _).deriv

lemma sq_block (s : Signed) (V : Config G c) (k : S.Choices) (u : Directions G f) (b : Bond c)
    (h : ContDiffAt ℝ ω (bTest (replica S.ratio (pull s 0 V)) (choice s k) b) 0) :
    qVar S (replica S.ratio (pull s 0 V)) b (choice s k) (inChannel s (replica S.ratio V) u) =
      blockJet V k s b u := by
  rw [← turn_replica] at h ⊢
  rw [blockJet,(block_turn s V b k h).2]
  let l := inChannel s (replica S.ratio V) u
  unfold qVar actuate; rw [zero_smul, Motion.increment_zero]
  exact (YM.Push.side (bTest (pull s 0 (replica S.ratio V)) (choice s k) b) (h.differentiableAt (by simp)) l).deriv

section kick
variable (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (W : Stencils S) (A : Stores S) (F : Forest S.ratio)
  (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F))

def common (a : Prices G (Active A x F)) := Rows.input x A F (autoShell q d V Y) + fresh x W A F (tape a)

def orientedLog (a : Prices G (Active A x F)) (s : Signed) := inChannel s (replica S.ratio V) (common x V W A F q d Y a)

lemma charged_face (P : Teller G) (h : P.Funds S T) (a : Prices G (Active A x F)) (s : Signed) (p : Cell f) :
    (∑ i : Bool, chargedUp T x V k W A F q d Y a s (p,i)) =
      if curb W A F x s (.inl p) then
        squareP T (till x) (temp x) (pull s 0 V) (replica S.ratio (pull s 0 V)) (orientedLog x V W A F q d Y a s) p
      else 0 := by
  classical
  rw [Fintype.sum_bool]
  unfold chargedUp
  by_cases H : curb W A F x s (.inl p)
  swap; rw [if_neg H, if_neg H, if_neg H, zero_add]
  rw [if_pos H, if_pos H, if_pos H]
  obtain ⟨r,t,h₁,h₂⟩ := h.feeds
  let u := common x V W A F q d Y a
  let v := inChannel s (replica S.ratio V) u
  let U := replica S.ratio (pull s 0 V)
  have he : facade S s V 0 = U := by rw [fixed_facade,turn_replica]
  have hf : affF0 T (till x) (temp x) (pull s 0 V) U v p =
      lands T x V k W A F q d Y a (s,.inl (p,false)) := by
    change _ = faceFixed T x s V (p,false)+faceKick T x V u s (p,false)
    simp only [affF0,firstFace,show faceVar U v p = _ from sq_face s V u p,faceFixed,faceKick,he,
      Bool.false_eq_true,↓reduceIte,Xf,plotted,shoot,smul_add]
    abel
  let z (p : Cell f) := G.curvature (faceValue U p)
  let y (p : Cell f) := plaquetteJet S V s p u
  have ht : firstCut T.up (till x) U v p = barrel T.up (till x) U (z+y) p := by
    unfold firstCut barrel
    refine tsum_congr fun i => ?_
    unfold perCharge; dsimp only; split
    next h => unfold firstSlot firstFace; rw [show faceVar U v _ = _ from sq_face s V u _]; rfl
    next _ => rfl
  have hr : affF1 T (till x) (temp x) (pull s 0 V) U v p =
      lands T x V k W A F q d Y a (s,.inl (p,true)) := by
    change _ = faceFixed T x s V (p,true)+faceKick T x V u s (p,true)
    rw [affF1,ht,barrel_add _ _ _ z p h₁ y, show barrel T.up (till x) U z p=shorten T.up (till x) 1 U p from barrel_term ..]
    simp only [faceFixed,faceKick,he,Xf,plotted,↓reduceIte,y]
    abel
  change _ = squareP T (till x) (temp x) _ U v p
  rw [squareP, hf,hr,add_comm]

lemma charged_block (a : Prices G (Active A x F)) (s : Signed) (b : Bond c)
    (h : curb W A F x s (.inr b) → ContDiffAt ℝ ω (bTest (replica S.ratio (pull s 0 V)) (choice s k) b) 0) :
    chargedSide T x V k W A F q d Y a s b =
      if curb W A F x s (.inr b) then
        squareQ T (till x) (temp x) (pull s 0 V) (replica S.ratio (pull s 0 V)) (choice s k) (orientedLog x V W A F q d Y a s) b
      else 0 := by
  unfold chargedSide; split
  next hi =>
    let v := pull s 0 V; let t := choice s k
    let U := replica S.ratio v
    let u := common x V W A F q d Y a
    rw [squareQ, orientedLog,sq_block s V k (common x V W A F q d Y a) b (h hi)]
    have he : facade S s V 0=U := by rw [fixed_facade,turn_replica]
    let z := Z S (S.prediction U t) v b
    let l := T.Mw (till x) (temp x) v b
    let m := Real.sqrt S.kernel.penalty • blockJet V k s b u
    change ‖noiseFixed (T:=T) x V k s b + noiseKick V k u s b‖^2/2 = ‖(z-m)-l‖^2/2
    unfold noiseFixed; rw [he]
    change ‖z-l+-m‖^2/2=_
    rw [show z-l+-m = z-m-l by abel]
  rfl

/-- Local authorization input. Restrictable to particular V/k and selected halo;
otherwise get even a global one at V from `SectorChange` when the output flag
record is exactly right. -/
def Issued (M : Window S) (s : Signed) := ∀ i ∈ M.noise, curb W A F x s (.inr i) →
  ContDiffAt ℝ ω (bTest (replica S.ratio (pull s 0 V)) (choice s k) i) 0

lemma wholeIssued {B : ℝ} (h : Authorized A V F x B) (M : Window S) (s : Signed) :
    Issued x V k (shots S x) A F M s := by
  intro i _ hh
  rw [← turn_replica]
  exact (h.noise s k i hh).2.1

/-- Restriction of the actual subtractions, at the transformed coordinates
(will call on both a(Z) and μ₀(Y)). -/
def extraction (M : Window S) (a : Prices G (Active A x F)) (s : Signed) :=
  (∑ i ∈ M.face, ∑ t : Bool, chargedUp T x V k W A F q d Y a s (i,t)) +
    (∑ i ∈ M.noise, chargedSide T x V k W A F q d Y a s i)

lemma extraction_pos (M : Window S) (a : Prices G (Active A x F)) (s : Signed) :
    0 ≤ extraction T x V k W A F q d Y M a s := by
  unfold extraction; refine add_nonneg (Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _ => ?_)
    (Finset.sum_nonneg fun _ _ => ?_)
  all_goals first | unfold chargedUp; split <;> positivity | unfold chargedSide; split <;> positivity

def emitted (M : Window S) (s : Signed) : Window S where
  face := M.face.filter fun i => curb W A F x s (.inl i)
  noise := M.noise.filter fun i => curb W A F x s (.inr i)
  coarse := ∅
  rows := ∅

lemma emitted_selects (M : Window S) (s : Signed) : (emitted x W A F M s).selects M := ⟨Finset.filter_subset ..,Finset.filter_subset ..⟩

lemma transported {P : Teller G} (h : P.Funds S T) (s : Signed) (M : Window S) (a : Prices G (Active A x F))
    (hh : Issued x V k W A F M s) :
    extraction T x V k W A F q d Y M a s = (emitted x W A F M s).extract T x (choice s k) (pull s 0 V) (orientedLog x V W A F q d Y a s) := by
  unfold extraction emitted Window.extract
  dsimp only
  classical
  rw [Finset.sum_filter,Finset.sum_filter]
  exact congr_arg₂ ((·+·) : ℝ → ℝ → ℝ) (Finset.sum_congr rfl (fun i _ => charged_face T x V k W A F q d Y P h a s i))
    (Finset.sum_congr rfl (fun i hi => charged_block T x V k W A F q d Y a s i (hh i hi)))

end kick
end YM.AnalyticBridge.AnnulusRatioInsertions

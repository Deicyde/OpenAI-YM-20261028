import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Aperture
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Relume
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Totals

/-!
# Covariance-local rotated probes. Don't presume agreement between rotations!

Blocks correspond *within* one sector, same station aperture.
Matrix-column extension fog, not assigning any two blocks with same budget.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Malachite
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open AnalyticBridge.NonflatCovarianceLocality AnalyticBridge.NonflatCovarianceLocality.Placement
open AnalyticBridge.NonflatCovarianceLocality.Matching
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} {E : Support f} {V : Config G c}

section anatomy
variable {I : Type} [Fintype I]
abbrev zone (p : I) (q : I) (A : Matrix (I × G.ColorIndex) (I × G.ColorIndex) ℝ) := A.submatrix (Prod.mk p) (Prod.mk q)
variable [DecidableEq I]
lemma tonewise (g : I → G.El) : ascent g=colorwise g := by
  apply Matrix.ext_iff_mulVec.mpr; intro z; rw [shade_act]; apply tape.injective; rw [ascent_read]; rfl


lemma curtain_left (A : Matrix (I × G.ColorIndex) (I × G.ColorIndex) ℝ) (g : I → G.El) (p q : I) : zone p q ((colorwise g)ᵀ* A)= (zone p p (colorwise g))ᵀ * zone p q A := by
  ext j k; change ((colorwise g)ᵀ * A) (p,j) (q,k)=_
  rw [Matrix.mul_apply,Fintype.sum_prod_type,Finset.sum_eq_single p]
  · rw [Matrix.mul_apply]; rfl
  · intro i hi he; exact Finset.sum_eq_zero fun _ _=> by rw [transpose_apply, Rotation.off g _ (p,j) (show i≠p from he),zero_mul]
  simp
lemma curtain_right (A : Matrix (I × G.ColorIndex) (I × G.ColorIndex) ℝ) (g : I → G.El) (p q : I) :
    zone p q (A * colorwise g)=zone p q A * zone q q (colorwise g) := by
  have hp:= congr_arg Matrix.transpose (curtain_left Aᵀ g q p); rw [transpose_mul] at hp
  change zone p q (((colorwise g)ᵀ * Aᵀ)ᵀ) = _ at hp
  rw [transpose_mul,transpose_transpose,transpose_transpose] at hp; exact hp
lemma pullsIn {A D : Matrix (I × G.ColorIndex) (I × G.ColorIndex) ℝ} {g : I → G.El} (h : D * colorwise g=colorwise g * A) (p q : I) :
    zone p q A=(zone p p (colorwise g))ᵀ * zone p q D * zone q q (colorwise g) := by
  rw [mul_assoc,← curtain_right D g p q, h,← curtain_left, ← mul_assoc,inverse_up,one_mul]
omit [Fintype I] in
lemma poreG (g : I → G.El) (i : I) (j k : G.ColorIndex) : zone i i (colorwise g) j k=(G.adjoint (g i) (ConnectedActivityE6.dot G k)) j := by
  unfold zone; rw [submatrix_apply,colorwise,of_apply]; unfold shade; rw [rises]; simp only [sing,ConnectedActivityE6.stand,Pi.single_eq_same]
end anatomy

section station
variable (a : Museum F X.x (bareStores S) E Y I) (k : I)

def scoop := (a.colorSeat G).trans (tube X)
-- cost integration uses these
abbrev lamp6 (V : Config G c):= (vary X V).relating.submatrix (scoop X a) (scoop X a)
abbrev lamp9 (V : Config G c) := a.twilight X.k T V
abbrev porch6 (B : Directions G c):=(stoneC X B).submatrix (scoop X a) (scoop X a)
abbrev porch9 (B : Directions G c):=(optics X B).submatrix (a.colorSeat G) (a.colorSeat G)
variable [Fintype I] [DecidableEq I]
variable (hB : Room P S T X.x) (b : Folio.Bulletin X.x P T) (hy : Disjoint X.seeds.place Y) (g : Site c → G.El)
    (B : Directions G c) (he : AgreeNear id (pole X a k) (reach X.x) (gauge g V) (increment 1 B)) (l : I)
include he hy hB
lemma ray6 :
    zone l k (lamp6 X a V) = (zone l l (a.toned g))ᵀ * zone l k (porch6 X a B) * zone k k (a.toned g) := by
  let Z:= sluice (vary X V) g
  let h:= sheen X g; let q:=scoop X a
  have hh := station_charge X a k hy g B he
  have hp : zone (a.address l) (a.address k) Z.relating = zone l k (porch6 X a B) := by
    ext i j; exact hh.cL (show Room P S T Z.x from hB) (a.address k,j) rfl (a.address l,i) (show 17*Z.B≤reach X.x by change 17*radiusB X.x ≤ _; unfold Heir.reach; omega)
  have hz := pullsIn (show Z.relating*h=h*(vary X V).relating from relatesG _ g hB.accepted) (a.address l) (a.address k)
  have hv j : zone (a.address j) (a.address j) h = zone j j (a.toned g) := by
    ext r s; unfold Museum.toned; rw [tonewise]; rw [poreG (a.badge g) j]; exact poreG (g ∘ Shell.atEdge S) (a.address j) _ _
  rw [hp,hv l,hv k] at hz; exact hz

omit hy hB
include b
omit [Fintype I] [DecidableEq I] in
lemma portal (j j' : I× G.ColorIndex) (hp : j.1=k) :
    a.twilight X.k T (gauge g V) j j' = porch9 X a B j j' := by
  rw [show porch9 X a B= a.twilight X.k T (increment 1 B) from rfl]
  have hr: Museum.Station Y X.x (pole X a k) := (Corona.halo_mono (Nat.le_add_right ..) (Finset.Subset.refl _)).trans (a.stores _)
  have hk := a.reads_bare hr he X.k
  have hh : separation (pole X a k) (pole X a j.1)=0 := by rw [hp,separation_self]
  unfold Museum.twilight; rw [submatrix_apply,submatrix_apply,← b.clouds_shared,← b.clouds_shared]
  refine (cloud_local b.priced b.geometry).both hk (a.address j.1,j.2) ?_ (a.address j'.1,j'.2) |>.1
  change separation (pole X a k) (pole X a j.1)+_ ≤ _; rw [hh]; unfold Heir.reach; have hf:=b.clearance_size; unfold Folio.shiftR Folio.settleR at hf; omega

lemma ray9 : zone k l (lamp9 X a V)=(zone k k (a.toned g))ᵀ * zone k l (porch9 X a B) * zone l l (a.toned g) := by
  let L:= a.badge g
  have hr : a.toned g=colorwise L := tonewise L
  have hh := a.twilight_gauge (T:=T) (k:=X.k) g b.priced V -- edit
  rw [hr] at hh
  have hf : lamp9 X a (gauge g V)*colorwise L=colorwise L*lamp9 X a V:= by
    unfold lamp9; rw [hh, Density.skim,mul_assoc,inverse_up,mul_one]
  rw [hr,pullsIn hf k l,show zone k l (lamp9 X a (gauge g V))=zone k l (porch9 X a B) from Matrix.ext fun j j'=> portal X a k b g B he (k,j) (l,j') rfl]
end station
end YM.PhysicalNext.Repeat.Malachite

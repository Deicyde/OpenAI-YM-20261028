import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Levan
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Par

/-! # Source stencil for extension. Equality on masked ALL V uses SlotBits, not
 differentiating the mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Shield
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush   Tablet Strokes Quill Bid Matter
open Packets Art  Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {z : Air f G} {E : Type*} [MeasurableSpace E]
variable {a A α β γ d η σ W s b μ r p q C C' v : ℝ} {j n l : ℕ} {Ñ : ChartRatio G}
variable {X' : Coat T F} (X : Coat T F) {H : Support c} {I : Finset (Tubular f G)}
variable (hΞ : ShellAccess S G X.x W X.width γ) (h : Intake P T X.x R) (hP : LocalRatio Ñ)
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} (U : Cash W s μ L Q o C T R)

include hP hΞ h
lemma finbars (I : Finset (Tubular f G)) (a : ℝ) (j : Molecule S) (l : ℕ) : Measurable fun y=> bars I (vary X y) j R Ñ W a l := by
  let E' := (Config G c × F.Slice G) × Body (↥ I)
  let V (t:E'):= t.1.1; let Y (t:E'):= t.1.2
  let f' (i:E') := lens₀ (Pond.circuit I (vary X (V i)).relating) i.2* Polar.floating (drive X (V i) (Y i)) a R W Ñ (Pond.spill I i.2) (own j) l j
  have hv : Measurable V := measurable_fst.comp measurable_fst
  have hh := c_measured X.shutter (A:=fun i=> (vary X (V i)).plate) (fun i j=> (Art.borel_plate X h.ready i j).comp hv)
  have hz : Measurable f' := (bulbB (fun i j=> hh.1 i.val j.val : Borel fun i=> Pond.circuit I (vary X (V i)).relating) measurable_snd).mul
    (Shield.collectionB X hΞ h hP hv (measurable_snd.comp measurable_fst) ((Pond.spill_m I).comp measurable_snd) ..)
  exact ((hz.stronglyMeasurable.integral_prod_right' (ν:=volume)).integral_prod_right' (ν:=F.order G)).measurable
lemma shelterB (a : ℝ) (j : Molecule S) (l : ℕ) : Measurable fun y=> shelter (vary X y) W a j R Ñ l := by
  classical
  change Measurable fun y=> if Ac.Spark (areas R T _ X.B) j ∧ troupe T R _ X.B j then _ else 0
  change Measurable fun y=> if Ac.Spark (areas R T l X.B) j ∧ troupe T R l X.B j then seating (ground R T l X.B j) _ (vary X y) _ _ _ _ _ _ else 0
  split_ifs
  · refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> ?_)
    let Z:= (preps X (roster j)).taggedL i
    exact finbars Z hΞ (show Intake P T Z.x R from h) hP (podium S G (ground R T l X.B j) X.B) a j l
  exact measurable_const
omit hP hΞ
lemma synchron (p : Molecule S) (hp : ground R T l X.B p ⊆ H) (hr : Room P S T X.x) (hV : Village X X' H)
    (hl : 500 ≤ l) (Ñ : ChartRatio G) (a W : ℝ) : bars (podium S G H X.B) X p R Ñ W a l=bars (podium S G H X.B) X' p R Ñ W a l := by
  let I:=podium S G H X.B
  have he : Pond.circuit I X.relating=Pond.circuit I X'.relating := by ext i j; exact hV.same_cov hr j.val j.property i.val
  unfold bars; rw [he]; apply integral_congr_ae; filter_upwards with q; apply integral_congr_ae; filter_upwards with y
  apply congr_arg₂ (·*·) rfl; let v:=Pond.spill I y
  refine Borough.flops (show Borough (X.wrapY q) (X'.wrapY q) H v v (own p) (own p) R from
    ⟨hV.wrap q q (fun _ _=> rfl),fun _ _=> rfl,fun _ _=>Iff.rfl⟩) hr hl (show Intake P T _ R from h) _ _ _ hp
lemma shelters (a W : ℝ) (i : Molecule S) (Ñ : ChartRatio G) (hX : Room P S T X.x) (hl : 500≤l) : LocalOn (ground R T l X.B i)
    (fun y:Config G c=> shelter (vary X y) W a i R Ñ l) := by
  intro V U he
  let s := ground R T l X.B i
  change (if Ac.Spark (areas R T l X.B) i ∧ troupe T R l X.B i then seating s X.B (vary X V) W a l i R Ñ else 0)=_
  change _=(if Ac.Spark (areas R T l X.B) i ∧ troupe T R l X.B i then seating s X.B (vary X U) W a l i R Ñ else 0); split
  next hp=> apply congr_arg likely; funext k; apply synchron (X:=(preps (vary X V) (roster i)).taggedL k) (show Intake P T _ R from h) _ (show ground R T l X.B i⊆s from Subset.refl _) hX _ hl
            exact ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,fun _ _=> rfl,fun _ _=>rfl,he⟩
  next => rfl
omit h

-- For all V (not just all-period Utem)
include U
lemma agreement (hX:X.x=s) (hv:X.width=o.K) (p : Molecule S) (ha : (roster p).flags=∅) :
    let Z:= U.unionP p
    U.emerging X p=masked (Pressure.temp X.x) Z (fun V=> shelter (vary X V) W o.a p R Q.table Q.halo) X.V := by
  intro Z; have ht : ground R T Q.halo X.B p=Z := by unfold Coat.B; rw [hX]; rfl
  by_cases hh : Healthy (Pressure.temp X.x) Z X.V
  swap; · rw [masked_ne _ _ _ _ hh,Cash.emerging,Matter.proceedsA,if_neg]
          intro hp; exact hh (Finset.disjoint_iff_inter_eq_empty.mpr (by rw [inter_comm, ← ht,hp.2.2,ha]))
  rw [masked_eq _ _ _ _ hh, show vary X X.V=X from rfl,Cash.emerging,Matter.proceedsA,shelter]
  split
  next hz =>
    rw [if_pos ⟨hz.1,hz.2.1⟩]; apply congr_arg likely; funext i
    let Y := (planted X p).taggedL i; let Y':= (preps X (roster p)).taggedL i
    change Y.attains R Q.table W o.a _ _ p = bars (podium S G (ground R T Q.halo X.B p) X.B) Y' p R Q.table W o.a Q.halo
    have hhV:= U.laws.data; rw [← selfish Y U hX hv (planted_valid X p) p _ hh (Subset.refl _)]
    have hG : Village Y Y' (U.unionP p) := by
      refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl⟩
      intro y hy; have hp : y ∉ RG.flags (Pressure.temp X.x) X.V := Finset.disjoint_left.mp hh hy
      unfold Y Y' taggedL planted preps place; simp [ha,hp]
    rw [ht]; exact Shield.synchron Y (h:=show Intake P T Y.x R from hX.symm ▸ U.laws.intake) p (show ground R T Q.halo Y.B p ⊆ U.unionP p from ht.le)
      (show Room P S T Y.x from hX.symm ▸ U.laws.data.room) hG Q.buys _ o.a W
  next hy =>
    rw [if_neg]; intro hZ
    apply hy; exact ⟨hZ.1,hZ.2,by rw [ht,inter_comm]; exact (Finset.disjoint_iff_inter_eq_empty.mp hh).trans ha.symm⟩
end YM.ConnectedActivityE6.Blaze.Shield

import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Islet
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Plot
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Poles


/-! # Core view on a scrim. Projects all arguments of inherited E in unmasked extension

Color and gauge transfers. Will integrate out only the permitted indices.
 *Both* endpoints convention in callbacks. Off-domain branch values allowed.
Ambiguous if h iteration only at top? We take any including many exterior flags.
 Don't vary Stamp or Plot knobs. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Baffle
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} {E : Support f} {V : Config G c}
variable {w d t b W v : ℝ}
section Scrimmage
variable (a : Museum F X.x (bareStores S) E Y I) {hp : P.Funds S T}

structure Scrim : Prop where
  outer : Disjoint X.seeds.place Y
  key i : i∈ X.plaza (baseRead E X.x S) ↔ i∈ Set.range a.address
include a
lemma Scrim.varies (h : Scrim X a) (V : Config G c): Scrim (vary X V) a:= ⟨h.outer,h.key⟩
omit a in
lemma scrim_at {l : ℕ} (h : 0 < radiusB X.x) (hv : 500 ≤ l) (he : Disjoint X.seeds.place (yFoot S E X.x l)) :
    Scrim X (seatsAt E X.x l h hv F (bareStores S) (nearby_zero ..)) :=
  ⟨he,fun i=> access E X.x l h hv F X.seeds he T X rfl rfl i⟩

variable (hs : Scrim X a)
include hs
lemma borne (i : I) : X.Hot (a.address i) := (Finset.mem_filter.mp ((hs.key _).mpr ⟨i,rfl⟩)).2.1
omit hs in
lemma falls (e : F.Free) (hi : e.val.1∈inspected E) (ht : e.val.1+step e.val.2∈inspected E) : e.val∈Set.range a.address := by
  apply a.address_range (i:=⟨e, a.admits hi ht⟩) hi ht

-- all argument X,Y, not assuming rotation smoothness
lemma rootVolt (h : Room P S T X.x) (i:I) (Y' : F.Slice G) : voltage (X.wrapY Y') (a.address i) = voltage X (a.address i) := by
  let r:= Heir.reach X.x; let x:= Malachite.pole X a i
  let M y:= X.wrapY y
  let K y:= vary (M y).blank X.V
  have hh (y:F.Slice G) : Zone (M y) (K y) x r := by
    refine ⟨rfl,rfl,rfl,fun u hu=> ⟨fun h=> ?_,fun h=>?_⟩,fun _ _=> rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
    · exact (Finset.disjoint_left.mp hs.outer h (a.stores i (halo_spec.mpr ⟨_,Finset.mem_singleton_self _,hu.trans (Nat.le_add_right ..)⟩))).elim
    exact (X.blank_no _ 0 (halo_subset _ X.blank.seeds.place h)).elim
  have he y := local_voltage (show Room P S T (M y).x from h) (hh y) (a.address i) rfl (show 17*(M y).B≤r by change 17*radiusB X.x ≤ _; unfold r Heir.reach; omega)
  change voltage (M Y') _ = voltage (M X.Y) _; rw [he,he]
  suffices hp : bar (K Y') 0=bar (K X.Y) 0 by unfold voltage well leanB; rw [hp]; rfl
  have hv (y:F.Slice G) : (K y).signal 0=0 := by
    unfold Coat.signal; rw [lens_zero,add_zero]; funext j; exact if_pos (or_iff_not_imp_left.mpr fun he=> (X.no_flat j).2 he)
  funext j; unfold bar strain; rw [hv,hv]; rfl

variable [Fintype I]
lemma plaza_cal : X.plaza (baseRead E X.x S) = Finset.univ.map (⟨a.address,a.address_inj⟩ : I↪Bond f) := by
  ext z; rw [hs.key]; symm; simp [Set.mem_range]

omit hs
-- casting
variable (V)
def isotope (x : I→G.Color) := Function.extend a.address x 0
omit [Fintype I] in
lemma tap (i:I) (x : I→G.Color) : isotope X a x (a.address i)=x i := a.address_inj.extend_apply x 0 i
lemma measure_tap : Measurable (isotope X a) := by
  apply measurable_pi_lambda; intro i; unfold isotope
  by_cases hi : i∈Set.range a.address
  · obtain ⟨j,rfl⟩:= hi; simp_rw [a.address_inj.extend_apply]; exact measurable_pi_apply j
  simp_rw [Function.extend_apply' _ _ _ hi]; exact measurable_const

abbrev strip6 (V : Config G c) (u : I→ G.Color): Config G f:=(vary X V).input (isotope X a u)
-- on Y' changed, use same visited exposures
variable {V}
include hs
set_option linter.unusedSectionVars false in
lemma entered (Y' : F.Slice G) (U : Directions G f) {u : I→ G.Color} (hp : ∀ i, U (a.address i)=u i) :
    Agrees (inspected E) (((vary X V).wrapY Y').input U) (strip6 X a V u) := by
  intro i he hi; let Z := vary X V; unfold strip6
  by_cases hf : i∈F.trunks
  · exact (F.on_tree _ ⟨i,hf⟩).trans (F.on_tree _ ⟨i,hf⟩).symm
  obtain ⟨z,rfl⟩:= falls X a ⟨i,hf⟩ he hi
  rw [Coat.viewing _ _ _ (show (Z.wrapY Y').Hot _ from borne X a hs z), Coat.viewing _ _ _ (show Z.Hot _ from borne X a hs z)]
  unfold increment; rw [hp,tap]; rfl

abbrev peanuts (V : Config G c) (β : ℝ) (w : Prices G I) (j:I) := volume6 X a j V + gStep β • tape w j
lemma shuttle (hP : Room P S T X.x) (Y' : F.Slice G) (β : ℝ) (z : Air f G) (i : I) (V : Config G c) :
    worldZ ((vary X V).wrapY Y') β z (a.address i)=peanuts X a V β (WithLp.ofLp z ∘ scoop X a) i := by
  unfold worldZ peanuts
  rw [Pi.add_apply,show voltage ((vary X V).wrapY Y') (a.address i)=volume6 X a i V from rootVolt (vary X V) a (hs.varies X a V) hP i Y']; rfl
end Scrimmage
end YM.PhysicalNext.Repeat.Baffle

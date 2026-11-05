import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Sofa



/-!
 # Assembling path-oriented outputs: proceed LOCAL at each Molecule
 Hops/F blend. no equivariance of regular Sup budget asserted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw Matter
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open Turn Greenbelt
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}{s:Signed}{b:Site c}{t:Site f}
  {R:Rep G f} {F:Forest S.ratio} {P:Teller G} {T:Tube G S} {X:Coat T F} {Y:Coat T (Locations.forest s b F)}
variable (p:R.activities.Moves s t)
namespace Wing
def labelRoute : Wing→ Wing
 | logKey i=> logKey (p.ep i)
 | gasKey i=> gasKey (p.kp i)
variable (i:Wing)
lemma supRoute : (labelRoute p i).support R=(i.support R).image (affine s t):= by cases i; exact p.reg_support _; exact p.forced_support _
lemma okRoute (V:Config G f) : (labelRoute p i).qualifies R V ↔ i.qualifies R (pull s t V):=by
   cases i
   · exact (vigor _ _ _ _ (p.reg_support _)).symm -- args
   exact Work.H03.eligible_send s t R.p.threshold V _ _ (p.forced_support _) (p.forced_inventory _) (p.forced_tests _ V)
lemma fuelRoute (h:i.blank R): (labelRoute p i).blank R:=by
   cases i with
   | gasKey i=> trivial
   | logKey i=> exact funext fun v=> (p.valuesE i v).trans (congr_fun h _)
end Wing
namespace Leaf
variable (M:Leaf R)
def route : Leaf R where
   turn:= M.turn.labelRoute p
   ingredient:= M.ingredient ∘ pull s t
   scopedR:= M.turn.supRoute p|>.symm ▸ Push.Local.uses_pull M.scopedR _ _
   grant V h:= (M.turn.okRoute p V).2 (M.grant _ h)
   blank:= M.turn.fuelRoute p M.blank
   weight:= M.weight
   earn _:= M.earn _
   glows:= Push.Local.invariant_pull M.glows s t
   borel:= M.borel.comp (continuous_pull ..).measurable
variable (e:R.activities.Moves s (S.ratio.embed b))
lemma cardRoute : (route e M).turn.badge S=Turn.badge R e (M.turn.badge S):=by
   change (Wing.labelRoute e M.turn).badge S= _; cases M.turn <;> rfl
variable {μ α W C:ℝ}{L:Side}{Q: YM.ConnectedActivityE6.Target G P}{o:ConnectedActivityE6.Target.Order G W} (H : Cash W α μ L Q o C T R)
include H
lemma preRoute (h:Tuned s b X Y) (z: Air f G) (hα:X.x=α)(hk:X.width=o.K)(hx:X.manifest)(hy:Y.manifest)(i:Molecule S)(l:Finset ℕ):
   M.premium Y W o.a Q.table l Q.halo (exhale s b X.V S z) i=(route e M).premium X W o.a Q.table (e.kp.finsetCongr l) Q.halo z (caravan R e i):=by
  let u := X.liftA R.beta z
  have hf := H.laws.intake.ready
  unfold premium; have ha:=h.axle hf (show ShellAccess S G X.x W X.width o.γ from (by rw [hα,hk];exact H.laws.data.access))
  rw [ha,cardRoute]; let V:=Turn.badge R e; have hV:∀j,j∈i↔V j∈ caravan R e i:=fun _=> by simp [V,caravan]
  by_cases hv: M.turn.badge S∈i
  swap; · rw [if_neg hv,if_neg (fun hx=> hv ((hV _).2 hx))]
  rw [if_pos hv,if_pos ((hV _).1 hv)]
  · apply congr_arg₂ (·*·)
    · unfold paidU fond; rw [h.completed,h.toParked.aligned.2.1,cardRoute]
      exact congr_arg (M.ingredient (pull _ _ (X.input u)) * ·) (h.imposes _ (h.plazas ((display (StepData.sendSites s b) _ _).1 (insignia T R e 0 X.B _))) u)
    apply values (Turn.badge R e)
    · intro j; rw [mem_erase,mem_erase]; exact and_congr (not_congr V.injective.eq_iff|>.symm) (hV _)
    intro j _; exact commend R e H h z hα hk hx hy j l

lemma toured (h : Parked s b X Y) (hχ : Y.χ=X.χ) (hK : Y.width=X.width) (he : Y.k=Channels.ticket s b X.k)
    (hα : X.x=α) (hw : X.width=o.K) (hx : X.manifest) (hy : Y.manifest) (i : Molecule S) (l : Finset ℕ) :
    M.tithe Y l W o.a Q.table Q.halo i=(route e M).tithe X (e.kp.finsetCongr l) W o.a Q.table Q.halo (caravan R e i) := by
  let g := M.into Y W o.a Q.table l Q.halo i
  have hp : MeasurePreserving (fun u : F.Slice G× Air f G => (glide s b F u.1, exhale s b X.V S u.2)) ((F.order G).prod X.dice)
      (((Locations.forest s b F).order G).prod Y.dice) := (forest_toll s b F G).prod (h.preserving H.laws.intake.ready (H.laws.data.localP F X hα hw hx).sails.fullC)
  have hm : Measurable g := (M.tip Y l (show Cash W Y.x μ L Q o C T R from (h.x.trans hα).symm ▸ H) (hK.trans hw) hy i).1.meas
  unfold tithe; rw [← Pond.reception hp g hm]; apply integral_congr_ae; filter_upwards with p
  obtain ⟨u,z⟩:=p; let X' := X.wrapY u; let Y':=Y.wrapY (glide s b F u)
  exact M.preRoute e H (X:= X') (Y:=Y') ⟨⟨h.seeds,h.x,h.v⟩,hχ,hK,he,rfl⟩ z hα hw hx hy i l

lemma blooming (hv : Y.V=pull s b X.V) (hx : Y.x=X.x) (hχ : Y.χ=X.χ) (hK : Y.width=X.width)
    (hα : X.x=α) (hw : X.width=o.K) (Z : Molecule S) : M.bloom Y W o.a Q.table Q.halo Z=(route e M).bloom X W o.a Q.table Q.halo (caravan R e Z) := by
  unfold bloom; rw [accounting hv hx R e]; split
  · let Z' := caravan R e Z; let A:=planted Y Z; let D:=planted X Z'
    have h : Parked s b D A := by
      refine ⟨?_,hx,hv⟩; unfold A D planted preps; dsimp only
      rw [mark R e Z,hx,hv]; apply congrArg (Stores.mk _ _); ext i; exact (Turn.toured s b ..).trans (atF s b D.seeds i).symm
    have hl: own Z'=e.kp.finsetCongr (own Z) := (given _ _ _).mpr (chart R e Z)
    rw [hl]; unfold steep Pond.likely; apply congr_arg; rw [← Equiv.sum_comp (S.withinChoice s b).symm]; exact sum_congr rfl fun v _ =>
      toured M e H (X:=D.taggedL v) (Y:=A.taggedL ((S.withinChoice s b).symm v)) ⟨h.seeds,h.x,h.v⟩ hχ hK rfl hα hw (planted_valid ..) (planted_valid ..) _ _
  rfl
lemma sails (χ:Chi) (V: Config G c)(p:Molecule S): M.lotus T α χ o.K W o.a Q.table Q.halo (pull s b V) p=(route e M).lotus T α χ o.K W o.a Q.table Q.halo V (caravan R e p):=by
  apply likely_congr (orbitKey s b S); intro i; rw [f_orbit]; exact blooming M e H (X:=prism T α χ o.K V (allot i)) (Y:=prism T α χ o.K (pull s b V) _) rfl rfl rfl rfl rfl rfl _
end Leaf
end YM.PhysicalNext.Repeat.Lotus

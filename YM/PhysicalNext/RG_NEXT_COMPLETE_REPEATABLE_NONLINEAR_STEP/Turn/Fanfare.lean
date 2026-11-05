import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Band

/-!
# Whole attraction symmetry; actual Coarse V and common dice

Including determinant trace residuals and actual tag well measure. Rotation
changes F. To use this for E/K Moves on an output need to deal with F
BEFORE log or prove another symmetry of the gas. Does not put federal
topology/smoothness assumptions on the Borel Masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Turn
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw Matter
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {s : Signed} {b : Site c}
    {F : Forest S.ratio} {P : Teller G} {T : Tube G S} {X : Coat T F} {Y : Coat T (Locations.forest s b F)}
    {W α μ C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {L : Side}
    (R : Rep G f) (π : R.activities.Moves s (S.ratio.embed b)) (H : Cash W α μ L Q o C T R)
include H
lemma commend (h : Tuned s b X Y) (z : Air f G) (hα : X.x=α) (hK : X.width=o.K) (hx : X.manifest) (hy : Y.manifest) (i : Head S) (l : Finset ℕ) :
    Y.vertex R Q.table W o.a l Q.halo (exhale s b X.V S z) i=X.vertex R Q.table W o.a (π.kp.finsetCongr l) Q.halo z (badge R π i) := by
  have hz:=H.laws.data
  have hp := H.laws.intake.ready
  have hr:=hz.localP _ X hα hK hx
  have ha:=hz.localP _ Y (h.x.trans hα) (h.width.trans hK) hy
  have hv : ShellAccess S G X.x W X.width o.γ := by rw [hα,hK]; exact hz.access
  have hg : 0<o.a*X.t := mul_pos o.large hr.sails.room.fiery
  have ht : 4*o.a*X.t<Q.table.radius := by unfold Coat.t; rw [hα,hz.funds.length_eq]; exact hz.covers
  unfold vertex; rw [h.axle hp hv]; rcases i with A|k|p|i
  · obtain ⟨A,rfl⟩ := (books s b S).surjective A
    change (if Packets.connected S _ _ _ then _ else _)=(if Packets.connected S _ X.B ((books s b S).symm ((books s b S) A)) then X.Pack R Q.table _ W o.a ((books s b S).symm ((books s b S) A)) _ else 0)
    rw [Equiv.symm_apply_apply,h.toParked.aligned.2.1]; exact if_congr (attached ..) (h.fired hr ha hp hv _ _ Q.table_exists o.a R hg ht l π) rfl
  · exact h.earned_bag ..
  · exact congr_arg (fun x=>Real.exp x-1) (h.carried hr ha hp hv p π Q.table_exists o.a hg ht z)
  exact h.heard_winds hp π (X.liftA _ z) o.a i l W

lemma tours (h : Parked s b X Y) (hχ : Y.χ=X.χ) (hK : Y.width=X.width) (he : Y.k=Channels.ticket s b X.k)
    (hα : X.x=α) (hw : X.width=o.K) (hx : X.manifest) (hy : Y.manifest) (i : Molecule S) (l : Finset ℕ) :
    Y.attains R Q.table W o.a l Q.halo i=X.attains R Q.table W o.a (π.kp.finsetCongr l) Q.halo (caravan R π i) := by
  let g := Y.body R Q.table W o.a l Q.halo i
  have hp : MeasurePreserving (fun u : F.Slice G× Air f G => (glide s b F u.1, exhale s b X.V S u.2)) ((F.order G).prod X.dice)
      (((Locations.forest s b F).order G).prod Y.dice) := (forest_toll s b F G).prod (h.preserving H.laws.intake.ready (H.laws.data.localP F X hα hw hx).sails.fullC)
  have hm : Measurable g := Y.body_b Q.table_exists ((h.x.trans hα).symm ▸ H.laws.intake) (show ShellAccess S G Y.x W Y.width o.γ from (by rw [h.x,hα,hK,hw]; exact H.laws.data.access)) ..
  unfold attains; rw [← Pond.reception hp g hm]; apply integral_congr_ae; filter_upwards with p
  obtain ⟨u,z⟩:=p; let X' := X.wrapY u; let Y':=Y.wrapY (glide s b F u)
  exact values (badge R π) i _ ((given _ _ _).1 rfl) _ _ (fun j _=> commend R π H (X:= X') (Y:=Y') ⟨⟨h.seeds,h.x,h.v⟩,hχ,hK,he,rfl⟩ z hα hw hx hy j l)

lemma ascent (h : Parked s b X Y) (hχ : Y.χ=X.χ) (hK : Y.width=X.width)
    (hα : X.x=α) (hw : X.width=o.K) (hx : X.manifest) (hy : Y.manifest) (i : Molecule S) (l : Finset ℕ) :
    Y.levelMean R Q.table W o.a l Q.halo i=X.levelMean R Q.table W o.a (π.kp.finsetCongr l) Q.halo (caravan R π i) := by
  unfold levelMean Pond.likely; apply congr_arg; rw [← Equiv.sum_comp (S.withinChoice s b).symm]; exact sum_congr rfl fun v _=> tours R π H (X:= X.taggedL v) (Y:=Y.taggedL ((S.withinChoice s b).symm v)) ⟨h.seeds,h.x,h.v⟩ hχ hK rfl hα hw hx hy i l

lemma trumpets (hv : Y.V=pull s b X.V) (hx : Y.x=X.x) (hχ : Y.χ=X.χ) (hK : Y.width=X.width)
    (hα : X.x=α) (hw : X.width=o.K) (Z : Molecule S) : proceedsA R Y W o.a Q.halo Q.table Z=
      proceedsA R X W o.a Q.halo Q.table (caravan R π Z) := by
  unfold proceedsA; rw [accounting hv hx R π]; split
  · let Z' := caravan R π Z; let A:=planted Y Z; let D:=planted X Z'
    have h : Parked s b D A := by
      refine ⟨?_,hx,hv⟩; unfold A D planted preps; dsimp only
      rw [mark R π Z,hx,hv]; apply congrArg (Stores.mk _ _); ext i; exact (toured s b ..).trans (atF s b D.seeds i).symm
    have hl: own Z'=π.kp.finsetCongr (own Z) := (given _ _ _).mpr (chart R π Z)
    unfold amountP; rw [hl]; exact ascent R π H h hχ hK hα hw (planted_valid ..) (planted_valid ..) _ _
  rfl
end YM.PhysicalNext.Repeat.Turn

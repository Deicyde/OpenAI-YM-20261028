import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Street
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Swirl

/-!
# integrated weights gauge covariance

Includes stage F.KY. Fixed F. Keep translational obligations separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees Multiple Letter OmitClusters Rotation Hues
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {L : Side}
variable {k k' : Finset ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W α μ L Q o C T R) (X : Coat T F) (hk : X.x=α) (he : X.width=o.K)
include H hk he

lemma stemming (z : Site c→ G.El) (hp : X.manifest) (l : Finset ℕ) (i : Molecule S) :
    (X.rinse z).attains R Q.table W o.a l Q.halo i= X.attains R Q.table W o.a l Q.halo i := by
  let Y := sluice X z
  have hx : Y.x=α := hk
  let g (Z : Coat T F) := Z.body R Q.table W o.a l Q.halo i
  have ht:= H.laws.data
  have hv : Measurable (g Y) := Y.body_b Q.table_exists (hx.symm ▸ H.laws.intake) (show ShellAccess S G Y.x W Y.width o.γ from
    (by change ShellAccess _ _ X.x W X.width _; rw [he,hk]; exact ht.access)) ..
  have hA : MeasurePreserving (fun v:F.Slice G × Air f G=> (pairs X z v.1, weep X z v.2)) ((F.order G).prod X.dice)
      ((F.order G).prod Y.dice) := (drinking X z).prod (speeds X z H.laws.intake.ready
      (ht.localP F X hk he hp).sails.fullC (ht.localP F Y hk he (wind X z hp)).sails.fullC)
  change (∫ v,g Y v ∂ ((F.order G).prod Y.dice))=_
  rw [← Pond.reception hA _ hv]; apply integral_congr_ae; filter_upwards with p
  obtain ⟨p,u⟩:=p
  exact Finset.prod_congr rfl fun j _=> H.scours (X.wrapY p) hk he hp l z u j

lemma radiant (s : Molecule S) (v : Site c→G.El) : H.emerging (X.rinse v) s= H.emerging X s := by
  unfold emerging proceedsA; let U:= planted X s
  rw [show standsIn (X.rinse v) R Q.halo s↔ standsIn X R Q.halo s by unfold standsIn claimed rinse; simp only [Coat.B,gauge_flags]]
  split
  next ht =>
    have hv : (planted (X.rinse v) s)= U.rinse v := by unfold planted preps U rinse; simp only [gauge_flags]; rfl
    unfold amountP; rw [hv]; exact congr_arg likely (funext fun i=> H.stemming (U.taggedL i) hk he v (planted_valid X s) _ s)
  next => rfl

lemma gauge_weight (s : Molecule S) : GaugeInvariant (fun V=> H.emerging (vary X V) s) := fun t V=>
    H.radiant (vary X V) hk he s t

end YM.ConnectedActivityE6.Cash

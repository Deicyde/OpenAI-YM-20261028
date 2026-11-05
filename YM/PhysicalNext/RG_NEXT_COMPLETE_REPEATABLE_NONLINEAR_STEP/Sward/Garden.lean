import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Manifesto
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Verge


/-! # Crop integral locality across tree masks

Keep actual same parent-block choices where supports require. Do not
cut off estimate at `trunks` card. Compare ejections of the SAME gas
via separate actual Gaussians; require principal subwindow agreement, not
matching normalization globally. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Horticulture
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}

lemma sway_one {p : Bond f} (hp : atEdge S p ∈ Z) (he : ∀ i : Site f,S.ratio.parent i∈Z→ F.up i=F'.up i) : p∈F.trunks→p∈F'.trunks := by
  intro h; rw [F.trunk_mem_iff] at h; obtain ⟨j,hj,hj'⟩:=h; rw [F'.trunk_mem_iff]; refine ⟨j,hj,?_⟩
  suffices h : S.ratio.parent j=atEdge S p from by rw [← he j (h.symm ▸ hp),hj']
  subst p
  have hh:= F.stays j hj; cases hi : (F.up j).neg
  · simp [Step.used,hi,atEdge]
  simp only [Step.used,hi,if_true]; simpa only [atEdge,Step.vec,hi,if_true,← sub_eq_add_neg] using hh.symm

lemma sway (he : ∀ i : Site f,S.ratio.parent i∈Z→ F.up i=F'.up i) : ∀ p : Bond f, atEdge S p∈Z → (p∈F.trunks ↔ p∈F'.trunks) := fun p hp => ⟨sway_one (p:=p) hp he,sway_one (p:=p) hp fun i hi=> (he i hi).symm⟩

def bridge (F : Forest S.ratio) (V : Config G f) : F.Slice G := fun i=> V i.val
lemma reserve (G : Gauge) (F : Forest S.ratio) : MeasurePreserving (bridge (S:=S) F) (prior G f) (F.order G) := by
  exact measurePreserving_snd.comp (show MeasurePreserving F.seam (prior G f) ((Measure.pi (fun _ : ↥F.trunks=> G.probHaar)).prod (F.order G)) from
    (by unfold prior Forest.order; convert! measurePreserving_piEquivPiSubtypeProd (fun _ : Edge (Site f)=> G.probHaar) (fun i=> i∈F.trunks)))

lemma foreclose (he : ∀ i : Site f,S.ratio.parent i∈Z→ F.up i=F'.up i) (U : Config G f) (p : Bond f) (hp : atEdge S p∈Z) :
    (p∈F.trunks ↔ p∈F'.trunks) ∧ F.drape (bridge (S:=S) F U) p=F'.drape (bridge (S:=S) F' U) p := by
  refine ⟨sway he p hp,?_⟩; by_cases hi : p∈ F.trunks
  · exact (F.on_tree _ ⟨p,hi⟩).trans (F'.on_tree _ ⟨p,(sway he p hp).1 hi⟩).symm
  exact (F.off_tree _ ⟨p,hi⟩).trans (F'.off_tree (bridge (S:=S) F' U) ⟨p,(sway he p hp).not.mp hi⟩).symm

namespace Travels
variable (X : Coat T F) (Y : Coat T F') (s : Molecule S)
    (hx : X.x=α) (hy : Y.x=α) (hK : X.width=o.K) (hK' : Y.width=o.K) (hv : X.V=Y.V) (hc : X.χ=Y.χ)
    (H : Cash W α μ L Q o C T R)
    (hw : ∀ i : Site f,S.ratio.parent i∈ground R T Q.halo (radiusB α) s→ F.up i=F'.up i)
include hx hy hK hK' hv hc H hw
lemma paths (ho : X.seeds=Y.seeds) (hk : X.k=Y.k) (hm : X.manifest) (hm' : Y.manifest) (l : Finset ℕ) :
    X.attains R Q.table W o.a l Q.halo s=Y.attains R Q.table W o.a l Q.halo s := by
  have hM {F' : Forest S.ratio} (X : Coat T F') (hx : X.x=α) (ht : X.width=o.K) : Measurable (X.body R Q.table W o.a l Q.halo s) := X.body_b Q.table_exists (hx.symm ▸ H.laws.intake) (by rw [hx,ht]; exact H.laws.data.access) ..
  unfold attains; rw [integral_prod _ (H.integrated X hx hK hm l s),integral_prod _ (H.integrated Y hy hK' hm' l s)]
  rw [← Pond.reception (reserve (S:=S) G F) _ ((hM X hx hK).stronglyMeasurable.integral_prod_right' (ν:=X.dice)).measurable,
    ← Pond.reception (reserve (S:=S) G F') _ ((hM Y hy hK').stronglyMeasurable.integral_prod_right' (ν:=Y.dice)).measurable]
  apply integral_congr_ae; filter_upwards with u
  let I:= podium S G (H.unionP s) X.B; let X':= X.wrapY (bridge (S:=S) F u); let Y':=Y.wrapY (bridge (S:=S) F' u)
  have he: Crop X' Y' (H.unionP s) := ⟨hx.trans hy.symm,hK.trans hK'.symm,hc,fun _ _=> ho ▸ Iff.rfl, foreclose hw u,
    fun i _=> (congr_fun (congr_arg Prod.fst hk) i), fun i _=> (congr_fun (congr_arg Prod.snd hk) i), fun i _ _=> congr_fun hv i⟩
  have hp : Room P S T X'.x := hx.symm ▸ H.laws.data.room
  have ht := Pond.orbit (H.laws.data.localP F X hx hK hm).sails.fullC.posSemidef I
  have ht' := Pond.orbit (H.laws.data.localP F' Y hy hK' hm').sails.fullC.posSemidef I
  let g (w:Air f G):=X'.term R Q.table W o.a l Q.halo w s
  let y (w:Air f G):=Y'.term R Q.table W o.a l Q.halo w s
  have hJ (p q) (h : swim I p=swim I q) : g p=y q := by
    have hh : Clump X' Y' (H.unionP s) p q l l R := ⟨he,(observe I).1 h,fun _ _=> Iff.rfl⟩
    refine prod_congr rfl fun i hi=> hh.complete hp Q.buys i ?_ (hx.symm ▸ H.laws.intake) o.a W Q.table
    change Mixed.foot S _ (radiusB X.x) (footprints _ R _ (radiusB X.x)) i⊆_
    rw [hx]; exact subset_biUnion_of_mem (H.supportP) hi
  change (∫ w,g w ∂X.dice)=∫ w,y w ∂Y.dice
  have hg : Measurable g := by
    change Measurable (fun z=> X.body R Q.table W o.a l Q.halo s (bridge (S:=S) F u,z))
    exact (hM X hx hK).comp (measurable_const.prodMk measurable_id)
  have hm : Measurable y := by
    change Measurable (fun z=>Y.body R Q.table W o.a l Q.halo s (bridge (S:=S) F' u,z))
    exact (hM Y hy hK').comp (measurable_const.prodMk measurable_id)
  have hC : circuit I X.relating=circuit I Y.relating := by
    ext i j
    exact he.same_cov hp (j:Tubular f G) j.property (i:Tubular f G)
  have hY : MeasurePreserving (swim I) Y.dice (arch I X.relating) := by unfold arch; rw [hC]; exact ht'
  calc
    _ = ∫ i,g (spill I i) ∂arch I X.relating := gathered _ (spill_m I) (show MeasurePreserving (swim I) X.dice (arch I X.relating) from ht) (settled I)
          (fun p q h=> (hJ p q h).trans (hJ q q rfl).symm) hg
    _ = ∫ i,y (spill I i) ∂arch I X.relating := integral_congr_ae (ae_of_all _ fun i=> hJ _ _ (show swim I (spill I i)=_ from rfl))
    _ = _ := (Pond.gathered (spill I) (spill_m I) hY (settled I) (f:=y)
          (fun p q h=> (hJ p p rfl).symm.trans (hJ p q h)) hm).symm

lemma tagLikely (k : Finset ℕ) (h : X.seeds=Y.seeds) (hm : X.manifest) (hm' : Y.manifest) : X.levelMean R Q.table W o.a k Q.halo s=Y.levelMean R Q.table W o.a k Q.halo s := by
  unfold levelMean; apply congr_arg likely; funext k'
  have hh:= paths (X.taggedL k') (Y.taggedL k') s
    (show (X.taggedL k').x=α from hx) (show (Y.taggedL k').x=α from hy) (show (X.taggedL k').width=o.K from hK) (show (Y.taggedL k').width=o.K from hK') (show (X.taggedL k').V=(Y.taggedL k').V from hv) (show (X.taggedL k').χ=(Y.taggedL k').χ from hc)
    H hw (show (X.taggedL k').seeds=(Y.taggedL k').seeds from h) (show (X.taggedL k').k=(Y.taggedL k').k from rfl) (show (X.taggedL k').manifest from hm) (show (Y.taggedL k').manifest from hm') k
  exact hh
lemma junction : amountP R X W o.a Q.halo Q.table s=amountP R Y W o.a Q.halo Q.table s := by
  unfold amountP
  have he : X.x=Y.x := hx.trans hy.symm
  refine tagLikely (planted X s) (planted Y s) s hx hy hK hK' hv hc H hw (own s) ?_ (planted_valid X s) (planted_valid Y s)
  unfold planted preps; dsimp only; rw [he,hv]
lemma sails : proceedsA R X W o.a Q.halo Q.table s=proceedsA R Y W o.a Q.halo Q.table s := by
  unfold proceedsA; refine if_congr ?_ (junction X Y s hx hy hK hK' hv hc H hw) rfl
  have he : X.x=Y.x := hx.trans hy.symm
  unfold standsIn claimed Coat.B; simp_rw [he,hv]
end Travels
end YM.ConnectedActivityE6.Horticulture

import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.SalesRoot
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Threads
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Verge

/-!
# values on one support/marginal
Proven unchanged taking Loans from another VALID Stamp in same budget.
V unnormalized. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {Z Z' : Support c}
variable {k k' : Finset ℕ} {w v : Air f G} {L : Side}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}

lemma Village.wrap {X X' : Coat T F} (h : Village X X' Z) (Y Y' : F.Slice G)
    (hd : ∀ i : F.Free, atEdge S i.1 ∈ Z → Y i=Y' i) : Village (X.wrapY Y) (X'.wrapY Y') Z :=
    ⟨h.weather,h.width,h.chi,h.places,hd,h.site,h.bond,h.actual⟩
lemma Village.refl (X : Coat T F) (Z : Support c) : Village X X Z :=
    ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl⟩

/- For valid actual Global choices. -/
namespace Coat
variable (X : Coat T F)

def attains (R : Rep G f) (Ñ : ChartRatio G) (W a : ℝ) (l : Finset ℕ) (m : ℕ) (s : Molecule S) :=
    ∫ i,X.body R Ñ W a l m s i ∂((F.order G).prod X.dice)
def taggedL (p : S.Choices) : Coat T F := { X with k:=p }

def levelMean (R : Rep G f) (Ñ : ChartRatio G) (W a : ℝ) (l : Finset ℕ) (m : ℕ) (s : Molecule S) :=
    likely fun p=> (X.taggedL p).attains R Ñ W a l m s
end Coat
namespace Cash
variable (H : Cash W α μ L Q o C T R) (s : Molecule S)
variable (X X' : Coat T F) (he : X.x=α)

lemma concord (X X' : Coat T F) (h : Borough X X' Z w v k k' R) (he : X.x=α) (hf : H.unionP s⊆ Z) :
    X.term R Q.table W o.a k Q.halo w s=X'.term R Q.table W o.a k' Q.halo v s := by
  unfold Coat.term; refine prod_congr rfl fun i hi=> ?_
  apply h.complete (he.symm ▸ H.laws.data.room) Q.buys i _ (he.symm ▸ H.laws.intake)
  unfold Coat.B; rw [he]
  exact (show H.supportP i⊆_ from subset_biUnion_of_mem _ hi).trans hf

include he
lemma vista (hk : X.width=o.K) (hX : X.manifest) (hX' : X'.manifest)
    (hd : Village X X' (H.unionP s)) (hg : ∀ i : Site f,S.ratio.parent i∈ H.unionP s →
      (i∈Contract.covered R k ↔ i∈Contract.covered R k')) :
    X.attains R Q.table W o.a k Q.halo s=X'.attains R Q.table W o.a k' Q.halo s := by
  let f (X : Coat T F) i := X.body R Q.table W o.a i Q.halo s
  unfold attains; rw [integral_prod _ (H.integrated X he hk hX k s),integral_prod _ (H.integrated X'
    (hd.weather ▸ he) (hd.width ▸ hk) hX' k' s)]
  apply integral_congr_ae; filter_upwards with y
  let I:= podium S G (H.unionP s) X.B
  have hp : X.relating.PosDef := (H.laws.data.localP F X he hk hX).sails.fullC
  have hv : X'.relating.PosDef := (H.laws.data.localP F X' (hd.weather ▸ he) (hd.width ▸ hk) hX').sails.fullC
  have hS : circuit I X.relating=circuit I X'.relating := by
    ext i j; exact hd.same_cov (he.symm ▸ H.laws.data.room) j.val j.2 i.val
  have hh : MeasurePreserving (swim I) X'.dice (arch I X.relating) := by rw [arch,hS]; exact orbit hv.posSemidef I
  have h1 (T : Coat _ F) (he : T.x=α) (hk : T.width=o.K) (i) : Measurable fun p=> f T i (y,p) :=
    ((T.body_b Q.table_exists (he.symm ▸ H.laws.intake) (by rw [he,hk]; exact H.laws.data.access) ..)).comp (measurable_const.prodMk measurable_id)
  have h2 (u v) (hh : swim I u=swim I v) : f X k (y,u)=f X' k' (y,v) := H.concord s (X.wrapY y) (X'.wrapY y)
    ⟨hd.wrap y y (fun _ _=>rfl),(observe I).mp hh,hg⟩ he (Finset.Subset.refl _)
  have h3 (u v) (he : swim I u=swim I v) : f X k (y,u)=f X k (y,v) := (h2 u v he).trans (h2 v v rfl).symm
  have h4 (u v) (he : swim I u=swim I v) : f X' k' (y,u)=f X' k' (y,v) := (h2 u u rfl).symm.trans (h2 u v he)
  rw [Pond.gathered (spill I) (spill_m I) (show MeasurePreserving (swim I) X.dice (arch I X.relating) from orbit hp.posSemidef I) (settled I) h3
    (h1 X he hk k), Pond.gathered (spill I) (spill_m I) hh (settled I) h4 (h1 _ (hd.weather ▸ he) (hd.width ▸ hk) k')]
  exact integral_congr_ae (ae_of_all _ fun _=> h2 _ _ rfl)
end Cash
end YM.ConnectedActivityE6

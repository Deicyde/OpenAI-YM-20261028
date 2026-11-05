import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Peoples

/-! # Same coefficient without knowing ANY off-support flag bits.

A basis even for ALL_FIELD to take gas reconstruction *from the local
values*, with its original distinction between stencil and predicates.
No assertion of Borel when *integrating* Dress V yet (see separately).
No inference of germ smoothness or 4-jet pricing there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Arbor
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open AnalyticBridge.Sharp AnalyticBridge.LocalGaussian Spot AnalyticBridge.RelativeLogdet
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace YM.Push.SectorMeasure
open Wires Geo Notify Voice Voice.Check Voice.Defenses Parcel Shipment   Route SectorNext.Reconnect SectorNext.Reconnect.Words
open Finset hiding card
variable {G : Gauge} {c f : Side} {S : StepData c f} {I : Type} [DecidableEq I]
    (D : AnalyticBridge.LocalGaussian.Desk G S) (Z : Art I D) (h : Lit D) (F : Forest S.ratio) (k₀ k : S.Choices) (V : Config G c)
    (i : Ensign S I) (hI : privilege D Z F V i) (t : ℝ)
local notation "x₀"=>D.betaHat
local notation "X₀"=>wood D Z i
local notation "K"=> Shipment.key D Z i
local notation "W₀"=>Route.Badge.near K
local notation "A₀"=>Shipment.station i
local notation "A₁"=>Route.patch x₀ V A₀
local notation "R₀"=>Badge.ribbon K F A₀
local notation "P"=> Native.kinetic D.tube F k₀ x₀
local notation "H"=> Shipment.theater D Z h F k₀ V

def attire (p : (R₀).Page G) : ℂ := ∏ j ∈ i,Shipment.shutter D Z t j i F A₀ (Fleet.kSet i) k V ((K).embroider p)

def medium := (piHaar G (R₀).live).prod (Gaussian.cloud (Arbor.service D Z F k V i))

def variation : ℂ := ∫ p,attire D Z F k V i t p ∂medium D Z F k V i

include h
lemma press (hw : Shipment.Valid D I Z) : Measurable (fun p : Config G c × Arbor.Policy D Z F i=>attire D Z F k p.1 i t p.2) := by
  let f := fun p : Config G c × Arbor.Policy D Z F i=> (p.1,(K).embroider p.2)
  have ht : Measurable f := measurable_fst.prodMk ((Badge.embroider_meas _).comp measurable_snd)
  unfold attire; exact Finset.measurable_fun_prod _ fun j _=> ((shutter_meas D Z t h hw j i F _ _ k).comp ht)

omit h in
private lemma steady {U V : Config G c} {l k : S.Choices} (hx : Tags.Synchronized X₀ l k) (ht : Agrees X₀ U V) :
    Physical.Reads X₀ A₀ A₀ F F U V l k := ⟨ht,hx.1,fun i hi=>hx.2 i (hi (Finset.mem_insert_self ..)) (hi (by simp [pinPos])),fun _ _ _=>Iff.rfl,
    fun _ _=>Iff.rfl,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl⟩

lemma pre (hw : Shipment.Valid D I Z) {U V : Config G c} {k l : S.Choices} (hx : Tags.Synchronized X₀ k l) (ht : Agrees X₀ U V) :
    attire D Z F k U i t = attire D Z F l V i t := funext fun _=> across D Z h F i t hw (steady D Z F i hx ht) ⟨fun _ _ _=>rfl,fun _ _ _=>rfl⟩

lemma read (hw : Shipment.Valid D I Z) {U V : Config G c} {k l : S.Choices} (hx : Tags.Synchronized X₀ k l) (ht : Agrees X₀ U V) :
    variation D Z F k U i t=variation D Z F l V i t := by
  unfold variation medium; rw [pre D Z h F i t hw hx ht, aired D Z h F i hx ht]

include hI
set_option maxHeartbeats 650000 in
lemma complete (hA : (stars D F k₀).Available V) : MeasurePreserving (Arbor.print D Z h F k V i hI) ((H).paper i k) (medium D Z F k V i) := by
  let v := (K)
  have ht : ((H).air i k).PosDef := (hA.trueCov _ k ((H).real i)).nativePos.submatrix (Ribbon.lighten ((H).checked i)).injective
  let u:=breathing D Z h F k V i hI
  unfold medium
  rw [show Arbor.service D Z F k V i=((H).air i k).submatrix u u from Matrix.ext (serviced D Z h F k₀ k V i hI)]
  exact (Projection.pi_projection G.probHaar (frosted D Z h F k V i hI)).prod (Projection.cloud_projection ht u)

lemma reads_head (hw : Shipment.Valid D I Z) (p : (H).point i) : lines D Z t h F k₀ V i k p = attire D Z F k V i t (Arbor.print D Z h F k V i hI p) := by
  unfold lines attire; rw [if_pos hI]
  symm; exact across D Z h F i t hw (reads D Z F V i hI (show Tags.Synchronized X₀ k k from ⟨fun _ _=>rfl,fun _ _ _=>rfl⟩)
    (show Agrees X₀ V V from fun _ _ _=>rfl)) (opt D Z h F k V i hI p)

abbrev rates := ∫ p,lines D Z t h F k₀ V i k p ∂(H).paper i k

lemma rate_align (hw : Shipment.Valid D I Z) (hA : (stars D F k₀).Available V) : rates D Z h F k₀ k V i t=variation D Z F k V i t := by
  have ht:=complete D Z h F k₀ k V i hI hA
  unfold rates; simp_rw [reads_head D Z h F k₀ k V i hI t hw]
  unfold variation; rw [← ht.map_eq]
  let f (p : Policy D Z F i):= attire D Z F k V i t p
  have hg : Measurable f := (Arbor.press D Z h F k i t hw).comp (measurable_prodMk_left (x:=V))
  exact (integral_map ht.measurable.aemeasurable (μ:=(H).paper i k) hg.aestronglyMeasurable).symm


-- pre-mask prices. Do not use `Legal within X` as a substitution
-- when selling on a changed sample. This uses numerical comparisons
-- above, not masks.
def quantity := if Ac.Spark (coat D Z) i ∧ permits (requirement D Z F) i then variation D Z F k V i t else 0

def bin : ℂ := (↑(Fintype.card S.Choices : ℝ)⁻¹ : ℂ) * ∑ k,quantity D Z F k V i t

def visits : ℂ := if (wood D Z i∩RG.flags (temp D.betaHat) V=(Shipment.station i).flags) then bin D Z F V i t else 0 -- replace
omit hI in
lemma valueOn (hw : Shipment.Valid D I Z) : LocalOn X₀ (fun V=>bin D Z F V i t) := by
  intro v w hx
  unfold bin quantity
  refine congr_arg _ (Finset.sum_congr rfl (fun k _=>?_))
  -- one arm
  split_ifs
  exact read D Z h F i t hw ⟨fun _ _=>rfl,fun _ _ _=>rfl⟩ hx
  rfl

end YM.PhysicalNext.Dictionary.Arbor

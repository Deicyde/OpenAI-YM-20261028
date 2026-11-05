import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Drew
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.RoomB

/-!
# Y/V shifting both. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Art
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees Multiple Letter OmitClusters
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {L : Side}
variable {A : Type*} [MeasurableSpace A] {V : A→ Config G c} {Y : A→F.Slice G} {z : A → Air f G}
variable (X : Coat T F) (h : P.Funds S T) (ht : ShellAccess S G X.x W X.width C)
variable (he : Measurable V) (hp : Measurable Y) (hk : Measurable z)

def drive (X : Coat T F) (V : Config G c) (Y : F.Slice G) := (vary X V).wrapY Y

include he hp
lemma entering {U : A→Directions G f} (hu : Measurable U) : Measurable fun x=> (drive X (V x) (Y x)).input (U x) := by
  let g x:= (drive X (V x) (Y x)).view (U x)
  have hv : Measurable g := by
    apply measurable_pi_lambda; intro i; by_cases hh : X.Hot i.1
    · have hx x : g x i=G.lieExp (U x i.1)*replica S.ratio (V x) i.1 := if_pos hh
      simp_rw [hx]; exact (G.lieExp_cont.measurable.comp ((measurable_pi_apply i.val).comp hu)).mul
        ((measurable_pi_apply i.val).comp (((Art.loyal (G:=G) (S:=S)).measurable).comp he))
    have hx x : g x i=Y x i := if_neg hh
    simp_rw [hx]; exact (measurable_pi_apply _).comp hp
  exact F.continuous_drape.measurable.comp hv

include h ht
lemma tumbling {U : A→Directions G f} (hu : Measurable U) (s : Signed) (p : Rod c f) :
    Measurable (fun x=> (drive X (V x) (Y x)).realPath s p (U x)) := by
  let Z x:= drive X (V x) (Y x)
  have hf : Measurable fun x=> (Z x).saved := by
    apply measurable_pi_lambda; intro i
    change Measurable fun x=> if _∨X.Hot i then 0 else cutLog X.χ (X.width*X.t) (F.drape (Y x) i * (replica S.ratio (V x) i)⁻¹)
    split_ifs
    · exact measurable_const
    have he : Measurable (fun x=> F.drape (Y x) i * (replica S.ratio (V x) i)⁻¹) :=
      ((((measurable_pi_apply i).comp F.continuous_drape.measurable).comp hp).mul ((measurable_pi_apply i).comp (((Art.loyal (G:=G) (S:=S)).measurable).comp he)).inv)
    exact (ht.log.borel X.χ).comp he
  have hg : Measurable X.lens := by
    apply measurable_pi_lambda; intro i; unfold Coat.lens; split_ifs
    · exact measurable_pi_apply _
    exact measurable_const
  let W (x) := pull s 0 (V x)
  have hh : Measurable W := (continuous_pull (G:=G) s (0:Site c)).measurable.comp he
  obtain ⟨hz,hx⟩:= (census_o h (U:=fun x=>replica S.ratio (W x)) (((Art.loyal (G:=G) (S:=S)).measurable).comp hh) hh (choice s X.k) X.x).1 p
  have hG : Measurable (fun x=> (V x, (Z x).signal (U x))) := he.prodMk (show Measurable (fun x=> (Z x).saved + X.lens (U x)) from hf.add (hg.comp hu))
  change Measurable (fun x=> (baseStroke T X.x (choice s X.k) (W x) p-guide T X.x (W x) p) + orientedRow T X.R s p (V x) ((Z x).signal (U x)))
  apply Measurable.add (f:=fun x=> baseStroke T X.x (choice s X.k) (W x) p-guide T X.x (W x) p) (g:=fun x=>orientedRow T X.R s p (V x) ((Z x).signal (U x)))
  · exact (hx.sub hz)
  have hH := (alongRow X h s p).measurable.comp hG; rw [Function.comp_def] at hH; exact hH
lemma wages :
    let Z x:=drive X (V x) (Y x)
    Measurable (fun x=> (Z x).linearBill) ∧ Measurable (fun x=> (Z x).driftM) ∧ Measurable (fun x=> (Z x).μ) := by
  intro Z
  have hm i : Measurable fun x=> (Z x).priced 0 i := by
    change Measurable fun x=> if X.selected _ _ then Coat.scale • (Z x).realPath i.1 i.2 0 else 0
    split_ifs
    · exact Measurable.smul (measurable_const (a:=Coat.scale)) (tumbling X h ht he hp (U:=fun _=>0) measurable_const i.1 i.2)
    exact measurable_const
  have hz : Borel fun x=> (Z x).form.transpose := fun i j=> (borel_form X h j i).comp he
  have hg i : Measurable fun x=> (Z x).linearBill i :=
    borel_times hz (d:=fun x=> stand ((Z x).priced 0)) (fun i=> (EuclideanSpace.proj (ι:=G.ColorIndex) (𝕜:=ℝ) i.2).measurable.comp (hm i.1)) i
  have hc : Borel fun x=> (Z x).plate := fun i j=> (borel_plate X h i j).comp he
  have hf : Borel fun x=> (Z x).kernelA.transpose := fun i j=> Art.borel_pad X.shutter _ hc j i
  have hu : Measurable fun x=> (Z x).driftM := (measurable_pi_lambda _ (borel_times hf hg)).neg
  refine ⟨measurable_pi_lambda _ hg,hu,measurable_pi_lambda _ fun i=> ?_⟩
  let l : (Tubular f G→ℝ) →ₗ[ℝ] G.Color :=
    { toFun v := erect G v i
      map_add' := fun _ _=> rfl
      map_smul' := fun _ _=> rfl }
  exact l.continuous_of_finiteDimensional.measurable.comp hu
lemma levitate (β : ℝ) (hk : Measurable z) : Measurable fun x=> (drive X (V x) (Y x)).liftA β (z x) := by
  have hh : Measurable fun x=> X.atmos (z x) := measurable_pi_lambda _ fun i=> (X.tale i).measurable.comp hk
  exact (wages X h ht he hp).2.2.add (Measurable.smul (measurable_const (a:=gStep β)) hh)
end YM.ConnectedActivityE6.Art

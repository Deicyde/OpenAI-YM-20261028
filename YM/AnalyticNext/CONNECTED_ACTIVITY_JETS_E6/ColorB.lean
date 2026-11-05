import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Facility
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Mill

/-! # Matrix log stamps, panic variants on V -/
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
include he h ht hp hk
lemma royal (β : ℝ) :
    let E t:= drive X (V t) (Y t)
    (∀ p,Measurable (fun t=> (E t).condensation p)) ∧
      ∀ p a,Measurable fun t=> (E t).fuel a β (z t) p := by
  intro E
  have hG : Borel fun t=> (E t).plate := fun i j=> (borel_plate X h i j).comp he
  have hF : Borel fun t=> (E t).blank.plate := by
    have hh i : (E i).blank.plate=X.blank.plate := neutral _ _ rfl
    intro i j; simp_rw [hh]; exact measurable_const
  have hh := amps X hG; have hf:= amps X hF
  refine ⟨fun p=> ?_,fun p a=> ?_⟩
  · exact (((hf.2.2 p).sub (hh.2.2 p)).div_const 2)
  have hZ i : Measurable (fun t=> (E t).aperture β (z t) a i) := by
    change Measurable (fun t=> if X.Hot i then X.cone (2*a) ((E t).liftA β (z t)) i else 1); split_ifs
    · exact (X.cone_b ..).comp (levitate X h ht he hp _ hk)
    exact measurable_const
  have hg : Borel fun i=> (E i).shreds := (c_measured X.shutter hG).2
  have hA (p : Tubular f G) : Measurable (fun t=> z t p) := (EuclideanSpace.proj (𝕜:=ℝ) (ι:=Tubular f G) p).measurable.comp hk
  rcases p with p|p|p|p|p
  · exact ((hh.2.1 p).neg.div_const 2)
  · exact ((hf.2.1 p).div_const 2)
  · exact ((hh.1 p).div_const 2)
  · obtain ⟨hu,hM,_⟩:= wages X h ht he hp
    have hv i : Measurable (fun t=> (E t).hatted β i) :=
      (measurable_const (a:= -(gStep β)⁻¹)).mul ((borel_times hG (d:= fun i=>(E i).driftM)
        (fun i=> (measurable_pi_apply i).comp hM) _).add ((measurable_pi_apply _).comp hu))
    exact (hZ _).mul (Finset.measurable_fun_sum _ fun k _=> (hA (p,k)).mul (hv _))
  let u := p.2.1; let v:=p.2.2; let w:= arrive u v
  have hz j : Borel fun t=> finale (E t) p.1 j := by
    unfold finale; split_ifs
    · exact fun i j=> (hg i j).neg
    exact hG
  have hD : Borel fun t=> combo u v ((E t).finale p.1) := comboB (D:=fun t j=> finale (E t) p.1 j) hz v u
  exact ((hZ u).mul (hZ w)).mul ((measurable_const (a:=(1/2:ℝ))).mul (Finset.measurable_fun_sum _
    fun i _ => (hA (u,i)).mul (Finset.measurable_fun_sum _ (fun j _=> (hD i j).mul (hA (w,j))))))

omit hk ht
lemma terror {u : A → Directions G f} (hu : Measurable u) (k : Finset ℕ) (R : Rep G f) :
    (∀ i Z, Measurable (fun t=> (drive X (V t) (Y t)).rawStorm (u t) W Z R k i)) ∧ ∀ i a, Measurable
      fun t=> (drive X (V t) (Y t)).detect (u t) W a R k i := by
  let E t:= drive X (V t) (Y t); let f t:= (E t).input (u t); have hf : Measurable f:= entering X he hp hu
  have hh i D : Measurable fun t=> (E t).rawStorm (u t) W D R k i := by
    rcases i with i|i|i|i|i
    · exact (X.fine_b ..).comp hf
    · have he := wire_meas X.k i (funds_branch h) hf he
      change Measurable fun t=> Mask.noise D X.χ i X.t W (f t) X.k (V t); unfold Mask.noise
      have he := X.χ.smooth.continuous.measurable.comp ((he.div_const (W*X.t)).pow_const 2)
      split_ifs
      · exact measurable_const.sub he
      exact he
    · exact (pin_b i X.k h).comp hf
    · exact (site_b i X.k).comp hf
    exact (contract_b ..).comp hf
  refine ⟨hh,fun i a=>?_⟩
  rcases i with i|i
  · let Y := X.plaza (halo X.B (districts S i))
    change Measurable fun t=> if mandatory X.seeds X.B i then 0 else X.enforce (2*a) (u t) Y*((E t).rawStorm (u t) W X.seeds R k i-1)
    split_ifs
    · exact measurable_const
    exact ((X.enforce_b (2*a) Y).comp hu).mul ((hh i X.seeds).sub measurable_const)
  change Measurable (fun t=> X.aura (u t) a i); unfold aura; split_ifs
  · exact ((X.cone_b i a).comp hu).sub measurable_const
  exact measurable_const
end YM.ConnectedActivityE6.Art

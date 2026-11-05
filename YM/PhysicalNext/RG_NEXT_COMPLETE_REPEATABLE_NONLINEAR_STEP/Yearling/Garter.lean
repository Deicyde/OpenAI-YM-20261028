import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Trinket

/-! # Calibrations LOOM *within* Spirit Captain. Needs exp next stage >0.
    purchases reusing `Armada` slack. Keep floor request pre-W. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Yearling
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet March Alabaster
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I : RG.Rep G f}
    {x μ C v : ℝ} {i j n m : ℕ} {χ : Chi} {H : Cash W x μ L Q o C T R}

structure Year (H : Cash W x μ L Q o C T R) (j : ℕ) (v : ℝ) (χ : Chi) where
  year : Rig H j v χ
  aa : ℝ
  b : ℝ
  ζ : ℝ
  δ : ℝ
  w : ℝ
  q : ℝ
  h : ℝ
  Z : ℝ
  r : ℕ
  net : Captain H j aa b v ζ δ w q h Z r χ
  A : ℝ
  pay : Armada Q L μ 0 x A h j r

lemma sterling (P : Teller G) (Q : ConnectedActivityE6.Target G P) (h:0<Q.exp) : ∃ N:ℕ,∀ L:Side,N≤L.val→∀ (D:Patch), D.Branches P.bind G→∀ (i:ℕ) (χ:Chi) (W μ : ℝ), 0<W→0<μ→ ∀ o:Target.Order G W,∀ᶠ x in atTop, ∃ v:ℝ,0<v∧∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D → Stamp T→∀ (R:RG.Rep G f) (C:ℝ) (H:Cash W x μ L Q o C T R),Nonempty (Year H i v χ):= by
  obtain ⟨N,hN⟩:= discover P Q; obtain ⟨M,hM⟩:= Oboe.ell P Q
  refine ⟨N+M,?_⟩; intro L hL D hD i χ W μ hW hμ o
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x:= 2*Pressure.fiery G x L; let v x:= ((i:ℝ)+1)*Z*t x
  have ht : Rate G L (-(1/2)) t:= Rate.flame.mul_left _; have hh : Rate G L (-(1/2)) v:= ht.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  have hv:∀ᶠ x in atTop,0 ≤ v x:=hp.mono fun x h=>by unfold v; positivity
  obtain ⟨C,q,r,p,l,hB,hX⟩:= hM L (by omega) D hD i χ W hW μ hμ o A a hA v hh hv
  let p' x:= |p x|
  obtain ⟨B,hT,hY⟩:= Armada.ensemble Q L hμ 0 le_rfl h i l (show Rate G L 0 p' from hB.compare (Eventually.of_forall fun x=> (abs_abs _).le))
  filter_upwards [hp,hX,hN L (by omega) D hD i χ W hW μ hμ o A a hA v hh hv, ired P D L hD W o Q,hY] with x hx hX hK hI hy
  have hs :0<v x:=by unfold v; positivity
  refine ⟨v x,hs,?_⟩; intro c f S T hS hT R C' H
  obtain ⟨Ξ,he⟩:=hX _ _ S T hS hT R C' H
  have hh := H.laws.data.room.temperatures; rw [H.laws.data.funds.length_eq] at hh
  let t':= Z*t x; have hC: i*t' ≤ v x := by unfold t' v; nlinarith only [mul_nonneg hZ.le hx.le];
  have hm :0≤t':=mul_nonneg hZ.le hx.le
  refine ⟨⟨A,a,(hK _ _ S T hS hT R C' H).some, _,_,_,Ξ,_,_,he,hI _ _ S T hS R μ C' H,t',hm,hC,⟨?_⟩⟩,C,q x,t x,A,a,r x,|p x|,Z*t x,l,⟨Ξ,he,hm,hx.le,hh,hs,abs_nonneg _,⟨fun c=> hq c _ hx.le⟩,hC⟩,B,hy⟩
  intro c e he; apply hq c (t x) hx.le e; exact he.trans hh
end YM.PhysicalNext.Repeat.Yearling

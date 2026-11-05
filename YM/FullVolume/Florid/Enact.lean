import YM.FullVolume.Sector.Hinge
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
lemma wombPlus (P : Teller G) (Q : ConnectedActivityE6.Target G P): ∃ N:ℕ,∀ L:Side,N≤L.val→∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ),0<W → ∀ μ:ℝ,0<μ→ ∀ (o:Target.Order G W) (A f₀:ℝ), Canary G A f₀→∀ V:ℝ→ℝ,Rate G L (-(1/2)) V→(∀ᶠ x in atTop,0≤V x) → ∃ (C':ℝ) (d r p:ℝ→ℝ) (k:ℕ),0≤C'∧ Rate G L 0 p ∧ Rate G L 0 r ∧ Rate G L (-(1/2)) d ∧
    ∀ᶠ x in atTop,∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→ Stamp T→ ∀ (R:Rep G f) (C:ℝ) (H:Cash W x μ L Q o C T R),Nonempty (Plot H i (V x) (d x) (r x) C' χ A f₀ (p x) k):=by -- edit
  obtain ⟨N,hN⟩:= Utopia.whittle P Q
  refine ⟨N,fun L hL D hD i χ W hW μ hm o A f hA V hV hv=>?_⟩
  obtain ⟨B,Z,hB,hZ,hX⟩:= Silica.clips hA P L i χ hV
  have hb:= hB.compare (v:=fun x=>|B x|) (Eventually.of_forall fun x=>(abs_abs _).le)
  obtain ⟨C,r,hC,hr,hχ⟩:= hN L hL D hD i χ W hW μ hm o V (fun x=>|B x|) hV hv hb
  obtain ⟨k,U,hU,hΓ⟩:= rump P L D hD o.K o.γ W o.a χ i hV hB hv hZ o.indexPay o.f A
  have hG:= Glass.portal P D L hD i χ hV hv o.K o.γ W o.indexPay o.f
  obtain ⟨Y,hY⟩:= apical P L D hD o.K o.γ W o.a χ i hV hv hb o.indexPay o.f
  refine ⟨C,fun x=> |B x|, r, fun x=>|U x|, k, hC, hU.compare (Eventually.of_forall fun x=>(abs_abs _).le),hr,hb,?_⟩
  filter_upwards [hχ,hΓ,hX, ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm),hY,hG,paysDia P L D hD _ _ W o.a χ i hV hB hv o.indexPay o.f A] with x Hx h hx hp hY hG hB c f S T hS hT R C' H
  have hθ:=H.laws.data; have hh:=hθ.funds; have hy := H.laws.intake
  have hp := (le_abs_self _).trans hp; obtain ⟨A',hC,hL⟩:= hB _ _ S T hh hS hθ.access R hy
  obtain ⟨Ξ⟩ := Hx _ _ S T hS hT R C' H
  refine ⟨⟨Ξ,hA,hp,abs_nonneg _,|Y x|,?_,?_⟩⟩
  · intro E _ _ _ F X w β V U z x' s y hX hF hM hψ hA h hζ
    exact hY c _ S T hS hh hθ.access E x' V F X β U w z hX hψ hF (hθ.localP F X hX hF hM) hA h s y hζ
  intro F X hX hF hζ hM E _ _ _ Y y hy' hf
  have hZ := hθ.localP F X hX hF hM
  refine ⟨hG c _ S T hS hh hθ.access F X hF hζ hX hZ E Y y hy' hf, fun z'=>?_⟩
  obtain ⟨hw,hD⟩:= hx _ _ S T F X hX hh hζ R.beta hy.positive z' E Y y hy' hf
  have hp := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [hX,hh.length_eq]; exact hp)
  exact ⟨hp,fun J=> ⟨(h c _ S T hh hS hθ.access E y Y F X z' R hX hF hζ hZ hy hf hp hw J), (hL E y Y F X z' hX hF hζ hZ hf hp J).smooth⟩⟩
end YM.ConnectedActivityE6.Empire

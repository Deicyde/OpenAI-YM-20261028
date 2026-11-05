import YM.FullVolume.E6.Proper
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hem
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pattern

/-!
# Unforced angular budget at calibrated Calendar

First polymer, *before* mask. All ordered-left derivatives at
 arbitrarily anchored costs. Preserve calibration order; Lean budget
allows smaller given order AND likewise branch arbitrary. Includes Brush ore
for further Uri variants including repeated cluster derivatives.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
open Next.Foundations

open Empire Lim
structure Bank where
    A:ℝ
    a:ℝ
    C:ℝ
    d:ℝ
    v:ℝ
    t:ℝ
    r:ℝ
    B:ℝ
    q:ℝ
    k:ℕ
    K:ℕ
    Δ:ℝ
    B0:ℝ
    B1:ℝ
    W:ℝ
    U:ℝ
    V:ℝ
    c:ℝ
    P0:ℝ
    p:ℝ
structure Station (f:Bank)(χ:Chi)(H : Cash W s μ L Q o C T R)(j:ℕ) where
    N: Captain H j f.C f.d f.v f.t f.A f.a f.r f.B f.q f.k χ
    fleets: ProperPlot H j f.v f.Δ f.P0 f.c χ f.A f.a f.p f.K f.B0 f.B1 f.W f.U
    army: Armada Q L μ 0 s f.V f.B j f.k
    anew : Cash.Renewed 0 0 f.V f.V H -- possible shrink
lemma patrol (P : Teller G) (Q: YM.ConnectedActivityE6.Target G P): ∃ n:ℕ,∀ (L:Side), n≤L.val → ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ),0<W → ∀ (μ:ℝ),0<μ → ∀ (o:Target.Order G W),0<Q.exp→ ∀ C':ℝ,∀ᶠ x in atTop,∃ K:Bank, ∀ (c f:Side) (S:StepData c f)(T:Tube G S), S.patch=D→Stamp T→∀ (R:Rep G f) (H:Cash W x μ L Q o C' T R), Nonempty (Station K χ H i) := by
  obtain ⟨n,h⟩:= Oboe.ell P Q; obtain ⟨n',h'⟩:= Empire.prom P Q; refine ⟨n+n', fun L hL D hD i χ W hW μ hm o hx C'=>?_⟩
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x := 2*Pressure.fiery G x L
  have he : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
  let v x := ((i:ℝ)+1)*Z*t x
  have hh : Rate G L (-(1/2)) v:= he.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  obtain ⟨C,d,r,B,k,hB,ht⟩:= h L (by omega) D hD i χ W hW μ hm o A a hA v hh (hp.mono (fun x hh=> by unfold v; positivity))
  let B' x:= |B x|; have hb' : Rate G L 0 B':= hB.compare (Eventually.of_forall fun x=> by simp [B'])
  obtain ⟨I,b₀,c₀,p₀,K,s₀,v₀,g₀,f₀,hI,h₀,hC,hV⟩:= h' L (by omega) D hD i χ W hW μ hm o A a hA v hh (hp.mono (fun x hh=> by unfold v; positivity))
  obtain ⟨e,HE,H⟩:=Armada.ensemble Q L hm 0 (by norm_num) hx i k hb'
  obtain ⟨z,hj⟩:= H.exists
  have He:=Cash.anew Q L o C' hm 0 (show (0:ℝ)≤0 from le_rfl) hj.delta hj.delta hj.little
  filter_upwards [hp,ht,hV,H,He] with x hx hD' hK hH hX
  refine ⟨⟨A,a,C,d x,v x,t x,r x,B' x,Z*t x,k,K,b₀ x,s₀ x,v₀ x,g₀ x,f₀ x,e,I,c₀ x,p₀ x⟩,fun c f S T hS hT R H=>?_⟩
  obtain ⟨Ξ,hF⟩:=hD' c f S T hS hT R _ H; have hZ := hZ; have h:= H.laws.data
  refine ⟨⟨⟨Ξ,hF,mul_nonneg hZ.le hx.le,hx.le,(by have he:= h.room.temperatures; rw [h.funds.length_eq] at he; exact he),
    (by unfold v; positivity),abs_nonneg _, ⟨fun c=> hq c _ hx.le⟩,(by unfold v; nlinarith [mul_nonneg hZ.le hx.le])⟩, (hK c f S T hS hT R C' H).some,hH,hX ..⟩⟩
end YM.ConnectedActivityE6.Blaze.March

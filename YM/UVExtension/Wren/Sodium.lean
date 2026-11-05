import YM.UVExtension.Wren.Taxis
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wren
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze March Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι} {P:BudgetPoint}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine PhysicalNext.Repeat PhysicalNext.Repeat.Match PhysicalNext.Repeat.Greenbelt Wick
open Polar Silica Shield Score Flux Matter Ursell Gas Trees Multiple Refrain

-- Captain leases come together with Score width for all L large and at any calendar.
namespace Hikes
open Blaze March
-- moving coordinates Captain & matching u service before waits.
lemma expenses (Q:ConnectedActivityE6.Target G X): ∃ z:ℕ,∀ (L:Side),z≤L.val→∀ k χ (D : RG.Patch) (W μ:ℝ), 0<W→0<μ → D.Branches X.bind G→∀ (o:Target.Order G W), 0<Q.exp → ∃ (A b C a:ℝ) (d t Z r B q : ℝ→ℝ) (m:ℕ),∀ᶠ x in atTop, Armada Q L μ 0 x a (B x) k m ∧ Service Q o L D μ χ k x (t x) ∧ ∀ (c f:Side) (S:StepData c f)(T:Tube G S)(R:Rep G f)(C':ℝ)(H:Cash W x μ L Q o C' T R),S.patch=D → Stamp T → Nonempty (Captain H k C (d x) (t x) (Z x) A b (r x) (B x) (q x) m χ):=by
    -- retains slope. require Q.exp>0? inspect. take when .fund >
    obtain ⟨i,hi⟩:= Span.finance Q; obtain ⟨n,h⟩:= Oboe.ell X Q; use i+n; intro L hL k χ D W μ hW hu hD o hqP
    obtain ⟨A,b,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G k
    let t x := 2*Pressure.fiery G x L
    have he : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
    let v x := ((k:ℝ)+1)*Z*t x
    have hh : Rate G L (-(1/2)) v:= he.mul_left _
    have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
    have hH : ∀ᶠ x : ℝ in atTop,0≤v x:=hp.mono (fun i hi=> by unfold v; positivity)
    obtain ⟨C,d,r,B,m,hB,ht⟩:= h L (by omega) D hD k χ W hW μ hu o A b hA v hh hH
    let B' x:= |B x|; have hb' : Rate G L 0 B':= hB.compare (Eventually.of_forall fun x=> by simp [B'])
    obtain ⟨a,-,hN⟩:= Armada.ensemble Q L hu 0 le_rfl hqP k m hb'
    refine ⟨A,b,C,a,d,v,t,r,B',fun x=> Z*t x,m,?_⟩
    filter_upwards [hN,hp,ht,hi L (by omega) D hD k χ W μ hW hu o v hh hH] with x ha hx hh hU
    refine ⟨ha,hU,fun c f S T R C' H hS hT =>?_⟩; obtain ⟨Ξ,hF⟩:=hh c f S T hS hT R _ H
    have h:= H.laws.data; exact ⟨Ξ,hF,mul_nonneg hZ.le hx.le,hx.le,(by have he:= h.room.temperatures; rw [h.funds.length_eq] at he; exact he), (by unfold v; positivity),abs_nonneg _,⟨fun c=>hq c _ hx.le⟩,(by unfold v; nlinarith [mul_nonneg hZ.le hx.le])⟩

structure Ledger (Q:ConnectedActivityE6.Target G X) (L:Side) (w μ:ℝ) (o:Target.Order G w) (s:ℝ) (k:ℕ) (χ:Chi):Prop where
    capitol : ∀ (ι:Type)(v:Filter ι)[NeBot v]{c f :Side}{S:StepData c f}(T:ι→Tube G S) (R:ι→ Rep G f)(A:ℝ) (H: ∀ i,Cash w s μ L Q o A (T i) (R i)),Concerted v T →(∀ i, Stamp (T i)) → Nonempty (Choir v T H k χ)
lemma purchases (Q:ConnectedActivityE6.Target G X) : ∃ z:ℕ,∀ L:Side,z ≤ L.val→∀ k χ (W μ:ℝ),0<W → 0<μ → ∀ (o: Target.Order G W),0<Q.exp → ∀ᶠ x in atTop, Ledger Q L W μ o x k χ:=by
    obtain ⟨z,hz⟩:= expenses Q; use z; intro L hL k χ W μ hW hu o he; by_cases hZ: ∃ D:Patch, D.L=L∧ D.J=X.j ∧ D.Branches X.bind G
    · obtain ⟨D,hv,hH,hD⟩:= hZ
      obtain ⟨A,b,C,a,d,t,Z,r,B,q,m,ht⟩:=hz L hL k χ D W μ hW hu hD o he
      filter_upwards [ht] with x ht; constructor; intro ι v hv' c f S T R J H hT hS
      obtain ⟨i,-⟩:= (show ∀ᶠ i in v, True from by simp).exists
      have hA:= (H i).laws.data.funds.patch hv hH
      obtain ⟨A',b',l,B',C',r',d',n,H₁,H₂,he,p⟩:= ht.2.1.dome
      refine ⟨⟨_,A',l,B',d',r',C',n,b',H₁,H₂,_,_,_,_,A,b,_,_,m,a,0,⟨hT,(hA.symm ▸ he),hS,fun E _ _ _ F V i X x hx hh hb hv hG hp=>?_⟩,fun i=> (ht.2.2 _ _ _ _ _ _ _ hA (hS i)).some,ht.1⟩⟩
      exact p _ _ S _ _ _ (H i) hA E F _ X x hx hh hb hv hG hp
    filter_upwards with x; constructor; intro ι v _ c f S T R C H h hp
    obtain ⟨i,-⟩:= (show ∀ᶠ i in v, True from by simp).exists
    let h':= (H i).laws.data.funds; exact (hZ ⟨S.patch,h'.length_eq,h'.funds.atStep,h'.funds.kernel⟩).elim
end Hikes
end YM.UVExtension.Wren

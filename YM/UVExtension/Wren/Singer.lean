import YM.UVExtension.Wren.Script
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
open AnalyticBridge VerifiedReset Collection Quotes WilsonStartup Extra.Iteration Next.Scheduling
open Song Strata Gala Concert Geo Chains Lamppost Tabernacle Progress.DirectedRecipe
namespace Verso
lemma limits(P:BudgetPoint)(f:ι→Support c) (K:ℝ) : ∃ u>0, ∀ i, Real.exp (K * coverNumber P.B (f i)) ≤ u :=by
   let X:= ∑ i:Support c, Real.exp (K * coverNumber P.B i); have he:0≤X:= by unfold X; positivity
   exact ⟨X+1,by linarith,fun i=> (single_le_sum (f:=fun i=> Real.exp (K * coverNumber P.B i)) (fun j _=> by positivity) (mem_univ (f i))).trans (le_add_of_nonneg_right zero_le_one)⟩
lemma invests(P:BudgetPoint)(X:ι→ RegularAddress c)(K:ℝ)(h:0≤K): Upper (fork P G X K) ∧ lower (fork P G X K):=by
   obtain ⟨u,hU,hV⟩:=limits P (fun i=>(X i).support) K; refine ⟨⟨u,hU,fun i j=>?_⟩,fun i=> ⟨(X i).site,?_⟩⟩
   · unfold fork; dsimp only; split; exact hV _; exact hU.le
   unfold fork; dsimp only; rw [if_pos rfl]; exact Real.one_le_exp (by positivity)
lemma bids(P:BudgetPoint)(X:ι→ ForcedAddress G c)(K:ℝ)(h:0≤K): Upper (bell X P.B K) ∧ lower (bell X P.B K):=by
   obtain ⟨u,hU,hV⟩:= limits P (fun i=> (X i).support) K; refine ⟨⟨u,hU,fun i j=>?_⟩,fun i=> ?_⟩
   · unfold Concert.bell; dsimp only; split; exact hV _; exact hU.le
   obtain ⟨x,hx⟩:= (X i).inventory_ne; refine ⟨x,?_⟩; unfold Concert.bell; dsimp only; rw [if_pos ((X i).inventory_sup hx)]; exact Real.one_le_exp (by positivity)
variable {x:ι→ Tabernacle.Field G n}(P:BudgetPoint)(a b:ℝ)(h:0<a)(hi:0<b) [NeBot v](p: ∀ i, Tabernacle.rake P (x i))
lemma visible (he: Notes v P (drawer G n).reg (fun i=> (x i).1)) (hq: Transit v (fun i=> (x i).2)): ∃ t, Tendsto (fun i=>tuning P a b (x i)) v (𝓝 t) :=by
    obtain ⟨c,hc⟩:=start (show Transit v (fun i=> sheetE P (x i)) from he.invests) ((invests P _ P.supportExponent P.exponent_pos.le).1)
    obtain ⟨g,hg⟩:= start (show Transit v (fun i=> sheetK P (x i)) from hq) ((bids P _ P.supportExponent P.exponent_pos.le).1)
    exact ⟨_, (hc.const_smul a⁻¹).prodMk_nhds (hg.const_smul b⁻¹)⟩
include h hi p
lemma won (hv: ∃ t, Tendsto (fun i=>tuning P a b (x i)) v (𝓝 t)): Notes v P (drawer G n).reg (fun i=> (x i).1) ∧ Transit v (fun i=> (x i).2) :=by
   obtain ⟨w,hv⟩:=hv; rw [nhds_prod_eq] at hv; have he:=hv.fst; have hh:=hv.snd
   have hE i : (tuningE P (x i))= a • ((tuning P a b (x i)).1):= by unfold tuning; simp only [smul_smul,mul_inv_cancel₀ h.ne',one_smul]
   have hK i: tuningK P (x i)= b • ((tuning P a b (x i)).2):=by unfold tuning; simp only [smul_smul,mul_inv_cancel₀ hi.ne',one_smul]
   refine ⟨⟨fun i j=>?_ ,lacks (T:=a • w.1) (M:=ChimeE G P n) _ ((invests P _ P.supportExponent P.exponent_pos.le).2) ?_ ?_⟩, lacks (T:=b • w.2) (M:=ChimeK G P n) (fun i=> sheetK P (x i)) ((bids P _ P.supportExponent P.exponent_pos.le).2) ?_ ?_⟩
   · obtain ⟨t,v,H⟩:=p i; exact H.regular.smooth j
   · intro n; obtain ⟨a,b,H⟩:=p n; exact ⟨a,(Above.floorE P (Tabernacle.floor P (x n))).2 H.boundE⟩
   · exact (he.const_smul a).congr' (Eventually.of_forall (fun i=> (hE i).symm))
   · intro n; obtain ⟨a,b,H⟩:=p n; exact ⟨b,(Above.floorK P (Tabernacle.floor P (x n))).2 H.boundK⟩
   exact (hh.const_smul b).congr' (Eventually.of_forall (fun i=> (hK i).symm))
end Verso
end YM.UVExtension.Wren
#print axioms YM.UVExtension.Wren.Verso.won

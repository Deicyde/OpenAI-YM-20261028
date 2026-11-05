import YM.UVExtension.Wren.Springs
import YM.UVExtension.Concert.Hearth
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
open Song Strata Gala Concert Geo
open Badge Chains Marlin Trio
namespace Aside
-- lenses on fixed Flags period. use Tilt to pay slides later. bar all world flags. No need to form complete measured Tome read at unanchored outside Y.
structure Stars (v:Filter ι)(P:BudgetPoint)(F:ι→Site c→ Config G c→ℝ):Prop where
   regular : ∀ i j,P.Regular Finset.univ (F i j)
   small : ∀ j,Tune v (fun n (x:Fly G c P)=> x.reel (F n j))
end Aside
namespace TransitM
lemma scaled (f: κ→ℝ)(hf:∀ i,|f i|≤a){T:κ→Type}{F:ι→(i:κ)→T i→ℝ}(h: Transit v F)(ha:0≤a): Transit v (fun n x i=> f x* F n x i):=by
    obtain ⟨C,hC,hF⟩:=h.rain; refine ⟨⟨_,hC.scales a ha,hF.mono fun i h x u=>?_⟩,fun i=> (Tune.constant _ (f i) tendsto_const_nhds).mul (h.meters _)⟩; rw [norm_mul]; exact mul_le_mul (hf x) (h _ _) (norm_nonneg _) ha
lemma under {A:κ→ RegularAddress c}{F:ι→κ→ Config G c→ℝ}(h: Notes v P A F): Transit v (fun n m V=> masked P.threshold (A m).support (F n m) V):=by
    -- avoid choosing Healthy i. use Cauchy
    obtain ⟨Z,hZ,hV⟩:=h.invests.rain; obtain ⟨B,hB⟩:=hZ.books
    have he: ∀ᶠ n in v,∀ i (U:Config G c), ‖masked P.threshold (A i).support (F n i) U‖≤Z n i:=by
        filter_upwards [hV,hB] with n hn hV i U; by_cases ht: Healthy P.threshold (A i).support U
        · rw [masked_eq _ _ _ _ ht]; exact hn i (⟨U,ht,[],by simp,by simp⟩)
        rw [masked_ne _ _ _ _ ht,norm_zero]; exact hV.1 _
    refine ⟨⟨_,hZ,he⟩,fun i=>⟨⟨B,(he.and hB).mono fun n hh x=> (hh.1 i x).trans (budget_single hh.2 _)⟩,fun ε hε=>?_⟩⟩
    filter_upwards [(h.invests.meters i).uv ε hε] with n hn V; by_cases ht: Healthy P.threshold (A i).support V
    · rw [masked_eq _ _ _ _ ht,masked_eq _ _ _ _ ht]; exact hn ⟨V,ht,[],by simp,by simp⟩
    rw [masked_ne _ _ _ _ ht,masked_ne _ _ _ _ ht,sub_self,norm_zero]; exact hε.le
lemma sorted {F:ι→κ→α→ℝ}(h:Transit v F)(U:ι→Finset κ)(c:κ→Prop)(hp:∀ i,∀ᶠ n in v,i∈ U n ↔ c i): Tune v (fun n x=> ∑ i∈U n,F n i x):=by
    let L:=h.varying (fun n i=>i∈U n) c (fun i=> (hp i).mono fun _ h=> propext h)
    refine (L.includes (fun x (i:κ)=> (x:α))).switch (Eventually.of_forall fun n=>?_); funext i; rw [tsum_eq_sum (s:=U n) (hf:=fun x hx=>if_neg hx)]; exact sum_congr rfl fun i hi=> if_pos hi
end TransitM
namespace Choir
variable {H:∀ i:ι,Cash w s q L Q U C (T i) (R i)} (p:Choir v T H k χ)(h:StableR v R)
variable (j:ι)(P:BudgetPoint)(d:ι→ℝ)(u:ι→ℕ)
variable [NeBot v][v.IsCountablyGenerated]
include h p
lemma upper (hp:Tendsto u v atTop)(i:ℕ): ∀ᶠ n in v, i∈ Meadow.panel (H n) (u n) ↔ ¬Meadow.keep (H j) (Song.pennant (H j) i).2:= by
   let Y:=(Song.pennant (H j) i).2; by_cases he: Meadow.keep (H j) Y
   · filter_upwards with n; rw [← p.in_panel h j n,Meadow.petaled]; exact ⟨Meadow.notKept Y,fun hx=> False.elim (hx he)⟩ -- implicit binder
   filter_upwards [hp.eventually (Meadow.unfurls Y he)] with i hi; rw [← p.in_panel h j i,Meadow.petaled]; exact iff_of_true hi he

variable (hp:Tendsto u v atTop) (hf:∃ t,Tendsto d v (𝓝 t))(hP:P.threshold=temp s)(ht:P.order ≤ k)(hC:Decent (T j).low P)
def bars (n:ι):= Meadow.barony (H n) χ (u n) (d n)
def chants (n:ι):= Meadow.timbres (helm (H:=H) n) (d n) (u n) (χ:=χ)
-- shadow when n
include j hp hf hP ht hC
lemma skyline : Aside.Stars v P (bars (χ:=χ) (H:=H) d u):=by
    let f(n:ι):=(plusone (H n) (helm (H:=H) n) χ (d n)).logRead
    let F:=Beam.marquee (H j) P
    have hN : Notes v P F.reg f := p.armory h j P hP ht d hf hC
    let A n:= Meadow.panel (H n) (u n); let U(o:Site c):= Meadow.garnerAt (H j) P o
    have hz o n : bars (H:=H) (χ:=χ) d u n o= ∑ i∈A n,U o i • f n i := by
       unfold bars f; rw [Meadow.aster χ P (helm (H:=H) n) rfl rfl rfl]; apply sum_congr rfl; intro i _; rw [tiles p h j]
    constructor
    · intro i j; rw [hz]; exact Meadow.regularA _ (fun b _=> CouplingShape.reg_scale _ (CouplingShape.reg_extend (hN.available _ _) (Finset.subset_univ _)))
    intro o; let f' n i (x:Fly G c P):= x.reel (f n i); have hp':Transit v f' := hN.invests.many id Function.injective_id (fun i (x:Fly G c P)=> x.taps _)
    let hF:= TransitM.scaled (U o) (show ∀ i, |U o i|≤1 from fun i=> by unfold U; rw [abs_of_nonneg (Meadow.nonnegative ..)]; exact Meadow.portions ..) hp' zero_le_one
    apply (TransitM.sorted hF A _ (p.upper h j u hp)).switch; filter_upwards with n; funext i; rw [hz]; unfold Fly.reel; rw [Push.Local.left_sum _ _ _ _ (fun j _=>show Push.Local.Chart P.order (U o j • f n j) _ from ((hN.available n j).smooth _ (i.taps (F.reg j)).live).const_smul (U o j)) i.lengthC]; exact sum_congr rfl fun j hj=> (WilsonStartup.Start.left_mult (f:=f n j) _ _ _).symm

lemma tinted : Notes v P (Beam.marquee (H j) P).reg (fun n=> (chants (H:=H) (χ:=χ) d u n).logRead):=by
   let f n (x:ℕ): Prop:= x∉ Meadow.panel (H n) (u n); let g i:= Meadow.keep (H j) (pennant (H j) i).2
   have he n i:(chants (H:=H) d u n (χ:=χ)).logRead i= if f n i then (plusone (H n) (helm (H:=H) n) χ (d n)).logRead i else 0:=by unfold f chants; rw [Meadow.compass]; simp_rw [Meadow.petaled,ite_not]
   have hF': (fun n=> (chants (H:=H) d u n (χ:=χ)).logRead)=(fun n i=> if f n i then (plusone (H n) (helm (H:=H) n) χ (d n)).logRead i else 0):= funext fun i=> funext fun n=> he i n
   rw [hF']; exact (p.armory h j P hP ht d hf hC).slides f g (fun i=> (p.upper h j u hp i).mono fun n he=> propext ((not_congr he).trans not_not))
lemma psy : Transit v (fun n i (V:Config G c)=> (chants (H:=H) d u n (χ:=χ)).hardRead i V):=p.stars h j P hP ht d

omit hp hf hP ht hC j h p
end Choir
end YM.UVExtension.Wren

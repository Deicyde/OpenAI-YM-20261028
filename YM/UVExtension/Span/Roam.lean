import YM.UVExtension.Span.Egis
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Span
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
namespace Score
open Oriented Vine Concerted
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Score v T H k l χ A b u B N r d f' V Z)
variable {t:κ→Bool→ι}(h:∀ b,Tendsto (fun n=> t n b) qq v)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {τ:κ→ E} {Y:κ→ E→ Config G c}
variable {F:Forest S.ratio} {M:κ→ Hat G F}
-- states use explicit
variable (he:∀ᶠ i in qq,Mode (Y i) (τ i) k u)(hK:∀ᶠ i in qq,(M i).legal s ∧ Y i (τ i)=(M i).bill)
variable (qV:StableR v R)
variable (Δ:κ→Directions G f) -- actual held displacement at test. no norm when prices all Compass later
open Silica Flux WithLp MeasureTheory
/-- coordinate fitting `β` stage. gives movement charts from own Hat. x,b assumed; no manifest needed. -/
def rent {P: Tube G S}(β:ℝ)(X: Coat (c:=c) (f:=f) P F)(v:Directions G f): Air f G:= -- P unknown
     WithLp.toLp 2 (stand ((gStep β)⁻¹ • (v-voltage X)))
lemma rent_bill {P:Tube G S}(β:ℝ)(X:Coat (G:=G) P F) (h:0<β)(v:Directions G f): worldZ X β (rent β X v)=v:=by
   unfold worldZ; rw [show atmos X (rent β X v)= (gStep β)⁻¹ • (v-voltage X) from rfl, smul_inv_smul₀ (show gStep β≠0 from (inv_pos.mpr (Real.sqrt_pos.mpr h)).ne')]; abel

def Abide (s:ℝ) (χ:Chi) (u:ℝ)(T:ι→Tube G S)(M:κ→ Hat G F)(t:κ→Bool→ι):= fun i b=> (M i).order (T (t i b)) s χ u
def prize (s:ℝ) (χ:Chi)(u:ℝ)(T:ι→ Tube G S)(R:ι→ Rep G f)(M:κ→ Hat G F)(t:κ→Bool→ι)(Δ:κ→ Directions G f) : κ→Bool→ Air f G:=fun i b=> rent (R (t i b)).beta (Abide s χ u T M t i b) (Δ i)
include p h he hK
lemma rights : ∀ᶠ n in qq,∀ b,
   let X:= (Abide s χ U.K T M t n b); let W:= prize s χ U.K T R M t Δ n b; let P:=(R (t n b)).beta; Clutch X W U.a P d (τ n) k (Y n) (fun v=> steer X A (Δ n) (Y n v)) (fun v=>course X A P W (Y n v)):=by
   filter_upwards [hK,he] with n hK he b X W P
   let K:= p.realm; have g:= H (t n b); have h':0<P:= g.laws.intake.positive; have hp:= (K.granted c f S _ (R (t n b)) _ g (p.rails _) rfl).2 E (Y n) F X (τ n) rfl rfl rfl hK.1 hK.2 he
   have ht : worldZ X (R (t n b)).beta W=Δ n:= rent_bill P X h' _
   have hh:= hp.2 W; simp only [ht] at hh; exact hh.1
variable (hx : ∃ r:ℝ,∀ᶠ i in qq,‖Δ i‖≤r)
include hx
lemma windsT : Walt qq τ k (fun n b i=> steer (Abide s χ U.K T M t n b) A (Δ n) (Y n i)):=by
   obtain ⟨r,hr⟩:= hx; apply Walt.assemble; intro i; apply Walt.twin (d+r) 1
   filter_upwards [hr,rights p h he hK Δ] with n hn hz; let P:= (hz true); let X:=(Abide s χ U.K T M t n true)
   have hX: ‖steer X A (Δ n) (Y n (τ n)) i‖≤r:= by rw [show steer X A _ _= _ from (show steer X _ _ _=Δ n from P.unseat.trans (rent_bill (R (t n true)).beta X (H (t n true)|>.laws.intake.positive) (Δ n)))]; exact (norm_le_pi_norm (Δ n) i).trans hn
   exact ⟨P.budded i hX,rfl⟩
section
omit hx he hK [FiniteDimensional ℝ E]
include qV
lemma betP : Together qq (fun i b=>gStep (R (t i b)).beta) ∧ Together qq (fun i b=> (gStep (R (t i b)).beta)⁻¹):=by
   rcases eq_or_ne qq ⊥ with h|h'
   · exact ⟨⟨⟨0,by simp [h]⟩,by rw [h]; exact tendsto_bot⟩,⟨⟨0,by simp [h]⟩,by rw [h]; exact tendsto_bot⟩⟩
   haveI : NeBot qq:=⟨h'⟩
   obtain ⟨a₀,hA⟩:=qV.beta
   have hV b: Tendsto (fun i=>(R (t i b)).beta) qq (𝓝 a₀):= hA.comp (h b)
   have hpL i: betaF G s S.patch.L/2 ≤ (R i).beta:= (H i).laws.intake.window.1
   obtain ⟨i,hi⟩:= (hV true|>.eventually_le_const (lt_add_one a₀)).exists
   have hx:0 < a₀:=lt_of_lt_of_le (half_pos (zero_lt_one.trans (H (t i true)|>.laws.intake.height))) (ge_of_tendsto (hV true) (Eventually.of_forall fun i=> hpL _))
   have hZ b:Tendsto (fun n=>gStep (R (t n b)).beta) qq (𝓝 (gStep a₀)) := (hV b).sqrt.inv₀ (Real.sqrt_pos_of_pos hx|>.ne')
   exact ⟨pairsHere _ _ hZ,pairsHere _ _ fun b=>(hZ b).inv₀ (by unfold gStep; positivity)⟩
end
include qV
private def toJet (G:Gauge)(c:Side): Directions G c →L[ℝ] Air c G:= LinearMap.toContinuousLinearMap (show Directions G c→ₗ[ℝ] Air c G from { toFun:=fun v=> WithLp.toLp 2 (stand v),map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl})
lemma sailsW : Walt qq τ k (fun n b y=> course (Abide s χ U.K T M t n b) A (R (t n b)).beta (prize s χ U.K T R M t Δ n b) (Y n y)):=by
    unfold course prize; simp_rw [rent_bill (R (t _ _)).beta _ (H _|>.laws.intake.positive)]; exact ((Walt.stamp (betP p h qV|>.2)).pay ((windsT p h he hK Δ hx).minus (pulses p h he hK))).leaf (toJet G _)
lemma fundsW : Together qq (prize s χ U.K T R M t Δ):= (sailsW p h he hK qV Δ hx).atProbe.shimmy ((rights p h he hK Δ).mono fun i hi=> funext fun b=> (hi b).birth)
end Score
end YM.UVExtension.Span

import YM.UVExtension.Wet.Pdr
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wet
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady PhysicalNext.Repeat Lotus
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Strata Strata.Polish Matrix MeasureTheory WithLp Shield
open Span Oriented Vine
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Span.Score v T H k l χ A b u B N r d f' V Z)
open Polar Silica Shield Score Flux Matter
variable {D : (i:ι)→ Lotus.Leaf (R i)} (hz:Constant (v:=v) D)
variable [NeBot v](hu:0≤u)(qV:StableR v R)
variable {t:κ→Bool→ι}(h:∀ b,Tendsto (fun n=> t n b) qq v)[qq.IsCountablyGenerated]
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {τ:κ→ E} {Y:κ→ E→ Config G c}
variable {F:Forest S.ratio} (M:κ→ Hat G F)
variable (he:∀ i,Mode (Y i) (τ i) k u)(hK:∀ i,(M i).legal s ∧ Y i (τ i)=(M i).bill)
variable (V':Air f G→ℝ)(P:ι→ Molecule S→ℝ)(hV: Roast (D:=D) (v:=v) (H:=H) (χ:=χ) (k:=k) (u:=u) (A:=A) V' P)
include hV hz h he hK qV p hu
lemma bough (B':Finset (Bond f))(L:Molecule S)(hh:∀ i b, Healthy (temp s) ((H (t i b)).unionP L) (Y i (τ i))) : Walt qq τ k (fun n b y=> ∫ i: (F.Slice G × Air f G), (D (t n b)).carat B' (Abide s χ U.K T M t n b) (Y n y) A Q.table L w U.a Q.halo i ∂((F.order G).prod (Abide s χ U.K T M t n b).dice)):=by
    let X i b:= Abide s χ U.K T M t i b; let μ i b:=(F.order G).prod (X i b).dice
    let g n b y:= (D (t n b)).carat B' (X n b) (Y n y) A Q.table L w U.a Q.halo
    have hp n b : Meristem (g n b) (τ n) (μ n b) k:=(D (t n b)).boosts (X n b) L (H _) rfl (hK n|>.1) B' ((p.realm.granted _ _ _ (T (t n b)) _ _ (H _) (p.rails _) rfl).2 E _ F (X n b) (τ n) rfl rfl rfl (hK n|>.1) (hK n|>.2) (he n)|>.1) p.realm.bay (by change 8*U.a*Pressure.fiery G s S.patch.L≤ A/2; rw [(H (t n b)).laws.data.funds.length_eq]; exact p.realm.foot)|>.1
    refine ⟨Eventually.of_forall fun n b=>(hp n b).calls.1,fun i hi=>?_⟩
    let v0 i b:=X i b; let fF n b:= shiftV (R:=R) (t n b) (v0 n b) (JetF (g n b) i (τ n));
    let P' := (F.order G).prod (volume : Measure (Air f G)); obtain ⟨d,hd,hr⟩:= hV.receipt.tills
    have hQ(n b):= pedals p (t n b) (X n b) rfl rfl (hK n|>.1) _ ((hp n b).calls.2 i hi).1
    have h : Together qq (fun n b=>∫ i,fF n b i ∂P'):=by
       refine oars (μ:=P') (f:=fF) (g:=fun i:F.Slice G × Air f G=> d * V' i.2) (hV.employs.comp_snd _|>.const_mul _) (eventually_all.mpr (fun b=>(h b).eventually (hV.uv.and hr)|>.mono fun j hj=>?_)) (ae_of_all _ (fun v=>Constant.motes p hz h M he hK qV hu B' L v i hi))
       refine ⟨(hQ j b).1,ae_of_all _ fun i'=>?_⟩
       have hh:=hh j b; rw [hK j|>.2] at hh
       exact ((hj.1 _ (X j b) rfl rfl (hK j|>.1) rfl L).2 E (τ j) _ (hK j|>.2) hh (he j) B' i hi i').trans (mul_le_mul_of_nonneg_right (budget_single hj.2 L) (hV.positive _))
    refine h.shimmy (Eventually.of_forall fun n=>funext fun b=> (((hp n b).calls.2 i hi).2.trans (hQ n b).2).symm)
omit he hK [FiniteDimensional ℝ E] in
lemma keeps (hm:∀ i,(M i).legal s) (L:Molecule S)(J:κ→Finset ℕ): Together qq (fun i b=> (D (t i b)).tithe (Abide s χ U.K T M t i b) (J i) w U.a Q.table Q.halo L):=by
    let μ:=(F.order G).prod (volume (α:=Air f G)); let X i b:= Abide s χ U.K T M t i b; let fF n b:= (D (t n b)).into (X n b) w U.a Q.table (J n) Q.halo L; let g n b:=shiftV (R:=R) (t n b) (X n b) (fF n b)
    obtain ⟨d,hd,hr⟩:= hV.receipt.tills; have hQ(i b):= pedals p (t i b) (X i b) rfl rfl (hm i) _ ((D (t i b)).tip (X i b) (J i) (H _) rfl (hm i) L|>.2.1)
    have he: Together qq (fun n b=>∫ i,g n b i ∂μ):=by
       refine oars (μ:=μ) (f:=g) (g:=fun i:F.Slice G×Air f G=> d * V' i.2) (hV.employs.comp_snd _|>.const_mul _) (eventually_all.mpr (fun b=>(h b).eventually (hV.uv.and hr)|>.mono fun j hj=> ⟨(hQ j b).1,ae_of_all _ fun i=>?_⟩)) (ae_of_all _ (fun x=> Constant.poles p hz h M qV hu hm L J x))
       exact ((hj.1 _ (X j b) rfl rfl (hm j) rfl L).1 (J j) _).trans (mul_le_mul_of_nonneg_right (budget_single hj.2 L) (hV.positive _))
    exact he.shimmy (Eventually.of_forall fun n=>funext fun b=>(hQ n b).2.symm)
end YM.UVExtension.Wet

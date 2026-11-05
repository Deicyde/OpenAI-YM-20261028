import YM.RemainderComparison.Herbal.Fount
import YM.RemainderComparison.Portal.Crests
/-!
 # Orbit portability and Pan proof. Accepts RG02 coefficient match J as is.
 Include precision polynomial costs at current Setup & k.
 Use on finite subquery Receipt. R LIVES at actual fine trajectory even on AUX.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Herbal
open Function Filter Metric Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token Aux Portal Merge Palette Cascade Lyric Lotus Marker Next.Rank.Glyph Next.Rank.Exponential
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {r j n k N m : ℕ} {Z σ C D W A v u d e t a c' B' c₀:ℝ}
variable {c f : Side} {S : StepData c f} {ι : Type} {α : Type}
variable {T : Tube G S} {F : Forest S.ratio} {Θ : ChartRatio G} {k': S.Choices} (ρ:Bid.Dir G c→AxisChart G F) (B V:BudgetPoint) (β:ℝ)
local notation "Xs"=> Positions (Uniform.Primary c G)
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "θ"=> Lapis.orbit F ρ
local notation "v'"=> eaves G L t
local notation "A'"=> Access.apron G L t
local notation "D'"=> wick G L d t
local notation "e'"=> furl G L t
local notation "g₁"=> gStep β
variable {x:Positions (Uniform.Primary c G)} {K:KernelChoices} {O:Teller G} {R:Rep G f}
lemma cottage (h:Weather T F Θ k' ρ B β d t a W u C K O k x L)(hl:j≤k): Weather T F Θ k' ρ B β d t a W u C K O j x L:=by
   refine {h with paint:={h.paint with core:={h.paint.core with curve:=fun _ hx=>(h.paint.core.curve _ hx).smaller (by omega),color:=fun z v x hz hv hy he=>?_,gram:=fun x hx=>⟨(h.paint.core.gram x hx).1,(h.paint.core.gram x hx).2.smaller hl⟩}}}
   have hp:= h.paint.core.color z v x hz hv hy he; exact ⟨hp.1.smaller (by omega),hp.2.smaller hl⟩

-- RG02+03 input & report ledgers. Aura rents this into the PUBLIC epochs
structure Airstrip {G:Gauge}(L:Side)(K:KernelChoices)(d a:ℝ) (w p q f:ℝ→ℝ) (j r n k N m:ℕ)(Z:ℝ) (C D B' A:ℝ→ℝ) (t:ℝ):Prop where
    income {c f':Side} {S:StepData c f'} {T: Tube G S} {F: Forest S.ratio} {k':S.Choices} {ρ:Bid.Dir G c→ AxisChart G F}
      {O:Teller G} {Q: ConnectedActivityE6.Target G O} {R:Rep G f'} {B V:BudgetPoint} (ι α:Type)[Fintype ι] (i:modes ι)(P:Eden f' G α)(M:ι→Leaf R)(L':ι→Eden f' G α) (H:Eden c G α)
      (hx:P.Culture N k B.threshold (fineCost G k Z) (f t) 1)(hM:∀ i,(L' i).Culture N k B.threshold (fineCost G k Z) (f t) 0)(hH:H.Culture N k V.threshold (outerCost G k Z) (f t) 0)(ht:Fintype.card ι≤ m) (z c₀ C₂:ℝ) (Φ:Config G c→ℝ) (hv:∀ U∈ Boulevard.sunny V,Portal.ideal (T:=T) (R:=R) V Φ i U+chronos c₀ i=H.groups R.beta U)
      (hw: ∀ y:Positions (Uniform.Primary c G), ‖y‖ ≤ z →Arc.route G R.beta y∈ Boulevard.sunny V→ Weather T F Q.table k' ρ B R.beta d t a (w t) (p t) (q t) K O k y L)
      (hc:∀ y:Positions (Uniform.Primary c G), ‖y‖ ≤ z→ Arc.route G R.beta y∈ Boulevard.sunny V →JMatch (Portal.offer (Q:=Q) (T:=T) k' ρ (vista ρ P M L') r i) (aria F ρ H) y r j C₂):
       Pan (R:=R) (Q:=Q) (T:=T) V (thicket B P M L' S) k' ρ B (vista ρ P M L') z (C t) (D t) n r j (wick G L d t) (A t) (furl G L t) (B' t) (Access.apron G L t) (p t) (stomp N n m) i Φ c₀ C₂ (aria F ρ H)

lemma compile (G:Gauge)(hp:0 < a)(hy:0<d)(L:Side)(K:KernelChoices)(w p q f:ℝ→ℝ) (h:Bolt G L w) (hP:Reserve G L p)(hq:Reserve G L q)(hf:Reserve G L f)
    (j r n k N m:ℕ)(hj:j+(r+1)+r+2≤ n)(hx:n+N≤k)(hb:PaintSupply G k Z) :
    ∃ C D B A:ℝ→ℝ, Reserve G L C∧ Reserve G L D∧ Reserve G L B ∧ Reserve G L A ∧ ∀ᶠ t in atTop,Airstrip (G:=G) L K d a w p q f j r n k N m Z C D B A t:=by
   obtain ⟨b,hB,hA⟩:= Brush.compact (s:=Set.Icc (-1:ℝ) 1) (k:=n) (f:=Real.exp) isCompact_Icc fun i _=> Real.contDiff_exp.contDiffAt
   let A t:=halberd G L n N t d (p t) (f t) (q t); let B t:=halberd G L (j+(r+1)) N t d (p t) (f t) (q t)
   have hB': Reserve G L B:= halberd_growth hP hf hq ..; let W t:= lightYear (A t) b n m; let C₀ t:= nightYear (N*fort G L N t (f t)) m
   have hW : Reserve G L W:= lightBudget _ _ _ (halberd_growth hP hf hq ..)
   have hC' : Reserve G L C₀:= nightBudget _ ((Reserve.const (N:ℝ)).mul (fortBudget hf _))
   obtain ⟨C,hC,H⟩:= Aux.horizon G L K hp hy w q p W C₀ h hq hP hW hC'.rate hj (stomp N n m)
   refine ⟨C,W,B,C₀,hC,hW,hB',hC',?_⟩; filter_upwards [paidGrit n N hP hf hq d,afforded p q hP hq d,H] with t ht hb' HY
   constructor; intro c f' S T F k' ρ O Q R B₀ V ι α _ i P M L' H hX hM hH hι y c₀ C₂ Φ hv hw hc
   constructor; intro x hx' hx₀
   have hA':= hw x hx' hx₀; have hβ:= lane T B₀ hA'.feed hA'.patch; have he:=hb' R.beta hβ
   have hz:=(cottage ρ B₀ R.beta hA' (show n ≤ k by omega)) -- edit
   have hL i:= symphonic ρ B₀ P M L' hA' he hx (show 1≤n by omega) hX hM hb ht.1 (ht.2 R.beta hβ) hA hι i
   exact ⟨HY c f' S T F _ k' ρ B₀ R.beta x O hz _ _ (hL (quiet ι)) (fun y _=> origin ρ B₀ P M L' hX y),hL, fellows F ρ B₀ V H Φ i hH hv hA' he hb (show j+(r+1)+N≤ k by omega) hx₀,hc x hx' hx₀⟩
end YM.RemainderComparison.Herbal

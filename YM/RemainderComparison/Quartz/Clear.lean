import YM.RemainderComparison.Musicology.Grounded
import YM.Extension.UV.Station.Delta
/-!
 # Stationary lead of uncut Aux. Nonempty instance of Φ.
 Surface: not claiming this suffice RG02/03 model at order ≥2.
 Foil equality at analytic input sector and bare root F.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Quartz
open Function Filter Metric Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token Aux Portal Merge Palette Cascade Lyric Lotus Marker Next.Rank.Glyph Next.Rank.Exponential
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {r j n k N m : ℕ} {Z σ C D W A v u d e t a c' B' c₀:ℝ}
variable {c f : Side} {S : StepData c f} {ι : Type} {α : Type}
variable {T : Tube G S} (F : Forest S.ratio) {Θ : ChartRatio G} (k': S.Choices) (ρ:Bid.Dir G c→AxisChart G F) (B V:BudgetPoint) (β:ℝ)
local notation "Xs"=> Positions (Uniform.Primary c G)
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "θ"=> Lapis.orbit F ρ
local notation "v'"=> eaves G L t
local notation "A'"=> Access.apron G L t
local notation "D'"=> wick G L d t
local notation "g"=> gStep β
variable {x:Positions (Uniform.Primary c G)} {K:KernelChoices} {O:Teller G} {R:Rep G f}
open Herbal
-- match API accepts Auth Hut. S topology same step threshold.
variable (h: ClassicalMatch F T.high T.low T.up T.down ρ)
variable (he:T.down.Bounds T.low σ C D)
open YM.WilsonStartup.Change
-- p=0 full projection at ANY x and both derivative conventions. ties to SELF formal P.As. WeightY correlation. E.Prec.Control Legacy erased at GLOBAL Affect.
def prism (c:Side)(P:PathData G)(m:Clip) : Eden c G Unit:=⟨{()},fun _=> 0,fun _=> 2,fun _ U=> - Herbal.center P m U ⟩
local notation "Ψ"=> Quartz.prism c T.down T.low
local notation "V₀"=> Extension.UV.LoopRate.Q' c T.low T.down
include h he
variable (tΘ : ChartRatio G) -- Θ
lemma authentic (x : Xs) : - Aux.drafting T F tΘ k' ρ (0,x)=Herbal.aria F ρ Ψ (0,x):= by
    let C:=T.low; let S:= T.down; let V:=V₀; let M x:= mainTerm T.low T.down (Precision.represent (x:Bid.Dir G c)); let Φ x:=tested F k' T.high T.up x (ρ x)
    let E':ℝ×Xs→Bid.Dir G c:=fun x=> tint G _ (x.1 • x.2)
    let F':=(Lapis.table F k' T.up T.high) ∘ nod F ρ; let K:=Quartz.prism c T.down T.low
    let P x:=(Herbal.center T.down T.low) (Herbal.sail F (Aux.nod F ρ x)); let Z:ℝ×Xs:= (0,x)
    have hV : F'=Φ ∘ E':= by funext x; change Lapis.table F k' T.up T.high (nod F ρ x) = _; unfold Aux.nod Germ.usage Germ.kite Lantern.visit; simp only [smul_zero,add_zero]; rfl -- adjust
    have hs : P= V ∘ E':= funext fun y=>rfl -- def proof? sail
    have hx:E' Z=0:=by simp [E',Z]
    have hQ : Matches 2 Φ M 0:=⟨(h 0 (by omega) k').1,(h 0 (by omega) k').2.1,fun i hi=> (h i (by omega) k').2.2⟩
    have ht:Matches 2 M V 0:= (Extension.UV.LoopRate.rooted T.down T.low ⟨_,_,_,he⟩).1
    have hb : Matches 2 F' P Z:= by rw [hV,hs]; exact  (show Matches 2 Φ V (E' Z) from hx.symm ▸ hQ.trans ht) |>.comp_refl (by exact (tint G _).contDiff.contDiffAt.comp Z (contDiffAt_fst.smul contDiffAt_snd)) -- notation test
    have hn:nod F ρ Z=nod F ρ 0:= by simp [Z,nod,usage,Lantern.visit,kite]
    have hh : Trace.pending (-P) 1 Z = -Trace.pending F' 1 Z:=by
       have hh : iteratedFDeriv ℝ 2 (-P) Z = - iteratedFDeriv ℝ 2 F' Z:=by rw [iteratedFDeriv_neg_apply,hb.jets 2 le_rfl]
       unfold Trace.pending; simp_rw [← smul_neg,← intervalIntegral.integral_neg]; congr 1; apply intervalIntegral.integral_congr; intro i hi; unfold Trace.toll Trace.plain; rw [show (i*Z.1,Z.2)=Z by simp [Z]]; change _ • (iteratedFDeriv ℝ 2 (-P) Z) _ = -_; rw [hh]; simp [Z] -- Z simp wrong
    unfold Herbal.aria Aux.drafting
    change - (Trace.pending F' 1 Z + (Lapis.mist _ _ _ (nod F ρ Z)-_) + _) = (∑ i∈({()} : Finset Unit),Herbal.poet F ρ K i Z 0)
    rw [hn,sub_self,zero_smul,sub_self,add_zero,add_zero,sum_singleton]
    change _= (0:ℝ)^0 • Trace.pending (-P) 1 Z; rw [pow_zero,one_smul,hh] -- def promote/sail
-- field rank orientation matter.
open Musicology Funk
variable (Q:ConnectedActivityE6.Target G O)
variable (u:α)(N:ℕ)
local notation "Ψ'"=> Portal.offer (Q:=Q) (T:=T) k' ρ
local notation "V'"=> Typeface.brand Musicology.valley u (R:=Pane.virgin T B β)
local notation "M₀"=> Next.Rank.Glyph.quiet Void
local notation "P'"=> Musicology.barren f G Unit
local notation "W₀"=> Herbal.vista ρ P' V' Musicology.dust M₀
include h he
lemma peal (hp: 0≤v)(x:Xs) : JMatch (Ψ' (Herbal.vista ρ P' V' Musicology.dust) N M₀) (Herbal.aria F ρ Ψ) x 0 j v:= by
    refine ⟨fun i hi=>?_⟩; have hp':i=0:= Nat.eq_zero_of_le_zero hi; subst i
    refine ((Brush.certified zero_le_one (x:=x) (0:ℝ)).climb (by rw [norm_zero]; exact hp) le_rfl).shimmy ?_; filter_upwards with i
    have he' : ∀ z:Poll.Body (Precision.Key F G),W₀ (0,i) z=1:=by intro z; exact Herbal.origin _ B _ _ _ (Musicology.grows (c:=f) B (fineCost G 0 0) 0 0 (le_refl 0)) i z -- test
    have hD:= Aux.model_anchor T F Q.table k' ρ W₀ N i he'
    unfold Trace.coefficient Trace.plain; simp only [Nat.factorial_zero,Nat.cast_one,inv_one,one_smul,iteratedFDeriv_zero_apply]
    simp only [Portal.offer]; change Aux.trial T F Q.table k' ρ W₀ N (0,i) - _=0 -- if equal not rfl
    rw [Aux.trial,Pi.sub_apply,Function.comp_apply,hD,Real.log_one,zero_sub, authentic F k' ρ h he,sub_self]
end YM.RemainderComparison.Quartz

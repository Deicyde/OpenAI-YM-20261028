import YM.RemainderComparison.Cadence.Melody
import YM.RemainderComparison.Cadence.Beat
/-! # pure Ω jets authorized. Payment set cash PRE.Trace coefficients.Still seed/far.Finn.Casts. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cadence
open Function Filter Metric Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token Aux Portal Herbal
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {r j n k N m : ℕ} {Z σ C D σ' C' D' W A v u d e t a c' B' c₀:ℝ}
variable {c f : Side} {S : StepData c f} {ι : Type} {α : Type*}
variable (T : Tube G S) (F : Forest S.ratio) {U₀:Teller G}(Q:ConnectedActivityE6.Target G U₀) (k': S.Choices) (ρ:Bid.Dir G c→AxisChart G F)
local notation "Xs"=> Positions (Uniform.Primary c G)
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "θ"=> Lapis.orbit F ρ
local notation "Θ"=> Q.table
local notation "f₀"=> Lapis.table F k' T.up T.high
variable (α₀ : α)(α₁ :ℝ) (B:BudgetPoint)(β:ℝ)
variable (hP:T.up.Bounds T.high σ C D)(hQ:T.down.Bounds T.low σ' C' D')
    (hc:Critical F T.high T.up ρ) (hG:G.Simple)
    (he:S.patch.Branches S.kernel G) (h₀:0<a)(hgap:PriceGap F T.high T.up a)
    (hp:ClassicalMatch F T.high T.low T.up T.down ρ)
variable (x:Positions (Uniform.Primary c G))
local notation "XsF"=> Lapis.gram F T.up T.high ρ k'
variable {T' M γ κ C₁ :ℝ}(hM:1≤ M)(hX:(Fintype.card (Uniform.Primary c G):ℝ) ≤ M) (hs:(Fintype.card (Site c):ℝ)≤ M)
   (H':FiniteBound F T.up T.down T.high T.low α₁ Q.table ρ T' γ κ) (hg:0<T')(hK: 0≤κ)
variable {A' :ℝ}(h : Aux.Pilot T F Q.table k' ρ B β W u v A' C₁ n x)
open Marker Next.Rank.Glyph Next.Rank.Exponential
open Musicology Cascade Lyric Mosaic Lobby Merge Palette Lotus
local notation "V₀"=> barren f G (Fin 3)
local notation "J₀"=> Musicology.Void
local notation "N₀"=> Musicology.valley
local notation "R₀"=> Pane.virgin T B β
local notation "M₀"=> Typeface.brand N₀ α₀ (R:= R₀)
local notation "P₀"=> Herbal.vista ρ V₀ M₀ dust
local notation "Y₀"=> Y
local notation "y"=> (quiet J₀)
local notation "L'"=> Germ.primary f₀ (mist F Θ T.up) θ XsF
def wealth :ℝ:= Germ.warrant ((XsF) 0)⁻¹ (L') 2 0
local notation "gV"=> wealth T F Q k' ρ
local notation "q" => tollS M 2 (Shellac.sailAmt M G*(T'*κ*Real.exp (-γ*c.val)))
lemma emptied {R:Rep G f} [Fintype ι] (M:ι→Lotus.Leaf R)(Lp:ι→ Herbal.Eden f G (Fin 3)) : Herbal.vista ρ V₀ M Lp (Next.Rank.Glyph.quiet ι) = fun _ _=>1:=by
    let Y':= Tickets.none (Palette.sign M S)
    have he:Y'∈ Herbal.grotto M S (Next.Rank.Glyph.quiet ι):=mem_filter.mpr ⟨mem_univ _,rfl⟩
    have hv:grotto M S (Next.Rank.Glyph.quiet ι)={Y'}:= Finset.eq_singleton_iff_unique_mem.mpr ⟨he, fun j hj=>Finset.card_le_one.mp (grove M _) _ hj _ he⟩
    funext i j; unfold Herbal.vista; rw [hv,Finset.sum_singleton]; simp [dawn,barren,Eden.proofE,Y',Tickets.none]
lemma vacant : P₀ y = fun _ _=>1:=by
    exact emptied F ρ M₀ dust
lemma offered [Fintype ι] (W:modes ι→ℝ×Xs→Y→ℝ): Portal.offer (T:=T) (Q:=Q) k' ρ W r (Next.Rank.Glyph.quiet ι)=trial T F Q.table k' ρ (W (Next.Rank.Glyph.quiet ι)) r := by funext j; simp [Portal.offer]

include h
variable (hf:2 ≤ n)
include hf
omit hf h in
lemma tide : Aux.model T F Θ k' ρ (P₀ y) 2=Germ.early ((XsF) 0)⁻¹ (L') 2:= by unfold Aux.model; rw [vacant]; unfold combo; dsimp only []; simp_rw [smul_eq_mul,mul_one]

def oxygen (n:ℕ)(c M D₀ W:ℝ):= Lantern.clump n (Germ.canopy n D₀ 1 W+ Germ.canopy n 1 1 (W+1)) (Glade.exAllowance n)* Germ.lump ((n+2)*n) (c/2)⁻¹ M
lemma pesos (hk:(Fintype.card (Precision.Key F G):ℝ) ≤ d) : ‖gV‖ ≤ oxygen n A' d W C₁:=by
    obtain ⟨v,-,hV⟩:= Glade.earnings h.core (by omega) 1 zero_lt_one
    exact Germ.care ((XsF) 0)⁻¹ hV ((h.core.gram 0 (norm_zero.trans_lt h.core.pos)).1.inv.posSemidef) h.inverse hk 0 (by simp) (show 0+2 ≤ n by omega)|>.bound
include hP hQ hc hG he h₀ hgap hp H' hg hK hM hX hs
lemma perishing (p:Xs)(hR: ‖p‖ ≤ e): JMatch (Portal.offer (T:=T) (Q:=Q) k' ρ P₀ 2 y) (Herbal.aria F ρ (sprigs T.down T.low α₁ (gV))) p 2 j (quota e (q) j):=by
    let L := Germ.early ((XsF) 0)⁻¹ (L') 2; let D:= (L')
    have he' :0<(A'/2)⁻¹ := by have hh:= h.gap; positivity
    have hm : (Portal.offer (T:=T) (Q:=Q) k' ρ P₀ 2 y)= Real.log ∘ L - drafting T F Θ k' ρ := by
        calc
            _ = Aux.trial T F Θ k' ρ (P₀ y) 2:= offered T F Q k' ρ P₀
            _ = _:= by rw [Aux.trial,tide]
    rw [hm]; apply visibility T F Q.table k' ρ α₁ hP hQ hc hG Q.table_exists he h₀ hgap hp h.core hM hX hs H' hg hK (gV) _ _ p hR
    intro p; have hk:= song h.core h.inverse he' hf p; refine ⟨hk.left.of_le le_top,fun i hi=>?_⟩; unfold Trace.coefficient Trace.plain; congr 1; exact DFunLike.congr_fun (hk.jets i hi) _
end YM.RemainderComparison.Cadence

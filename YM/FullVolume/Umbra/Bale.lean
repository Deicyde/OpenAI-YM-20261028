import YM.FullVolume.Panel.Hangar
import YM.FullVolume.Umbra.Belles
import YM.FullVolume.Rank.Mesa
-- one real mark among any two epoch carpets at the same stamp
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
namespace Umbra
open Lotus
open Draft
variable {Υ:ℕ→ Draft F G} {V:ℕ→ Config G c} {M:Bank}(I:Depot Q o x μ L C₀ K) (T:Depot Q o x μ L C₀ H)(R:∀ n, Station M Chi.canonical (I n) j)(P':∀ n,Station M Chi.canonical (T n) j)
variable {F₀:BatchK K} {F₁:BatchK H}{δ δ':ℕ→ Molecule S→ℝ}{Δ Δ':ℕ} (h:Seats I (F₀:=F₀) (χ:=Chi.canonical) (M:=M) (j:=j) δ Δ) (hq: Seats T (F₀:=F₁) (χ:=Chi.canonical) (M:=M) (j:=j) δ' Δ') {k:Wing}(hm:Rhyme F₀ F₁ k)(hM:Mirror K H)(hJ:(J:Filter ℕ)≤ atTop) (m:Molecule S)
open Blush Mallow Daisy Charity FullVolume.Paint
variable {B:BudgetPoint}
variable (M':∀ i,Cloud (K i).kin) (Y:∀ i,Cloud (H i).kin) (s:ℝ)(hs:0<s) (x':Site c) {b₁ b₂:Wing}
-- format issue with two sheets after Mint solved via scaling. keep separate
variable (hk: Rhyme (fun i=>(M' i).live) (fun i=>(Y i).live) k)(hK: Rhyme (fun i=>(M' i).pale) (fun i=>(Y i).pale) k)
set_option quotPrecheck false
section readings
lemma ballast (p:(I 0).fragrances)(hh:Rhyme (fun i=>(M' i).live) (fun i=>(Y i).live) k)(i:ℕ): Charity.locus (Y i|>.live) (T i) x' p= Charity.locus (M' 0|>.live) (I 0) x' p:=by unfold Charity.locus speaks; rw [hh.left.met,hh.right.met];rfl
end readings
local notation "U₀"=>fun n=> Blush.fields (I n) (M' n) s
local notation "U₁"=>fun n=> Blush.fields (T n) (Y n) s
-- Cash cast Sonia.
include hs in
lemma sensed {u:ℕ}(he:∀ p,B.Regular (Blush.scope (I u) (M' u) x' p) (U₀ u p))(z:(I 0).fragrances):
   B.Regular (Charity.locus (M' u).live (I u) x' z) (matin (M' u).live (I u) z Chi.canonical) ∧ B.Regular (Charity.locus (M' u).pale (I u) x' z) (matin (M' u).pale (I u) z Chi.canonical):=by
    let T':=Blush.pane (I u) (M' u) (s:ℂ) z; let Z:= Charity.locus (M' u).live (I u) x' z; let R:= (M' u)
    have hh:B.Regular Z T':=by have hv:=he (Blush.enter (I u) z); unfold Blush.scope Blush.fields at hv; dsimp only at hv; rw [(Blush.enter (I u)).injective.extend_apply,stuffed] at hv; exact hv
    rw [← Blush.arches]
    let Z':= Complex.ofReal s
    let f₀ x:= (T' x); have h₀ : (↑(s⁻¹):ℂ) * ↑s=1:=by rw [Complex.ofReal_inv]; exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hs.ne')
    let f(y:ℕ):Fin 1→Prop:=fun _=>True
    let F':=( (s:ℂ))⁻¹ • T'; have he':F'= (Complex.ofReal ∘ matin R.live (I u) z Chi.canonical)+ Complex.I • (Complex.ofReal ∘ matin R.pale (I u) z Chi.canonical):=inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr hs.ne') _
    have hf:B.Regular Z F':= Next.Foundations.regular_smul _ hh
    constructor
    · have hx:=Graces.readings Complex.reCLM hf -- reads
      rw [he'] at hx -- simp
      convert hx using 1
      ext i; simp [Function.comp_apply,R]
    have hx:=Graces.readings Complex.imCLM hf
    rw [he'] at hx; convert hx using 1; ext i; simp [Function.comp_apply,R]
section chi
include I T M' Y s hs hk hK R P' hM
variable (h₁:Sweep K)(h₂:Sweep H)
include h₁ h₂
lemma spanV (hT:B.threshold=Pressure.temp x)(hS:B.order≤ j) (hf:∀ n i,B.Regular (Blush.scope (I n) (M' n) 0 i) (U₀ n i))(hy:∀ n i,B.Regular (Blush.scope (T n) (Y n) 0 i) (U₁ n i))(he:∀ i,(0:Site c)∈Blush.scope (I 0) (M' 0) 0 i) : let S'0:=Blush.scope (I 0) (M' 0) 0; (∀ n,Blush.scope (I n) (M' n) 0=S'0) ∧ (∀ n,Blush.scope (T n) (Y n) 0=S'0) ∧ SeatE U₀ U₁ B S'0:=by
    intro x; let E:= fun i:(I 0).fragrances=> Charity.locus (M' 0).live (I 0) 0 i
    let D:= Blush.enter (I 0); have hz(u): x (D u)=E u:= D.injective.extend_apply ..
    let A i:RegularAddress c:= ⟨0,E i, hz i ▸ (he (D i))⟩
    obtain ⟨Δ,v,hv⟩:= spout I R h₁ hk.left; obtain ⟨Δ',q,hq⟩:= spout T P' h₂ hk.right; obtain ⟨G',u,hU⟩:= spout I R h₁ hK.left; obtain ⟨E',w,hW⟩:= spout T P' h₂ hK.right
    have hE n i: Charity.locus (M' n).live (I n) 0 i=E i:= flagL I R i 0 hk.left; have hF n i: Charity.locus (Y n).live (T n) 0 i= E i:=flagV I T R P' hv hq hk i 0 n
    have hl n : Blush.scope (I n) (M' n) 0=x:=by unfold x Blush.scope; rw [funext (hE n)];rfl
    have hp n : Blush.scope (T n) (Y n) 0=x:=by unfold Blush.scope; rw [funext (hF n)];rfl
    have hE₁ n i: Charity.locus (M' n).pale (I n) 0 i=E i:= (Blush.arches (I n) (M' n) 0 i).symm.trans (hE n i); have hF₁ n i: Charity.locus (Y n).pale (T n) 0 i=E i:= (Blush.arches (T n) (Y n) 0 i).symm.trans (hF n i)
    have hy₁(n:ℕ)(i:(I 0).fragrances):= sensed I M' s hs 0 (hf n) i; have hy₂(n:ℕ)(i:(I 0).fragrances):= sensed T Y s hs 0 (hy n) i
    have he := swan I T R P' hv hq hk hM h₁ h₂ 0 A hT hS (fun _=> rfl) (fun n i=> show B.Regular (E i) _ from hE n i ▸ (hy₁ n i).1) (fun n i=> show B.Regular (E i) _ from hF n i ▸ (hy₂ n i).1)
    have hw := swan I T R P' hU hW hK hM h₁ h₂ 0 A hT hS (fun i=> (hE₁ 0 i).symm) (fun n i=> show B.Regular (E i) _ from hE₁ n i ▸ (hy₁ n i).2) (fun n i=> show B.Regular (E i) _ from hF₁ n i ▸ (hy₂ n i).2)
    have h₀ := SeatE.castC he (s:=E) (fun _=>rfl) (fun _=>rfl); have h₁:= SeatE.castC hw (s:=E) (fun _=>rfl) (fun _=>rfl)
    have ht:= (SeatE.sum h₀ (h₁.scaler Complex.I)|>.scaler (s:ℂ)).extendsE x D hz
    exact ⟨hl,hp,ht⟩ -- defeq trust
end chi
end Umbra
end YM.ConnectedActivityE6.Lim

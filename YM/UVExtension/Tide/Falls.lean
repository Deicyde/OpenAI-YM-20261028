import YM.UVExtension.Tide.Petal
import YM.UVExtension.Harvest.Barn
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Tide
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Pier MergeProof.Ribbons
open Source Labels Gale Mast MergeProof Cells GridApprox Accent Extra.Histories
open Swell Stock Harvest
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {Q:Factor A} {S: Uses Q hG} {C:ℕ→ℝ}{w:Bid.Worth}{R: Bandage Q C w} {t:ℕ→ℕ}(L:Cellar S t R)
    (N n m k d:ℕ) {a:ℝ}(ha:0<a)(hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a)
open Cellar Gale.Circuit
local notation "T"=> A.B.a.S
local notation "φ"=> A.B.a
local notation "P"=> A.B.a.budget m
local notation "R0"=> desk a ha
local notation "ℍ"=> Row a
set_option quotPrecheck false
local notation "V0"=> Cellar.yard (roseA S) L
variable (I:ℕ→ℕ)(H':Harvest.Barn S R I L)(hK:Mix.paidL (Cellar.yard (roseA S) L))
local notation "x!"=> ((frames G).level d).Coeff
-- prevent costly defEq comparing furrows
local notation "n₀"=> n
local notation "s0"=> Tabs.chosen A.B.a 1 H'.tithe
private lemma wname (x j m d:ℕ)(K:Keys S)(y:ℝ) : expense (V0) y j m d= expense (L.yard K) y j m d:= by
   -- directly via Mix args structure. avoid full delta path
   let h(k:Levels G)(C:ℝ):= (k.S.a j/k.S.a m)^4 * Vac.treasury k m+6-Real.log C
   show h (φ) (plumR (V0) d y m)= h (φ) (plumR (L.yard K) d y m); refine congr_arg (h (φ)) (?_) -- furnish plasmR via ad hoc. cost
   let C (p: Levels G):= p.S.a m ^ d*(p.clock.hatCoupling m ^ (2*winter G d) / (y*(p.params m).columns * ∏ j∈ Finset.range m,(p.params (j+1)).columns)); exact (show plumR (V0) d y m=C (φ) from rfl).trans (show plumR (yard K L) d y m=C (φ) from rfl).symm
def len (G:Gauge)(d:ℕ) := (((localSection G d).stencil).sup fun x => Finset.univ.sup fun i=>(x i).natAbs)+4
include H' hK
set_option quotPrecheck false
lemma slips (d:ℕ)(x:((frames G).level d).Coeff): ∃ b:ℝ,4≤b∧ ∀ᶠ j in atTop,∀ k : ℕ,∀ hk:j ≤ k,b*(A.B.a.S.scale j) ≤ A.B.a.S.scale k → ∃ hY:t d ≤ k, GridApprox.room A.B.a j k (len G d) ∧ ∀ N (hN:k < N) (W:Circuit S d N n R L a) (u: Keys S), ((u N n).val:ℂ)∈ball 0 a→
     let h:= yard u L; let Y:= fetch S d N n R L W x k hY ((u N n).val:ℂ)
     let f:= h.O N n (d:=d) x 0; let F:= science h k N n d Y; let T':= tilesAt A.B.a.S n (show j≤N from hk.trans hN.le)
     Interior (T'.chamber 0) f ∧ Interior (window (0:Site (A.B.a.S.side k n)) (len G d)) F ∧ T'.rootTest (h.beta N n) f ≤ expS (φ|>.S) (d+1) j ∧ T'.rootTest (h.beta N n) (backTo h.path N n hN.le F-f) ≤ expS (φ|>.S) (-1/16) k :=by
    let F:= V0; let B:=H'.tithe
    let y:=((frames G).level d).coeffSize x+1; have hy:0<y:= add_pos_of_nonneg_of_pos (WilsonStartup.Mark.coeff_nn _) zero_lt_one
    obtain ⟨b,h₁,h₀⟩:= peony hG F B d x; refine ⟨b,h₁,?_⟩
    filter_upwards [eventually_ge_atTop (t d),h₀,ocean A.B.a (len G d), F.S.divergent.eventually_gt_atTop 0, coastwise F d y hy B hG hK zero_lt_one] with j hj h hr hB ht k hk he
    let P':= F.S; let z:= s0 j; have hL:t d ≤ k:= hj.trans hk; have hS :GridApprox.room A.B.a j k (len G d):= hr k hk ((mul_le_mul_of_nonneg_right h₁ hB.le).trans he)
    refine ⟨hL,hS,fun N hN W u hx=>?_⟩; intro C' Y' f F' T'; have H:= (H'.sponsors u).2.1; obtain ⟨h₂,w,hv,hG₀,heE⟩:=h k hk he; have hK: Tabs.opens A.B.a 1 j z:=Tabs.opened ..; have hQ:t d ≤ z:= hj.trans hK.1
    have hm : GridApprox.room C'.path.levels j k (lensScope C' d):=by
       let S':= (localSection G d); let v:=(S'.stencil.sup fun x => Finset.univ.sup (fun i=>(x i).natAbs))+4
       exact (show GridApprox.room (φ) j k v from hS)
    have hs (U: ((frames G).level d).Coeff) := clearance C' d N k j n (intakeV u L) hk hN.le hm U
    let f':= Real.exp (1/8*((T).scale k-(T).scale z)); have hg : w*‖(((T).a z:ℂ)^d)⁻¹‖*(4*(1+(A.B.a.params k).columns)/f') ≤ Bandage.fly A.B.a d z/2:=hG₀
    have hT:= W.cadent S d N n R L u hx k I H B z j hK hQ h₂ w hv hm hg x hN hs
    refine ⟨hs x,?_,?_, ?_⟩
    · exact hT.1
    swap; · apply hT.2.trans; let q:=Real.exp (((T).a j/(T).a z)^4* Vac.treasury (φ) z+5); exact (show 2*Real.exp (Work.D01.columnLogs A.B.a k)*((frames G).level d).coeffSize x*(q/w) ≤ expS (T) (-1/16) k from heE)
    let W₁:= Vintage.YM.MergeProof.Accent.tent C' N z j n d x y hy B (intakeV u L) H.1 H.2 hK hj (lt_of_le_of_lt h₂ hN) (le_add_of_nonneg_right zero_le_one)
    apply W₁.trans; apply Real.exp_monotone; change expense C' y j z d≤(d+1:ℝ)*(T).scale j
    exact ((wname L 0 j z d u y).symm).trans_le ht
end YM.UVExtension.Tide

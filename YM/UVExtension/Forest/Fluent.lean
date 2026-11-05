import YM.UVExtension.Forest.Views
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{Q:Roost.Factor A} (S:Uses Q hG) (v:Keys S) {C:ℕ→ℝ}{W:Bid.Worth}(R:Legato.Bandage Q C W)
    (d m N n:ℕ)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T'"=> (Orchard.Path S v).levels
local notation "π"=> localSection G d
local notation "O!"=> hol G
open Metric Wet Wren
variable {V:Org.Bolt A}(a:Upland.Arc Q S V)
variable (x:Rose S)(hv : Tendsto (fun i=>(v i n).val) atTop (𝓝 x.val))
local notation "K'"=> A.B.a.budget m
open Steady Planned.GuardedAtom Guard Roads.Unum Wet.MarketP
variable {ι:Type}{w:Filter ι} [w.NeBot][w.IsCountablyGenerated](t:ι→ ℕ)(ht:Tendsto t w atTop)
variable (hh: cashr (A:=A) w t m)(hq:cashr (A:=A) w t (m+1))
variable (hm:∀ i,m<t i)
local notation "x'"=> fun i=> v (t i) n
local notation "g'"=> fun i=> S.realBeat ((x' i).val) (t i) n
local notation "b"=> fun i=> S.realBeat ((x' i).val) (t i) n (m+1)
local notation "gL"=> fun i=> slots0 S (t i) m n (x' i) (hm i)
local notation "N₁"=> A.B.a.S.side (m+1) n
local notation "N₀"=> A.B.a.S.side m n
local notation "shearsD"=> fun i=> slots1 S (t i) m n (x' i) (hm i)
local notation "W'"=> fun i=> (ray S (t i) n m (x' i) (hm i)).body
local notation "gM"=> fun i=> Keeper.sufficient (gL i)
local notation "F"=> (frames G).level d
variable (Z:(i:ι)→Blush.Cloud (S.realBeat ((v (t i) n).val) (t i) n (m+1))) (hD:Wet.Constant (v:=w) (fun i=>(Z i).live))(hC:Wet.Constant (v:=w) (fun i=>(Z i).pale))
    (hd:d+3 ≤ A.B.a.clock.J m)
local notation "L"=> fun i=> tide S R d (t i) m n (x' i)
local notation "κ"=> Real.sqrt (A.B.a.clock.forcedAllowance (m+1))
local notation "Ψ"=> Doors.rate (A.B.a.S.block m)
local notation "Γ"=> Eyelet.Cow G N₁ (A.B.a.budget (m+1)) d (hol G)
variable (he:(1+2*(A.B.a.params m).columns)*Doors.rate (A.B.a.S.block m) ≤ Bid.barunit (A.B.a.S.block m))
include hv ht hh hq he a hd hm
lemma floatsIn (g:ι→Γ){xg:Γ}(hx:Tendsto g w (𝓝 xg))(i:Option (F).Index) : ∃ y,Tendsto (fun k=>L k|>.rain (g k) i) w (𝓝 y):=by -- x' notation shadows!!
    have hf(k):=ting S v R d (t k) m n (hm k) hd he; let T:= L
    have hp(k) : Counts (T k) Ψ:=by obtain ⟨v,hV,h⟩:=(hf k).1.efforts; exact hV.counts
    have hη: 0<Ψ:= Doors.rate_pos _
    have hA(i j): (T i).route = (T j).route := (Waged.route (dons S v R d m n t hm hd i)).trans (show cart (R:=b i) _=(T j).route from (Waged.route (dons S v R d m n t hm hd j)).symm) -- likely defeq?
    apply tempest hp hA _ _ (pivotW S v R d m n a x hv t ht hh hq hm hd he) hx i
    · intro i z; let u:= Eyelet.fee (A.B.a.budget (m+1)) i.1.val; have he : (u:ℂ)≠0:= by exact_mod_cast (toll_pos _ i.1.val).ne'
      apply Knot.cordial (twig (tin d (hol G) i.1 _)) u he (steams _) (fun n=>T n|>.glass i) hη _ (firstly S v R d m n a x hv t ht hh hq hm hd i)
      intro n X; obtain ⟨hl,hK,hF⟩:=(hp n).glass i X; exact Rainfall.Wallet.leans ⟨by simpa only [sub_zero] using hl,hK,hF⟩
    intro i z; let u:=Eyelet.fee (A.B.a.budget (m+1)) i.val.1 / κ; have hz: (u:ℂ)≠0:=by exact_mod_cast (div_pos (toll_pos ..) (glyphBound ..|>.1)).ne'
    apply Knot.cordial (twig (sink (G:=G) _ i)) u hz (steams _) (fun n=>T n|>.wing i) hη _ (nymph S v R d m n a x hv t ht hh hq hm hd i)
    intro n X; obtain ⟨hl,hK,hF⟩:=(hp n).wing i X; exact Rainfall.Wallet.leans ⟨by simpa only [sub_zero] using hl,hK,hF⟩
omit ht hh hq hm
lemma curbstone : Lacing.Course (fun i=> tide S R d i m n (v i n)):=by
    constructor; intro g i hg; obtain ⟨X,hg⟩:=hg; obtain ⟨k,hK⟩:= Roads.Unum.tier a.fields m; obtain ⟨h,hH⟩:= Roads.Unum.tier a.fields (m+1); let j:= k+h+m+1; let t(n:ℕ) := n+j; have ht:Tendsto t atTop atTop := tendsto_atTop_mono (f:=id) (g:=_) (fun _=> Nat.le_add_right ..) tendsto_id
    have hm(i):m < t i:= by unfold t j; omega
    obtain ⟨Z,hZ⟩:= floatsIn S v R d m n a x hv t ht (hK _ _ t ht (fun i=>(hm i).le) (by unfold t j; omega)) (hH _ _ t ht hm (by unfold t j; omega)) hm hd he _ (hg.comp ht) i
    exact ⟨Z,(by rw [← tendsto_add_atTop_iff_nat j]; exact hZ)⟩
end YM.UVExtension.Mast

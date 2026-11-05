import YM.UVExtension.Mast.Ladder
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
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "O!"=> hol G
local notation "V!"=> Voice F H n
local notation "μ!"=> Music F H N n
local notation "sT"=> Legato.Bandage.waybill (A.B.a)

open Eyelet
variable {L:∀ i:ℕ,ℕ → Lacing.Banner («H»:=A.B.a) ((frames G).level d) (p:=n) (A:=hol G) i} {r:ℕ}{u c w a:ℕ→ℝ}
variable (hp:d+3≤ A.B.a.clock.J r)(hx:∀ i:ℕ,r ≤ i→Ability S d n R i (L i) (u i) (c i) (w i) (a i) (a (i+1)) v)


namespace Lyrics
open Motion
variable {S v d N n}
    {V :Extra.Histories.Music ((frames G).level d) (Orchard.Path S v) N n} (hV:Lyrics S v (W:=W) d N n r (fun i _=> L i N) V)
local notation "pr"=> terrain H N n O!
def Vista (i:ℕ) : Card (F) («H»:=A.B.a) (p:=n) (A:=hol G) i:= if he: r ≤ i∧i ≤ N then IsLinearMap.mk' (terrain H N n O! i (V.tone i)) (hV.incomeX i he.1 he.2) else 0
lemma takes (i:ℕ)(hr:r ≤ i)(he:i ≤ N) (v:(F).Coeff) : Vista hV i v= terrain H N n O! i (V.tone i) v:=by unfold Vista; rw [dif_pos (And.intro hr he)]; rfl

local notation "zG"=> Size.axis F
lemma spaceF (i:ℕ)(hv:r ≤ i)(hm: i<N) (x:(F).Coeff):
    let s:= V.tone i; let t:= V.tone (i+1); let Z:=hV.Vista (i+1)
    let L':=fun _:Motion=> L i N; let Y':=fun _: Motion=> Z
    let B:= (T'|>.S.side i n); let h:= glaring T' i n
    s.index x= major L' Y' h (t.index x) ∧ Vista hV i (s.index x) =minor L' Y' h (t.index x):=by
   intro s t Z L' Y' B h; let f' := V.tone i; let v0:= t.index x; let μ:= s.index x
   let z:=Lacing.Face H N n O! i s x; have he:= hV.comes i hv hm|>.2.2
   have hh : z.1=s.index x:= (sees ..).trans ((hV.earned.earned _ hv hm.le).currents x)
   have hb: z= ∑ j:Tally (F), chips F v0 j • (sell L' Y' h j) := by
       apply Eq.trans (he x); unfold Lacing.load weaves; apply Finset.sum_congr rfl; intro j _; unfold sell
       -- Φ Alias - Tally d syntactic
       unfold Y' Z L'; simp only [hV.takes (i+1) (hv.trans i.le_succ) hm]; rw [map_smul]; rfl
   have hg : Vista hV i μ= z.2:=by
       rw [takes hV i hv hm.le]; change (Lacing.Face H N n O! i s (s.index.symm μ)).2= _; rw [show s.index.symm μ=x from (s.index.symm_apply_apply x)]
   rw [hg,← hh,hb,(pieces L' Y' h v0).1,(pieces L' Y' h v0).2]; simp_rw [Prod.fst_sum,Prod.snd_sum]; exact ⟨rfl,rfl⟩
include hx
-- `Uplate` refers Lacing.Tribe; b Blend.E
lemma eqst (i:ℕ)(hv:r ≤ i)(hm:i<N):
    let U:= fun _:Motion=> L i N; let Y:= fun _:Motion=> Vista hV (i+1); let t:=glaring (A.B.a) i n
    (∀ x:(F).Coeff,(V.tone i).index x=steer U Y t ((V.tone (i+1)).index x))∧ Vista hV i=crown U Y t:=by
   intro U Y t
   have hZ: ∀ m x, ‖Y m x‖≤ a (i+1)*(F).coeffSize ((F).core x):= by
       have hq:=hv.trans i.le_succ; intro m x; rw [show Y m x=_ from (takes hV (i+1) hq hm x)]; exact (climbs hV _ hq hm x).trans (mul_le_mul_of_nonneg_right (hx _ hq|>.size) (Work.G08.size_nonneg ..))
   obtain ⟨T,hT,hC⟩:= Tribe.efforts (hx i hv|>.plays N hm);
   let h0(y:Motion): Tips (U y) (A.B.a.S.block i) _ _ _:= hT; have he:=hx i hv|>.owns
   constructor
   · intro x; rw [focal he h0 hC hZ]; exact (hV.spaceF i hv hm x).1
   apply LinearMap.ext; intro x; obtain ⟨x,rfl⟩:=(V.tone i).index.surjective x; obtain ⟨hE,hH⟩:= hV.spaceF i hv hm x; rw [hH]; show _= crown U Y t _; rw [hE]; exact (pilfer he h0 hC hZ t _).symm
end Lyrics
end YM.UVExtension.Mast

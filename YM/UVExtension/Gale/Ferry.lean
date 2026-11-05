import YM.UVExtension.Gale.Mare
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Gale
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard Metric Lamppost Motion Work.G08
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Roost.Factor A}
    (S:Uses X hG) (d N n:ℕ)
variable {a:ℝ}(ha:0 < a)(hp: Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a)
set_option quotPrecheck false
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "n0"=> A.B.a.S.side N n
local notation "D"=> Row a
local notation "T"=> desk a ha
local notation "Z"=>Metric.ball (0:ℂ) a
local notation "W₀"=> A.B.a.clock.forcedAllowance N
local notation "p"=> A.B.a.budget N
local notation "O"=> hol G
local notation "H"=> S.fits N n
open Mast Fitted Tabernacle Dales Rafter
open Mast Cellar
variable {t:ℕ→ℕ}{C:ℕ→ℝ}{w:Bid.Worth}(R:Legato.Bandage X C w)
    (U:Cellar S t R)
local notation "s!"=> A.B.a
local notation "r"=> t d
local notation "Φ"=> Cow G (A.B.a.S.side N n) (A.B.a.budget N) d (hol G)
set_option quotPrecheck false
variable (hN:t d ≤ N)
open Pans Relay
variable (u:ℝ)(v:Keys S)(U₀:ℂ→ Card A.B.a ((frames G).level d) (hol G) n N) (Z1:∀ i:ℕ,ℂ→ Banner A.B.a ((frames G).level d) (hol G) n i)
    (hx:∀ i,t d ≤ i→i<N→Z1 i (u:ℂ)= U.line d n i N (v N n))(he:∀ x,U₀ (↑u:ℂ) x=rise S d N n (v N n) x)
local notation "Pt"=> Orchard.Path S v
local notation "K"=> U.cantors v d n
local notation "V0"=> ((K).song N)
local notation "A!"=> ((K).lyr N hN)
variable {q:ℕ} (hf:t d ≤ q)(h:q < N)(x:((frames G).level d).Index) (T₁:∀ i:ℕ, Solo (frames G|>.level d) (Orchard.Path S v) n i)
    (hT: T₁ q = Relay.pair (Orchard.Path S v) N n ((U.cantors v d n).song N) (Extra.Histories.primary 0 (Size.axis ((frames G).level d) x)) 0)
    (hw:Quired (L:=fun i _=> U.paths S v R d n i N) (Orchard.Path S v) N n (hol G) ((U.cantors v d n).song N) (t d) q T₁ h.le)
local notation "T'"=> shuttle Z1 N U₀ q (u:ℂ) x
local notation "Y'"=> Eyelet.Eye
local notation "f'"=> fire Z1 N U₀
local notation "P₁"=>fun i=>(V0).tone i
local notation "gl"=> fun i:ℕ=> Lacing.photo Pt N n (hol G) i (T₁ i)
include U he hx hN
private lemma page (i:ℕ)(hi:t d ≤ i)(h:i≤ N)(w:(F).Coeff): Face Pt N n O i (P₁ i) ((P₁ i).index.symm w)= (w, f' i (u:ℂ) w):=by
    let Q:= (P₁ i); let v₀:= Q.index.symm w; let L:= (Pt).levels; let hp:=((K).lyr N hN).earned.earned i hi h
    refine Prod.ext (show _= w from ?_) ?_
    · exact (sees ..).trans ((hp.currents v₀).trans (Q.index.apply_symm_apply w))
    rw [makes S d N n R U hN u v U₀ Z1 hx he i hi h]; exact (Lyrics.takes (A!) i hi h w).symm
private lemma shiftIndex (i:ℕ)(hi:t d≤ i)(h:i<N)(w:(F).Coeff): turn Z1 N U₀ i (u:ℂ) ((P₁ (i+1)).index w)= (P₁ i).index w:=by
    have hs:= Pans.sym S v R d n (U.pay v d n) K i N hi h
    have hp:= LinearMap.congr_fun hs w; rw [ties S d N n R U hN u v U₀ Z1 hx he i hi h]; exact (Pans.stalls S v d n K i N).apply_eq_iff_eq_symm_apply.mpr hp

include hf h hT hw
-- glove pinned ALL levels; tone uses mixed path in N. independent.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 840000 in
lemma hip (i:ℕ)(hi:r≤ i)(hp:i≤q): (T' i hp).1= gl i∧ (T' i hp).2= (P₁ i).index (T₁ i|>.a):=by
    have hr(z:ℕ)(h': r≤ z)(hs:z≤N)(w:(F).Coeff):= page S d N n R U hN u v U₀ Z1 hx he z h' hs w
    induction hp using Nat.decreasingInduction with
    | self=> dsimp only; rw [shuttles,hT]
             let Zq:=Size.axis (F) x; let Vx:= Extra.Histories.primary (0:Site ((Pt).S.side q n)) Zq
             let g:=(Pt).rep N n q; let y:= Real.sqrt ((Pt).levels.clock.forcedAllowance q); let S':=(V0).tone q; let p₀:= -S'.index.symm Vx.x
             constructor; swap; · exact (S'.index.apply_symm_apply _).symm
             have hP := q.lt_succ_self; have hm := (A!).earned.earned q hf h.le
             have hv_: Nonempty (Keeper g.p g.activities):=⟨Keeper.sufficient (Vintage.YM.PhysicalNext.Repeat.Graces.Nest.samples hG (housed ..) N q n h.le)⟩
             have hc: Eligible Vx O g y:= ⟨hv_, primary_format _,_, primary_rem _ (Real.sqrt_pos.mpr (forcedPos A.B.a q))⟩
             change cuff Z1 N U₀ q (u:ℂ) x=tracks Pt N n q O (Relay.beside Vx (S'.plays p₀)); rw [Lacing.stanzaP Pt N n O q Vx (S'.plays p₀) hc (show Eligible .. from Eligible.mk hv_ (hm.earns p₀).1 ⟨_,(hm.earns p₀).2⟩), show tracks Pt N n q O Vx=(Zq,0) from ?_]; swap
             · change Eye Vx O g y= _; rw [hc.vistas]; exact Prod.ext rfl (Prod.ext (Eligible.blankC hc).1 (Eligible.blankC hc).2)
             have hz: tracks Pt N n q O (S'.plays p₀)= (-(Size.axis (F) x),fire Z1 N U₀ q (u:ℂ) (- Zq)):= by rw [show p₀=S'.index.symm (-Zq) from (map_neg ..).symm]; exact hr q hi h.le _
             rw [hz]; rfl
    | of_succ i ih IH=>
       have hg := ih.trans h; obtain ⟨h₁,h₂⟩:= IH (hi.trans i.le_succ); let Zp:=Z1 i u; let P':=(V0).tone i; let L:= U.paths S v R d n i N; have hq : L= Zp:= (hx i hi hg).symm
       let Gx:= gl (i+1); let a:= L.rain Gx.2 none; let z:= a.1; let p₀:= P'.index; let b:=(T₁ (i+1)).a; let Vx:= P'.plays (-(p₀.symm z)); let v0:= tracks Pt N n i O Vx
       obtain ⟨h,hQ⟩:=(Quired.aim hw i hi ih).delta
       have he: v0=(-z,fire Z1 N U₀ i (u:ℂ) (-z)) := by unfold v0 Vx; rw [←map_neg]; exact hr i hi hg.le _
       rw [wheels Z1 N U₀ x q i ih (u:ℂ)]; unfold raftS
       change spool _ _ _ _ _ _ = _∧ _=_; dsimp only; rw [h₂,h₁,hQ,show Z1 i (↑u:ℂ) = L from hq.symm]; refine ⟨?_,?_⟩
       · change spool ..= ∑ i:Bool,rooms ((Pt).S.side _ n) F O _ _ (twain a v0 i)
         rw [he]; rfl
       rw [h,map_add]; apply congr_arg₂ (·+·) (shiftIndex S d N n R U hN u v U₀ Z1 hx (by assumption) i hi hg _) ((p₀.apply_symm_apply z).symm)
end YM.UVExtension.Gale

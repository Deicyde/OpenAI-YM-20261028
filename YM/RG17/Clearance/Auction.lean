import YM.RG17.Feather
import YM.RG17.Clearance.Payment

/-! Adapt `Feather.factorShipFlex17` adding a slot for another post-L/pre-Bar purchase. Use before choosing Run; retain Dense/Mantle and other alignment witnesses on this actual construction. No comparison to different Run constructors. Here buy `Payment` at that port. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent

open ClearanceR
-- Slot for further costs after PostCost, permitting gradual strengthening. Replaying the ctor.
structure CustodyR (G:Gauge) where
   items {M:Metals G} {D:Rolls M.p} (P:PostCost D) (y:ℕ→ℝ) (w:Bid.Worth) {u:ℝ}
      (q:Luna.Tableau u 300) (a:Levels G) : Prop
   buys {M:Metals G} {D:Rolls M.p} (P:PostCost D) (y:ℕ→ℝ) (w:Bid.Worth) {u:ℝ}
      (q:Luna.Tableau u 300) {T:Protection D} (U:Delays T) : ∃ V, DelayLe U V ∧
          ∀ W, DelayLe V W → ∀ (B:Bar W) (Y:Wait B) (a:Levels G), Paid Y a → items P y w q a

def CustodyR.minted (G:Gauge) : CustodyR G :=
   ⟨fun {_ _} P _ _ {_} _ a=> Mine a P.g ∧ ∀ m, Deposit a m,fun {_ _} P _ _ {_} _ {_} U=> by
     obtain ⟨V,hV,h⟩:= mine_delay P U
     obtain ⟨X,hX,hY⟩:= deposits_delay V
     exact ⟨X,hV.trans hX,fun W hw b y a ha=>⟨h W (hX.trans hw) b y a ha,hY W hw b y a ha⟩⟩⟩
variable (hG:G.Simple)
include hG
theorem factorAuctionR (ℋ:CustodyR G) {β:ℝ} (h:0<β) : ∃ (M:Metals G)(P:Rolls M.p)(A:Alloy M P)(X:Factor A)(Y:ℕ→ℝ)(K:Bid.Worth)(b:Bandage X Y K),
    Stationary.Artes.Cadre A.post A.B.kin ∧ Next.Free.Amplify A.B.M ∧ Jams.Wild X.shape A.delay ∧ A.B.a.clock.kernel.penalty=β ∧ Flick A.B.a ∧ Ahead b (fun _=>1) ∧ Mallow.AccordV X.shape (fun _=>1) A.delay ∧ OPE.HaloGate A.B.a ∧ Unlatched b (fun _=>1) (fun T t S _ => let Z := Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; ∃ h:Z.Makes, SharpGram.Dense.Coverage Z h) ∧ ∃ ξ t τ a, ∃ (V:Roof.Lyrics X t t), Muse.Plato V ξ a a τ ∧ ∃ θ1:Luna.Tableau ξ 300, ℋ.items A.post Y K θ1 A.B.a ∧ Jams.PaysW X.shape a A.delay ∧ Luna.Spire θ1 X.shape (Luna.costP M.p P) A.delay ∧ (∀ i:ℕ,100 ≤ (A.B.a.budget i).supportExponent) ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) ∧ ∃ UX,FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 UX P.L ∧ Mallow.Canyon ξ X.shape Y θ1 UX A.delay := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G β h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨q,hq⟩:=Muse.concert.exists
  obtain ⟨θ1⟩:= Luna.Tableau.access 300 (show 1≤q by linarith [hq.1])
  let a':ℝ:= 1/1024; have hh:0<a':=by norm_num [a'];
  obtain ⟨t,ht,hu,hU⟩:=Jams.ball_on (q:=q) (s:=a') (r:=1) (by linarith [hq.1]) hh (by norm_num [a']) (by norm_num)
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= freakFare17 hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) θ1 hU hE
  have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [H.jets]; exact (le_max_right ..).trans (he.k i)) tendsto_id
  obtain ⟨R,hR⟩:= Pert.Dense.bulletin s (ThroughLaunch.raging s T) ho
  obtain ⟨O⟩:= Next.Rank.exists_budget G
  let M:=ThroughLaunch.bountyV s T (l⊔R)
  obtain ⟨⟨P⟩,H⟩:= hK (l⊔R) le_sup_left
  have hz : Pert.Dense.Relay M.p M.K R:=by
     obtain ⟨b,F,ψ,he,v⟩:= hR.bulletin
     refine ⟨b,F,ψ,he,v.same,?_,?_,?_⟩
     · intro i; exact ⟨(v.buys i).1,(v.buys i).2⟩
     · intro i; exact ⟨(v.shops i).1⟩
     intro i d j;exact v.lifts i d j
  have hUQ :∀ i,R i ≤ (P.L i).val:=fun i=>(le_sup_right (a:=l) (b:=R) i).trans (P.large i).need
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩
  obtain ⟨Ugate,-,hgate⟩ := OPE.halo_delay U
  obtain ⟨Us1,hS1,hstep⟩:= flickDelay Ugate
  obtain ⟨Ustep,hS2,hCustody⟩:= ℋ.buys F Y K θ1 Us1
  have hStep:= hS1.trans hS2
  obtain ⟨V,h₁,hK⟩:= hH Q J₀ Ustep
  obtain ⟨V',H',Hp'⟩:=Tent.quotes V hh
  obtain ⟨Vx,hx,hV⟩:=Muse.header hG V' hh q
  obtain ⟨D,-⟩:= Bar.exists_above Vx 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y0,-,H⟩:= hK Vx (H'.trans hx) D I
  let W0 : Wait D:= ⟨fun _ => 0,SharpGram.Dense.slim D,SharpGram.Dense.slimWindow hG D,0⟩
  obtain ⟨W2,_,hSlim,WP,hWP⟩ := Pert.Dense.slim_wait_for M.K O (Next.Foundations.chart G) W0 hG hz hUQ (Next.Foundations.chart_ok G) rfl
  obtain ⟨Y,hYT,hLate⟩:= SharpGram.Dense.loadBoth hG Y0 W2
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,hU⟩:= H Y hYT.ready hYT.range hYT.minL a ha hp
  obtain ⟨hA,hC,hM,hη,hW,hL,hU',hE,hR,hCσ,hPΩ,U₁,HΩ,hYe,hYv,hY₁,hYs,hAr⟩:=W
  have ht':= Hp' Vx hx
  obtain ⟨p,hh'⟩:= Tent.verses R ht' hR hE
  refine ⟨_,_,_,_,_,_,c,hCσ,hPΩ,hYs,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hstep Vx (hS2.trans (h₁.trans (H'.trans hx))) _ _ B.a B.valid,hU,hAr,hgate Vx (hStep.trans (h₁.trans (H'.trans hx))) Y B.a B.valid, ?_, q,t,a',a',p,⟨hL,hU',by norm_num [a', FullVolume.Amp.glint],hq, ht', hR,hB.symm ▸ hV Vx (DelayLe.refl _) D Y a ha,by norm_num [a', FullVolume.Amp.glint],hh',hG, Drifting.pay B.valid⟩,θ1,hCustody Vx (h₁.trans (H'.trans hx)) _ _ B.a B.valid,U₁,HΩ,hYe,hYv,hY₁⟩
  intro t u S v Xf K C hx hp ht
  obtain ⟨hX,hq,hπ,hv,hS,hn,hL',-⟩:= hU t u S v Xf K hx hp ht; refine ⟨hX,hq,hπ,hv,hS,hn,hL',?_⟩
  obtain ⟨hC,hM,hA,hS,hL₀,S',hA,hC,h₃⟩:= hX.reception
  exact ⟨hM,SharpGram.Dense.covered M.K O (Next.Foundations.chart G) WP hWP hSlim hLate B.valid S' hC hM (Next.Rank.East.enclosing Xf hX.freight hM)⟩

end YM.PhysicalNext.Repeat.Legato
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set MeasureTheory Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash FullVolume
open YM.MergeProof MergeProof.Accent
open Muse
namespace Campaign
set_option quotPrecheck false
open Boutique
section
variable {M : Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:ℕ→ℝ}{K:Bid.Worth}{b:Bandage X Y K}
/- Construction independent of p sampling. k>=1. later reserve may request hard-limit recipe. -/
lemma pillarAuctionR (ℋ:CustodyR G) (h:G.Simple){q:ℕ→ℕ}(hh:Ahead b q) (hQ:Mallow.AccordV X.shape q A.delay)(hU:Unlatched b q (fun T t S _ => let Z := Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; ∃ h:Z.Makes, SharpGram.Dense.Coverage Z h)){c u t τ:ℝ}{L: Roof.Lyrics X u u}(Φ:Muse.Plato L c t t τ) (hP : Stationary.Artes.Cadre A.post A.B.kin)(he : Next.Free.Amplify A.B.M)(hy:Jams.Wild X.shape A.delay)(θ1:Luna.Tableau c 300) (v:ℕ→ℕ→ℝ)(hcR:ℋ.items A.post Y K θ1 A.B.a)(hν:Jams.PaysW X.shape t A.delay)(hΩ:Luna.Spire θ1 X.shape (Luna.costP M.p P) A.delay)(hPγ:FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 v P.L) (hv:∀ i:ℕ,100 ≤ (A.B.a.budget i).supportExponent)(hψ:∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) (hG:Mallow.Canyon c X.shape Y θ1 v A.delay):∃ (R:Run G)(T:Campaign R), Locrian R∧ Jams.Wild R.kit.shape R.alloy.delay ∧ Nonempty (Pillars R T)  ∧ R.family.path.levels=A.B.a ∧ Mallow.AccordV R.kit.shape R.Q R.alloy.delay ∧ SharpGram.Dense.Coverage R.family R.makes ∧ ∃ Θ, ℋ.items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Sky R T Θ v :=by
    let C:=b
    choose s hp using fun d:ℕ=> ((eventually_ge_atTop 1).and (A.B.a.fits.deep.eventually_ge_atTop (d+3))).exists
    have hb (d): 1 ≤ s d:= hp d|>.1
    obtain ⟨T,⟨Z⟩,hD⟩:= FullVolume.rodB X Φ
    let ht(d):d+3 ≤ (Issue.trail T).levels.clock.J (s d):= hp d|>.2
    have hZ:=Z.receipts
    choose B hB using fun N p m (hm : m < N)=> Boutique.taste h (F₀:=L) hZ (hD N p) hm
    let U (N p:ℕ):Branch X T.history N p 0 := ⟨T.choice,fun i _ hm=> hZ.samples h _ _ _ hm,fun m _ he=> B N p m he⟩ -- dots need explicit
    obtain ⟨V,hC,hY,H⟩:= Bandage.coming h b hZ s ht U; let R : Run G:= ⟨M,P,A,X,Y,K,b,q,hh,T,Z,s,ht,ease U,V,hC,fun N m p hx=> Boutique.mountain T (B N p m hx),hY⟩
    let T':Campaign R:= ⟨c,τ,u,t,L,Φ,hD⟩; obtain ⟨-,-,-,-,-,-,-,z,hz⟩:= hU T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books; exact ⟨R,T',⟨hP,he⟩,hy,⟨hb,U,rfl,fun N p m hm=> hB N p m hm,H⟩,rfl,hQ,hz,θ1,hcR,⟨hv,hψ,hν,hΩ,hPγ,hG⟩⟩
end
theorem operaAuctionR (ℋ:CustodyR G) (h:G.Simple)(w:ℝ)(hw:0<w):∃ (R:Run G)(T:Campaign R), Locrian R∧ Jams.Wild R.kit.shape R.alloy.delay∧ Nonempty (Pillars R T) ∧ R.family.path.levels.clock.kernel.penalty=w ∧ Mallow.AccordV R.kit.shape R.Q R.alloy.delay ∧ OPE.HaloGate R.family.path.levels ∧ SharpGram.Dense.Coverage R.family R.makes ∧ Flick R.family.path.levels ∧ ∃ v:ℕ→ℕ→ℝ, ∃ Θ, ℋ.items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Sky R T Θ v:=by
   obtain ⟨X,P,A,F,L,Q,b,hY,hC,hYs,hW,hFlick,hH,hAr,hGate,hdens,ξ,v,t,a,D,Φ,θ1,hℋ,hν,hφ,hv,hψ,UΩ,hP,hZ⟩ := factorAuctionR h ℋ hw
   obtain ⟨R,T,hx,hp,hb,h,hQ,hc,hγ⟩:= pillarAuctionR ℋ h hH hAr hdens Φ hY hC hYs θ1 UΩ hℋ hν hφ hP hv hψ hZ; rw [← h] at hW hGate hFlick; exact ⟨_,_,hx,hp,hb,hW,hQ,hGate,hc,hFlick,UΩ,hγ⟩

end Campaign
end YM.PhysicalNext.Repeat.Legato

namespace YM.RG17
set_option maxHeartbeats 1200000
open Function Filter YM.PhysicalNext YM.PhysicalNext.Repeat YM.PhysicalNext.Repeat.Legato
open YM.FullVolume YM.FullVolume.Final Extraction Campaign
open scoped Topology BigOperators Classical

/-- Retains Dense Coverage hence also Mantle allocation compatible on ANY such fuse; same Full-volume UV and every-phase joint endpoint with OPE Services and
an ordinary exact OPE Reader, weak leading correlation estimates (as
`FirstExtension`), actual beta limits all fixed levels. Still not
physical Wilson perturbative comparison. Same hierarchy, fields, and
`Pillars`; this selects ONCE on a schedule further paying halos. -/
theorem spreadWithR (G:Gauge) (ℋ:CustodyR G) (h:G.Simple) (δ:ℝ) (hd:0<δ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      R.family.path.levels.clock.kernel.penalty = δ ∧ Flick R.family.path.levels ∧ Jewel R T W ∧ SharpGram.Dense.Coverage R.family R.makes ∧
      (∃ Θ v, ℋ.items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Sky R T Θ v) ∧
      ∀ f : Extraction.Order,
        ∃ (g : Extraction.Order) (S : Table R.family.book)
          (F : Spec.Final R.family (f.refine g) S),
          (Extraction.Order.mk Extraction.Sequence.full (f.refine g).per).Ordered R.family S ∧
          PositionsUV R.family Extraction.Sequence.full ∧
          ∃ (L : YM.EveryPhase.Almanac F) (P:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
              (X:Climb.Scaling S) (B:ℕ→ℝ), YM.EveryPhase.Completed F L ∧
              OPE.Services R.family (f.refine g) S ∧ OPE.Orbits.Foundation F P ∧ Pert.FirstExtension F X ∧
              (∀ m:ℕ,(f.refine g).limits (fun _=>True) (fun N p=>R.family.path.β N p m) (B m)) ∧
              PertExtension.Running.isLimit R.family (f.refine g) B ∧
              ∀ U:Ultrafilter (ℕ×ℕ), (U:Filter _) ≤ (f.refine g).fuse → Nonempty (SharpGram.Lenses.Mantle F (U:Filter _)) := by
   obtain ⟨R,T,hT,hY,⟨W⟩,hP,hV,hG,hCov,hFlick,v,Θ,hℋ,hW⟩:= Campaign.operaAuctionR ℋ h δ hd
   have J:= jewelOf17 T W h hT hY v Θ hW
   have he:= Campaign.opePackage17 W h hV hG hW
   refine ⟨R,T,W,hP,hFlick,J,hCov, ⟨Θ,v,hℋ,hW⟩, fun f=>?_⟩
   obtain ⟨g,B,hB⟩ := PertExtension.Running.extraction R.family J.actual f
   obtain ⟨w,S,F,X,hS,hX⟩:= R.extractible17 h he (f.refine g)
   obtain ⟨L,hL⟩:= EveryPhase.all_characters F
   let t:=F.phase.transport
   obtain ⟨p,hp⟩:= OPE.Prescription.chosen F.room.kernel.laws.toSymmetric t.injection
   let r:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin := ⟨p,hp,F.room.kernel,t.injection,t.rights,t.spots⟩
   have hb m:=Extraction.Order.retained (g:=w) (hB m)
   have hf : f.refine (g.refine w) = (f.refine g).refine w := rfl
   refine ⟨g.refine w, ?_⟩
   rw [hf]
   exact ⟨S,F,from_spec ((f.refine g).refine w) ⟨F⟩ J.fullMesh,J.fullMesh,L,r,X,B,
     hL,hS,OPE.Orbits.produce F r hS,hX,hb,(fun m=> Order.along (hb m)),fun U hl=> SharpGram.Lenses.attains_mantle17 F hS U hl hCov⟩
end YM.RG17


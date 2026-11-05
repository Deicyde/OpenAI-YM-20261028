import YM.RG08.Wisp.Bulb
import YM.RG08.Prism.Glow

/-!
# If rail transform shifts variables at scale g before chart, apply to exactly
   normalized responses, no parity/mixed factor. Can consume only genuine packs
   satisfied at overlap tori by Booth/Centric.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Wisp
open Function Finset Jetty Skiff Forms Steam Glyph Room Cloud Camera Room.Haze Fold Filter Matrix
open scoped BigOperators Topology PowerSeries Classical Matrix ContDiff
set_option backward.isDefEq.respectTransparency false
variable {I U J O Y R T:Type}[Fintype I][Fintype U][Fintype J][Fintype O][Fintype Y][Fintype R][Fintype T]
variable (A:Peak I O R)(B:Peak I Y T)

/-- Construct Rail/Decked explicitly, from the same physical `Bore` accounting
input BEFORE linear heat, exact. Just drilled out from proof of Fold.Peak.ate
without connected restriction. API intended for insertion supply, with
both external alphabets possibly including direction sources.
-/
lemma deck (q:Camera.Strip (Camera.Raw I Y) (Camera.Raw I O))(hq:∀ i,Pace (q i))(h0:Camera.roll q 0=0)(ht: silent q)
   (p:Still (Camera.Raw I O))(v:Still (Camera.Raw I Y))(hp:Pace p)(hv:Pace v)(hp0:p 0=1)(hv0:v 0=1)
   (c:Port (Camera.Raw I O))(d:Port (Camera.Raw I Y))
   (hc:A.toLedger.printed=c+flask (Real.log ∘ p)-liftInn A.K-A.κ)(hd:B.toLedger.printed=d+flask (Real.log ∘ v)-liftInn B.K-B.κ)
   (H:c=belt (rescaleFields q) d)(hg:p=ᶠ[𝓝 0] fun x=>v (Camera.roll q x)* |Peak.rated q x|):∃ r:Rail I O Y,r.h=q∧Nonempty (Rail.Decked A.toLedger B.toLedger r):=by
 have hU:IsUnit (peek q):= by
    apply (isUnit_iff_isUnit_det _).mpr
    rw [isUnit_iff_ne_zero]; intro h;have he:=hg.self_of_nhds;simp only [hp0,h0,hv0,one_mul,Peak.rate_birth,h,abs_zero,one_ne_zero] at he
 have he {E I T:Type}[Fintype E][Fintype I][Fintype T](S:Peak I E T){c:Port (Camera.Raw I E)}{p:Still (Camera.Raw I E)}(h:S.toLedger.printed=c+flask (Real.log ∘ p)-liftInn S.K-S.κ)(hp:p 0=1):
    tap 0 c =heater S.inside E+sink S.outside I:=by
    have hh:=S.toLedger.cold S.orientation
    change PowerSeries.coeff 0 (S.toLedger.printed)=0 at hh
    rw [h,map_sub,map_sub,map_add,S.warm,S.cold] at hh;simp [flask,Camera.print,hp,Fold.platen] at hh
    rw [tap,PowerSeries.coeff_zero_eq_constantCoeff]; exact eq_add_of_sub_eq' (sub_eq_zero.mp hh)
 have hr:=acclimatize ht c c d (he A hc hp0) (he B hd hv0) H
 obtain ⟨r,Hr⟩:=railize hr hU B.mirror B.inverse ht hq h0
 subst Hr
 refine ⟨r,rfl,Nonempty.intro {A.complete B r hr with
    a:=p,b:=v,smoothL:=hp,smoothR:=hv,fixedL:=hp0,fixedR:=hv0,haar:=Peak.rail_treasury r p v hp0 hv0 hg,
    c:=c,d:=d,born:=hc,again:=hd,forward:=H}⟩

open Lattice Exterior Wilson RG Precision Stationary Tack Fold Prism Prism.Drum Bloch Laurent Mount Tree
variable {l:ℕ}

def review (A:Drum I J U)(E:J ⊕ U ≃ R)(V:Grain R)(l:ℕ)(M:GrainS R)(f:Pearl):Port U:=Trickle.mark l (Trickle.mouth (script A E) (Skiff.spin l (press A E) V M 1)) f
lemma scale (P:Drum I J U)(E:J⊕U≃R)(t:U→O)(h:P.Flourishes)(V:Grain R)(M:GrainS R)(he:Eligible V)(hV:waxed V)(f:Pearl):
 pulse (Prism.forges P E t h V he hV).toLedger l M f = belt (fun i:U=>rod (I:=Camera.Raw I O) (.inr (t i))) (review P E V l M f):=by
 let W:I⊕O→ℝ:=fun _=>0
 let U':=Haze.mView (morn P.dark (P.direction h) O) (speak P E t)
 let Z:=Skiff.spin l (press P E) V M 1
 ext n:1; let π(i:U):Camera.Raw I O:= .inr (t i)
 change tap n (Trickle.mark l (Trickle.mouth U' Z) f) = tap n (belt (fun i=>rod (π i)) (Trickle.mark l (Trickle.mouth (script P E) Z) f));rw [Cairn.censor,Trickle.kissed,Trickle.kissed,tap,PowerSeries.coeff_map]
 unfold tap; rw [PowerSeries.coeff_map]
 apply MvPolynomial.funext;intro x; rw [MvPolynomial.eval_rename]
 erw [aim_eval (I:=R) U' x,aim_eval (I:=R) (script P E) (x∘π),mvread P E t h x];rfl

omit [Fintype Y] in
lemma scale_up (P:Drum I J U)(E:J⊕U≃R)(t:U→O)(h:P.Flourishes)(V:Grain R)(M:GrainS R)(he:Eligible V)(hV:waxed V)(f:Pearl)(q:Camera.Raw I O→Port Y):
 belt q (pulse (Prism.forges P E t h V he hV).toLedger l M f)=belt (fun i=>q (.inr (t i))) (review P E V l M f):=by
 rw [scale]
 change ((belt q).comp (belt (fun i:U=>rod (I:=Camera.Raw I O) (.inr (t i))))) _=_;rw [switched];simp_rw [belt_x]

section
variable {G:YM.Gauge}{c f:Side}(S:StepData c f)
variable (F:Forest S.ratio)(A B:Bed){X Y:Type}[Fintype X][Fintype Y]
variable (x:Lines G c 1→X)(y:Lines G c 1→Y)
lemma rooted {Z:ChartRatio G}(W:Bore S F A B x y Z)
    {C:Castle G}(hh:S.patch.Branches S.kernel G)(hs:Mount.Stable C)(hZ:LocalRatio Z)(hc:Proceed C A f)(hv:(grace G S F A B).Flourishes)
    (R P:Skiff.GrainS (Epic S.patch G c))(f':Pearl)
    (heR:Lit l R)(hR:Trickle.Combed R)(heP:Lit l P)(hP:Trickle.Combed P)
    (hF:belt (rescaleFields W.map) (belt (rescaleFields (implant F A B y)) (Trickle.mark l R f'))=belt (rescaleFields (implant F A B x)) (Trickle.mark l P f')):
    let V:=unveil (inlet hh C Z) c; let T:=grace G S F A B; let E:=fir (G:=G) S
    ; belt (fun i:Lines G c 1=>rescaleFields W.map (.inr (y i))) (review T E V l R f')=belt (fun i=>rod (I:=Camera.Raw (Key F G) X) (.inr (x i))) (review T E V l P f'):=by
 intro V T E
 let U:=implant F A B y
 let D:=fun i=>U i ∘ roll W.map
 have he:Steam.Eligible V:=unveiled_eligible _ (inlet_eligible hh Z hs) _;have ht:waxed V:=unsealed_wax (legal_inlet hh Z hs) _
 let H:=forges T E x hv V he ht; let N:=forges T E y hv V he ht
 have hca:H.toLedger.printed=belt (rescaleFields (implant F A B x)) (china hh C)+flask (Real.log ∘ trophy F A B x Z)-liftInn H.K-H.κ:=by
    change belt (fun i:Epic S.patch G c=>liftInn (median (speak T E x) i)) (stock V)=_
    rw [← mode_cash];exact mapped F A B x hh hZ hs hc hv
 have hcb:N.toLedger.printed=belt (rescaleFields (implant F A B y)) (china hh C)+flask (Real.log ∘ trophy F A B y Z)-liftInn N.K-N.κ:=by
    change belt (fun i:Epic S.patch G c=>liftInn (median (speak T E y) i)) (stock V)=_
    rw [← mode_cash];exact mapped F A B y hh hZ hs hc hv
 have ha (i:Epic S.patch G c):Pace (D i):=ContDiffAt.comp (0:_) (g:=U i) (by rw [W.level]; exact uniform F A B y i) (roll_pace W.fine)
 have hg:roll D 0=0:=by change roll U (roll W.map 0)=_;rw [W.level,seated]
 -- build vacuum law W
 have hL:=Mount.blossom S hh hs W.logo W.root (implant F A B x) D (uniform F A B x) ha (seated F A B x) hg W.heritage (fun u=>by
    apply Tack.redress hh u (uniform F A B x) ha (seated F A B x) hg
    filter_upwards [W.heritage] with z hz; obtain ⟨v,h1,h2⟩:=hz;dsimp only
    -- use existing `torch` only private; adapt by reducibility tone & D
    change represent (low S (roll D z))= _ at h1
    change represent (high S (roll D z))= _ at h2
    rw [h1,h2,S.covary hh,S.channel hh];rfl)
 have hk:belt (rescaleFields (implant F A B x)) (china hh C)=belt (rescaleFields W.map) (belt (rescaleFields (implant F A B y)) (china hh C)):=hL.trans ((DFunLike.congr_fun (pluto U W.map (uniform F A B y) W.fine (seated F A B y) W.level) (china hh C)).symm)
 obtain ⟨q,hq,⟨hp⟩⟩:=Wisp.deck H N W.map W.fine W.level W.tags _ _ (trophy_pace F A B x hZ) (trophy_pace F A B y hZ) (trophy_root F A B x hZ) (trophy_root F A B y hZ) _ _ hca hcb hk W.tangle
 have hj:belt q.x (forge N.toLedger (Trickle.mark l R f'))=forge H.toLedger (Trickle.mark l P f'):=by
    rw [Rail.x,hq];unfold implant at hF
    rw [mode_cash,mode_cash] at hF;exact hF
 have heq:= Wisp.journey hp _ _ hj
 rw [←rush _ _ _ _ H.orientation heP hP,←rush _ _ _ _ N.orientation heR hR] at heq
 rw [scale_up,scale] at heq; exact ((show belt (fun i=>rod (I:=Camera.Raw (Key F G) X) (.inr (x i))) _=belt (fun i:Lines G c 1=>q.x (.inr (y i))) _ from heq).symm.trans rfl) |> fun hh=>by rw [Rail.x,hq] at hh;exact hh
end
end YM.RG08.Wisp

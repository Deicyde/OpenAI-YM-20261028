import YM.RG08.Steam.Ballot
import YM.RG08.Necks.Prior
/-! # Hull calculation strict part anchored transfer D,L. Paired sails.
 Distinct absolute+rates. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Necks
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry Steam
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free Atrium
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {G:Gauge}{n m d p l e k c:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{P:Patch}{K:KernelChoices}{I:Type}{L:Jetty.Loom I}{h:0<σ}{A A':Bed}
local notation "E₀"=>Loc G 1
local notation "E"=> Ed G Cover

-- o-root grouping charge/d
def cloud (P:Patch)(g:ℕ)(S:Site P.L→Pack n I):Pack n I:= (((P.L.val:ℝ)^g)/Fintype.card (Site P.L)) • ∑ i,S i
lemma cloud_opt (P:Patch){S S':Site P.L→Pack n I}(g:ℕ)(hd:0≤δ)(he:∀ i,Dyad L d h B δ (S i) (S' i)):Dyad L d h ((P.L.val:ℝ)^g*B) δ (cloud P g S) (cloud P g S'):=by
 let J:=Site P.L; let c:ℝ:=Fintype.card J;have hc:0<c:=Nat.cast_pos.mpr Fintype.card_pos
 let u:ℝ:=P.L.val; have hu:0 ≤ u:=Nat.cast_nonneg _
 have hf:= (Dyad.sum (C:=fun _=>B) univ (fun i _=>he i) hd).smul (u^g/c)
 convert hf using 1 <;> try rfl
 rw [sum_const,card_univ,nsmul_eq_mul,abs_of_nonneg (div_nonneg (pow_nonneg hu _) hc.le)];change u^g*B=u^g /c *(c*B);field_simp
lemma cloud_add (P:Patch)(g:ℕ)(S S':Site P.L→Pack n I):cloud P g (S+S')=cloud P g S+cloud P g S':=by unfold cloud; simp only [Pi.add_apply,sum_add_distrib,smul_add]
lemma cloud_sub (P:Patch)(g:ℕ)(S S':Site P.L→Pack n I):cloud P g (S-S')=cloud P g S-cloud P g S':=by unfold cloud; simp only [Pi.sub_apply,sum_sub_distrib,smul_sub]
lemma cloud_expr (S:GrainS E):Yurt.forecast P K A S p e n=cloud P p (fun o=>ridges P K A o S e n):=by unfold Yurt.forecast;rw [Pi.smul_apply,Pi.smul_apply, Finset.sum_apply,Finset.sum_apply];rfl

-- one step first compiler splitting.
def scene (T:Patch)(K:KernelChoices)(H:T.Branches K G)(A:Bed)(C:Mount.Castle G)(Z:ChartRatio G)(d l:ℕ)(P:GrainS (Ed G Cover))(i k:ℕ):Pack k (Ed G Cover):= cloud T d (fun o=>Necks.brine T K A (Mount.inlet H C Z) l o P i k)
-- inlet namespace
variable {Z:ChartRatio G}{F₀ F₁:Mount.Castle G}{hp:P.Branches K G}
local notation "bet"=> Sepals G P K η W δ A A' (Mount.inlet hp F₀ Z) (Mount.inlet hp F₁ Z)
lemma shrunk (he:bet e)(he':c≤e):bet c:=⟨he.base,he.gift,he.hit,he.hit',he.cut,he.wax,fun i n h=>he.turn i n (by unfold taps at *;omega)⟩
lemma stress_price (n e l:ℕ):∃ J:ℝ→ℝ,Wage J∧∀{G:Gauge}{P:Patch}{K:KernelChoices}{Z:ChartRatio G}{F F':Mount.Castle G}{h:P.Branches K G}{σ η W δ:ℝ}{D d:ℕ}{A A':Bed},
 Sepals G P K η W δ A A' (Mount.inlet h F Z) (Mount.inlet h F' Z) e → ∀{S S':GrainS (Ed G Cover)}(hk:0<η),η≤1→∀{hp:0<σ},η*Carrier.unitStep P.L≤σ→∀{B B':ℝ},0≤B→0≤B'→Folk D l S→Folk D l S'→
 (∀ i r,r≤l+i→(i<e∨i=e∧n<r)→ Dyad (stance _) D hp B δ (S i r) (S' i r))→ (Dyad (stance _) D hp B' δ (S e n) (S' e n))→ ((P.L.val:ℝ)^d≤W) →
 let Y:=Lagoon.bustle P K A F Z h d l S;let O:=Lagoon.bustle P K A' F' Z h d l S'
 let U:=Yurt.forecast P K A S d e n;let U':=Yurt.forecast P K A' S' d e n
 let N:=scene P K h A F Z d l S e n;let N':=scene P K h A' F' Z d l S' e n
 let R:=Yurt.forecast P K A S' d e n
 ; Dyad (stance _) D hk (J W*B') δ U U' ∧ Dyad (stance _) D hk (J W*B) δ N N'∧ Y e n=U+N∧ O e n=U'+N' ∧ U-R=Yurt.forecast P K A (S-S') d e n ∧ Sings (stance _) D hk (R-U') (J W*B'*δ):=by
 obtain ⟨J,hJ,H⟩:=slushy_uniform n e l
 let Y(x:ℝ):= x*(J x+(n+1:ℝ)*Real.exp 16*x^n)
 have hr:=Real.exp_pos (16:ℝ)
 refine ⟨Y,Wage.input.mul (hJ.add (Wage.mul (P:=fun (_:ℝ)=> ((n+1:ℝ)*Real.exp 16)) (Wage.constant _ (by positivity)) (Steam.wagepow n))),?_⟩ -- namespace?
 intro G P K Z F F' h σ η W δ D d A A' he S S' hη hη' hs hσ B B' hB hB' hP hP' hS hv hF y y' u u' z z' x
 have hδ:=he.gift; have hw:=he.base;have hW:0≤W:=zero_le_one.trans hw;have hR:=hJ.nn hw
 let J':=(n+1:ℝ)*Real.exp 16*W^n;have hJ':0≤J':=by unfold J';positivity
 have hh(o:Site P.L):=H (P:=P) he o hη hη' hσ hB hP hP' hS; dsimp only at hh
 let V(o:Site P.L):=ridges P K A o S e n;let V'(o:Site P.L):=ridges P K A o S' e n;let V''(o:Site P.L):=ridges P K A' o S' e n
 have hz(o):=ridges_price (G:=G) he o hη hη' hσ hv
 have h1: u=cloud P d V:=cloud_expr _
 have h2: x=cloud P d V':=cloud_expr _;have h3: u'=cloud P d V'':=cloud_expr _
 have hX: (P.L.val:ℝ)^d*((n+1:ℝ)*(Real.exp 16*B')*W^n)≤ Y W*B':=by
    have ht0: (P.L.val:ℝ)^d*J' ≤ W*(J W+J'):=mul_le_mul hF (le_add_of_nonneg_left hR) hJ' hW
    unfold Y;calc
     _ = (P.L.val:ℝ)^d*J'*B':=by unfold J'; ring
     _ ≤ _:=mul_le_mul_of_nonneg_right ht0 hB'
 have hU: Dyad (stance _) D hη (Y W*B') δ u u':=by rw [h1,h3];exact (cloud_opt P (S:=V) (S':=V'') d hδ hz).mono hX
 have hZ':=(cloud_opt P d hδ (fun o=>(hh o).2)).mono (show (P.L.val:ℝ)^d*(J W*B)≤Y W*B from by unfold Y;nlinarith only [mul_le_mul hF (le_add_of_nonneg_right hJ') hR hW,mul_nonneg hB (show 0≤W*(J W+J')-(P.L.val:ℝ)^d*(J W) by nlinarith only [mul_le_mul hF (le_add_of_nonneg_right hJ') hR hW])]) -- RHS definitional parser  n+1 term type? x
 have hY(o):=ferryPhase P o hv hη hη' hσ
 have hI(o):=hY o|>.near;have hj(o):=hY o|>.far
 have hA {Q:Bed}{C0:Mount.Castle G}(U:GrainS (Ed G Cover))(hK:Skiff.Parade (stance _) (stance _) η (flare _ _ η) (Steam.repeatLine (Prism.rains P K (G:=G) Q) n) (fun _=>W)) (hY:∀ o,Lyrics (steeped P o (U e n))∧Sings (stance _) D hη (steeped P o (U e n)) (Real.exp 16*B'))
       (hu:∀ (o:Site P.L), let R:=shaker l (Prism.ice P K Q) (Mount.inlet h C0 Z) (Weald.plank P o (flow P.L o U)) 1 e n
                            ; Lyrics R∧ Sings (stance _) D hη R (J W*B)):
  Lagoon.bustle P K Q C0 Z h d l U e n=Yurt.forecast P K Q U d e n+scene P K h Q C0 Z d l U e n:=by
   unfold Lagoon.bustle Yurt.forecast scene cloud; simp only [Pi.smul_apply, Finset.sum_apply,←smul_add,←sum_add_distrib];congr 1;apply sum_congr rfl;intro i _
   unfold Weald.carrier Weald.vessel;rw [cruising];change kennel _ (Weald.plank P i (flow P.L i U) e n+shaker _ _ _ _ _ _ _)=_
   exact kennel_linear (hY i).1 (hu i).1 (hY i).2 (hu i).2 hK
 have he' : x=u-(Yurt.forecast P K A (S-S') d e n):=by
    rw [h1,h2,cloud_expr,← cloud_sub]; congr 1;funext i
    change _=V i-ridges P K A i (S-S') e n;rw [ridges_diff he i hη hη' hσ hv,sub_sub_cancel]
 have Hg :Dyad (stance _) D hη (Y W*B') δ x u':=by rw [h2,h3]; exact (cloud_opt P d hδ (fun i=>ridges_price (S:=S') (S':=S') he i hη hη' hσ (Dyad.pure he.gift hB' hv.voices.2 hv.far))).mono hX
 exact ⟨hU,hZ',hA _ (tracks hη (he.wax n).near) (fun i=>⟨(hY i).voices.1,hI i⟩) (fun i=>⟨(hh i).1.voices.1,(hh i).1.near⟩),hA _ (tracks hη (he.wax n).far) (fun i=>⟨(hY i).voices.2,hj i⟩) (fun i=>⟨(hh i).1.voices.2,(hh i).1.far⟩),by rw [he',sub_sub_cancel],Hg.switch⟩
end YM.RG08.Necks

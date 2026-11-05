import YM.UVExtension.Gale.Ship
/-!
 # REAL spigot on the short-upper interval. No full-sequence assumptions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Cloud
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard
open Fitted
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Camp Oriel Lamppost
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{A: Hol G}{n m:Side}{Q P:BudgetPoint} {b r t:ℝ}
local notation "L'"=> RoutesF F n m P Q A
local notation "N!"=> Bucket F Q A n
variable (L:Shade→RoutesF F n m P Q A)(Y:Side)
private lemma agreeU {T T' : Lacing.RoutesF F n m P Q A} (h:T.vane=T'.vane)(hp:T.glass=T'.glass)(hg:T.wing=T'.wing)(hr:T.route=T'.route): T=T':=by rcases T with ⟨a,b_1,f,g⟩; rcases T' with ⟨x,y,z,r⟩; dsimp only at *; subst_vars; rfl
structure Bright (Q':ℂ→ L') (a r:ℝ): Prop where
    noneM z:(Q' z).vane none=0
    unit z:(Q' z).vane (some 0) = (((Y.val:ℂ)^d) • F.e0,0)
    key b:Q' (spreadK.call b)= L b
    comes (i:F.Index):Bumps spreadK.span (fun z=> (Q' z).vane (some i))
    stems i v:Bumps spreadK.span (fun z=> (Q' z).glass i v)
    peals i v:Bumps spreadK.span (fun z=> (Q' z).wing i v)
    bear i:i≠0→∀ z∈ spreadK.span, ‖(Q' z).vane (some i)‖≤ a
    moor i z:z∈spreadK.span→∀ v, ‖(Q' z).glass i v‖≤r*‖v‖
    routes i z:z∈spreadK.span→∀ v, ‖(Q' z).wing i v‖≤r*‖v‖
    rout i j: (Q' i).route=(Q' j).route

set_option synthInstance.maxHeartbeats 140000
set_option maxHeartbeats 380000 in
lemma reflects (hE:∀ i:F.Index,i≠0→∃ g:ℂ→N!,Bumps spreadK.span g∧(∀ b,g (spreadK.call b)=(L b).vane (some i))∧∀ z∈ spreadK.span,‖g z‖≤ r)(hG: ∀ i:Eyelet.Slot m,∃ g:ℂ→ Gondola d A i.1 P→L[ℂ] N!,(∀ v,Bumps spreadK.span (fun z=>g z v))∧ (∀ b,g (spreadK.call b)=(L b).glass i)∧∀ z∈ spreadK.span,∀ v,‖g z v‖≤ t*‖v‖)(hP: ∀ i:StockTag m,∃ g:ℂ→ Eyelet.Stream G P i→L[ℂ] N!, (∀ v,Bumps spreadK.span (fun z=>g z v)) ∧ (∀ b,g (spreadK.call b)=(L b).wing i)∧∀ z∈ spreadK.span,∀ v,‖g z v‖≤ t*‖v‖)(hR:∀ i j,(L i).route=(L j).route)(hX:∀ i,(L i).vane (some 0)= (((Y.val:ℂ)^d) • F.e0,0))(hN:∀ i,(L i).vane none=0):∃ Q':ℂ→L', Bright L Y Q' r t:=by
    choose Gp hG' hG0 hU using hG
    choose U hU' hF hY using hP
    choose! P' hP hx hφ using hE
    let t':Shade:=⟨0,by norm_num [Spire.spatial,rad,rim]⟩
    let A'(z:ℂ)(i:Option (F.Index)):N! := i.elim 0 (fun i=> if i=0 then (((Y.val:ℂ)^d) • F.e0,0) else P' i z)
    let q(z:ℂ): L' :=⟨A' z,fun i=> Gp i z,fun i=> U i z,(L t').route⟩
    have h0 z:(q z).vane (some 0) = (((Y.val:ℂ)^d) • F.e0,0):=by change A' z (some 0) = _; unfold A'; simp
    refine ⟨q,fun z=>rfl,h0,fun i=>?_ ,fun i=>?_ ,hG',hU',fun i hi z h=>?_,hU,hY,fun _ _=>rfl⟩
    · have hp : (L t').route=(L i).route:= hR _ _
      apply agreeU -- inspect
      · ext1 i_; cases i_ with
        | none=> exact (hN i).symm
        | some j=> by_cases h:j=0; subst j; exact (h0 _).trans (hX i).symm
                   exact (if_neg h : (q (spreadK.call i)).vane (some j)= _).trans (hx _ h i)
      · exact funext fun j=>hG0 j i
      · exact funext fun j=>hF j i
      exact hp
    · by_cases h:i=0; subst i; simp_rw [h0]; exact bumps _ _ (differentiableOn_const _)
      have he z:((q z).vane (some i))=P' i z:=if_neg h; simp_rw [he]; exact hP _ h
    erw [show (q z).vane (some i)=P' i z from if_neg hi]; exact hφ i hi z h
end YM.UVExtension.Cloud

import YM.MergeProof.Ballad
import YM.MergeProof.North.Junction
import YM.MergeProof.North.Nigella
import YM.MultipleContact.Bunch.Focal
import YM.MultipleContact.Bunch.Dew
import YM.MultipleContact.Bunch.Gush
import YM.MultipleContact.Bunch.Sugary
import YM.MultipleContact.Bunch.Stained
import YM.MultipleContact.Bunch.Stator
import YM.MultipleContact.Bunch.Fermi
import YM.MultipleContact.Bunch.Junction
import YM.MultipleContact.Bunch.Corn
import YM.MultipleContact.Bunch.Lyme
import YM.MultipleContact.Bunch.Nigella

/- generalized from YM.MergeProof.North.Buoy to arbitrary arity -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus Switch
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V ι J : Type}[Fintype V][DecidableEq V][Fintype ι]{G:Gauge}{f c:Side}{R:Rep G f}
local notation "X"=> Aged V slot
variable (F:ι→ Config G f→Poly (Aged V slot))(v:V)(E:V→Equiv.Perm ι)(B:V→Equiv.Perm V)(m:V→Motion)(x:V→Site f)(w:Name V slot→ℝ)
    (T:ι→Wing→Prop)(Y:ι→Support f)
    (π:∀ i, R.activities.Moves (m i).1 (x i))
    (hR:∀ u:V,u≠v→B u v=u)
    (h:∀ u:V,u≠v→∀ i U,Harm v (B u) (m u) (F i (pull (m u).1 (x u) U)) (F (E u i) U))
-- Crest+trace Bake. consumers concrete
structure Baker (p:Viv F)(A:Bool→ Hat (Aged V slot) R): Prop where
   head i: (A i).s=p.val.2 ∧ (A i).M.crest= Y p.val.1 ∧ T p.val.1 (WKey (A i))
   score : ∑ i, Menu.fare (A i) w = 2*(table w p)
   sums U : ∑ i,amount (A i) U=Poly.send p.val.2 ((F p.val.1 U).part p.val.2)
variable {F w v} (hw:∀ u:V,u≠v→∀ i:slot,w (u,i)=w (v,i))
    (ht:∀ u:V,u≠v→∀ i, Y (E u i)= sky (m u) (x u) (Y i))
    (hp:∀ u:V,u≠v→∀ i a, T i a→ T (E u i) (Wing.labelRoute (π u) a))
set_option quotPrecheck false
local notation "S"=> fun u=> Equiv.prodCongr (E u) (drum (slot:=slot) (B u))
local notation "K"=> fun u=>shuttled (B u) (m u) (x u) (π u)
include h hR hp hw ht
lemma tastes (u:V)(he:u≠v)(p t:Viv F)(hy:t.val=(S) u p.val)(hV:Focused v p.val.2) (A:Bool→Hat (Aged V slot) R) (hg:Baker F w T Y p A): Baker F w T Y t ((K) u ∘ A):=by
   have hs:t.val.1= E u p.val.1:=congr_arg Prod.fst hy; have hl:t.val.2=drum (slot:=slot) (B u) p.val.2:=congr_arg Prod.snd hy
   refine ⟨fun i=>⟨?_,?_,?_⟩,?_,fun U=>?_⟩
   · exact ((congr_arg (drum (slot:=slot) (B u)) (hg.head i).1).trans hl.symm)
   · rw [hs, ht u he]; change (Leaf.route (π u) (A i).M).crest=_; rw [crestSky (m u) (x u),(hg.head i).2.1]
   · rw [hs]; exact hp u he _ _ (hg.head i).2.2
   · unfold table; rw [show ∑ i:Bool, Menu.fare (((K) u ∘ A) i) w=∑ i:Bool,Menu.fare (A i) w from sum_congr rfl fun i _=> forecast v u (B u) _ _ (π u) (hR u he) (fun i=>(hw u he i).symm) _ ((hg.head i).1 ▸ hV),hg.score]
     unfold table; rw [hs,hl,equals F v (E u) (B u) (m u) (x u) (h _ he) _ _ hV]; unfold Poly.toll; rw [drum,pares,prod_image _]; refine congr_arg _ (congr_arg (·*_) (prod_congr rfl ?_));
     · rintro ⟨i,j⟩ hi; have he': i=v:=mem_singleton.mp (hV (mem_image_of_mem Prod.fst hi)); rw [he']; change w (v,j)= w (B u v,j); rw [hR u he]; exact (hw u he j).symm
     exact (nome (slot:=slot) _).injective.injOn
   rw [hs,hl, h u he _ U _ hV]; exact amounts _ _ _ (π u) p.val.2 (fun U=>(F p.val.1 U).part p.val.2) A (fun i=> (hg.head i).1) hg.sums _
local notation "K0" u=> Focused u
lemma joined (hh:∀ i:Viv F,∃ P:Bool→Hat (Aged V slot) R,Baker F w T Y i P) :∃ q:Viv F×Bool→Hat (Aged V slot) R,(∀ i:Viv F,Baker F w T Y i (fun j=>q (i,j)))∧∀ u:V,u≠v→∃ e:Equiv.Perm (Viv F×Bool), Kin q v u (B u) (m u) (x u) (π u) e:=by
   let a:=fun (v:V)(i:Viv F)=>Focused v i.val.2
   have he : ∀ u:V,∃ b:Equiv.Perm (Viv F), u≠v→(∀ i,a v i↔ a u (b i))∧ ∀ i,a v i→ (b i).val=(S) u i.val := fun u=>by by_cases hx:u≠v; obtain ⟨b,he⟩:= align F v u (E u) (B u) (m u) (x u) (h u hx) (hR u hx); exact ⟨b,fun _=>he⟩; exact ⟨Equiv.refl _,fun he=>(hx he).elim⟩
   choose b hb using he; choose q hq using hh
   let J(i:Viv F):= ∃ u:V, u≠v∧a u i
   have hl v u i (ht:a v i)(hs:a u i): v=u:=by
       have hh:= (q i false).shiny; rw [(hq i).head false|>.1] at hh; obtain ⟨l,h⟩:= hh.image Prod.fst; exact (mem_singleton.mp (ht h)).symm.trans (mem_singleton.mp (hs h))
   let J' i:= if he:J i then (K) he.choose ∘ q ((b he.choose).symm i) else q i
   let L:= fun i:Viv F×Bool=> J' i.1 i.2
   have H0(u)(i:Viv F)(hi:a u i)(hH:u≠v) : J' i=(K) u ∘ q ((b u).symm i):=by
       have he':J i:= ⟨u,hH,hi⟩; unfold J'; rw [dif_pos he',hl he'.choose u _ he'.choose_spec.2 hi]
   have hx i:Baker F w T Y i (J' i):=by
       by_cases hk:J i
       · obtain ⟨u,hw',hy⟩:=hk; rw [H0 _ i hy hw']; obtain ⟨i,rfl⟩:= (b u).surjective i; rw [(b u).symm_apply_apply]; have hh:= (hb u hw').1 i|>.mpr hy; exact tastes E B m x T Y π hR h hw ht hp u hw' i _ ((hb u hw').2 _ hh) hh (q i) (hq i)
       rw [show J' i=q i from dif_neg hk]; exact hq _
   refine ⟨L,hx,fun u h'=>⟨Equiv.prodCongr (b u) (Equiv.refl _), hR u h',fun i=>?_,fun i hi=>?_⟩⟩
   · rcases i with ⟨i,j⟩; change Focused v (J' i j).s ↔ Focused u (J' (b u i) j).s; rw [(hx i|>.head j).1,(hx _|>.head j).1]; exact (hb u h').1 i
   rcases i with ⟨i,j⟩; have ht : a v i:=by change Focused v (J' i j).s at hi; rw [(hx i|>.head j).1] at hi; exact hi
   have hM: J' i=q i:=dif_neg (by rintro ⟨u,he,hu⟩;exact he (hl u v i hu ht))
   have hz: L (Equiv.prodCongr (b u) (Equiv.refl Bool) (i,j)) = shuttled (B u) (m u) (x u) (π u) (L (i,j)):=by
       change J' (b u i) j= shuttled _ _ _ _ (J' i j)
       rw [H0 u _ ((hb u h').1 i|>.mp ht) h',Equiv.symm_apply_apply,hM];rfl
   rw [hz]; exact ⟨rfl,rfl,rfl⟩
end YM.MergeProof.BatchRibbons

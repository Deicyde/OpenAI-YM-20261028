import YM.MergeProof.North.Buoy
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
import YM.MultipleContact.Bunch.Buoy

/- generalized from YM.MergeProof.North.Gild to arbitrary arity -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus Switch
open GridApprox.Nil
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V ι J : Type}[Fintype V][DecidableEq V][Fintype ι]{G:Gauge}{f c:Side}{R:Rep G f}
local notation "X"=> Aged V slot
variable {F:ι→ Config G f→Poly (Aged V slot)}{a:Name V slot→ Site f}{d t:ℝ}{w:Name V slot→ℝ}{Y:ι→Support f}(hw:∀ i,0<w i)
    (T:ι→Wing→Prop)
    (h:∀ i,Borne a (Y i) (F i) R.p.threshold) (hr:∀ i U,rises (F i U)) (ht:Towed w Y F R.p.B t d)
include h hr ht hw T
lemma certifies (i:Viv F) (hk:∃ a:Wing,a.blank R∧ a.support R=Y i.val.1 ∧ T i.val.1 a ∧∀ U, F i.val.1 U≠0 → a.qualifies R U): ∃ A:Bool→Hat (Aged V slot) R, Baker F w T Y i A:=by
   obtain ⟨v,hv,hS,hT,hq⟩:= hk; let p:= i.val.1; let j:= i.val.2; have hp:j.val.Nonempty:= card_pos.mp ((show 0<2 by decide).trans_le (?_ : 2 ≤ j.val.card)) -- fix
   · let f':= fun U=> (F p U).part j; have hg:=h p
     obtain ⟨A,hA,hB,hC⟩:= Menu.couple v f' w (s:=j) (hS.symm ▸ (show UsesFinal _ _ f' from fun U V hp hx=> congr_arg (·.part j) (hg.home _ _ hp hx))) (fun U hF=> hq U (fun he=> hF (by unfold f' p; rw [he,Poly.part_nil]))) hv (hg.me j) (fun i U=>congr_arg (·.part j) (hg.turns i U)) ((r_ated w hw ht).1 p j|>.2) hp
     exact ⟨A, ⟨fun i=>⟨(hA i).2, (show (WKey (A i)).support R=Y p from by rw [(hA i).1]; exact hS), (hA i).1.symm ▸ hT⟩,hB,hC⟩⟩ -- part.s typo
   exact hr i.val.1 i.property.choose _ i.property.choose_spec

lemma ranks (q:Viv F×Bool→Hat X R)(hp:∀ i:Viv F,Baker F w T Y i (fun j=>q (i,j))) : (∀ i,2 ≤ (q i).s.val.card) ∧ Offer a q w R.p.B t (2*d):=by
   refine ⟨fun i=> ?_,fun i=> ?_,fun i=> ?_⟩
   · rcases i with ⟨x,j⟩; rw [show (q (x,j)).s=x.val.2 from (hp x).head j|>.1]; exact hr _ _ _ x.property.choose_spec
   · rcases i with ⟨x,j⟩; rw [show (q (x,j)).s= x.val.2 from (hp x).head j|>.1,show (q (x,j)).M.crest=Y x.val.1 from (hp x).head j|>.2.1]; exact (h _).place _ _ x.property.choose_spec
   have ht:=(r_ated w hw ht).2 i
   refine ⟨fun i=>?_,Summable.of_finite,?_⟩
   · dsimp only; split; exact mul_nonneg (Crew _ hw) (Real.exp_pos _).le; rfl
   rw [tsum_fintype,Fintype.sum_prod_type]; apply le_trans _ (mul_le_mul_of_nonneg_left (Extra.Multi.Budget.cap ht univ) zero_le_two); rw [Finset.mul_sum]; refine Finset.sum_le_sum fun j _=>?_ ; let Xk:= Y j.val.1; dsimp only; simp_rw [show ∀ k,(q (j,k)).M.crest=Xk from fun k=> (hp j).head k|>.2.1];
   by_cases he:i∈Xk
   · rw [if_pos (show i∈Y j.val.1 from he)]; simp_rw [if_pos he]; rw [← Finset.sum_mul]; erw [(hp j).score]; exact (mul_assoc ..).le
   rw [if_neg (show i∉Y j.val.1 from he),mul_zero]; simp_rw [if_neg he]; exact sum_const_zero.le
omit h hr ht hw
lemma yielded (q:Viv F×Bool→ Hat X R)(hp:∀ i:Viv F,Baker F w T Y i (fun j=> q (i,j))) (i:ι) (U:Config G f) : ∑ j:Viv F×Bool, (if j.1.val.1=i then amount (q j) U else 0)=F i U:=by
   rw [Fintype.sum_prod_type]; let v:=fun j:(X).Mode=>Poly.send j ((F i U).part j); let g (x:Viv F):= if x.val.1=i then v x.val.2 else 0
   have hg(x: Viv F): ∑ b:Bool,(if x.val.1=i then amount (q (x,b)) U else 0)= g x:=by
      by_cases h:x.val.1=i
      · unfold g; simp_rw [if_pos h]; exact (hp x|>.sums U).trans (congr_arg (fun i'=> Poly.send x.val.2 ((F i' U).part x.val.2)) h)
      simp [g,h]
   simp_rw [hg]
   let t:= univ.filter (Vivid F i); let b (p : {p//Vivid F i p}):Viv F:= ⟨(i,p.val),p.property⟩
   have hv : ∑ p:{p// Vivid F i p},g (b p)=∑ x,g x:=by
       apply Finset.sum_of_injOn b (fun i hi j hj he=> Subtype.ext (Prod.mk.inj (congr_arg Subtype.val he)|>.2)) (fun _ _=> mem_univ _) (fun j _ hh=> ?_) (fun _ _=> rfl)
       apply if_neg; intro he; have hx:Vivid F i j.val.2:=he ▸ j.property
       exact hh ⟨⟨j.val.2,hx⟩,mem_univ _,Subtype.ext (Prod.ext he.symm rfl)⟩
   rw [← hv]; conv_rhs=> rw [← Poly.studs (F i U)]
   trans ∑ x∈t,v x
   · simp only [g,b, ↓reduceIte]; exact (sum_subtype t (p:=Vivid F i) (fun i=>by simp [t]) v).symm
   · exact sum_subset (subset_univ _) fun j hj hh=>by have hx : ¬ Vivid F i j:=fun he=> hh (mem_filter.mpr ⟨hj,he⟩); unfold v; rw [show (F i U).part j=0 from Classical.byContradiction (fun he=> hx ⟨U,he⟩),Poly.send_zero]
end YM.MergeProof.BatchRibbons

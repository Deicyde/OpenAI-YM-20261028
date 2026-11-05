import YM.RG08.Gallery.Slate

/-!
# Sparse point-gradient directions and actual stencil Closure on unmarked tensors
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Gallery
open Forms Glyph Room Camera Finset Lattice Laurent Pert.Bulk Function MvPolynomial Filter Isles
open Carrel Rudder Rudder.Symmetry Anchor
open AnalyticNext.QuarticMatch.BoxChain
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {I:Type}{n e :ℕ}

private def up (z:Cover)(t:I)(i:Axis): Mix I 1:=(z-step i,Exterior.coord i,t)
private def down (z:Cover)(t:I)(i:Axis): Mix I 1:=(z,Exterior.coord i,t)
def bolt (z:Cover)(t:I):Demo (Mix I 1) where
 firm:= univ.image (up z t)∪ univ.image (down z t)
 play x:=∑ i:Axis,((if x=up z t i then 1 else 0)-(if x=down z t i then 1 else 0))
 size' x hx:=Finset.sum_eq_zero fun i _=> by
    rw [if_neg (fun (h:x=up z t i)=>hx (h ▸ mem_union_left _ (mem_image_of_mem _ (mem_univ i)))), if_neg (fun (h:x=down z t i)=>hx (h ▸ mem_union_right _ (mem_image_of_mem _ (mem_univ i)))),sub_self]
lemma bolt_any (z:Cover)(t:I)(F:Mix I 1→ℝ): (∑ x∈(bolt z t).firm,(bolt z t).play x * F x)=∑ i:Axis,(F (up z t i)-F (down z t i)):=by
 simp only [bolt,Finset.sum_mul,sub_mul,ite_mul,one_mul,zero_mul];rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro i _;rw [Finset.sum_sub_distrib];simp
-- exported without a particular DecidableEq I on the chart
lemma bolt_eval (z:Cover)(t:I)(x:Cover)(j:Axis)(l:I):(bolt z t).play (x,Exterior.coord j,l)=(if (x+step j,l)=(z,t) then (1:ℝ) else 0)-(if (x,l)=(z,t) then (1:ℝ) else 0):=by
 unfold bolt; dsimp only;rw [Finset.sum_eq_single j (fun i hi hh=>?_) (by simp)];
 · simp [up,down,eq_sub_iff_add_eq] -- Type annotation of x pairs
 simp [up,down,Exterior.coord_iff,(Ne.symm hh)]
-- Pred: can add each translated & color based free cochain gradient at leading W while staying on
-- the same effective orbit, with all nonlinear corrections allowed as long as sparse.
def Gauged (V:Script (Mix I 1))(e:ℕ):Prop:=∀ (s:Demo (Mix I 1))(r q:ℝ)(z:Cover)(t:I),
 ∃ a b : Tray (Mix I 1), (Demo.flat a).play = r • s.play ∧ (Demo.flat b).play=r • (s.play+q • (bolt z t).play) ∧ tap e (announced V a)=tap e (announced V b)

lemma nocturnal (V:Script (Mix I 1))(e:ℕ)(h:Gauged V e)(ht:∀ k<e,∀ i≠0,V k i=0)
    {j:ℕ}(u:Fin j)(hp:j≤e+2)(hs:Forms.Sym (V e j)) (Y:Slide (Anchor.Kind I 1) j)(r:Cover)(i:I):
   (∑ a:Axis,(V e j (update Y u (up r i a))-V e j (update Y u (down r i a))))=0:=by
 rw [←bolt_any r i (fun x=> V e j (update Y u x))];apply work_any hs
 intro b c z H
 apply sorting V e _ _ ht (fun s=> ?_) _ hp
 rw [H];exact h b s z r i

private lemma hood (x:Tape n (Market (Tone I)))(u:Fin n)(y:Mix I 1)(h:∀ i ≠ u,(x i).2.1.card=1):
   let X := update x u ((y.1,(y.2.1).val,y.2.2):Market (Tone I)); Anchor.permitted Cover I 1 X:=by
 intro X i; by_cases he:i=u
 · subst i;exact (by unfold X;simp only [update_self];exact y.2.1.property)
 unfold X;rw [update_of_ne he];exact h i he

lemma gauge_closes {V:Script (Mix I 1)}(h:Gauged V e)(ht:∀ k<e,∀ i≠0,V k i=0)(hp:n≤e+2)(hs:Forms.Sym (V e n)) : Closing (Anchor.extend 1 (V e n)):=by
 let F:= V e n;let U:= Anchor.extend 1 F
 intro y i
 ext z; change boundary i U (lyre z y)=_
 let R:=lyre z y
 have hx:R i=(z i|>.1,z i|>.2,y i):=rfl
 by_cases he:(z i).2.card=0; swap
 · exact graded_at (r:=fun j=>if j=i then (0:ℕ) else 1) (graded_iff.mpr (fun l=>by
    split; next h=>subst l;exact enters (graded_iff.mp (expand_grade (F:=F)) i)
    next h=>exact passive (graded_iff.mp (Anchor.expand_grade (F:=F)) _) h)) (i:=i) (x:=R) (show (R i).2.1.card≠(if i=i then _ else _) by rwa [if_pos rfl])
 by_cases ha:∀ j≠i,(R j).2.1.card=1; swap
 · obtain ⟨l,hL⟩:=Classical.not_forall.mp ha;push Not at hL;exact passive (F:=U) (graded_iff.mp (Anchor.expand_grade (F:=F)) _) hL.1 _ hL.2
 let t:=y i; let r:Cover:=(z i).1
 let X(j:Fin n):Mix I 1:=if h:j=i then down r t 0 else decoded Cover I 1 (R j) (ha _ h)
 have heq(a:Mix I 1):U (update R i ((a.1,(a.2.1).val,a.2.2):Market (Tone I)))=F (update X i a):=by
    unfold U;rw [Anchor.extend,dif_pos (hood R i a ha)];apply congrArg F;funext j;by_cases h:j=i
    · subst j;simp [decoded]
    conv_rhs=>rw [update_of_ne h]
    unfold X;rw [dif_neg h]; -- update R dependent
    apply ec_injective;exact update_of_ne h _ R
 change boundary i U R=0
 rw [chart];apply Eq.trans _ (nocturnal V e h ht i hp hs X r t)
 apply Finset.sum_congr rfl;intro a _
 unfold lifted
 rw [if_neg (by simp only [hx, Finset.card_eq_zero.mp he,Finset.notMem_empty];trivial)]
 have hu : kick (R i) a (-step a)=((up r t a).1,(up r t a).2.1.val,(up r t a).2.2) :=by rw [kick,hx,Finset.card_eq_zero.mp he,←sub_eq_add_neg];rfl
 have hv : kick (R i) a 0=((down r t a).1,(down r t a).2.1.val,(down r t a).2.2):=by rw [kick,hx,Finset.card_eq_zero.mp he,add_zero];rfl
 rw [hu,hv,heq,heq,hx,Finset.card_eq_zero.mp he]; unfold AnalyticNext.QuarticMatch.BoxChain.sign Exterior.parity Exterior.pre; simp [F]
end YM.RG08.Gallery

import YM.RG08.Anchor.Show
import YM.AnalyticNext.QUARTIC_MATCH.Cells.Post -- scatter

noncomputable section
namespace YM.RG08.Anchor
open Forms Rudder Packets Isles Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch
open AnalyticNext.QuarticMatch.BoxChain hiding sway
open scoped Topology BigOperators Classical ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
local notation "Box"=> YM.AnalyticNext.QuarticMatch.BoxChain.Cell
variable {I : Type}{n:ℕ}{P:Side}{σ C:ℝ}{F:Raw I n}

abbrev Postel (P:Side):=Box (Per P)→ℝ

def finger (a:Axis)(F:Postel P)(x:Box (Per P)):=if a∈x.2 then sign x.2 a * (F (x.1+step a,x.2.erase a)-F (x.1,x.2.erase a)) else 0
def margin (F:Postel P):Postel P:=∑ a,finger a F

private lemma turn_one (a:Axis)(L F:Postel P) : ∑ x: Box (Per P),(sect a L x)*F x=∑ x: Box (Per P),L x*finger a F x:=by
 let t:Equiv.Perm (Finset Axis):={ toFun S:=if a∈S then S.erase a else insert a S,invFun S:=if a∈S then S.erase a else insert a S,left_inv:=fun S=>by by_cases H:a∈S<;>simp [H],right_inv:=fun S=>by by_cases H:a∈S<;>simp [H]}
 rw [Fintype.sum_prod_type,Fintype.sum_prod_type,sum_comm];conv_rhs=>rw [Finset.sum_comm,←Equiv.sum_comp t]
 apply sum_congr rfl;intro b _;by_cases h:a∈b
 · simp [finger,t,h,sect_at]
 have he:t b=insert a b:=if_neg h
 simp_rw [he,sect_at,finger];simp only [h,if_false,mem_insert_self,if_pos,sign_insert b a h,erase_insert h,smul_eq_mul,mul_assoc,mul_left_comm (L (_, _)) (sign b a),sub_mul,mul_sub, ← Finset.mul_sum,sum_sub_distrib] -- maybe order
 let E:=Equiv.subRight (step a:Site P)
 have he:=Equiv.sum_comp E (fun i:Site P=>L (i,insert a b)* F (i+step a,b))
 rw [←he]
 congr 2;apply sum_congr rfl;intro i _;change _=L _* F (i-step a+ step a,b);rw [sub_add_cancel];rfl

def stroke (A:ArrayC (Fin n) (Per P) ℝ)(F:Fin n→Postel P):ℝ:=∑ x:Tape n (Box (Per P)),A x*∏ i,F i (x i)

private lemma paid_one (L F:Postel P): ∑x:Box (Per P), rim L x*F x= ∑x : Box (Per P),L x * margin F x:=by
 simp_rw [rim_at,margin,Finset.sum_apply,Finset.sum_mul,Finset.mul_sum]
 rw [sum_comm];conv_rhs=>rw [Finset.sum_comm]
 exact sum_congr rfl fun _ _=>turn_one ..

lemma paint (A:ArrayC (Fin n) (Per P) ℝ)(F:Fin n→Postel P)(i:Fin n):stroke (lower i A) F=stroke A (update F i (margin (F i))):=by
 let Z:=Box (Per P);let q:ℝ:=Fintype.card Z
 have hq:q≠0:=Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
 apply mul_left_cancel₀ hq; unfold stroke q
 rw [←nsmul_eq_mul,←nsmul_eq_mul,← scatter i,← scatter i]
 apply Finset.sum_congr rfl;intro x _
 let K:=∏ j∈univ.erase i,F j (x j)
 let L:=peek i x A
 have he{F G:Fin n→Postel P}(h:∀ j,j≠i→F j=G j)(z:Z): ∏ j,G j ((update x i z) j)=G i z* ∏ j∈univ.erase i,F j (x j):=by
    rw [←Finset.mul_prod_erase _ _ (mem_univ i),update_self]; congr 1; apply Finset.prod_congr rfl;intro j hj;rw [update_of_ne (mem_erase.mp hj).1,h _ (mem_erase.mp hj).1]
 have hp:= paid_one L (F i)
 apply Eq.trans (b:=K * ∑ z:Z,rim L z*F i z)
 · rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro z _
   change peek i x (lower i A) z*_=_;rw [peek_lower,he (F:=F) (fun _ _=>rfl)];unfold K L;ring
 rw [hp,Finset.mul_sum];apply Finset.sum_congr rfl;intro z _
 change _=L z * _
 rw [he (F:=F) (fun _ hj=> (update_of_ne hj _ _).symm),update_self];unfold K;ring

lemma paint_all (A:ArrayC (Fin n) (Per P) ℝ)(F:Fin n→Postel P): stroke (YM.AnalyticNext.QuarticMatch.BoxChain.solve (List.finRange n) A) F=stroke A (fun i=>margin (F i)):=by
 have he(s:List (Fin n))(hs:s.Nodup)(F:Fin n→Postel P):stroke (YM.AnalyticNext.QuarticMatch.BoxChain.solve s A) F=stroke A (fun i=>if i∈s then margin (F i) else F i):=by
    induction s generalizing F with
    | nil=>simp [solve_empty]
    | cons a s ih=>
        rw [solve_head,paint,ih (List.nodup_cons.mp hs).2]
        congr 1;ext i:1;rcases eq_or_ne i a with hh|hh <;> simp [hh,(List.nodup_cons.mp hs).1]
 simpa only [List.mem_finRange,if_true] using he _ (List.nodup_finRange n) F

/-- Translation including harmonic frequencies! `i` is external anchor ANY, `y` fixed
generators. No sym/numerical combinatorial factors or test-derivative ambiguity. -/
theorem curl_pour (i:Fin n)(h:NextTo F σ C)(y:Tape n I)(w:Tape n (Postel P)):
 stroke (fun x=> pour (picture I n F) i (herald x y)) w=stroke (fun x=>pour F i (herald x y)) (fun j=>margin (w j)):= by simp_rw [turns i F h,paint_all]
end YM.RG08.Anchor

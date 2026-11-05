import YM.TraceExtension.Perfect.Margin
import YM.Next.FREE_KERNELS.Traffic

/-!
# Second order θ polynomial on raw low modes
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Stationary Filter Function Matrix Lattice Precision Finset Laurent
open scoped Topology BigOperators ContDiff
variable {I : Type}[Fintype I]
lemma sh_zero (A:I→ℕ)(a t r): sh A a t r 0=0:=by simp [sh]
lemma sh_scale (A a t r)(q : I→ℝ)(v : ℝ): sh A a t r (v • q)= |v| * sh A a t r q:=by unfold sh; simp_rw [Pi.smul_apply,norm_smul, Real.norm_eq_abs, Finset.mul_sum, mul_left_comm |v|]
lemma sh_sum (A a t r){Y:Type}(F:Y→I→ℝ)(J:Finset Y): sh A a t r (∑ i∈J,F i) ≤ ∑ i∈J, sh A a t r (F i):=by
 classical
 induction J using Finset.induction with
 | empty=>simp [sh_zero]
 | insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact (sh_add ..).trans (add_le_add_right ih _)

lemma backwalk (x : Cover) (h:x≠0) : ∃ (i:Axis)(y:Cover), size x=size y+1 ∧ (x=y+step i ∨ y=x+step i):=by
 obtain ⟨i,hi⟩ : ∃ i : Axis,x i≠0:= by simpa [Ne,funext_iff] using h
 have h s (hs : ∀ j : Axis, j≠i → s j = x j) (hp :(s i).natAbs+1=(x i).natAbs) : size x=size s+1:=by
     unfold Laurent.size
     rw [← add_sum_erase _ _ (mem_univ i)]; rw [← add_sum_erase _ (fun j=> (s j).natAbs) (mem_univ i)]
     rw [← hp,add_right_comm]; congr 2; apply Finset.sum_congr rfl; intro j h; rw [hs j (mem_erase.mp h|>.1)]
 rcases lt_or_gt_of_ne hi with hu|hu
 · refine ⟨i,x+step i,h _ ?_ ?_,Or.inr rfl⟩
   · intro j hj; simp [hj,Ne.symm hj]
   have hx:=hu; simp; omega
 refine ⟨i,x-step i,h _ ?_ ?_,Or.inl (sub_add_cancel ..).symm⟩
 · intro j hj; simp [hj,Ne.symm hj]
 have hx:=hu; simp; omega

variable {A:I→ℕ}{α:ℝ}{t R:ℕ}
def move (V:Cover→ I→ℝ)(i:Axis) := fun x : Cover=> V (x+step i)-V x
private lemma crawls (V: Cover→ I→ℝ)(P:ℝ)(h:∀ x:Cover,size x≤R →∀ a:Axis, sh A α t 0 (move V a x) ≤ P) (x : Cover) (hr:size x ≤ R):
    sh A α t 0 (V x-V 0)≤size x*P:=by
 generalize he : size x=n
 rw [he] at hr
 induction n using Nat.strong_induction_on generalizing x with | h n IH=>_
 by_cases ht:x=0
 · subst x; rw [← he]; simp [Laurent.size,sh_zero]
 obtain ⟨i,y,hY,hp|hp⟩:= backwalk x ht
 · specialize IH (size y) (by omega) y (by omega) rfl
   rw [show V x-V 0=move V i y+(V y-V 0) from by rw [hp]; unfold move;abel]
   refine (sh_add ..).trans ((add_le_add (h y (by omega) i) IH).trans_eq ?_); rw [← he,hY]; push_cast;ring
 specialize IH (size y) (by omega) y (by omega) rfl
 rw [show V x-V 0= -(move V i x)+(V y-V 0) from by rw [hp]; unfold move; abel]
 apply (sh_add ..).trans; rw [sh_neg]
 exact (add_le_add (h x (by omega) i) IH).trans_eq (by rw [← he,hY];push_cast;ring)

lemma walk_tiny (V:Cover→I→ℝ)(P:ℝ)(h:∀ x:Cover,size x≤R →∀ a:Axis,sh A α t 0 (move V a x)≤P)(x:Cover)(hx:size x≤R) : sh A α t 0 (V x-V 0)≤size x*P:= crawls V P h x hx

def lin (V:Cover→ I→ℝ)(x : Cover): I→ℝ:=∑ i:Axis,(x i:ℝ) • move V i 0
def quadT (i j:Axis)(x : Cover):ℝ:= ((x i:ℝ)*(x j)-(if i=j then (x i:ℝ) else 0))/2
def quad (V:Cover→ I→ℝ)(x : Cover): I→ℝ:=∑ i:Axis,∑ j:Axis,quadT i j x • move (move V i) j 0

lemma move_swap (V:Cover→ I→ℝ)(x:Cover)(i j:Axis): move (move V i) j x= move (move V j) i x:=by unfold move; rw [add_right_comm]; abel
lemma move_lin (V:Cover→ I→ℝ)(a : Axis) (x:Cover): move (lin V) a x=move V a 0:=by
 unfold move lin; rw [← Finset.sum_sub_distrib,Finset.sum_eq_single a]; rotate_left
 · intro b _ hb; simp [hb,Ne.symm hb]
 · simp
 simp [add_smul, move]
private lemma tip (a b c:Axis)(x:Cover): (quadT b c (x+step a) - quadT b c x)= (if b=a then (x c:ℝ)/2 else 0)+(if c=a then (x b:ℝ)/2 else 0):=by
 by_cases hb:b=a <;> by_cases hc:c=a <;> subst_vars <;> push_cast [quadT] <;> simp_all [quadT,eq_comm,Int.cast_one] <;> ring_nf
lemma move_quad (V : Cover→ I→ℝ)(a : Axis)(x : Cover): move (quad V) a x=lin (move V a) x:=by
 let T i j:= move (move V i) j 0
 change (∑ i: Axis, ∑ j:Axis,quadT i j (x+step a) • T i j) -_=_
 unfold quad
 rw [← Finset.sum_sub_distrib]
 change (∑ i:Axis,(_-(∑ j:Axis, quadT i j x • T i j)))=_
 simp_rw [← Finset.sum_sub_distrib,← sub_smul,tip, add_smul,Finset.sum_add_distrib]
 rw [Finset.sum_comm (f:=fun i j => (if i=a then (x j:ℝ)/2 else 0) • T i j)]; unfold lin; simp [apply_ite (fun u:ℝ=> u • _)]
 rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [show T i a=T a i from move_swap .., ← add_smul]; congr 1;ring
lemma move_subV (V W:Cover→I→ℝ)(a:Axis): move (V-W) a=move V a-move W a:= by funext j; simp only [move,Pi.sub_apply]; abel

lemma second_tiny (V:Cover→ I→ℝ)(P:ℝ)(h:∀ x:Cover,size x ≤ R→ ∀ i j k, sh A α t 0 (move (move (move V i) j) k x) ≤ P)(hu:0≤P)(x:Cover)(ht:size x≤R) :
     sh A α t 0 (V x-V 0-lin V x-quad V x) ≤ R^3*P:=by
 let F (z:Cover):= V z-V 0-lin V z-quad V z
 have he (i:Axis)(x:Cover): move F i x=move V i x-move V i 0-lin (move V i) x:=by
    change move (V-(fun _ => V 0)-lin V-quad V) i x=_; rw [move_subV,move_subV,move_subV]; simp only [Pi.sub_apply,move_lin,move_quad,show move (fun _=>V 0) i x=0 from sub_self _,sub_zero]
 have he' (i j:Axis)(z:Cover): move (move F i) j z= move (move V i) j z-move (move V i) j 0:=by
   change move F i (z+step j)-move F i z=_; rw [he,he]; have hx:= move_lin (move V i) j z
   rw [← hx]; unfold move;abel
 have hu' : sh A α t 0 (F x-F 0) ≤ size x*((R:ℝ)^2*P):=by
   refine walk_tiny F _ (R:=R) (fun i hi j=>?_) _ ht
   have hN : move F j 0=0:=by rw [he]; simp [lin]
   have hy : sh A α t 0 (move F j i-move F j 0) ≤ size i*((R:ℝ)*P):=by
      refine walk_tiny (move F j) _ (R:=R) (fun i hi k=>?_) _ hi
      rw [he']; refine (walk_tiny (move (move V j) k) _ (fun i hi l=> h i hi j k l) i hi).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) hu)
   rw [hN,sub_zero] at hy; exact hy.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) (show 0 ≤ (R:ℝ)*P by positivity)).trans_eq (by ring))
 have hF : F 0=0:=by simp [F,lin,quad,quadT]
 rw [hF,sub_zero] at hu'; exact hu'.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) (show 0≤(R:ℝ)^2*P by positivity)).trans_eq (by ring))
end YM.Trace.Perfect

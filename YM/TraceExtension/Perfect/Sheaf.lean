import YM.TraceExtension.Anchor.Derivative
import YM.TraceExtension.Perfect.Crawl

/-!
# finite offset sheaves, unsymmetrized cochain corrections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Lattice Laurent RG Wilson Function Finset Filter
open scoped BigOperators Topology
inductive Sheaf
| stay : Sheaf
| mon (z:Cover) : Sheaf
| scale (c:ℝ)(X:Sheaf): Sheaf
| duo (X Y : Sheaf): Sheaf
| mix (X Y : Sheaf): Sheaf
namespace Sheaf
def radius : Sheaf→ℕ
| stay=>0
| mon z => Laurent.size z
| scale _ X=> X.radius
| duo X Y=> max X.radius Y.radius
| mix X Y=>X.radius+Y.radius
def debt : Sheaf→ℝ
| stay=>0
| mon _=>1
| scale c X=> |c| *X.debt
| duo X Y=>X.debt+Y.debt
| mix X Y=>X.debt*Y.debt
def gold : Sheaf→ℝ
| stay=>0
| mon _=>1
| scale c X=> c*X.gold
| duo X Y=>X.gold+Y.gold
| mix X Y=>X.gold*Y.gold
lemma debt_pos (X:Sheaf): 0 ≤ X.debt:=by induction X <;> unfold debt <;> positivity
variable {A:Type*} [AddCommGroup A] [Module ℝ A]

def take (f:Cover→A) : Sheaf → Cover→A
| stay=>0
| mon z=>fun x=> f (x+z)
| scale c X=>c •take f X
| duo X Y=>take f X+ take f Y
| mix X Y=>take (take f Y) X
lemma earns_gold (X:Sheaf)(v:A): take (fun _=>v) X=(fun _ => X.gold • v):=by induction X generalizing v with
| stay=> ext1; simp [take,gold]
| mon=> simp [take,gold]
| scale c X h=> rw [take,h,gold]; ext1; simp [smul_smul]
| duo X Y h p=> rw [take,h,p,gold]; ext1; simp [add_smul]
| mix X Y h p=> rw [take,p,h,gold]; simp [smul_smul]
lemma add_f (X:Sheaf)(f g : Cover→A): take (f+g) X=take f X+take g X:=by induction X generalizing f g with
| stay=>simp [take]
| mon=>rw [take,take,take]; rfl
| scale=>simp only [take, *,smul_add]
| duo X Y h p=>simp only [take,h,p]; abel
| mix X Y h p=>simp only [take,h,p]
lemma smul_f (X:Sheaf)(f:Cover→A)(q:ℝ):take (q • f) X= q • take f X:=by induction X generalizing f with
| stay=>simp [take]
| mon=>rw [take,take]; rfl
| scale c X h=>simp only [take,h]; rw [smul_comm]
| duo=>simp only[take, *,smul_add]
| mix=>simp only[take, *]
lemma shift_f (X:Sheaf)(f:Cover→A)(z:Cover): take (fun x=>f (x+z)) X= fun x=>take f X (x+z):=by induction X generalizing f with
| stay=>rw [take]; simp only[take]; rfl
| mon q=> rw[take]; simp only[take]; simp_rw [add_right_comm _ q]
| scale=>simp only[take,Pi.smul_apply, *]; rfl
| duo=>simp only[take, *,Pi.add_apply]; rfl
| mix=>rw[take]; simp only[take, *]
lemma rope (X Y:Sheaf)(f:Cover→A): take (take f Y) X=take (take f X) Y:=by
 induction X generalizing f with
 | stay=> simp only [take]; rw [show (0:Cover→A)=(fun _=>0) from rfl,earns_gold]; simp
 | mon z=> simp only[take,shift_f]
 | scale=>simp only[take, *,smul_f]
 | duo=>simp only[take, *,add_f]
 | mix X Z h p=>simp only[take,h,p]
abbrev bead (a:Sheaf)(f:Cover→A): Cover→A:=take f a

def Δ (v:Cover):=duo (mon v) (scale (-1) (mon 0))
lemma rises (x v:Cover)(f:Cover→A): take f (Δ v) x=f (x+v)-f x:=by simp [take,Δ,sub_eq_add_neg]
-- additive offsets
lemma size_nsmul (v:Cover)(n:ℕ): Laurent.size (n • v) ≤ n*Laurent.size v:=by induction n with
| zero=>simp [size]
| succ n h=>
   rw [add_smul,one_smul]
   refine (Laurent.size_add ..).trans ?_
   simp [add_mul]; omega
lemma size_step_one (a:Axis):Laurent.size (step a:Cover)=1:=by simp [size,apply_ite Int.natAbs]
-- sum shifts 0..n-1 along vector v
def disk (v:Cover):ℕ→Sheaf
| 0=>stay
| t+1=>duo (disk v t) (mon (t • v))
lemma disk_step (v:Cover)(X:Cover→A)(t:ℕ): bead (Δ v) (take X (disk v t))=take X (Δ (t • v)):=by
 rw [bead,rope]; induction t with
 | zero=> ext1 x; rw[disk,take,rises,zero_smul,add_zero,sub_self];rfl
 | succ n h=> rw [disk,take,h]; ext1 x; rw [Pi.add_apply,take]; dsimp only; rw [rises,rises,rises,add_smul]; rw [one_smul,add_assoc]; abel
lemma disk_cost (v:Cover)(p:ℕ): (disk v p).radius ≤ p*Laurent.size v ∧ (disk v p).debt=(p:ℝ) ∧ (disk v p).gold=(p:ℝ):=by induction p with
| zero=> simp [disk,radius,gold,debt]
| succ n h=> simp only[disk,radius,gold,debt,Nat.cast_add,Nat.cast_one,h.2.2,h.2.1,eq_self,and_true,max_le_iff,add_mul,one_mul]; exact ⟨Nat.le_trans h.1 (Nat.le_add_right ..),Nat.le_trans (size_nsmul ..) (Nat.le_add_right ..)⟩

def little (v:Cover)(n:ℕ):= mix (mon (-(n • v))) (disk v (n+n))
lemma little_fee (v:Cover)(n:ℕ): (little v n).gold=(n:ℝ)+n ∧ (little v n).debt=(n:ℝ)+n ∧ (little v n).radius≤ 3*n*Laurent.size v:=by
    obtain ⟨hv,h,hp⟩:=disk_cost v (n+n); simp only[little,gold,debt,radius,Nat.cast_add,h,hp, one_mul,true_and, Laurent.size_neg] ; apply (Nat.add_le_add (size_nsmul ..) hv).trans; exact le_of_eq (by ring)
lemma little_step (v:Cover)(n:ℕ)(f:Cover→A)(x:Cover): take (take f (Δ v)) (little v n) x=f (x+n • v)-f (x-n • v):=by
 rw [little,take,take,rope]; dsimp only; rw [show take (take f (disk v (n+n))) (Δ v)=_ from disk_step v f (n+n), rises]; rw [← sub_eq_add_neg,add_smul]; congr 2; abel

def pack (P:Fin 4→Sheaf):=duo (duo (P 0) (P 1)) (duo (P 2) (P 3))
def band (v:Cover):=pack fun i=> scale (Pull.cash i) (little v (Pull.steps i))
lemma pack_take (X:Fin 4→Sheaf)(f:Cover→A): take f (pack X)=∑ i:Fin 4,take f (X i) := by rw [pack,Fin.sum_univ_four,take,take,take]; abel
lemma calc_fd (v:Cover)(f:Cover→A)(x:Cover): take (take f (band v)) (Δ v) x= Pull.dTap (fun l=> f (x+l • v)) 0:=by
 rw [rope,band,pack_take,Finset.sum_apply]; unfold Pull.dTap; apply Finset.sum_congr rfl; intro i _; rw [take,Pi.smul_apply,little_step]; simp [sub_eq_add_neg]
lemma pack_bill (P:Fin 4→Sheaf): (pack P).debt=∑ i:Fin 4,(P i).debt := by rw [pack,debt,debt,debt,Fin.sum_univ_four]; abel
lemma pack_pay (P:Fin 4→Sheaf): (pack P).gold=∑ i:Fin 4,(P i).gold:=by rw [pack,gold,gold,gold,Fin.sum_univ_four]; abel
lemma pack_r (P:Fin 4→Sheaf)(t:ℕ)(h:∀ i,(P i).radius ≤ t): (pack P).radius ≤ t:=by simp only [pack,radius]; exact max_le (max_le (h _) (h _)) (max_le (h _) (h _))
private lemma gold_band (v:Cover):(band v).gold=1:=by
 rw [band,pack_pay]; simp_rw [gold, (little_fee ..).1]; have h:=Pull.credit 1 (by decide); simpa only [pow_one,sub_neg_eq_add,if_true] using h
lemma band_fee (v:Cover): (band v).gold=1∧(band v).radius ≤ 12*Laurent.size v∧(band v).debt ≤ 32:=by
 refine ⟨gold_band v, pack_r _ _ (fun i=>?_),?_⟩
 · refine (little_fee v _).2.2.trans (Nat.mul_le_mul_right _ ?_)
   fin_cases i<;> norm_num [Pull.steps]
 rw [band,pack_bill]; simp_rw [debt,(little_fee ..).2.1]; rw [Fin.sum_univ_four,show Pull.cash 2 = 4/105 from rfl,show Pull.cash 3= -1/280 from rfl]; norm_num [Pull.cash,Pull.steps]
end Sheaf
end YM.Trace.Perfect

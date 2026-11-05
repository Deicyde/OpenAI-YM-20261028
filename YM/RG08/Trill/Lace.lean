import YM.RG08.Lagoon.Socks
import YM.Analysis.SmoothJets
/-! # Test monomial α costs per ordinary axis derivative, no factorial absorbed.
 Canonical finite test/profile contraction dictionary. test derivatives at actual endpoints via ordered seats.
 Rescaling/currency Fk sec kforms. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Trill
open Function Finset Jetty Lagoon
open scoped Classical Topology ContDiff
variable {q d:ℕ}

abbrev pedal:= Axis→ℕ
def stepUp (i:Axis) : pedal:=Pi.single i 1
def faceT (v:pedal)(x:E4):ℝ:=∏ i,x i ^ v i
def weight (v:pedal):=∑ i:Axis,v i
def capture (s:Cargo q):pedal:= ∑ i:Fin q,stepUp (s i)
def beta (v:pedal):ℕ:=∏ i,(v i).factorial
lemma beta_nz (v:pedal):beta v ≠0:= Finset.prod_ne_zero_iff.mpr fun _ _=>Nat.factorial_ne_zero _ -- check
lemma faceT_add (u v:pedal)(x:E4):faceT (u+v) x=faceT u x * faceT v x:=by simp_rw [faceT,Pi.add_apply,pow_add,Finset.prod_mul_distrib]
lemma faceT_one (i:Axis)(x:E4):faceT (stepUp i) x=x i:=by unfold stepUp faceT;simp [Pi.single_apply]
lemma capture_cons (i:Axis)(s:Cargo q):capture (Fin.cons i s)=stepUp i+capture s:=by unfold capture;simp [Fin.sum_univ_succ]
lemma weight_capture {q}(s:Cargo q):weight (capture s)=q:=by
 unfold weight capture; simp_rw [Finset.sum_apply]; rw [sum_comm];simp [stepUp,Pi.single_apply]
lemma capture_act (s:Cargo q)(x:E4):faceT (capture s) x= (pal s).val x:=by
 induction q with
 | zero=> simp only [capture,Finset.univ_eq_empty, sum_empty];simp [faceT,pal,profile]; -- step n=0
 | succ q hi=> rw [← Fin.cons_self_tail s,capture_cons,faceT_add,faceT_one,hi];unfold pal profile; simp [Fin.prod_univ_succ]; left; rfl

lemma capture_all (v:pedal):∃ s:Cargo (weight v),capture s=v:=by
 -- strip by recursion on q excluding type intros.
 suffices h:∀ n:ℕ,∀ v:pedal,weight v=n→∃ s:Cargo n,capture s=v by exact h _ v rfl
 intro n;induction n with
 | zero=>intro v hv; refine ⟨Fin.elim0,?_⟩;rw [capture,sum_of_isEmpty];exact (funext fun i=>show v i=0 by have h:=single_le_sum (f:=v) (by simp) (mem_univ i);change v i≤weight v at h;omega).symm
 | succ n ih=>
    intro v hv; obtain ⟨i,hi⟩:∃ i,v i>0:=by by_contra! h;have hx:v=0:=funext fun i=>le_antisymm (h i) (Nat.zero_le _);simp [weight,hx] at hv
    let w:pedal:=Function.update v i (v i-1)
    have ht:stepUp i+w=v:=by funext j; by_cases h:j=i; subst i; simpa [w,stepUp] using (show 1+(v j-1)=v j by omega);simp [h,stepUp,w]
    have hr:=congrArg weight ht;simp only [weight,Pi.add_apply,sum_add_distrib,show ∑ a:Axis,stepUp i a=1 by simp [stepUp,Pi.single_apply]] at hr
    change 1+weight w=weight v at hr
    obtain ⟨s,hs⟩:=ih w (by omega)
    refine ⟨Fin.cons i s,?_⟩;rw [capture_cons,hs,ht]

def concert (v:pedal):Cargo (weight v):=Classical.choose (capture_all v)
lemma concert_at (v:pedal):capture (concert v)=v:=Classical.choose_spec (capture_all v)
def celloTest (v:pedal):Pearl:=((beta v:ℝ)⁻¹) • pal (concert v)
lemma cello_val (v:pedal)(x:E4):(celloTest v).val x=(beta v:ℝ)⁻¹ * faceT v x:=by unfold celloTest;change ((beta v:ℝ)⁻¹) * _=_;rw [←capture_act,concert_at]

lemma faceT_down (i:Axis)(v:pedal)(x:E4): fderiv ℝ (faceT v) x (basis i)=(v i:ℝ)*faceT (Function.update v i (v i-1)) x:=by
 let F(j:Axis):E4→L[ℝ]ℝ:= EuclideanSpace.proj (𝕜:=ℝ) j
 have h:=HasFDerivAt.finsetProd (u:=univ) (x:=x) (g:=fun j u=> (u j)^v j) (g':=fun j=> (v j • (F j x) ^ (v j-1)) • F j) (fun j _=>(F j).hasFDerivAt.pow (v j))
 unfold faceT;rw [h.fderiv];rw [_root_.sum_apply, sum_eq_single i]
 · let w:pedal:=Function.update v i (v i-1)
   rw [_root_.smul_apply,_root_.smul_apply,show F i (basis i)= (1:ℝ) from by change basis i i=1; simp]
   change (∏ j∈ (univ: Finset Axis).erase i, x j ^ v j) • ((v i • (x i) ^ (v i-1)) • (1:ℝ))=(v i:ℝ)*∏ j,x j^w j
   rw [←Finset.mul_prod_erase (s:=univ) (f:=fun j=>x j ^ w j) (mem_univ i), show w i = v i - 1 from Function.update_self ..]
   rw [show (∏ j∈ (univ:Finset Axis).erase i, x j^w j)=∏ j∈(univ:Finset Axis).erase i,x j ^ v j from Finset.prod_congr rfl (fun j hj=> by unfold w; simp [(Finset.mem_erase.mp hj).1])];simp only [nsmul_eq_mul,smul_eq_mul];ring
 · intro j hj hh;rw [_root_.smul_apply,_root_.smul_apply,show F j (basis i)=0 from by change basis i j=0;simp [hh]];simp
 simp
-- factorial directly, at normalized dual
lemma descend (v:pedal)(i:Axis): YM.Analysis.D (basis i) (celloTest v).val = if v i=0 then 0 else (celloTest (Function.update v i (v i-1))).val:=by
 funext x;let w:pedal:=Function.update v i (v i-1); let s:= (univ:Finset Axis).erase i
 unfold YM.Analysis.D;rw [show (celloTest v).val=(beta v:ℝ)⁻¹ • faceT v from funext fun u=>cello_val v u, fderiv_const_smul -- signature?
   ,_root_.smul_apply,faceT_down]; rotate_left
 · unfold faceT;exact (show ContDiff ℝ 1 (fun x:E4=>∏ j:Axis, x j ^ v j) from contDiff_prod (fun j _=> ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.pow ..))).differentiable (by norm_num) x
 by_cases h:v i=0; · simp [h]
 have he: beta v = beta w*(v i):=by
    unfold beta; rw [←mul_prod_erase (s:=univ) (f:=fun j=>(v j).factorial) (mem_univ i),←mul_prod_erase (s:=univ) (f:=fun j=>(w j).factorial) (mem_univ i),show w i=v i-1 from Function.update_self .., show (v i).factorial=v i*(v i-1).factorial from by
      have hh: (v i-1)+1=v i:=Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h)
      rw [←hh,Nat.factorial_succ,Nat.add_sub_cancel]]
    rw [show ∏ j∈s,(w j).factorial=∏ j∈s,(v j).factorial from Finset.prod_congr rfl (fun j hj=>by unfold w; simp [(Finset.mem_erase.mp hj).1])];ring -- rw s fail
 rw [if_neg h,cello_val];rw [he]; push_cast
 change _=(beta w:ℝ)⁻¹ * _;have ht:(v i:ℝ)≠0:=by exact_mod_cast h
 rw [mul_inv,smul_eq_mul];field_simp

lemma faceT_flat (v:pedal):faceT v 0= if v=0 then 1 else 0:=by
 split_ifs with hv; simp [hv,faceT]
 obtain ⟨i,hi⟩:=not_forall.mp (mt funext hv); unfold faceT; apply prod_eq_zero (mem_univ i); exact zero_pow hi

/-- actual axis derivative evaluated on normalized test letter, includes repeated coordinates. -/
lemma cello_dual (v:pedal)(s:Cargo q):loot s 0 (celloTest v) = if capture s = v then 1 else 0:=by
 induction q generalizing v with
 | zero=> change iteratedFDeriv ℝ 0 (celloTest v).val (0:E4) (basis ∘ s) = if capture s=v then (1:ℝ) else 0;simp [capture,cello_val,faceT_flat,beta,eq_comm];split_ifs <;> simp_all
 | succ q ih=>
    let i:=s 0;let t:=Fin.tail s
    change iteratedFDeriv ℝ (q+1) _ 0 (basis ∘ s)=_
    have hx:basis ∘ s=Fin.cons (basis i) (basis ∘ t):=by rw [← Fin.cons_self_tail (basis ∘ s)];rfl
    rw [hx,YM.Analysis.cons_inner ((celloTest v).order _|>.contDiffAt),descend]
    have ht:capture s=stepUp i+capture t:=by conv_lhs=> rw [← Fin.cons_self_tail s];exact capture_cons ..
    by_cases h:v i=0
    · rw [if_pos h,if_neg (show capture s≠v from fun H=>by have hz:=congrFun (ht.symm.trans H) i;simp [stepUp,h] at hz)]
      rw [iteratedFDeriv_zero];rfl
    rw [if_neg h];change loot t _ _=_;rw [ih,ht]
    congr 1;ext -- a=b Prop
    constructor
    · intro hx; rw [hx];funext j; by_cases hc:j=i;subst j; simp [stepUp]; omega; simp [stepUp,hc]
    intro H; funext j; have hh:=congrFun H j; by_cases hc:j=i;subst j; simp [stepUp] at hh ⊢; omega; simpa [stepUp,hc] using hh
end YM.RG08.Trill

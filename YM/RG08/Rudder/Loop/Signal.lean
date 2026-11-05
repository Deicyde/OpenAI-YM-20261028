import YM.RG08.Rudder.Loop.Null
import Mathlib.Logic.Equiv.Fintype

noncomputable section
namespace YM.RG08.Rudder.Loop
open scoped Topology BigOperators Classical ENNReal
open Forms Packets Finset Function Lattice Laurent Pert.Bulk Exterior AnalyticNext.QuarticMatch.BoxChain Symmetry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
local notation "o"=> (0:Fin 2)
local notation "p"=> (Fin.succ (0:Fin 1))
variable {I:Type}{F: Raw I 2}

private lemma distinguishing {a b:Tablet} (h:a.card=b.card)(he:a≠b): ∃ i,i∈a∧i∉b:=by
 by_contra! H;exact he (Finset.eq_of_subset_of_card_le H h.ge)
lemma reflect_flag (a:Tablet)(i:Axis):marks (Signed.mirror i) a=a:=by simp [marks,Signed.mirror]
lemma reflect_toll (a:Tablet)(i:Axis):toll (Signed.mirror i) a=if i∈a then -1 else 1:=by
 have he:address (Signed.mirror i) a=1:=by
    unfold address;split_ifs with h
    · let b:Lattice.PlaqAxes:=plaqEquiv.symm ⟨a,h⟩
      change arrow b.val.1 b.val.2=1;exact if_pos b.property
    rfl
 rw [toll,he,mul_one]
 have hh(j:Axis):Symmetry.spin (Signed.mirror i) j = if i=j then -1 else 1:=by by_cases h:i=j<;>simp [h,Signed.mirror,Symmetry.spin]
 simp_rw [hh,Finset.prod_ite_eq]

def spectrum (F:Raw I 2)(a b:Tablet)(y:Tape 2 I):ℝ := load (col (hum F y) a b)
lemma spectrum_off (h:Cohort F)(H:Symmetry.Cardinal F)(hF:Graded F 2)(a b:Tablet)(he:a≠b)(y:Tape 2 I):spectrum F a b y=0:=by
 by_cases hh:a.card=b.card
 · obtain ⟨i,ha,hb⟩:=distinguishing hh he
   have ht:=orbit_load H h y (Signed.mirror i) a b
   rw [reflect_toll,reflect_toll,reflect_flag,reflect_flag,if_pos ha,if_neg hb] at ht
   unfold spectrum;linarith
 unfold spectrum load
 rcases show a.card≠2∨b.card≠2 by omega with h₁|h₂
 · have hz(x:Cover):col (hum F y) a b x=0:=hF y o _ h₁
   simp [hz]
 have hz(x:Cover):col (hum F y) a b x=0:=hF y p _ h₂
 simp [hz]
lemma spectrum_on (h:Cohort F)(H:Symmetry.Cardinal F)(a b:Tablet)(he:a.card=b.card)(y:Tape 2 I): spectrum F a a y=spectrum F b b y:=by
 obtain ⟨s,hs⟩:= Equiv.Perm.exists_map_finset_eq a b he
 let t:Signed:=⟨s,fun _=>false⟩
 have he:marks t a=b:=by simpa [t,marks, Finset.map_eq_image] using hs
 have hx:=orbit_load H h y t a a; rw [← sq,toll_sq,one_mul,he] at hx;exact hx
lemma spectrum_sym (h:Cohort F)(H:Forms.Sym F)(a b:Tablet)(y:Tape 2 I):spectrum F a b y=spectrum F b a (y ∘ Equiv.swap o p):=by
 have he(v:Cover):col (hum F y) a b v=col (hum F (y ∘ Equiv.swap o p)) b a (-v):=by
   let x:=place ((0,a):_×Tablet) (v,b)
   have he:lyre (place ((v,b):_×Tablet) (0,a)) (y ∘ Equiv.swap o p)=(lyre x y ∘ ⇑(Equiv.swap o p)):=by
      ext i:1;cases i using Fin.cases with
      | zero=> simp [lyre,x,place]
      | succ i=>rw [Subsingleton.elim i (0:Fin 1)];change _=lyre x y (Equiv.swap o p p);rw [Equiv.swap_apply_right];simp [lyre,x,place]
   have hh:= congrFun (H (Equiv.swap o p)) (lyre x y)
   calc
   _ = F (lyre (place (v,b) (0,a)) (y ∘ ⇑(Equiv.swap o p))) := he ▸ hh.symm -- ?
   _ = _:=by
      change hum F _ _=_;rw [prices (show Cohere (hum F (y ∘ ⇑(Equiv.swap o p))) from fun t x=>h t (lyre x _))]
      simp
 unfold spectrum load;simp_rw [he]; exact (Equiv.neg _).tsum_eq _
end YM.RG08.Rudder.Loop

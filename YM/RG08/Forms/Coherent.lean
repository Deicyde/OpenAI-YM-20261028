import YM.RG08.Forms.Dial
import YM.RG08.Forms.PontChange

noncomputable section
namespace YM.RG08.Forms
open Pert.Bulk Packets Finset Function Lattice Laurent
open scoped Topology BigOperators ENNReal Classical
set_option autoImplicit false
variable {I J:Type}{n p:ℕ}{σ B:ℝ}

def sway (p:Cover)(x:Tape n (Market I)):Tape n (Market I):=pass p ∘ x
def Cohort (F : Flake n (Market I)):=∀ p x,F (sway p x)=F x
lemma pass_zero (x:Market I):pass 0 x=x:=by simp [pass]
lemma pass_pass (p q:Cover)(x:Market I):pass p (pass q x)=pass (p+q) x:=by unfold pass;congr 1;dsimp;abel

def sail (p:Cover):Equiv.Perm (Market I):=⟨pass p,pass (-p),fun x=>by rw [pass_pass,neg_add_cancel,pass_zero],fun x=>by rw [pass_pass,add_neg_cancel,pass_zero]⟩
lemma sway_zero (x:Tape n (Market I)):sway 0 x=x:=funext (fun _=>pass_zero _)
lemma sway_sway (p q:Cover)(x:Tape n (Market I)):sway p (sway q x)=sway (p+q) x:=funext fun _=>pass_pass ..
def tides (p:Cover):Equiv.Perm (Tape n (Market I)):=⟨sway p,sway (-p),fun x=>by rw [sway_sway,neg_add_cancel,sway_zero],fun x=>by rw [sway_sway,add_neg_cancel,sway_zero]⟩
lemma sway_cons (p:Cover)(x:Market I)(y:Tape n (Market I)):Fin.cons (sail p x) (sway p y)=sway p (Fin.cons x y):=by ext i:1;cases i using Fin.cases <;> rfl

variable {F T:Flake n (Market I)}
lemma Cohort.smul (h:Cohort F)(a:ℝ):Cohort (a • F):=fun _ _=>congr_arg (a • ·) (h ..)
lemma Cohort.add (h:Cohort F)(H:Cohort T):Cohort (F+T):=fun _ _=>congr_arg₂ (·+·) (h ..) (H ..)
lemma Cohort.neg(h:Cohort F):Cohort (-F):=fun _ _=>congr_arg Neg.neg (h ..)
lemma Cohort.sub (h:Cohort F)(H:Cohort T):Cohort (F-T):=h.add H.neg
lemma Cohort.sum {J:Type}(s:Finset J)(F:J→Flake n (Market I))(he:∀ i∈s,Cohort (F i)):Cohort (s.sum F):=by intro u x;simp only [Finset.sum_apply];exact sum_congr rfl fun i hi=>he i hi u x
lemma Cohort.clean (h:Cohort F):Cohort (bleach F):= by
 unfold bleach; apply Cohort.smul;apply Cohort.sum;intro i _ p x; unfold woven; exact h p (x ∘ i)

lemma Cohort.raft' (h:Cohort F){K:Cables n (Market I) (Market J)}(he:∀ i,city 1 (K i)):Cohort (raft K F):=by
 intro u x; rw [raft,raft,←(tides u).tsum_eq];apply tsum_congr;intro y
 change F (sway u y)*(∏ i,K i _ _)=_
 unfold vat design; rw [h];congr 1; refine prod_congr rfl fun i _=> ?_
 simpa only [tides,sway,Equiv.coe_fn_mk,comp_apply,one_smul,show (1:Side).val=1 from rfl] using he i (y i) (x i) u

variable {Γ:Kernel I I}
lemma Cohort.lap' {F:Flake (n+2) (Market I)}(h:Cohort F)(he:city 1 Γ):Cohort (lap Γ F):=by
 unfold Forms.lap;apply Cohort.clean
 intro u x; unfold run lam;rw [← (Equiv.prodCongr (sail u) (sail u)).tsum_eq]; apply tsum_congr;rintro ⟨j,k⟩
 change F (Fin.cons (sail u j) (Fin.cons (sail u k) (sway u x))) * Γ (sail u j) (sail u k)=_
 rw [sway_cons,sway_cons,h];congr 1;simpa only [sail,Equiv.coe_fn_mk,one_smul,show (1:Side).val=1 from rfl] using he j k u

lemma Cohort.bridge' {F:Flake (n+1) (Market I)}{G:Flake (p+1) (Market I)}(h:Cohort F)(hh:Cohort G)(he:city 1 Γ):Cohort (bridge Γ F G):=by
 unfold bridge;apply Cohort.clean
 intro u x; unfold weld seam;rw [← (Equiv.prodCongr (sail u) (sail u)).tsum_eq]; apply tsum_congr; rintro ⟨j,k⟩
 change F (Fin.cons (sail u j) (sway u (fun i=>x (Fin.castAdd p i))))*Γ (sail u j) (sail u k)*G (Fin.cons (sail u k) (sway u (fun i=>x (Fin.natAdd n i))))=_
 rw [sway_cons,h,sway_cons,hh];have hx:Γ (sail u j) (sail u k)=Γ j k:=by simpa only [sail,Equiv.coe_fn_mk,one_smul,show (1:Side).val=1 from rfl] using he j k u
 rw [hx]

end YM.RG08.Forms

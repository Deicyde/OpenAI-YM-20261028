import YM.RG08.Invert.Frequency
/-!
 # Unmodified before-block kernels at true offsets in inversion. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Invert
open Function Filter Lattice Wilson Exterior Precision Laurent Next.Free Next.Free.Flight RG RG.Supply Bloch Input Finset Matrix
open Planned.PrimaryIntegral295 Carrier
open scoped BigOperators Topology Real Classical Matrix
variable {G:Gauge}{i j k t r:ℕ}{L c f:Side}

def brim (a:TypeFace r):Cover:= ∑ i∈a.val,step i
lemma crown (p:Momentum)(a:TypeFace r) : inventory a (penny p)=(-1:ℂ)^r* mode p (brim a):= by
   have hp (v:Finset Axis): inventory (r:=v.card) ⟨v,rfl⟩ (penny p)=(-1:ℂ)^v.card*mode p (∑ i∈v,step i):= by
      unfold inventory; induction v using Finset.induction_on with
      | empty=>simp
      | insert i t h ih=>
         change (∏ j∈t,penny p j)=_ at ih; change (∏ j∈insert i t,penny p j)=_; rw [prod_insert h,card_insert_of_notMem h,sum_insert h,mode_shift,ih,penny_at]; ring
   obtain ⟨a,h⟩:=a; subst r; exact hp a

def pole (a:TypeFace r) (x:Cover) := -x-brim a
def twin (a:TypeFace r): Equiv.Perm Cover:= (Equiv.neg Cover).trans (Equiv.addRight (-brim a))
lemma tw_p (a:TypeFace r)(x:Cover): twin a x=pole a x:= (sub_eq_add_neg ..).symm
lemma backwards (p:Momentum)(a:TypeFace r)(x:Cover): mode (-p) (pole a x)=mode p x*mode p (brim a) := by unfold pole; rw [sub_eq_add_neg,mode_shift]; simp

def localeV {α β:Type} (W:Cross L α β) (x:Cover)(a:α)(b:β)(y:Cover): ℝ := W (wrap L x,a) b (y-cellar L x)
lemma leer {u: Thread i j (TypeFace r) (TypeFace r)}(h:Secured u)(P:Flight i j) (e:ℕ)(x:Cover)(a b:TypeFace r)(p:Momentum)(hx:p∈baseCube):
    RRead (localeV (meshBook u e [] P) x a b) p= ∑ l:Site P.L, (mode (aliasAt p l) x * toll P.L e)*u P p l a b:=by
    let v:= meshBook u e [] P; let w:= lift (wrap P.L x); let k:= cellar P.L x; let f:= v (wrap P.L x,a) b
    have he : RRead f p= spread u e [] P (wrap P.L x) p a b:= h.bankRead P.legal e (by simp) P _ hx a b
    have ht: RRead (localeV v x a b) p = mode p k* RRead f p:= market_move ..
    rw [ht,he]; unfold spread listChip; rw [Matrix.sum_apply,mul_sum]; refine sum_congr rfl fun i _=>?_
    have hz:mode p k*mode (aliasAt p i) w=mode (aliasAt p i) x:= by conv_rhs=> rw [balance P.L x,mode_shift,← mode_scale,alias_scale,mode_phase,mode_periodic,mul_one,mul_comm];
    rw [← hz]; simp only [Matrix.smul_apply,smul_eq_mul,List.map_nil,List.prod_nil,mul_one]; change _*(mode _ w*_)=(mode _ k * _ *_)*_; ring
set_option maxHeartbeats 520000 in
lemma coherent {u: Thread i j (TypeFace r) (TypeFace r)}(h:Secured u)(P:Flight i j) (e:ℕ)(hh:∀ p∈baseCube,∀ l:Site P.L, shineF (aliasAt p l) r * u P (-p) (-l)=u P p l * shineF p r) (x y:Cover)(a b:TypeFace r):
     let A:= meshBook u e [] P; localeV A x a b y=localeV A (pole a x) a b (pole b y):=by
    intro A; let F x:= localeV A x a b; let x':=pole a x; let G:= F x'∘ twin b
    suffices hx:F x=G by rw [← tw_p b y]; exact congr_fun hx y
    have hx (x): Summable (fun i=> ‖F x i‖):= shift_sound _ (h.bankSafe P.legal e (u:=[]) (by simp) P _ _) _ -- param
    refine RRead_injective (hx x) ((twin b).summable_iff.mpr (hx x')) ?_; intro p hp
    apply mul_right_cancel₀ (mode_ne p (brim b))
    have hv: RRead G p* mode p (brim b)=RRead (F x') (-p):=by
       unfold RRead Laurent.read; rw [← tsum_mul_right]; rw [← (twin b).tsum_eq (fun i:Cover=> mode (-p) i • (↑(F x' i):ℂ))]; apply tsum_congr; intro i
       simp only [tw_p,G,Function.comp_apply,backwards,smul_eq_mul]; ring
    change RRead (F x) p * _= _; rw [hv]; simp_rw [show RRead (F x) p=_ from leer h P e x a b p hp,show RRead (F x') (-p)= _ from leer h P e x' a b (-p) (by simpa only [sig_act] using signed_base hp sigma)];
    rw [Finset.sum_mul]; rw [← Equiv.sum_comp (Equiv.neg (Site P.L)) (fun l=>mode (aliasAt (-p) l) x' * toll P.L e*u P (-p) l a b)]; -- which sum?
    apply Finset.sum_congr rfl; intro l _; let q:= aliasAt p l
    have hL:= congr_fun (congr_fun (hh p hp l) a) b
    unfold shineF mask at hL; rw [Matrix.diagonal_mul,Matrix.mul_diagonal,crown,crown] at hL
    simp only [Equiv.neg_apply,alias_reverse p P.odd, x',backwards]
    have ht:mode q (brim a)*u P (-p) (-l) a b=u P p l a b*mode p (brim b):= by apply mul_left_cancel₀ (show (-1:ℂ)^r≠ 0 by simp); simpa only [mul_left_comm (u P p l a b),← mul_assoc] using! hL
    calc
       _ = (mode q x*toll P.L e) * (u P p l a b*mode p (brim b)):= by ring -- align
       _ = _ := by rw [← ht]; dsimp only [q]; ring
lemma axisKeep (P:Flight i j) (v:ℝ)(h:0<v)(hk:4 ≤ j)(a b:TypeFace 1)(x y) : localeV (P.duo v).A0 x a b y=localeV (P.duo v).A0 (pole a x) a b (pole b y):= coherent (secure_both v h P.legal hk).1 P _ (fun p hp i=>prospect P v p h hp i|>.1) x y a b
lemma angleKeep (P:Flight i j) (v:ℝ)(h:0<v)(hk:4 ≤ j)(a b:TypeFace 2)(x y) : localeV (P.duo v).T x a b y=localeV (P.duo v).T (pole a x) a b (pole b y):= coherent (secure_both v h P.legal hk).2 P _ (fun p hp i=>prospect P v p h hp i|>.2) x y a b
end YM.RG08.Invert

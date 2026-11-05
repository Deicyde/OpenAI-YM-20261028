import YM.RG08.Forms.Ground

noncomputable section
namespace YM.RG08.Forms
open Pert.Bulk Packets Finset Function
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false
variable {I : Type} {p q n : ℕ}

/- Basic equivalences and Tonelli reindexings. -/
theorem tsum_cons (f : Tape (p+1) I→ℝ≥0∞) : ∑' x,f x = ∑' (a : I),∑' (x : Tape p I), f (Fin.cons a x) := by
 rw [← (Fin.consEquiv (fun _:Fin (p+1)=>I)).tsum_eq f, ENNReal.tsum_prod']
 rfl

theorem tsum_append (f : Tape (p+q) I→ℝ≥0∞) : ∑' x,f x = ∑' (a : Tape p I),∑' (x : Tape q I), f (Fin.append a x) := by
 rw [← (Fin.appendEquiv p q).tsum_eq f, ENNReal.tsum_prod']
 rfl

lemma ensign_face {V : Tape (p+1) I→ℝ≥0∞} (z : I) :
   ∑' w, row V 0 z w = ∑' (x:Tape p I), V (Fin.cons z x) := by
 rw [tsum_cons, ENNReal.tsum_comm]
 simp only [row,Fin.cons_zero]; simp [tsum_ite_eq] -- ?

lemma ensign_later {V : Tape (p+1) I→ℝ≥0∞} (i : Fin p) (z : I) :
   ∑' w, row V i.succ z w = ∑' (x:Tape p I), ∑' a : I,row (fun w=> V (Fin.cons a w)) i z x := by
 rw [tsum_cons, ENNReal.tsum_comm]; simp only [row,Fin.cons_succ]

def twist (e : Equiv.Perm (Fin n)) : Equiv.Perm (Tape n I) where
 toFun f:=f ∘ e
 invFun f:=f ∘ e.symm
 left_inv:= fun f=>funext fun i=>congr_arg f (e.apply_symm_apply i)
 right_inv:=fun f=>funext fun i=>congr_arg f (e.symm_apply_apply i)

def woven (F : Flake n I) (e : Equiv.Perm (Fin n)) : Flake n I:= fun x=> F (x ∘ e)

def Sym (F : Flake n I):Prop:=∀ e,woven F e=F

def bleach (F : Flake n I) : Flake n I:= ((Fintype.card (Equiv.Perm (Fin n)):ℝ)⁻¹) • ∑ e,woven F e

theorem symmetric (F : Flake n I) : Sym (bleach F) := by
 intro e; ext x
 simp only [woven,bleach,Pi.smul_apply,Finset.sum_apply]
 congr 1
 -- (x∘e)∘e' = x ∘ (e' *? e)
 refine Fintype.sum_equiv (Equiv.mulLeft e) (fun e'=> F ((x ∘ ⇑e) ∘ ⇑e')) (fun e'=> F (x ∘ ⇑e')) ?_
 intro e';rfl

theorem bleached {F : Flake n I} (hF : Sym F) : bleach F=F := by
 unfold bleach
 simp_rw [hF _]
 simp only [sum_const,card_univ]
 ext x
 simp only [Pi.smul_apply,smul_eq_mul,nsmul_eq_mul]
 simp

lemma Sym.zero : Sym (0 : Flake n I) := fun _ => rfl
lemma Sym.add {F F' : Flake n I}(h : Sym F)(h' : Sym F') : Sym (F+F') := by
 intro e; exact congrArg₂ (fun (v w : Flake n I)=>v+w) (h e) (h' e)
lemma Sym.smul {F : Flake n I}(h : Sym F) (a : ℝ) : Sym (a • F) := by intro e; exact congr_arg (a • ·) (h e)

lemma bleach_add (F F' : Flake n I) : bleach (F+F') = bleach F+bleach F':= by
 unfold bleach;rw [←smul_add,←Finset.sum_add_distrib]; rfl
lemma bleach_sub (F F' : Flake n I) : bleach (F-F')=bleach F-bleach F':=by
 unfold bleach;rw [←smul_sub,←Finset.sum_sub_distrib];rfl

variable {d : Ground I} {σ C : ℝ} {F : Flake n I}
lemma Held.perm (h : Held d σ C F) (e : Equiv.Perm (Fin n)) : Held d σ C (woven F e) := by
 rw [ensign]
 intro i z
 have he (x : Tape n I): row (mark d σ (woven F e)) i z x=row (mark d σ F) (e.symm i) z (twist e x):=by
   simp only [row,mark,woven,twist,Equiv.coe_fn_mk,comp_apply,e.apply_symm_apply,d.radius_perm]
 simp_rw [he,(twist (I:=I) e).tsum_eq];exact (ensign.mp h) _ z

lemma Held.bleach (h : Held d σ C F) (hC : 0≤C) : Held d σ C (Forms.bleach F) := by
 let w:ℝ:=Fintype.card (Equiv.Perm (Fin n))
 have hw:0<w:=Nat.cast_pos.mpr Fintype.card_pos
 unfold Forms.bleach
 apply (Held.smul w⁻¹ (Held.sum _ _ (fun _=> C) (fun _ _=> hC) fun e _=> h.perm e)).mono le_rfl ?_ (fun _=>le_rfl)
 simp only [sum_const,card_univ,nsmul_eq_mul,← mul_assoc,abs_of_pos (inv_pos.mpr hw),← show w=(Fintype.card (Equiv.Perm (Fin n)):ℝ) from rfl, inv_mul_cancel₀ (ne_of_gt hw), one_mul]; rfl

/-- Diameter Held charge gives the previously used Folded charge, spending a fixed arity
factor in width. No loss of expense constants beyond that. -/
def spin {I : Type} (F : Flake (n+1) (Market I)) : Packet n I := fun i x=> F (Fin.cons i x)
theorem Held.fold {I : Type}{σ C : ℝ} {F : Flake (n+1) (Market I)} (h : Held (carpet I) (n*σ) C F) (hs : 0 ≤ σ) : Folded σ (spin F) C := by
 intro i
 calc
   _ ≤ ∑' x : Tape n _, mark (carpet I) (n*σ) F (Fin.cons i x) := by
     apply ENNReal.tsum_le_tsum
     intro x
     unfold mark spin
     refine bill_mono le_rfl ?_
     have haux (j : Fin n) : sep i.1 (x j).1 ≤ (carpet I).radius (Fin.cons i x) := by
       simpa [carpet,HAdd.hAdd] using (carpet I).le_radius (Fin.cons i x) 0 j.succ
     have he := mul_le_mul_of_nonneg_left
       (Finset.sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin n))) => haux j) hs
     simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at he
     unfold expense
     linarith [he]
   _ ≤ _ := by rw [← ensign_face]; exact (ensign.mp h) 0 i

/- Conversely on a symmetric positive-rank tensor, spend factor two of width across
its distinguished root to get diameter. Any slot holds at no additional cost. -/
private lemma all_slots {d : Ground I}{F : Flake (n+1) I} (hF:Sym F) (σ C : ℝ)
    (hf : ∀ z,∑' w,row (mark d σ F) 0 z w ≤ ENNReal.ofReal C) : Held d σ C F := by
 rw [ensign];intro i z
 let e:=Equiv.swap 0 i
 have hi : e i=0:=Equiv.swap_apply_right ..
 have he (x : Tape (n+1) I):row (mark d σ F) i z (twist e x)=row (mark d σ F) 0 z x:=by
   have h:F (x ∘ ⇑e)=F x:=congrFun (hF e) x
   simp only [row,mark,twist,Equiv.coe_fn_mk,comp_apply,hi,h,d.radius_perm]
 simp_rw [← (twist (I:=I) e).tsum_eq (row (mark d σ F) i z),he];exact hf z

theorem Held_of_folded {I : Type}{σ C : ℝ}{F : Flake (n+1) (Market I)} (hF : Sym F)(hs:0≤σ)(h : Folded (2*σ) (spin F) C) : Held (carpet I) σ C F := by
 apply all_slots hF
 intro i; rw [ensign_face]
 apply (ENNReal.tsum_le_tsum ?_).trans (h i)
 intro x; unfold mark spin
 refine bill_mono le_rfl ?_
 have hx :(carpet I).radius (Fin.cons i x) ≤ 2 * expense i x:=by
   have ht (j:Fin n):sep i.1 (x j).1≤expense i x:=Finset.single_le_sum (f:=fun j=>sep i.1 (x j).1) (fun j _=>sep_nonneg ..) (mem_univ j)
   have hz (j:Fin (n+1)):sep i.1 ((Fin.cons i x : Tape (n+1) (Market I)) j).1≤expense i x:=by
    cases j using Fin.cases <;> simp [sep_self,expense_nonneg,ht]
   apply (carpet I).radius_le _ (by nlinarith [expense_nonneg i x]); intro j k
   refine (sep_triangle _ i.1 _).trans ?_
   rw [sep_comm]; linarith [hz k,hz j]
 nlinarith
end YM.RG08.Forms

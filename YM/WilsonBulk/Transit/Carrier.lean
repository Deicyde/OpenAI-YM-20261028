import YM.WilsonBulk.Transit.Departures
import YM.WilsonBulk.Web.Volume

/-!
# Matching even across meshes; row and column periodization for multi-leg pulls.

No quotient and no hidden intermediate volume. Because keeps BOTH positions
in the transfer tests, the proof permits (no estimate yet on) measuring a
arbitrary support per leg. Also good for showing consistency against synth.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical BigOperators ENNReal
open Equiv Function Filter Finset Lattice Pert.Bulk Bloch
variable {X Y X' Y' : Type} {x : X} {p q M σ θ : ℝ} {P : X→ X'} {Q : Y→ Y'} {D : Rule X} {E : Rule Y} {m k n : ℕ}

structure GaugeLine (P : X→X') (Q : Y→Y') (A : Duct X Y) (B : Duct X' Y') : Prop where
  row x y : B (P x) y=∑' z:{z//Q z=y}, A x z.val
  col x y : B x (Q y)=∑' z:{z//P z=x}, A z.val y

def pintrail (a : X') (u : Legs X' n) (P : X→ X') : ({x//P x=a} × Trail P u) ≃ Trail P (hitch a u) where
  toFun z := ⟨hitch z.1.val z.2.val,by rw [hitch_comp,z.1.property,z.2.property]⟩
  invFun z := (⟨z.val 0,congr_fun z.property 0⟩,⟨crop z.val,by rw [← crop_comp,z.property,crop_hitch]⟩)
  left_inv z := Prod.ext (Subtype.ext (hitch_zero z.1.val z.2.val)) (Subtype.ext (crop_hitch z.1.val z.2.val))
  right_inv z := Subtype.ext (hitch_crop ..)

-- separate product on a fixed finite list of possibly different heads; useful many places
lemma tail_product (Q : X→ X') (f : Fin n→ X→ℝ) (h : ∀ i,Summable (f i)) (v : Legs X' n) :
    Summable (fun z:Trail Q v=> ∏ i,f i (z.val i)) ∧
      ∑' z: Trail Q v, ∏ i,f i (z.val i) = ∏ i,∑' z:{z//Q z=v i},f i z.val := by
  induction n with
  | zero =>
     let x : Trail Q v := ⟨Fin.elim0,Subsingleton.elim _ _⟩; letI : Unique (Trail Q v):= { default:=x, uniq:=fun y=> Subsingleton.elim _ _ }
     refine ⟨Summable.of_finite,?_⟩; simp
  | succ n ih =>
     revert v; refine legs_succ _ ?_; intro x v
     let e' := pintrail x v Q; let g : {z//Q z=x}→ℝ:= fun i=> f 0 i.val; let k : Trail Q v → ℝ:= fun z=> ∏ i:Fin n, f i.succ (z.val i)
     have hz : Summable g:= (h 0).subtype _
     obtain ⟨hk,hh⟩:= ih (crop f) (fun i=>h i.succ) v
     have ht (i : {z//Q z=x} × Trail Q v) : (∏ j,f j ((e' i).val j))=g i.1*k i.2 := by
       change (∏ j,f j (hitch _ _ j))=_; simp only [Fin.prod_univ_succ,hitch_succ,hitch_zero]; rfl
     refine ⟨(Equiv.summable_iff e').1 ((summable_mul_of_summable_norm hz.norm (show Summable k from hk).norm).congr (fun z=> (ht z).symm)),?_⟩
     rw [← e'.tsum_eq _, Fin.prod_univ_succ (f:=fun j=>∑' z:{z//Q z=hitch x v j}, f j z.val),tsum_congr ht,← tsum_mul_tsum_of_summable_norm hz.norm (show Summable k from hk).norm]
     exact congr_arg ((∑' z,g z)* ·) hh

variable {K : Legs (Duct X Y) (n+1)} {B : Legs (Duct X' Y') (n+1)} {R S : Fin (n+1)→ℝ} {d : Duct X Y}
variable {u : Page X (n+1)} {v : Page X' (n+1)}

lemma dispatched_inner (h : ∀ i, GaugeLine P Q (K i) (B i)) (p : ∀ i,AuditLine (K i) d (n+1) (R i) (S i)) (w : Legs X (n+1))
    (y : Y) (z : Legs Y' n) :
 (∑' t : Trail Q z, metal K u (hitch y t.val) w) = K 0 (w 0) y * (u w * lot (crop B) (P ∘ crop w) z) := by
  revert w; refine legs_succ _ ?_; intro x w
  have hk := (tail_product Q (fun i : Fin n=>K i.succ (w i)) (fun i=> (p i.succ).total_row _) z).2
  simp_rw [metal_head,tsum_mul_left]; rw [hitch_zero,crop_hitch]; unfold lot; simp only [Function.comp_apply,crop]; simp_rw [GaugeLine.row (h _)]; exact congr_arg (fun q=> K 0 x y*(u (hitch x w)*q)) hk

lemma quota_page (h : Orates P u v) (x : X) (v' : Legs X' n) {z : X'} (hh : P x=z) :
    v (hitch z v')=∑' a:Trail P v',u (hitch x a.val) := by subst z; rw [h 0 x _ (hitch_zero ..),bind_pin]
lemma event_trail (f : Legs X n→ℝ) (h : Summable f) (P : X→X') (x : Legs X' n) : Summable fun z : Trail P x=> f z.val := h.subtype _
lemma event_tsum {f : Legs X n→ℝ} (h : Summable f) (P : X→X') :
      ∑' v,f v = ∑' v',∑' z:Trail P v',f z.val := (h.hasSum.tsum_fiberwise (fun v:Legs X n=> P∘v)).tsum_eq.symm

set_option maxHeartbeats 100000 in
lemma dispatched (g : Geometry D E θ σ d) (he : ∀ i, AuditLine (K i) d (n+1) (R i) (S i)) (hv : Within D θ M u) (hp : 0≤σ)
    (h : Orates P u v) (hh : ∀ i,GaugeLine P Q (K i) (B i)) (y : Y) (z : Legs Y' n) :
    page Q 0 y (tele K u) (hitch (Q y) z)=tele B v (hitch (Q y) z) := by
  let F (p : Legs X (n+1) × Trail Q z) := metal K u (hitch y p.2.val) p.1
  let U (w : Legs X (n+1)) := K 0 (w 0) y * (u w * lot (crop B) (P ∘ crop w) z)
  have e (w : Legs X (n+1)) : (∑' t:Trail Q z,F (w,t))= U w := dispatched_inner hh he w y z
  let E' (x:Legs X (n+1) × Trail Q z): Legs X (n+1) × Legs Y n:= (x.1,x.2.val)
  have hi : Injective E' := by
    intro x y e; have hu := congr_arg Prod.fst e; have hv := congr_arg Prod.snd e; exact Prod.ext hu (Subtype.ext hv)
  have hF : Summable F := by
    have Hx := (bullet g he hv hp y).comp_injective hi; exact Hx
  have hu : Summable U:= hF.prod.congr e
  calc
   _ = ∑'z:Trail Q z,∑'w:Legs X (n+1),F (w,z) := by rw [bind_pin]; rfl
   _ = ∑' w,U w := (Summable.tsum_comm (f:=fun p q=> F (p,q)) hF).trans (tsum_congr e)
   _ = _ := by
      rw [event_tsum hu P]; unfold tele; refine tsum_congr (legs_succ _ ?_)
      intro x w
      have ht (i:{i//P i=x}) (a:Trail P w) : U (hitch i.val a.val)= K 0 i.val y*(u (hitch i.val a.val)*lot (crop B) w z) := by simp only [U,hitch_zero,crop_hitch, a.property]
      let E := pintrail x w P
      rw [← E.tsum_eq (fun t:Trail P (hitch x w)=> U t.val)]; refine Eq.trans ((Equiv.summable_iff E).mpr (event_trail U hu P _)).tsum_prod ?_
      change ∑' i:{i//P i=x}, ∑' a:Trail P w, U (hitch i.val a.val) = _
      have H (i:{i//P i=x}): v (hitch x w) = ∑' a:Trail P w,u (hitch i.val a.val) := quota_page h i.val _ i.property
      simp_rw [ht,tsum_mul_left,tsum_mul_right,← H,tsum_mul_right, ← (hh 0).col]; rw [metal_head]
lemma page_account (e : Fin n≃Fin k) (i : Fin n) (t : Legs Y' k) (y : Y) (P : Page Y k) :
    page Q (e i) y P t=page Q i y (escort e.symm P) (t ∘ e) := by
  rw [page_tsum,page_tsum,← (casesEquiv e (Equiv.refl Y)).tsum_eq _]
  apply tsum_congr; intro a; rw [casesEquiv_apply]
  simp only [Equiv.coe_refl,id_comp]; unfold escort
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  have hT : Q ∘ (a ∘ e.symm)= t ↔ Q ∘ a=t ∘ e :=
    ⟨fun h=> by simpa [comp_assoc] using congr_arg (fun f=>f ∘ e) h,fun h=> by simpa [comp_assoc] using congr_arg (fun f=> f ∘ e.symm) h⟩
  simp only [hT]

lemma Orates.tele (g : Geometry D E θ σ d) (he : ∀ i, AuditLine (K i) d (n+1) (R i) (S i)) (hv : Within D θ M u) (hp : 0≤σ)
    (h : Orates P u v) (hh : ∀ i,GaugeLine P Q (K i) (B i)) : Orates Q (tele K u) (tele B v) := by
  intro i x w hx
  let q := Equiv.swap i 0
  have ht : q 0=i:= Equiv.swap_apply_right ..
  have e' : ∀ j,AuditLine ((K∘q) j) d (n+1) (R (q j)) (S (q j)):= fun j=>he (q j)
  have hh' : ∀ j,GaugeLine P Q ((K∘q) j) ((B∘q) j):= fun j=> hh (q j)
  have h' := dispatched g e' (hv.reindex q.symm) hp (h.reindex q.symm) hh' x (crop (w ∘ q))
  rw [show Q x=(w ∘ q) 0 from (by simp [ht,hx]),hitch_crop,teleport_escort, teleport_escort] at h'
  exact (Eq.trans (show _ = escort q.symm (Sheet.tele B v) (w ∘ q) from by simp [escort,comp_assoc]) h'.symm).trans ((ht ▸ page_account (Q:=Q) q 0 w x (Sheet.tele K u)).symm)
end YM.WilsonBulk.Sheet

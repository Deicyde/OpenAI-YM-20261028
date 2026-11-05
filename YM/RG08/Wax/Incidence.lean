import YM.RG08.Wax.Fuses
import YM.RG08.Bands.Codex
/-! # Finite marker polynomial calculus for the formal log, factorial by
mark count. Distinct slot positions are not separate tags; same slot ANY ν
annihilates. Restrictions consumer (nonuniform ideals) per-root evaluation. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter Finset RG Stationary Quire Bands
open scoped Topology ContDiff BigOperators
variable {I : Type} [DecidableEq I] {k:Finset I} {s: Finset I×Finset I} {E:Type*}
def partners (T:Finset I) := (T.powerset ×ˢ T.powerset).filter fun z=> T=z.1∪z.2 ∧ Disjoint z.1 z.2
lemma norms_par (T: Finset I)(A : Finset I×Finset I): A∈ partners T ↔ T=A.1∪A.2 ∧ Disjoint A.1 A.2 := by
  simp only [partners,mem_filter,mem_product,mem_powerset]; exact ⟨And.right,fun he=> ⟨by rw [he.1]; exact ⟨subset_union_left,subset_union_right⟩,he⟩⟩
lemma par_count (h:s∈partners k): k.card=s.1.card+s.2.card:=by obtain ⟨rfl,p⟩:= (norms_par k s).mp h; exact card_union_of_disjoint p
@[simp] lemma par_once : partners (∅:Finset I)={(∅,∅)}:= by ext p; rw [norms_par]; simp [Prod.ext_iff]; grind
lemma partners_flip [AddCommMonoid E] (k:Finset I) (f:Finset I × Finset I → E) : ∑ p∈partners k,f p=∑ p∈partners k,f (p.2,p.1) := by
   refine Finset.sum_bij' (i:=fun p _=>p.swap) (j:=fun p _=> p.swap) ?_ ?_ ?_ ?_ (fun _ _=>rfl) <;> intro p hp
   all_goals try rfl
   all_goals obtain ⟨H,hz⟩:= (norms_par k p).mp hp; exact (norms_par ..).2 ⟨H.trans (union_comm ..),hz.symm⟩
lemma partners_3 [AddCommMonoid E] (k:Finset I)(f:Finset I→Finset I→Finset I→E) :
   ∑ p∈partners k,∑ u∈partners p.1,f u.1 u.2 p.2=∑ p∈partners k,∑ u∈partners p.2, f p.1 u.1 u.2:= by
  rw [sum_sigma', sum_sigma'];
  refine Finset.sum_bij' (i:=fun ⟨⟨p,q⟩,r,s⟩ _=> ⟨(r,s∪q),s,q⟩) (j:=fun ⟨⟨p,q⟩,r,s⟩ _=>⟨(p∪r,s),p,r⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨p,q⟩,r,s⟩ h
    rw [mem_sigma,norms_par,norms_par] at h ⊢
    rcases h with ⟨⟨hx,hb⟩,he,hv⟩; dsimp only at *; rw [he] at hx hb; rw [disjoint_union_left] at hb; exact ⟨⟨hx.trans (union_assoc ..),disjoint_union_right.mpr ⟨hv,hb.1⟩⟩,rfl,hb.2⟩
  · rintro ⟨⟨p,q⟩,r,s⟩ h
    rw [mem_sigma,norms_par,norms_par] at h ⊢; rcases h with ⟨⟨hx,hb⟩,he,hv⟩; dsimp only at *; rw [he] at hx hb; rw [disjoint_union_right] at hb; exact ⟨⟨hx.trans (union_assoc ..).symm,disjoint_union_left.mpr ⟨hb.2,hv⟩⟩,rfl,hb.1⟩
  · rintro ⟨⟨p,q⟩,r,s⟩ h
    dsimp only; rw [← show p=r∪s from ((norms_par ..).1 (mem_sigma.mp h).2).1]
  · rintro ⟨⟨p,q⟩,r,s⟩ h; dsimp only; rw [← show q=r∪s from ((norms_par ..).1 (mem_sigma.mp h).2).1]
  rintro ⟨⟨p,q⟩,r,s⟩ h; rfl
-- product index
abbrev Topaz (I:Type) (E:Type*) := Finset I→E
def festival [AddCommMonoid E] (op:E→ E → E)(a b:Topaz I E):Topaz I E:= fun t=>∑ p∈partners t,op (a p.1) (b p.2)
def sons [AddCommMonoid E] [Module ℝ E] (a:Topaz I E): Topaz I E:= fun t=>(↑t.card:ℝ) • a t

variable [AddCommGroup E] [Module ℝ E] {k:E} {op:E→E→E} {a b c d : Topaz I E}
def Bulb (k:E)(op:E→E→E)(l r:Topaz I E):Prop:= l ∅=0 ∧ r ∅=k ∧ sons r=festival op (sons l) r
lemma sons_empty (a:Topaz I E) : sons a ∅=0:=by simp [sons]
lemma sons_add (a b:Topaz I E): sons (a+b)=sons a+sons b:=funext fun i=> smul_add ..
lemma sons_sub (a b:Topaz I E): sons (a-b)=sons a-sons b:=funext fun i=> smul_sub ..
lemma sons_one (h:a ∅=b ∅) (hz:∀ x,op 0 x=0) (he:sons a-sons b=festival op (sons c) a-festival op (sons c) b): a=b:= by
  funext t; induction t using strongInductionOn with
  | _ t ih=>
    by_cases hx:t=∅; · subst t; exact h
    let T:= (↑t.card:ℝ); have ht:T≠0:= by unfold T; exact Nat.cast_ne_zero.mpr (card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hx))
    have hp : festival op (sons c) a t=festival op (sons c) b t:= by
      refine sum_congr rfl fun p hp=>?_ ; by_cases hh:p.2=t
      · have hl : p.1.card=0:= by have hu:=par_count hp; rw [hh] at hu; omega
        rw [card_eq_zero.mp hl,sons_empty,hz,hz]
      rw [ih _ (Finset.ssubset_iff_subset_ne.mpr ⟨(mem_powerset.mp (mem_product.mp (mem_filter.mp hp).1).2),hh⟩)]
    have hQ := congr_fun he t; rw [Pi.sub_apply,Pi.sub_apply,hp,sub_self] at hQ; exact (smul_right_injective _ ht) (sub_eq_zero.mp hQ)
lemma bulb_one (h:Bulb k op a b)(hp : Bulb k op a c)(hz:∀x,op 0 x=0): b=c:= sons_one (h.2.1.trans hp.2.1.symm) hz (by rw [← h.2.2,←hp.2.2])
lemma bulb_log (h:Bulb k op a b)(hv:Bulb k op c b) (hp:∀ x,op x k=x) : a=c:= by
    funext t; induction t using strongInductionOn with
    | _ t ih=>
      by_cases hx:t=∅; · subst t; exact h.1.trans hv.1.symm
      let u:=(partners t).erase (t,∅); let f (a:Topaz I E) (p:Finset I×Finset I):= op (sons a p.1) (b p.2)
      have hd (A:Topaz I E): festival op (sons A) b t=sons A t+ ∑ p∈u, f A p:= by
         unfold festival; rw [← add_sum_erase _ _ (show (t,∅)∈partners t by rw [norms_par]; simp),h.2.1,hp]
      have he : ∑ p∈u,f a p=∑ p∈u, f c p:= by
        refine sum_congr rfl fun p hp=>?_ ; obtain ⟨hx,hp⟩:= mem_erase.mp hp; obtain ⟨hh,hb⟩:= (norms_par ..).1 hp
        have hS : p.1⊂ t:= by
          apply Finset.ssubset_iff_subset_ne.mpr; refine ⟨hh.symm ▸ subset_union_left,fun hm=>hx ?_⟩
          have hb:= par_count hp; exact Prod.ext hm (card_eq_zero.mp (by rw [hm] at hb; omega))
        unfold f sons; rw [ih _ hS]
      have ht : festival _ (sons a) b t= festival _ (sons c) b t:= congr_fun (h.2.2.symm.trans hv.2.2) t
      rw [hd,hd,he,add_left_inj] at ht; exact (smul_right_injective _ (show (↑t.card:ℝ)≠0 from Nat.cast_ne_zero.mpr (card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hx)))) ht
end YM.RG08.Wax

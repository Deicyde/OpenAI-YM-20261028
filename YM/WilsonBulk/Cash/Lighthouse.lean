import YM.WilsonBulk.Cash.Teles

/-! # DISS and the kinetic pole transfer measured on parameter continuations

Kinematics: canonical axis0 encodes movement of an infinitesimal unit based gauge slot.
Maps `spur` exact action on all periods by composing tattoo incl stationary. DISS public
without using any physical C. keep all not importing RG03 pressure witnesses (pure formal).
Do not assert kernel length constants already chosen in any particular Calendar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Function Filter Equiv Finset Lattice Pert.Bulk Laurent Bloch Matrix Work.F08
open Exterior Precision Stationary Audience Wilson RG Sheet Atelier FreeResolvent
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n k d : ℕ} {f c L : Side} {V : Text (Cloth G) (n+1)} {p x σ : ℝ}
variable (G)

abbrev sleeve (x : Cloth G) := (vac,x.2)
def turmoil : Row (Cloth G) (Cloth G) := fun i j z=> if j.1=coord 0 then stillColor G (cobound 0) i (sleeve G j) z else 0
lemma turmoil_ready : Stamped (turmoil G) := by
  intro s hs; obtain ⟨M,hM,hK⟩:= (show Stamped (stillColor G (cobound 0)) from Stamped.painted _ _ _ _ (Stamped.cobound 0)).bound s
  refine ⟨M,hM,fun i j=>?_⟩; by_cases h: j.1=coord 0
  · unfold turmoil; simp_rw [if_pos h]; exact hK _ _
  simp [turmoil,h,Width,SumBudget,hM]
lemma turmoil_spurs (x y : Pennant G c) : (turmoil G).acts c x y= if y.2.1= coord 0 then patron G (Exterior.d 0 c) x (y.1,sleeve G y.2) else 0 := by
  rw [← see_stillColor c 1 0 (cobound 0)]; split <;> simp_all [Row.acts,turmoil]
lemma turmoil_hint (x y : Pennant G c) : (turmoil G).acts c x y= if y.2.1=coord 0 ∧ x.2.2=y.2.2 then
    ((if x.1=backed true x.2.1 y.1 then 1 else 0) - if x.1=y.1 then 1 else 0) else 0 := by
  obtain ⟨i,h⟩:= axisEquiv.surjective x.2.1; have hz : backed true (axisEquiv i) y.1=y.1-step i := by unfold backed; rw [Equiv.symm_apply_apply]; rfl
  have hp (x z : Site c) : x=z-step i ↔ z=x+step i := eq_sub_iff_add_eq.trans eq_comm
  rw [turmoil_spurs,match_tensor]; unfold tensor
  simp only [Matrix.of_apply,sleeve]
  by_cases hX : y.2.1=coord 0; swap; · simp [hX]
  simp only [hX,↓reduceIte,true_and]; split; swap; rfl
  simp only [← h,hz,hp]; have ht:= d_sites x.1 i (Pi.single (y.1,vac) 1); rw [Matrix.mulVec_single_one] at ht -- inspect
  simpa [Pi.single_apply, eq_comm (a:=y.1)] using ht


variable {G}
-- since core tests every native mark even before budgets.
abbrev troops (G : Gauge) (n : ℕ) := hitch (turmoil G) (fun _:Fin n=> unitRow _)
lemma troops_cost (G : Gauge) (n : ℕ) : Plaza (troops G n) := plaza fun i=>by cases i using Fin.cases with
 | zero => exact beacon _ (turmoil_ready G)
 | succ k=> simp only [troops,hitch_succ]; exact beacon _ Stamped.unit
abbrev awalk {G : Gauge} {α : Type} (t : Legs (Row (Cloth G) α) n) (c : Side) (i : Fin n) := (fun (x : Pennant G c) (y : Co c α) => (t i).acts c x y)
lemma winter (V : Page (Pennant G c) (n+1)) (x : Pennant G c) (b : Legs (Pennant G c) n) :
    tele (awalk (troops G n) c) V (hitch x b)=∑ y : Pennant G c,(turmoil G).acts c y x*margin V y b := by
  let M := awalk (troops G n) c; have hp i (y z : Pennant G c) : crop M i y z= if y=z then 1 else 0:= by simp [crop,M,awalk,troops,acts_unit, Matrix.one_apply]
  unfold tele; rw [tsum_fintype,typeset_fin_hitch]; refine sum_congr rfl fun i hi=>?_ ; rw [sum_eq_single b]; rotate_left
  · intro z _ hz; obtain ⟨i',hi'⟩:= Function.ne_iff.mp hz; rw [metal_head,lot, Finset.prod_eq_zero (mem_univ i') (show _=_ from (hp i' (z i') (b i')).trans (if_neg hi')),mul_zero,mul_zero]
  · simp
  rw [metal_head, lot]; change _*(V (hitch i b)* ∏ j:Fin n, crop M j (b j) (b j))=_; simp only [hp,↓reduceIte,Finset.prod_const_one,mul_one]; exact rfl
lemma winter_pool (V : Page (Pennant G c) (n+1)) : diss backed V = tele (awalk (troops G n) c) V := by
  apply margin_force; rintro ⟨x,i,j⟩; rw [margin_sub]; funext z; unfold squire; rw [Pi.sub_apply,post_mark,post_mark,margin,winter]; -- maybe unfold diss after rw already
  simp_rw [turmoil_hint]
  by_cases h:i=coord 0; swap; · simp [h]
  simp only [h,true_and,↓reduceIte, Finset.sum_apply]
  rw [swatch_split,Fintype.sum_prod_type,sum_comm]; simp only [ite_mul,selvedge, zero_mul, Finset.sum_ite_eq', if_pos (mem_univ j)] -- congr_prod_type and engine
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun a _=> ?_; simp [sub_mul,ite_mul,cameo,backed] -- unfolds h?
variable {D : ℕ→ Side} {G : Gauge} -- G repeat not V! inspect
lemma sentry_up {V : Text (Cloth G) (n+1)} (t : Bool) (x : Legs (Mark G) (n+1)) (p : Public V) (he : Tendsto (fun i=> (D i).val) atTop atTop) : Tendsto (fun i=> squire backed t (coupon (D i) _ V) (small (D i) _ ∘ x)) atTop (𝓝 (squire backed t V x)) := by
  let q:Mark G:= x 0
  have hh i (a : PotentialForm) : small (D i) (Cloth G) (selvedge (cameo backed t a (x 0).1) (x 0).2.2)= _ :=
    (show _=selvedge (cameo backed t a (wrap (D i) (x 0).1)) q.2.2 from Prod.ext (shift_card _ _ t) rfl)
  unfold squire castTail; by_cases h:q.2.1=coord 0; swap; · have hp i:(small (D i) (Cloth G) q).2.1≠coord 0 := h; exact Tendsto.congr' (Eventually.of_forall fun i=> by simp only [q] at hp h; dsimp only [Function.comp_apply]; rw [if_neg h,if_neg (hp i)]; rfl) tendsto_const_nhds -- inspect
  have hp i:(small (D i) (Cloth G) (x 0)).2.1=coord 0:=h
  unfold q at h; simp only [Function.comp_apply,h,hp,↓reduceIte, Finset.sum_apply]
  refine tendsto_finsetSum _ fun a _=> ?_; refine (Public.introduction _ p he (hitch (selvedge (cameo backed t a (x 0).1) (x 0).2.2) (crop x)) (by omega)).congr' (Eventually.of_forall fun i=>?_); dsimp only; rw [hitch_comp, hh]; rfl
lemma march_spur {V : Text (Cloth G) (n+1)} (h : Public V) : diss backed V=tele (plain ∘ troops G n) V := by
  ext1 i; let D:= cascade (1:Side); have hD:= cascade_up (c:=(1:Side)); let T:= tele (plain ∘ troops G n) V; let u (j:ℕ):=squire backed true (coupon (D j) _ V) (small (D j) _ ∘ i)
  refine tendsto_nhds_unique_of_eventuallyEq ((sentry_up true i h hD).sub (sentry_up false i h hD)) (Public.introduction T (h.ascend (troops_cost ..)) hD i (by omega)) (Eventually.of_forall fun j=>?_)
  change diss backed _ (small (D j) _ ∘ i)=coupon _ _ (tele _ V) _; rw [winter_pool, ascend_coupon h (troops_cost G n)]
end Parapet
end YM.WilsonBulk

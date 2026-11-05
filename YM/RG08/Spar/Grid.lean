import YM.RG08.Spar.Paid
import YM.RG08.Cell.Grid

/-!
# Tilings for Flake, true all-leg cost and exact per-root translation (also large wraps)
-/
noncomputable section
namespace YM.RG08.Spar
open Forms Rudder Packets Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch Anchor Symmetry Isles Stationary RG
open scoped Topology BigOperators Classical ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I : Type}{n:ℕ}{σ τ C:ℝ}{c f L:Side}

def carton (n:ℕ)(α β:Type)(T:α≃β):Tape n α≃Tape n β:=Equiv.arrowCongr (Equiv.refl _) T

def farm (L:Side)(F:Flake n (Market I)):Flake n (Market (Co L I)):=fun x=> F (Cell.column L I ∘ x)

lemma farm_path {F:Flake n (Market I)}(h:Cohort F): Cohort (farm L F):=by
 intro u y;unfold farm
 have he:Cell.column L I ∘ sway u y=sway (L.val • u) (Cell.column L I ∘ y):=funext fun i=> Cell.column_map (y i) u
 rw [he,h]

lemma farm_cost {F:Flake n (Market I)}(hs:0≤τ)(hσ:τ≤L.val*σ)(hk:Held (carpet I) σ C F)(hC:0≤C): Held (carpet _) τ (C* Real.exp (8*τ)) (farm L F):=by
 let W:=Cell.column L I
 have hm(x:Tape n (Market (Co L I))): τ*(carpet _).radius x ≤ σ*(carpet _).radius (W ∘ x) + 8*τ:=by
   let d:= (carpet _).radius (W ∘ x)
   have he:(carpet _).radius x ≤ d/L.val+8:=by
      have hp:= (carpet _).radius_nn (W ∘ x)
      apply Ground.radius_le; · unfold d;positivity
      intro i j;exact (Cell.separation_to (x i) (x j)).trans (add_le_add_left (div_le_div_of_nonneg_right ((carpet _).le_radius (W ∘ x) i j) (by positivity)) _)
   let l:ℝ:=L.val; have hl:0<l:=by unfold l;positivity
   have hh:τ / l≤ σ:=by rw [div_le_iff₀ hl]; linarith only [hσ]
   have hd:= (carpet _).radius_nn (W ∘ x)
   change _ ≤ σ*d+_
   calc
   _ ≤ τ*(d/l+8):= mul_le_mul_of_nonneg_left he hs
   _ = τ/l*d+8*τ:=by ring
   _ ≤ _:=by gcongr
 rw [ensign,ENNReal.ofReal_mul hC];intro i z
 calc
  _ ≤ ∑' x:Tape n (Market (Co L I)), Forms.row (mark (carpet _) σ F) i (W z) (W ∘ x)*ENNReal.ofReal (Real.exp (8*τ)):= ENNReal.tsum_le_tsum fun x=>?_
  _ ≤ _:=by
    let E:=carton n _ _ W
    change (∑' x, Forms.row _ _ _ (E x)*_)≤_
    rw [ENNReal.tsum_mul_right, E.tsum_eq (Forms.row _ i _)];exact mul_le_mul_left (ensign.mp hk i _) _
 unfold Forms.row; split_ifs with he hf ht
 · unfold mark;rw [←Pert.Bulk.bill_add];apply Pert.Bulk.bill_mono le_rfl (hm x)
 · exact (hf (congr_arg W he)).elim
 all_goals exact zero_le

/- exact pour in packed form with linear ratio data (uses all periods and all lengths;
requires F is a *translated* kernel so that fixed first position in the pour may be
moved by a period). -/
lemma farmed {F:Flake n (Market I)}(hc:Cohort F)(S: StepData c f)(i:Fin n)(w:Tape n (Cove c (Co S.patch.L I))):
 pour (farm S.patch.L F) i w=pour F i ((splitCo S.ratio I).symm ∘ w):=by
 let L:=S.patch.L;let W:=Cell.column L I;let z:Tape n (Cove f I):=(splitCo S.ratio I).symm ∘ w
 -- cart maps anchor to another lift, shifted by common u
 let u:Cover:=(W (reach (w i))).1-Lattice.lift (z i).1
 have hu:port f (W (reach (w i)))=z i:=by change _=(splitCo ..).symm _; have ht:=Cell.convert_origin S (reach (w i)); unfold reach at ht;dsimp at ht; rw [wrap_lift] at ht;exact ht.symm
 have hv:wrap f u=0:=by rw [map_sub,wrap_lift]; exact sub_eq_zero.mpr (congr_arg Prod.fst hu)
 let T:= (carton n _ _ W).trans (tides (-u))
 have he(x:Tape n (Market (Co L I))): x∈lantern i w ↔ T x∈ lantern i z:=by
    have H:port f ∘ (T x)=(splitCo S.ratio I).symm ∘ (port c ∘ x):=by
      ext j:1;change port f (pass (-u) (W (x j)))=_
      simp only [port,pass,comp_apply,map_add,map_neg,hv,neg_zero,add_zero];exact (Cell.convert_origin S (x j)).symm
    have hz:port c ∘ x=w ↔ port f ∘ (T x)=z:=by unfold z; rw [H];exact ((splitCo S.ratio I).symm.injective.comp_left).eq_iff.symm
    have hy:x i=reach (w i)↔ T x i=reach (z i):=by
       rw [←(W.injective.eq_iff (a:=x i) (b:=reach (w i))),←((sail (-u)).injective.eq_iff (a:=W (x i)) (b:=W (reach (w i))))]
       have ht:pass (-u) (W (reach (w i)))=reach (z i):=by
          apply Prod.ext
          · change _ + -( _ - _) =_;abel
          exact congr_arg (fun x:Cove f I=>x.2) hu
       rw [show sail (-u) (W (reach (w i)))= _ from ht];rfl
    exact and_congr hy hz
 unfold pour; rw [← T.tsum_eq (fun x=> (lantern i z).indicator F x)]
 refine tsum_congr fun x=> ?_
 simp only [Set.indicator_apply,he]
 split_ifs; · exact (hc (-u) (W ∘ x)).symm
 rfl
end YM.RG08.Spar

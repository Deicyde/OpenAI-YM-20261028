import YM.RG08.Wax.Stems
import YM.RG08.Wax.Fuses
import YM.RG08.Plot.Isle
/-! # Fine sources and full marker evaluation. Real gauge all origins, exponential stencil subcalculations. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall
open scoped Topology ContDiff BigOperators Real Classical
variable {I α β X: Type} [Fintype I][Fintype α][DecidableEq I][Fintype β]{G:Gauge}{a:I→ℕ}{f: Topaz I (Tale G)}{τ:ℕ}
section bannerstone
abbrev Fabrics (G:Gauge)(f:Topaz I (Tale G)): Topaz I (Tale G):= fun t=>banner t f gust (spine_one _)
lemma part_lt {U:Finset I×Finset I}{T:Finset I}(hp:U∈directVote T): U.2 ⊂ T:= Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp (mem_product.mp (mem_filter.mp (show U∈partners T from (mem_filter.mp hp).1)).1).2, fun h=>not_lt_of_ge (congr_arg Finset.card h).ge (shrank _ hp)⟩
lemma stone_p (h:∀ t,Stone (vanes a t) (f t))(t:Finset I): Stone (vanes a t) (Fabrics G f t):= by
   induction t using strongInductionOn with
   | _ t ih =>
     unfold Fabrics; rw [Wax.banner]; split; next he=> subst t; rw [vanes_empty]; exact stone_start G
     apply Stone.weight; refine Stone.group _ _ (fun i _=>?_)
     rw [wind_cell a _ (mem_filter.mp i.property).1]; exact wind ((h i.val.1).weight _) (ih _ (part_lt i.property))

lemma banner_back (h:∀ t,Stone (vanes a t) (Fabrics G f t))(hp:∀ t, Sails (vanes a t) (f t))(hz:f ∅=0)(t:Finset I): Stone (vanes a t) (f t) := by
   let v:= Fabrics G f; have hb: Bulb (spine_one _) gust f v:= bannerC _ _ _ gust_z hz -- syntax
   induction t using strongInductionOn with
   | _ t ih =>
     by_cases hh:t=∅; · subst t; rw [hz]; exact Stone.zero
     let k:Finset I×Finset I:= (t,∅); have hk:k∈partners t:= by simp [k,norms_par]
     let V:= (partners t).erase k; let g (p:Finset I×Finset I):= gust (sons f p.1) (v p.2)
     have hg:Stone (vanes a t) (∑ p∈V,g p):= Stone.group _ _ (fun i hi=> by
        obtain ⟨hs,hh⟩:=mem_erase.mp hi
        rw [wind_cell a i hh]; apply wind
        · unfold sons; apply Stone.weight; exact ih _ (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp (mem_product.mp (mem_filter.mp hh).1).1,fun he=>hs (Prod.ext he (Finset.card_eq_zero.mp (by have ht:= par_count hh; rw [he] at ht; omega)))⟩)
        exact h _)
     let C:ℝ:= t.card; have ht:C ≠0:= Nat.cast_ne_zero.mpr (card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hh))
     have hs : C • v t = C • f t +∑ p∈V,g p:= by
       rw [show C•v t=∑ p∈partners t,g p from congr_fun hb.2.2 t,← Finset.add_sum_erase _ _ hk]
       refine congr_arg (·+_) ?_; dsimp only [g,k]; rw [hb.2.1]; refine gust_coin (swung (k:=vanes a t) fun i=>?_); exact ((hp t).thin i).sc _
     have hd:= (Stone.less ((h t).weight C) hg).weight C⁻¹; change Stone (vanes a t) (C⁻¹ • (C • v t - ∑ p∈V,g p)) at hd; rwa [hs,add_sub_cancel_right, inv_smul_smul₀ ht] at hd
end bannerstone
section substitution
-- auxiliary push of moments; uses Stone framework with Only for any type full slots
variable {A:Type} [Fintype A][DecidableEq A][Nonempty A][Zero A]
abbrev subroll (T:Finset I)(A:Type):= T→ A
-- explict outside T ignored, flexible zero
abbrev enter [Zero X] (j:Finset I)(K:subroll j X)(i:I) := if h:i∈j then K ⟨i,h⟩ else 0
def scope {X Z:Type}(T:Finset I)(e:(I→X) → Z):Prop:= ∀ x y, (∀ i∈T,x i=y i) → e x=e y
lemma scope.outside {Z: Type} {V U:Finset I}(he:U⊆V){X:Type}{f: (I→X)→Z}(h:scope U f):scope V f:= fun p q hP=> h p q fun i hi=>hP i (he hi)
lemma scope_screw {g:(I→A)→ Topaz I (Tale G)}(h:∀ t,scope t (fun i=>g i t))(t):scope t (fun i=>Fabrics G (g i) t) := by
   induction t using strongInductionOn with
   | _ t ih=>
     intro x y he; dsimp only; unfold Fabrics; rw [Wax.banner,Wax.banner]; split; next hx=> rfl
     congr 1; refine sum_congr rfl ?_; intro i _
     obtain ⟨hv,hP⟩:= mem_product.mp (mem_filter.mp (show i.val ∈ partners t from (mem_filter.mp i.property).1)).1; congr 1
     · unfold sons; rw [show g x i.val.1=g y i.val.1 from h i.val.1 x y fun a ha=>he a (mem_powerset.mp hv ha)]
     exact ih _ (part_lt i.property) x y (fun a ha=> he a (mem_powerset.mp hP ha))
-- Partition sums over restrictions. Fintype proof via completeness
variable {T U V:Finset I}{F:(I→A)→ Topaz I (Tale G)}
abbrev portion (hv:U⊆T)(p:subroll T A): subroll U A:= fun i=> p ⟨i.val,hv i.property⟩
lemma part_eq (h:T=U∪V)(hv:Disjoint U V): Function.Bijective fun q:subroll T A=> (portion (T:=T) (show U⊆ T from by rw [h]; exact subset_union_left) q, portion (show V⊆ T from by rw [h]; exact subset_union_right) q) := by
  constructor
  · intro a b hp; funext i; have ht : T ⊆ U ∪ V := h.le; obtain ht|ht:=mem_union.mp (ht i.property)
    · exact congr_fun (Prod.ext_iff.mp hp).1 ⟨i,ht⟩
    exact congr_fun (Prod.ext_iff.mp hp).2 ⟨i,ht⟩
  intro k; let q:subroll T A := fun i=> if H:i.val∈U then k.1 ⟨_,H⟩ else enter V k.2 i
  refine ⟨q,Prod.ext (funext fun i=>dif_pos i.property) (funext fun i=>?_)⟩
  dsimp only [portion,q,enter]
  rw [dif_neg (fun h=>Finset.disjoint_left.mp hv h i.property),dif_pos i.property] -- fix
lemma swell_group {F:X→Tale G}{V:Tale G}(p:Finset X)(h:∀ i∈p,Stone τ (F i)){r:ℕ}(hp:Stone r V): gust (∑ i∈p,F i) V=∑ i∈p,gust (F i) V:= by
   induction p using Finset.induction_on with
   | empty=> rw [sum_empty,sum_empty,gust_z]
   | insert i p hi ih=> rw [sum_insert hi,sum_insert hi,swell_left (h i (mem_insert_self ..)) (Stone.group _ _ (fun j hj=>h j (mem_insert_of_mem hj))) hp, ih (fun j hj=>h j (mem_insert_of_mem hj))]
-- define Euler expo natural interning. scalar factors attached to slots in advance.
def convent (A:Type)[Zero A][Fintype A](I:Type)[DecidableEq I](k:(I→A)→Topaz I (Tale G)): Topaz I (Tale G) := fun t=> ∑ i:subroll t A,k (enter t i) t
lemma rolls_f {f g:(I→A)→Tale G}(h: (U,V)∈partners T)(hv:scope U f)(he:scope V g){j k:ℕ}(hg:∀ x, Stone k (g x))(hf:∀ x, Stone j (f x)):
   (∑ p:subroll T A,gust (f (enter T p)) (g (enter T p)))=gust (∑ x:subroll U A,f (enter U x)) (∑ x:subroll V A,g (enter V x)):= by
    obtain ⟨ht,hV⟩:=(norms_par _ _).mp h
    have hU:U⊆T:= by rw [ht]; exact subset_union_left
    have hZ:V⊆T:= by rw [ht]; exact subset_union_right
    let M:= fun i:subroll T A=> (portion hU i,portion hZ i)
    let S(p:subroll U A ×subroll V A):=gust (f (enter U p.1)) (g (enter V p.2))
    have hx: (∑ p:subroll T A, gust (f (enter T p)) (g (enter T p)))=∑ p :subroll U A ×subroll V A, S p:= by
       refine Fintype.sum_bijective M (part_eq ht hV) _ S ?_
       intro i; unfold S M; dsimp only; exact congr_arg₂ gust (hv _ _ fun a ha=> (show enter T i a =_ from dif_pos (hU ha)).trans (show enter U (portion hU i) a=i ⟨a,hU ha⟩ from dif_pos ha).symm) (he _ _ fun a ha=> (show enter T i a=_ from dif_pos (hZ ha)).trans (show enter V (portion hZ i) a=i ⟨a,hZ ha⟩ from dif_pos ha).symm)
    rw [hx, Fintype.sum_prod_type]; let K : Tale G:= (∑ x:subroll V A,g (enter V x)); have hk:Stone k K:= Stone.group _ _ fun i _=> hg _
    rw [swell_group (h:=fun i _=> hf (enter U i)) _ hk]; apply sum_congr rfl; intro i _
    unfold S; dsimp only
    rw [gust_same (hf _) hk,show gust K (f (enter U i)) =_ from swell_group _ (fun i _=>hg (enter V i)) (hf (enter U i))]
    exact sum_congr rfl fun p _=> gust_same (hf _) (hg _)
set_option maxHeartbeats 220000 in
lemma convent_g (hF:∀ p t,Stone (vanes a t) (F p t))(hV:∀ t,scope t (fun p=>F p t))(he: ∀ p,F p ∅=0) :
     convent A I (fun p=>Fabrics G (F p))= Fabrics G (convent A I F):= by
  let V(x):= Fabrics G (F x)
  let K:=convent A I F; let Q:=convent A I V
  have hz x:F x ∅=0:= he x
  have hx x: Bulb (spine_one _) gust (F x) (V x):= bannerC _ _ _ gust_z (hz x)
  have hu:K ∅=0:= Finset.sum_eq_zero fun _ _=>hz _
  have hp : Bulb (spine_one _) gust K Q:= by
     refine ⟨hu,?_,funext fun t=>?_⟩
     · unfold Q convent; let P : subroll (∅:Finset I) A := fun _=> 0
       rw [sum_eq_single_of_mem P (mem_univ _), (hx _).2.1]; intro i _ hi; exact False.elim (hi (funext fun x=> by have hh:= x.property; exact False.elim (notMem_empty _ hh))) -- names
     let q : ℝ:= t.card
     calc
      q • Q t = ∑ i:subroll t A,∑ p∈partners t,gust (sons (F (enter t i)) p.1) (V (enter t i) p.2) := by
          change q • (∑ i:subroll t A,V (enter t i) t)=_; rw [smul_sum]; exact sum_congr rfl fun i _=>congr_fun ((hx (enter t i)).2.2) t
      _= festival gust (sons K) Q t:= by
         unfold festival; rw [sum_comm]; apply sum_congr rfl; intro i hi
         have hh : sons K i.1 =∑ k:subroll i.1 A, sons (F (enter i.1 k)) i.1:= by unfold sons K convent; rw [smul_sum]
         rw [hh]; exact rolls_f (f:=fun x=>sons (F x) i.1) (g:=fun p=>V p i.2) (U:=i.1) (V:=i.2) hi (fun p q he=>congr_arg (fun x:Tale G=> (↑i.1.card:ℝ) • x) (hV i.1 p q he)) (scope_screw hV i.2) (fun x=>stone_p (hF x) i.2) (fun x=> (hF x i.1).weight _)
  exact bulb_one hp (bannerC _ _ _ gust_z hu) gust_z
-- multiplicative scalars in projection
lemma guill (hF:∀ t,Stone (vanes a t) (f t))(H:I→ℝ)(p:Finset I): Fabrics G (fun t=>(∏ i∈t,H i) • f t) p= (∏ i∈p,H i) • Fabrics G f p:=by
   induction p using strongInductionOn with
   | _ t ih=>
     unfold Fabrics; rw [Wax.banner,Wax.banner]; split; next hh=> subst t; rw [prod_empty, one_smul]
     rw [smul_comm (∏ i∈t,H i)]; refine congr_arg (fun s:Tale G=> ((↑t.card:ℝ))⁻¹ • s) ?_; rw [smul_sum]; apply sum_congr rfl; intro i _
     obtain ⟨hx,hP⟩:= (norms_par _ _).mp (mem_filter.mp i.property).1
     rw [show (∏ i∈t,H i)=(∏ j∈i.val.1,H j)*(∏ j∈i.val.2,H j) from (congr_arg (fun s=>∏ i∈s,H i) hx).trans (prod_union hP)]; unfold sons; rw [smul_comm ((↑i.val.1.card):ℝ),show banner i.val.2 _ _ _ = _ from ih _ (part_lt i.property),← smul_smul]
     have he:= stone_p hF i.val.2; have hp:= (hF i.val.1).weight (i.val.1.card:ℝ)
     rw [swell_w hp (he.weight _)]; congr 1; rw [gust_same hp (he.weight _),swell_w he hp, gust_same he hp]
end substitution
end YM.RG08.Creek

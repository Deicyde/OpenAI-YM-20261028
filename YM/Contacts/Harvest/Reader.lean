import YM.Contacts.Harvest.Yield
import YM.Contacts.Layers.Trees
/-!
# Continuations in the extended recipe

Pass words to context on each open group. At presence of (legal) halo or when resolving with other
groups, the continuation is not merely pairing with a list of exterior point fields. Record the
ability to read linear combinations of the indicated groups as words, with *local* regularity
(never require a continuum correlate on a coincidence plane), ranges of variation given by the
stage, and the ability to charge the readings along layer paths. All enlarged while preserving the
geometry of placements. This also retains every tested disappearance due to an ancestor subtraction
instead of estimating only absolute polynomials in the heuristics after the split. Only readability
and regularity here; later get charges from the same continuations.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Harvest
open Function Filter Set Metric MeasureTheory Table OPE Normal MultipleContact MultipleContact.Script Layers
open scoped Topology Classical ContDiff BigOperators
variable {G : Gauge} {L : Register G}{S : Table L}{M' : DiffPlan S} {M : Devices M'}
variable {E W I X : Type} {k : ℕ}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {g : Normal.Group k} {Q : Pieces g} {P : E→ₗᵢ[ℝ] Points k}
variable [NormedAddCommGroup X][NormedSpace ℂ X]
local notation "GN" => Normal.Group k
local notation "E!" => Expression M'
local notation "A!" => Letter M'
abbrev Reader (E W X : Type) [AddCommMonoid X][Module ℂ X] (k : ℕ) (M' : DiffPlan S) := W→ E→ Board (Normal.Group k) (Letter M') →ₗ[ℂ] X
-- reading a product of group factors
@[simp] lemma welded_update (i : Q.parts) {A : Type} (t : GN→ Grammar A) (u : Grammar A) :
 ∏ j∈Q.parts,tag j (Function.update t i.val u j)= (∏ j∈Q.parts.erase i.val,tag j (t j))*tag i.val u:= by
   rw [← Finset.prod_erase_mul _ (f:=fun j=> tag j (Function.update t i.val u j)) i.property,Function.update_self]; exact congrArg (· * (tag i.val u)) (Finset.prod_congr rfl fun j hj=> by rw [Function.update_of_ne (Finset.mem_erase.mp hj).1])
lemma weld_factors {g : Normal.Group k}{Q : Pieces g}(i : Q.parts){A : Type} (U : Pieces i.val) (F : Grammar A→ₗ[ℂ] Grammar A) (t : GN→ Grammar A):
    System.review Q i U F (∏ j∈ (replace i U).parts, tag j (t j)) = ∏ j∈Q.parts,tag j (Function.update t i.val (F (∏ j∈U.parts,t j)) j):= by
   rw [welded_update, replace_parts,Finset.prod_union (replace_disj i U)]
   let K:= Q.parts.erase i.val; let x:= ∏ j∈K, tag j (t j); let z:= ∏ j∈U.parts,t j; let D : Set GN:=U.parts; let y:= ∏ j∈U.parts,tag j (t j);
   have he : fork D x = outlet x:= by
      conv_lhs=> unfold x; rw [map_prod]
      rw [show outlet x=∏ j∈K,outlet (tag j (t j)) from map_prod outlet ..]
      exact Finset.prod_congr rfl fun j hj=> fork_out D j (show j∉D from Finset.disjoint_left.mp (replace_disj i U) (show j∈ K from hj)) (t j)
   have hy : fork D y=inlet z:=by unfold y z; rw [map_prod,map_prod]; exact Finset.prod_congr rfl fun j hj=> fork_in D j (show j∈D from hj) (t j)
   exact weld_untouched D ((tag i.val).toLinearMap.comp F) he hy

namespace Route
variable (r : Route P Q I W)
def palette (w : W) (j : Normal.Group k)(x:E) := Set.range fun p:Nails j=> r.oculus w p.val x
lemma centre (i : Q.parts) (w x) : r.oculus w i.val x∈ r.palette w i.val x:= ⟨⟨i.val,by rfl,Q.nonempty_of_mem_parts i.property⟩,rfl⟩
lemma inherits (w) {j i : GN} {x : E} (h : j ⊆ i) : r.palette w j x ⊆ r.palette w i x:= by rintro y ⟨a,rfl⟩; exact ⟨⟨a.val,Finset.Subset.trans a.property.1 h,a.property.2⟩,rfl⟩
lemma palette_fits (i : Q.parts) (w x) : r.palette w i.val x⊆ closedBall (r.oculus w i.val x) ‖(normalOn P i.val).starProjection x‖:= by rintro y ⟨a,rfl⟩; rw [mem_closedBall,dist_eq_norm]; exact r.oculus_extent w x i a
lemma palettes_stable {i j : Normal.Group k} (w) {x y:E}(h : x-y∈ normalOn P i)(hx : Disjoint j i) : r.palette w j x ⊆ r.palette w j y := by rintro z ⟨a,rfl⟩; exact ⟨a,(r.oculus_still w a.val x y h (.inr (Disjoint.mono_left a.property.1 hx|>.symm))).symm⟩
lemma palette_others (i : Q.parts)(u : Fans P i.val)(q : Splittings i.val){w:W}{a:ℝ} (ha:0<a)(x:E)(hm : x∈ u.patch q a) : (q.val.parts:Set GN).Pairwise (fun l p=> Disjoint (r.palette w l x) (r.palette w p x)) := by
   refine fun l hl p hp he=> Set.disjoint_left.mpr (fun z hz hw=>?_); obtain ⟨c,rfl⟩:=hz; obtain ⟨b,hb⟩:=hw
   have he':= u.lights (r.displaysNormals i.val i.property) q ha hm (⟨l,hl⟩:q.val.parts) ⟨p,hp⟩ (fun e=>he (congr_arg Subtype.val e)) c b
   apply he'; apply sub_eq_zero.mp; exact Eq.trans
       ( (r.oculus_diff w x i ⟨c.val,Finset.Subset.trans c.property.1 (q.val.le hl),c.property.2⟩ ⟨b.val,Finset.Subset.trans b.property.1 (q.val.le hp),b.property.2⟩).symm) (sub_eq_zero.mpr hb.symm)

def Authority (M : Devices M') (d : Fin k→ℕ) := r.ceiling ≤ M.clearance (∑ i,d i+0) -- use total k
lemma clearance_through {d : Fin k→ℕ} (h : r.Authority M d) (i : GN){u : ℕ}(hh : u < levels d i): r.ceiling ≤ M.clearance u:= by
    apply le_trans h (M.antitone_clearance ?_); simp only [add_zero]
    have ht : i.sum d ≤ ∑j,d j:= Finset.sum_le_sum_of_subset (Finset.subset_univ _); unfold levels at hh; omega

-- projection/residue choice and merge into parent in one call, keep reader applied before testing!
def listener (M : Devices M') (i : Q.parts) {d : Fin k→ℕ}(v:Way d i.val) (u:Fans P i.val) (q:Splittings i.val) (H : Reader E W X k M') : Reader E (r.ramp i (outward v) u q) X k M' :=
    fun s x=> (H s.val.1 x).comp (System.review Q i q.val (wind M d i.val v (r.oculus s.val.1 i.val x)))
-- explicit identity later

-- only regular when knowing the support geometry of all the placements. Separate charge.
structure Fixed (H : Reader E W X k M') (Q : Pieces g) (P:E→ₗᵢ[ℝ] Points k) : Prop where
   keeps w (i : Q.parts) {x y : E} : x-y∈ normalOn P i.val → H w x= H w y
structure Lit (r : Route P Q I W) (H : Reader E W X k M') : Prop extends Fixed H Q P where
   scene {V : Type} [TopologicalSpace V] {v : V→ E}{U : Set V} (w : W) (hU:IsClosed U) (hv' : ContinuousOn v U)(h : MapsTo v U (r.stage w))
      (t : Normal.Group k → V→ Expression M')(hx : ∀ i∈Q.parts, Displays U (r.palette w i ∘ v) (t i)) : ContinuousOn (fun y=> H w (v y) (∏ i∈Q.parts,tag i (t i y))) U
-- local continuity. Does not assert that the charges will not use a larger reserve than the palette size
variable {H : Reader E W X k M'}
lemma inheritsFixed (hi : Fixed H Q P) (M : Devices M') (i : Q.parts){d : Fin k→ℕ}(v : Way d i.val) (u q) : Fixed (r.listener M i v u q H) (replace i q.val) P:= by
   constructor; rintro w ⟨j,hj⟩ x y hx; change x-y ∈ normalOn P j at hx
   unfold listener; rw [replace_parts] at hj; rcases Finset.mem_union.mp hj with h|h
   · obtain ⟨hh,h⟩:= Finset.mem_erase.mp h; rw [hi.keeps _ ⟨j,h⟩ hx, r.oculus_still _ i.val _ _ hx (.inr (Q.disjoint h i.property hh))]
   have he:=normal_le P (q.val.le h) hx; rw [hi.keeps _ i he, r.oculus_still _ i.val _ _ he (Or.inl rfl)]

-- local assembly preserves eligibility and proof of validity on all terminal readings here
lemma combines_plot (i : Q.parts) (u q) {V : Type} [TopologicalSpace V] {U : Set V} (f : GN→ V→ Expression M') {s : V→E}{w:W}{a:ℝ}(hx : MapsTo s U (Fans.patch (P:=P) (g:=i.val) u q a))(he:0<a)
   (h : ∀ j∈ q.val.parts,Displays U (r.palette w j ∘ s) (f j)): Displays U (r.palette w i.val ∘ s) (fun t=>∏ j∈q.val.parts,f j t):=
   (Displays.prod h (fun _ ht=>r.palette_others i u q he _ (hx ht))).widen fun _ _=> Set.iUnion₂_subset fun _ hj=> r.inherits w (q.val.le hj)

-- inherited projected plot is allowed also when replacing actual position by a proxy in parent U
lemma sends (i : Q.parts){V : Type}[TopologicalSpace V]{U : Set V}{v : V→E}{w:W} (hh : ContinuousOn v U){d:Fin k→ℕ}(hA:r.Authority M d)(x : Way d i.val) {f : V→ Expression M'} {y: V→ E}
  (hx : ∀ t∈U,v t - y t ∈ normalOn P i.val)(hz : outward x=false → EqOn v y U)
  (hk : MapsTo v U (halo (normalOn P i.val) (r.length w) (outward x) (r.stage w))) (hs : Displays U (r.palette w i.val ∘ v) f) : Displays U (r.palette w i.val ∘ y)
             (fun t=> wind M d i.val x (r.oculus w i.val (v t)) (f t)) := by
   have he:∀ t∈U, r.oculus w i.val (v t) ∈ r.palette w i.val (y t):= fun t ht=> (r.oculus_still w i.val (v t) (y t) (hx t ht) (Or.inl rfl)).symm ▸ (r.centre i ..)
   have hb(j:Fin (levels d i.val)) : Displays U (r.palette w i.val ∘ y) (fun t=> M.insertRow (r.oculus w i.val (v t)) j (f t)):= by
      have hm:= (r.oculus_continuous w i.val).comp_continuousOn hh
      refine Displays.field he hm (M.row_continuous j hs hm (fun k hk'=>?_)); refine (r.palette_fits i w (v k)).trans (closedBall_subset_closedBall ?_); exact le_trans (r.fitted i w (outward x) (hk hk')) ((r.clearance_through hA i.val j.isLt).trans (M.clearance_le j.val))
   cases x with
   | some x=> exact hb x
   | none=> exact ( (hs.widen (fun t ht=> by rw [Function.comp_apply,Function.comp_apply,hz rfl ht])).diff (Displays.sum (fun i (_ : i∈Finset.univ)=>hb i))).agree (fun t ht=> by change f t-_ = f t- (∑ j:Fin (levels d i.val), M.insertRow (r.oculus w i.val (v t)) j) (f t); rw [LinearMap.sum_apply])

-- union of closed eligibility pieces along paths. Use twice for projected branches including in nonidentity roots.
lemma listener_plot (hh : Lit r H) (i:Q.parts) {d:Fin k→ℕ}(x:Way d i.val) (u:Fans P i.val)(q:Splittings i.val) (hA:r.Authority M d)(hp:1 < i.val.card) : Lit (r.renew i (outward x) u q hp) (r.listener M i x u q H):= by
   refine ⟨r.inheritsFixed hh.toFixed M i _ u q,?_⟩; rintro V _ v U b hU hv hs t ht
   let w:= b.val.1; let a:= b.val.2; let K:= normalOn P i.val; let Z:=replace i q.val
   let y (x':V):= ∏ j∈ q.val.parts, t j x'; let t'(x':V):= Function.update (fun j=> t j x') i.val (wind M d i.val x (r.oculus w i.val (v x')) (y x')); let F(x:V):=H w (v x) (∏ j∈ Q.parts,tag j (t' x j)); change ContinuousOn (fun u'=> H w (v u') (System.review Q i q.val (wind M d i.val x (r.oculus w i.val (v u'))) (∏ j∈Z.parts,tag j (t j u')))) U
   let f' (u' : V) := H w (v u') (System.review Q i q.val (wind M d i.val x (r.oculus w i.val (v u'))) (∏ j∈ Z.parts, tag j (t j u'))); change ContinuousOn f' U
   rw [show f'= F from funext fun j=> congrArg (H w (v j)) (weld_factors i q.val (wind M d i.val x (r.oculus w i.val (v j))) (fun i=> t i j))]
   have hw(x':V)(hx':x'∈U) : v x'∈ r.site i (outward x) u q w a:=hs hx'; have ht' (j) (hj:j∈ (Q.parts.erase i.val∪ q.val.parts)) : Displays U (r.palette w j ∘ v) (t j):= ht j (by rw [replace_parts]; exact hj)
   have hy : Displays U (r.palette w i.val ∘ v) y:= r.combines_plot i u q t (fun x hx=> (hw x hx).2) b.property.1.1 (fun j hj=> ht' j (Finset.mem_union_right _ hj))
   have he (X : Set V)(hX : IsClosed X) (hc : X ⊆ U) {V' : V→ E} (hq : ContinuousOn V' X)(hh' : MapsTo V' X (r.stage w))(hK : ∀ t∈X,v t-V' t∈ K)(hx : outward x=false → EqOn v V' X) : ContinuousOn F X := by
       apply ContinuousOn.congr (hh.scene _ hX hq hh' (fun j x=> t' x j) ?_) (?_)
       swap
       · intro x' hx'; unfold F; rw [hh.keeps w i (hK x' hx')]
       intro j hj; by_cases he:j=i.val
       · subst j; simp_rw [t',Function.update_self]; exact r.sends i (hv.mono hc) hA x hK hx (fun x hh'=> (hw x (hc hh')).1) (hy.subreg hc (fun _ _=>by rfl))
       simp_rw [t',Function.update_of_ne he]; exact (ht' j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hj⟩))).subreg hc (fun x hx=> r.palettes_stable w (hK x hx) (Q.disjoint hj i.property he))
   let X:= U ∩ v ⁻¹' (r.stage w); let k:= slide K 0 ∘ v; let Y:= U ∩ k ⁻¹' (r.stage w)
   have heL : ContinuousOn F X:= he _ (hv.preimage_isClosed_of_isClosed hU (r.closedStage w)) inter_subset_left (hv.mono inter_subset_left) inter_subset_right (fun x hx=> by rw [sub_self]; exact K.zero_mem) (fun _ x hx=> rfl)
   by_cases hW : outward x=true; swap; · have hh':outward x=false:= Bool.eq_false_of_not_eq_true hW; refine heL.mono fun w hw'=> ⟨hw',?_⟩; have hv:= (r.shadeLifts i _ _ _ _ _ (hw w hw')); rw [hh'] at hv; exact hv
   have hk : ContinuousOn k U:= (slide K 0).continuous.comp_continuousOn hv
   have hR : ContinuousOn F Y:= he Y (hk.preimage_isClosed_of_isClosed hU (r.closedStage w)) inter_subset_left (hk.mono inter_subset_left) inter_subset_right (fun x _=> relative_change K _) (fun he=> by rw [he] at hW; contradiction)
   refine (heL.union_of_isClosed hR (hv.preimage_isClosed_of_isClosed hU (r.closedStage w)) (hk.preimage_isClosed_of_isClosed hU (r.closedStage w))).mono fun x' hx'=>?_ ; have he:= (r.shadeLifts i _ _ _ _ _ (hw x' hx')); rw [hW] at he; exact Or.elim he (fun h=>Or.inl ⟨hx',h⟩) (fun h=> Or.inr ⟨hx',h.1⟩)
end Route
end YM.Contacts.Harvest

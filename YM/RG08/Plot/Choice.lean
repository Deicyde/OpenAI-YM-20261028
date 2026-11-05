import YM.RG08.Plot.Points
/-!
# Product keeps full volume independent roots
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Plot
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands
open scoped BigOperators Topology Real ContDiff
variable {I:Type} {h k e r:ℕ} {L:Side}{G:Gauge}{P:StripU G L}{F V U:Tale G}{p:List I}{A:I→ℕ}{z:Cover}
section algebra
lemma swell_left (h: Stone k F)(hz:Stone k V)(hp:Stone e U): gust (F+V) U=gust F U+gust V U:= by
  classical
  have hx:= h.more hz; apply unrolled (sails_from (wind hx hp)) (sails_from ((wind h hp).more (wind hz hp))); intro i m
  rw [sing_k (sails_from hx) (sails_from hp), show (gust F U+gust V U) i=gust F U i+gust V U i from rfl,spool_more (o:=_) ((sails_from (wind h hp)).thin _) ((sails_from (wind hz hp)).thin _),sing_k (sails_from h) (sails_from hp),sing_k (sails_from hz) (sails_from hp)]
  unfold billow; simp_rw [Pi.add_apply,fun i=> spool_more ((sails_from h).thin i) ((sails_from hz).thin i) (0:Site m),add_mul,sum_add_distrib]
lemma larger_w (v:ℝ)(V:Tale G)(k:ℕ)(h:Stone k V)(r i:ℕ)(p:Site L) : large p i ((v • V) r)= v • large p i (V r):= by unfold large; rw [Finset.smul_sum]; exact sum_congr rfl fun j _=>root_scale _ ((h.tidy r j).pens) _
lemma swell_w (h: Stone k F)(hp:Stone e U)(v:ℝ): gust (v • F) U= v • gust F U:= by
   apply unrolled (sails_from (wind (h.weight v) hp)) (sails_from ((wind h hp).weight _)); intro i m; rw [larger_w v _ _ (wind h hp),sing_k (sails_from (h.weight v)) (sails_from hp),sing_k (sails_from h) (sails_from hp)]; unfold billow; rw [Finset.smul_sum]; refine sum_congr rfl ?_; intro j _; simp only; rw [larger_w v _ k h,smul_mul_assoc]
lemma gust_same (h: Stone k F)(hp:Stone e U): gust F U=gust U F:= by
   let p:=wind hp h
   apply unrolled (sails_from (wind h hp)) (τ:=k+e) (by rw [add_comm k e]; exact sails_from p); intro i m; rw [sing_k (sails_from h) (sails_from hp),show k+e=e+k from add_comm k e,sing_k (sails_from hp) (sails_from h)]; unfold billow; -- commute wheel
   unfold wheel; rw [← Nat.sum_antidiagonal_swap]; exact sum_congr rfl fun i _=>mul_comm ..
lemma scale_space (z:Cover)(V U:Tale G)(hz:Stone k V)(hu:Stone e U): season z (gust V U)=gust (season z V) (season z U):= by
   let A:= gust V U; have hh:= wind hz hu; have hP:=hz.transport z; have hV:=hu.transport z
   apply unrolled (sails_from (hh.transport z)) (sails_from (wind hP hV)); intro i m; have he (U:Tale G)(k i:ℕ)(h:Stone k U): large (0:Site m) (k+i) (Town.season z U i)=large (0+wrap m z) (k+i) (U i):= by unfold large; exact sum_congr rfl fun j _=> roam_song (x:=z) (h.tidy i j).pens 0
   rw [he _ _ _ hh,sing_k (sails_from hz) (sails_from hu),sing_k (sails_from hP) (sails_from hV)]; unfold billow; exact sum_congr rfl (fun i _=> (congr_arg₂ (·*·) (he _ _ i.1 hz) (he _ _ i.2 hu)).symm)
lemma unit_space (G:Gauge)(z:Cover): season z (spine_one (Loc G 1))=spine_one (Loc G 1):= by
   ext1 i; ext1 j; by_cases he:i+j=0; · unfold spine_one; simp only [Town.season,he,↓reduceIte]; rfl
   unfold spine_one; simp only [Town.season,he,↓reduceIte,roam_zero]

lemma space_for (z:Cover){U:I→Tale G}(h:∀ i∈p,Stone (A i) (U i)): Town.season z (castF U p)=castF (fun i=> Town.season z (U i)) p := by
   induction p with
   | nil=> exact unit_space _ _
   | cons b u ih=>
     have hp i hi:=h i (List.mem_cons_of_mem _ hi); change Town.season z (gust (U b) (castF U u))=gust _ (castF _ u); rw [scale_space z _ _ (h b List.mem_cons_self) (stone_cast hp),ih hp]

-- Multilinearity use normalized Stone submodule so no branch on summability.
def mason (G:Gauge)(k:ℕ) : Submodule ℝ (Tale G) where
  carrier := {x| Stone k x}
  zero_mem' := Stone.zero
  add_mem' := Stone.more
  smul_mem' a _ h := Stone.weight h a
abbrev Car (G:Gauge)(k:ℕ):= ↥(mason G k)
abbrev Wagon (G:Gauge)(A:I→ℕ):= ∀ i,Car G (A i)
lemma Car.cer (v:Car G k): Stone k v.val:=v.property
private def playW (S:Wagon G A)(p:List I): Tale G:= castF (fun i=> (S i).val) p
private lemma loses [DecidableEq I] (S:Wagon G A){a:I}(x:Car G (A a))(p:List I)(h:a∉ p): playW (update S a x) p= playW S p:= by
   induction p with
   | nil => rfl
   | cons b u ih=>
     rw [show playW (update S a x) (b::u)=gust (update S a x b).val (playW (update S a x) u) from rfl,ih (fun z=>h (List.mem_cons_of_mem _ z)),update_of_ne (show b≠a from fun hx=>h (by simp [hx]))]; rfl
private lemma play_b (S:Wagon G A)(p:List I): Stone (loadᵣ A p) (playW S p):= stone_cast (fun i _=> Car.cer (S i))
private lemma pact [DecidableEq I](S:Wagon G A)(hp:p.Nodup)(a)(hx:a∈p)(x y:Car G (A a)): playW (update S a (x+y)) p=playW (update S a x) p+playW (update S a y) p:= by
   induction p with
   | nil=> simp at hx
   | cons b u ih=>
     have ht:= List.nodup_cons.mp hp; change gust (update S a _ b).val (playW _ u)=gust (update S a x b).val (playW _ u)+gust (update S a y b).val (playW _ u)
     by_cases h:b=a
     · subst b; rw [update_self,update_self,update_self, loses S (x+y) u ht.1,loses S x u ht.1,loses S y u ht.1]; exact swell_left (Car.cer x) (Car.cer y) (play_b S u)
     have he:= ih ht.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm h))
     rw [update_of_ne h,update_of_ne h,update_of_ne h]; have hp(U:Wagon G A):gust (S b).val (playW U u)=gust (playW U u) (S b).val := gust_same (Car.cer _) (play_b ..)
     rw [hp,hp,hp,he, swell_left (play_b (update S a x) u) (play_b (update S a y) u) (Car.cer (S b))]
private lemma prism [DecidableEq I](S:Wagon G A)(hp:p.Nodup)(a)(hx:a∈ p)(s:ℝ)(x:Car G (A a)): playW (update S a (s • x)) p=s • playW (update S a x) p:= by
   induction p with
   | nil=> simp at hx
   | cons b u ih=>
     have ht:=List.nodup_cons.mp hp; change gust (update S a _ b).val (playW _ u)=s • gust (update S a x b).val (playW _ u)
     by_cases h:b=a
     · subst b; rw [update_self,update_self,loses S _ u ht.1, loses S _ u ht.1]; exact swell_w (Car.cer _) (play_b ..) s
     rw [update_of_ne h,update_of_ne h]; have he(U:Wagon G A): gust (S b).val (playW U u)= gust (playW U u) (S b).val := gust_same (Car.cer _) (play_b ..)
     rw [he,he,ih ht.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm h)), swell_w (play_b (update S a x) u) (Car.cer (S b))]
def junta (A:I→ℕ)(G:Gauge){p:List I}(hp:p.Nodup)(he:∀ i,i∈p): MultilinearMap ℝ (fun i=> Car G (A i)) (Tale G) :=⟨fun x=>playW x p,fun m i x y=>pact m hp i (he i) x y, fun m i s x=>prism m hp i (he i) s x⟩
-- expansion into rooted monomials
variable [Fintype I][DecidableEq I] {J:I→Type}
lemma pact_product (s:∀ i,Finset (J i))(F:∀ i,J i→Tale G)(h:∀ i j,Stone (A i) (F i j))(hp:p.Nodup)(he:∀ i,i∈p):
    castF (fun i=>∑ j∈s i,F i j) p= ∑ w∈ Fintype.piFinset s,castF (fun i=>F i (w i)) p := by
   let v i j:Car G (A i):=⟨F i j,h i j⟩
   let S:= junta A G hp he
   refine Eq.trans ?_ (S.map_sum_finset v s); refine congr_arg (fun x:I→ Tale G=> castF x p) ?_
   funext i; change _ = ((mason G (A i)).subtype (∑ j∈s i,v i j)); rw [map_sum]; rfl
lemma jam_grows (P:StripU G L)(h:Fair P)(hp:p.Nodup)(he:∀ i,i∈p)(s:∀ i, Finset (J i))(F:∀ i,J i→Tale G)(hv:∀ i j,Stone (A i) (F i j))(u:Site L):
   jamT P (fun i=> ∑ j∈s i,F i j) u A p=∑ w∈Fintype.piFinset s,jamT P (fun i=> F i (w i)) u A p:= by
   unfold jamT; rw [pact_product s F hv hp he,inscript_list (Fintype.piFinset s) u _ (fun i _=> stone_cast (fun v (h':v∈p)=>hv v (i v))) h]; simp_rw [fun i=>inscript_list (s i) u (F i) (fun j _=>hv i j) h]
   rw [pact_product s (fun i j=> inscribed (A i) P u (F i j)) (fun i j=>inscribe_law _ h (hv i j)) hp he, ← Finset.sum_sub_distrib]
end algebra
end YM.RG08.Plot

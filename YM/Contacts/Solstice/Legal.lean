import YM.Contacts.Solstice.Venue
/-!
# Actual use of detectors inside their apertures

The formulas are pointwise only after totalizations. Eg. a projectAt x n can be invoked on any
finite field-expression, but doesn't denote a projection on overlarge geometry or on a multi-field
expression right on its own coincidence. Here we prove independence of any aberrant readings on
arbitrary words **outside** the apertures and distinct placements of the probes (within linear
words). Thus the integrals on their indicated patches, including all the projected arms & shells,
are bona fide legal detector readings. This is more than just saying the individual root coefficient
uses the correct apertures. The key is it's the *choice of arm and its output* with which the
context reads inside the range. A Taylor projection of a child may use larger radii and invoke own
projections where the ancestor has no clearance; the result uses only the original aperture for
ancestor probes.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact MultipleContact.Script OPE Layers Ordered Harvest Route TopologicalSpace
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory TensorProduct
variable {E X W I : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup X][NormedSpace ℂ X]
variable {k : ℕ}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{Z:Final C F S}
variable {g : Normal.Group k}{P:E→ₗᵢ[ℝ] Points k} {Q : Pieces g}{d : Fin k→ℕ}
local notation "E!"=> Expression Z.sector.derivatives
local notation "GN"=> Normal.Group k

-- at predicate specialized to a point, supports truly on distinct configurations
abbrev FitsBasis {G:Gauge}{C:Family G}{S:Table C.book}{P:DiffPlan S} (F:Expression P)(a:Set E4):= Displays (Set.univ:Set Unit) (fun _=>a) (fun _=>F)
-- projections use M.aperture & M.clearance (≤ aperture) this formula's sole geometric qualification
abbrev Mirror (Z:Final C F S) := E4→ ℕ→ Expression Z.sector.derivatives →ₗ[ℂ] Expression Z.sector.derivatives
variable (M : Devices Z.sector.derivatives)
def Mirror.Consent (Y : Mirror Z) := ∀ (k : E4) n e,FitsBasis e (closedBall k (M.clearance n)) → Y k n e=M.insertRow k n e

variable (r:Route P Q I W)(T: W→ Cells S d) (Y : Mirror Z)
def footprint (k:E4)(v:Way d g) : Expression Z.sector.derivatives→ₗ[ℂ] Expression Z.sector.derivatives := v.elim (LinearMap.id-∑j:Fin (levels d g), Y k j) (Y k ·)
def tailor (w : W) : System E (Expression Z.sector.derivatives) k := { r.components M T w with deg:=d, reader i n x:= Y (r.oculus w i x) n }
lemma loom (i : GN)(w : W)(x:E)(b : Way d i): (tailor M r T Y w).treatment i b x= footprint (g:=i) Y (r.oculus w i x) b:= by
   cases b; · change LinearMap.id- (∑ j:Fin (levels d i), fun x=> Y (r.oculus w i x) j.val) x = _; rw [Finset.sum_apply]; rfl
   rfl

structure Mirrors (Z:Final C F S)(r : Route P Q I W)(H D : Reader E W X k Z.sector.derivatives) : Prop where
    kept : Fixed H Q P
    as_kept : Fixed D Q P
    tested : ∀ w,∀ x∈r.stage w,∀ e : Normal.Group k → Expression Z.sector.derivatives, (∀ i∈Q.parts,FitsBasis (e i) (r.palette w i x)) →
       H w x (∏ i∈ Q.parts,tag i (e i)) = D w x (∏ i∈ Q.parts,tag i (e i))
variable (i : Q.parts)(u:Fans P i.val)(v:Splittings i.val)(b:Way d i.val)(h : 1 < i.val.card)

variable (D : Reader E W X k Z.sector.derivatives)
def ask : Reader E (r.ramp i (outward b) u v) X k Z.sector.derivatives:= fun t x=> (D t.val.1 x).comp (System.review Q i v.val (footprint Y (r.oculus t.val.1 i.val x) b))
variable {D M r Y} {H : Reader E W X k Z.sector.derivatives}
lemma Fonts (hs:r.Authority M d) {x : E}{w : W}(hx : x∈ halo (normalOn P i.val) (r.length w) (outward b) (r.stage w)) {e}
   (hE : FitsBasis e (r.palette w i.val x)) (he : Y.Consent M) : footprint (d:=d) (g:=i.val) Y (r.oculus w i.val x) b e= wind M d i.val b (r.oculus w i.val x) e:= by
   have ht(w':Fin (levels d i.val)):Y (r.oculus w i.val x) w' e = M.insertRow (r.oculus w i.val x) w' e:= he _ _ e (hE.widen (fun t _=> (r.palette_fits i w x).trans (closedBall_subset_closedBall (( (show ‖(normalOn P i.val).starProjection x‖≤r.ceiling from r.fitted i w (outward b) hx)).trans (r.clearance_through hs i.val w'.isLt))))) -- .. greedy
   cases b with
   | none=> change e-(∑ j:Fin (levels d i.val), Y (r.oculus w i.val x) j) e= e-(∑ j: Fin (levels d i.val), M.insertRow (r.oculus w i.val x) j) e; rw [LinearMap.sum_apply,LinearMap.sum_apply]; exact congrArg (e-·) (Finset.sum_congr rfl fun i _=> ht i)
   | some t=> exact ht t

lemma fixed_shift (hd : Fixed D Q P) : Fixed (ask r Y i u v b D) (replace i v.val) P:= by
   constructor; rintro w ⟨k,hk⟩ x y (hx:x-y∈normalOn P k); unfold ask; rw [replace_parts] at hk; rcases Finset.mem_union.mp hk with h|h
   · obtain ⟨hh,h⟩:= Finset.mem_erase.mp h; rw [hd.keeps _ ⟨k,h⟩ hx, r.oculus_still _ i.val _ _ hx (.inr (Q.disjoint h i.property hh))]
   have he:= normal_le P (v.val.le h) hx; rw [hd.keeps _ i he,r.oculus_still _ i.val _ _ he (.inl rfl)]

lemma mirrors_front (hm:r.Authority M d)(hL : Mirrors Z r H D) (hY : Y.Consent M) : Mirrors Z (r.renew i (outward b) u v h)
     (r.listener M i b u v H) (ask r Y i u v b D):= by
   refine ⟨r.inheritsFixed hL.kept M i b u v, fixed_shift i u v b hL.as_kept,?_⟩; intro w x hx e he
   have hx:x∈r.site i (outward b) u v w.val.1 w.val.2:= hx; obtain ⟨y,hy,hK,hW⟩:= follows _ hx.1
   let t:= ∏ j∈ v.val.parts,e j; let L:= r.oculus w.val.1 i.val x; let t' := wind M d i.val b L t
   have hp : FitsBasis t (r.palette w.val.1 i.val x):= r.combines_plot i u v (fun i (_:Unit)=>e i) (s:=fun _=>x) (fun _ (_: _∈ (Set.univ:Set Unit))=> hx.2) w.property.1.1 (fun j hj=> he j (by rw [replace_parts]; exact Finset.mem_union_right _ hj)) -- Mapsto inference
   unfold ask listener; rw [LinearMap.comp_apply,LinearMap.comp_apply,weld_factors,weld_factors]
   rw [show footprint (d:=d) (g:=i.val) Y (r.oculus w.val.1 i.val x) b t=t' from Fonts i b hm hx.1 hp hY,hL.kept.keeps _ i hK,hL.as_kept.keeps _ i hK] -- abbrev
   refine hL.tested w.val.1 y hy (Function.update e i.val t') (fun j hj=> ?_)
   by_cases hh:j=i.val; swap; · rw [Function.update_of_ne hh]; exact (he j (by rw [replace_parts]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hh,hj⟩))).widen (fun _ _=> r.palettes_stable w.val.1 hK (Q.disjoint hj i.property hh))
   subst j; rw [Function.update_self]; exact r.sends i (v:=fun (_:Unit)=>x) (V:=Unit) (U:=(Set.univ:Set Unit)) (y:=fun _=>y) continuousOn_const hm b (fun _ _=> hK) (fun h _ _=> hW.resolve_right (fun hh=> by rw [h] at hh; contradiction)) (fun _ _=> hx.1) hp

end YM.Contacts.Solstice

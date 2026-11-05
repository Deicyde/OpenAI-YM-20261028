import YM.Contacts.Harvest.Absolute
/-!
# Achieving the base case

No more collisions. But the outputs might be entering many successive linear readings with
previous subtractions. Use precisely the signed estimates on the *unit case*. Absolute bounds
pass in a geometry measured by our ambient volume. Not just at a common root. Under normalization
each leaf input still can pay at most its stipulated own weight.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Harvest.Route
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact MultipleContact.Script OPE Layers Ordered
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory TensorProduct
variable {E X W I : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup X][NormedSpace ℝ X][NormedSpace ℂ X][IsScalarTower ℝ ℂ X][CompleteSpace X]
variable {G: Gauge} {C: Family G}{F: Extraction.Order}{S : Table C.book} {Z: Final C F S}
variable {k : ℕ} {d : Fin k→ℕ}{g : Normal.Group k} {P : E→ₗᵢ[ℝ] Points k} {Q : Pieces g} {γ : ℝ}

local notation "GN" => Normal.Group k
private def Carry (E A : Type)[NormedAddCommGroup E][NormedSpace ℝ E][CommRing A][Algebra ℂ A] : (E → A) →ₐ[ℂ] Score E A:= Algebra.TensorProduct.includeLeft
private def basics (_P : E→ₗᵢ[ℝ] Points k) (_s : ℝ) {A : Type}(Y:System E (Grammar A) k) (i:GN)(x : E) := ∏ j∈i,Y.field j x

variable (r : Route P Q I W) (H : ∀ i∈Q.parts,i.card≤1)
include H
lemma alone_in {i : GN}(h : i∈Q.parts): ∃ j,i={j}:= Finset.card_eq_one.mp (le_antisymm (H i h) (Q.nonempty_of_mem_parts h|>.card_pos))
lemma no_shadow (f : Menu k) : shadow Q f γ=1 := Finset.prod_eq_one fun i hi=> paid (H i hi)
private lemma stripped (s : ℝ) {A : Type}(Y:System E (Grammar A) k) (f : Menu k)
    (a : SmoothTests E)(x : E): action x a (Y.election P s f Q) = a.val x • ∏ i∈Q.parts, tag i (basics P s Y i x) := by
   let t(j:GN) (x:E) := tag j (basics P s Y j x); let R:= Y.present P s f; let L':= Board GN A
   have he:Ordered.product Q.parts R=Ordered.product Q.parts (fun i=> Carry E L' (t i)):= by refine Ordered.eq_product fun i hi=>?_ ; obtain ⟨j,rfl⟩:=alone_in H hi; simp_rw [R,t,System.present, System.alone P Y s _ _ (H _ hi), System.full_single, Carry,retags, reshape_tape]; change evaluateHeads _ _ ⊗ₜ[ℂ] _ = ((fun x => _):E→ L') ⊗ₜ[ℂ] _; congr; funext x; simp [evaluates,basics]
   change action x a (Ordered.product Q.parts R)= _; rw [he,← show Carry E L' (Ordered.product Q.parts t)=Ordered.product Q.parts (fun i=> Carry E L' (t i)) from Ordered.mapped _ t (Carry E L').toRingHom, Ordered.product_true]; change action x a ((∏ i∈Q.parts,t i) ⊗ₜ[ℂ] (1:Optical E))=_; rw [action_tmul, Finset.prod_apply]; rfl

omit H
variable (M : Devices Z.sector.derivatives) (T : W→ Cells S d) (D : Reader E W X k Z.sector.derivatives)
/-- Bounded uniformly on external parameter. -/
def Given {L : Register G}{S: Table L}(T: W→ Cells S d) := ∃ c:ℝ, ∀ i w, ‖T w i‖ ≤ c
private def charge (w : W)(x : E) := D w x (∏ i∈Q.parts, tag i (basics P (r.length w) (r.components M T w) i x))
include H
omit [NormedSpace ℝ X] [CompleteSpace X] [IsScalarTower ℝ ℂ X]
private lemma raw_scene {w : W} (h : Lit r D) : ContinuousOn (r.charge M T D w) (r.stage w):= by
   refine h.scene w (r.closedStage _) continuousOn_id (Set.mapsTo_id _) (fun i x=> basics P (r.length w) (r.components M T w) i x) ?_; intro i hi; obtain ⟨v,rfl⟩:= alone_in H hi; simp_rw [basics,Finset.prod_singleton, (r.core_field M T)]; refine Displays.field (fun x _=> ?_) (f:=fun _=> T w v) (((Normal.position v).continuous.comp (r.actual_continuous w)).continuousOn) continuousOn_const
   change r.actualAt w x v ∈ r.palette w {v} x; rw [← centroid_single]; exact r.centre ⟨_,hi⟩ w x
lemma wind_charge (w x a) (f : Menu k) : r.windings M D T f w a x=a.val x • r.charge M T D w x:= by unfold windings scoreAt; rw [stripped (P:=P) H,map_smul]; rfl
variable [Fintype I]
private lemma initial_loan {B : W→ℝ}(h : Loan Z M r B D)(hh : Given T) (he : 0<γ): ∃ L > (0:ℝ),∀ w,∀ x∈ r.stage w, ‖r.charge M T D w x‖ ≤ L*(r.face d w * B w)* surcharges r.diameter w γ:= by
   let U : Set (W×E):={p| p.2∈r.stage p.1}; let v (p:W×E):= r.face d p.1 * B p.1; let f (p:W×E):= r.charge M T D p.1 p.2
   obtain ⟨c,hc⟩:=hh; obtain ⟨A,hA,H'⟩:= compactify (U:=U) (q:=v) (fun i p=>r.diameter i p.1) f he (fun x hx i=> r.accounted i x.1) (fun φ _ T' w ht hv=> by
     let x : ℕ→ E:= Prod.snd ∘ w; let y : ℕ→ W:= Prod.fst ∘ w; have hQ : Ride r.diameter φ T' y:= ⟨ht.height,ht.entries⟩
     choose p hp he using ht.entries; obtain ⟨c',hc'⟩:= h.currency.exactRate φ T' y hQ (fun i=>Set.mem_univ _)
     let b(i:GN):= arityRate d i * (p (r.register i)); have hB : RateIs φ T' (v ∘ w) (c'+Q.parts.sum b):= ((r.prices_height (p ∘ r.register) d (U:=y) (fun i hi=> he (r.register i)) ht.height).mul hc').swap (add_comm ..)
     refine ⟨c'+Q.parts.sum b,hB,h.path hQ hc' (fun i=>hv i) b (fun i t=> basics P (r.length (y t)) (r.components M T (y t)) i (x t)) (fun i hi=>?_)⟩
     obtain ⟨v,rfl⟩:= alone_in H hi; intro t hT; let j:=r.register {v}; have ht':t=p j:= Entry.same hT ⟨hp j,he j⟩; subst t; simp_rw [basics,Finset.prod_singleton,r.core_field M T];
     refine (Fine.field ht.height (p:=fun i=>T (y i) v) (?_) (?_)).funds (hp j).2
     · exact ⟨⟨{v},by rfl,Finset.singleton_nonempty _⟩,funext fun j=>  centroid_single (r.actualAt (y j) (x j)) v⟩
     unfold b arityRate; rw [Finset.sum_singleton,sub_self]; exact RateLE.absBound _ ht.height (Eventually.of_forall fun j=> hc v _))
   exact ⟨A,hA,fun w x hx=>H' (w,x) hx⟩
variable [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure]
omit [Fintype I] H in
lemma normal_volume (A : E≃L[ℝ] E)(x : ℝ) : volume.real (limited A x) = basic A * volume.real (closedBall (0:E) x) := by
   unfold limited; simp_rw [measureReal_def]; rw [← A.image_eq_preimage_symm,Measure.addHaar_image_continuousLinearEquiv, ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)]; rfl
omit [Fintype I] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ X] [NormedSpace ℂ X] [CompleteSpace X] [IsScalarTower ℝ ℂ X] H in
private lemma bounded_set {T : Set E} {f : E→ X} {c : ℝ}(hc : IsCompact T)(h : ContinuousOn f T)(hm : ∀ x∉T,f x=0)(hp : ∀ x∈T,‖f x‖ ≤ c) : Dust f (c*volume.real T):= by
   have he:T.indicator f=f:= by funext i; by_cases hi:i∈T; simp [Set.indicator,hi]; simp [Set.indicator,hi,hm i hi]
   constructor
   · exact he ▸ (h.integrableOn_compact hc).integrable_indicator hc.measurableSet
   rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f:=fun i=>‖f i‖) (fun i hi=> by rw [hm i hi,norm_zero])]; refine (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const hc.measure_lt_top (fun x hx=> by rw [norm_norm]; exact hp x hx))

lemma achieved_alone {B : W→ℝ} (hl : Loan Z M r B D) (hp : Given T)(hhY : Economy Q γ): ∃ C >(0:ℝ), Achieves Z M r T B D γ C := by
   let V:= generosity Q γ; obtain ⟨C,hc,h⟩:= r.initial_loan H M T D hl hp (generosity_pos hhY.pos); -- name clash
   let C':= volume.real (closedBall (0:E) r.reserve)
   let L := max 1 C'; have hL : 0<L:= zero_lt_one.trans_le (le_max_left ..)
   refine ⟨C*L,mul_pos hc hL,?_⟩; constructor; intro f w p a ht hh; rw [no_shadow H f,mul_one]
   let F : E→ X:= r.windings M D T f w p; let U:=r.stage w; have hm:F=fun x=> p.val x • r.charge M T D w x:=funext fun x=>r.wind_charge H M T D w x p f
   let K:= C*(r.face d w*B w)*surcharges r.diameter w V
   have he:= r.limited_stage w; have hx : IsCompact U:= limit_compact.of_isClosed_subset (r.closedStage w) he
   have hz : ∀ x, ‖p.val x‖ ≤ a:=by
       intro x; have hh:= hh.value (Set.mem_univ ((r.frame w).symm x)); change ‖p.val (r.frame w ((r.frame w).symm x))‖ ≤ a at hh; rwa [ContinuousLinearEquiv.apply_symm_apply] at hh
   change Dust F _; rw [hm]; have ha:=hh.pos; have hb:= hl.currency.pos w (Set.mem_univ _); -- use B currency
   refine (bounded_set (f:=fun x=>p.val x • r.charge M T D w x) (c:=a*K) hx ((infSmooth p).continuous.continuousOn.smul (r.raw_scene H M T D ?_)) (fun x hx=> by rw [notMem_support.mp (show x∉ support p.val from fun hh=> hx (ht (subset_closure hh))),zero_smul]) (fun x hx=> ?_)).mono (?_)
   · exact hl.toLit
   · rw [norm_smul]; gcongr; exacts [hz x,h w x hx]
   have hZ:0<K:= mul_pos (mul_pos hc (mul_pos (r.face_pos w d) hb)) (r.fees_pos w)
   have he : volume.real U ≤ basic (r.frame w)* L:= (measureReal_mono he limit_compact.measure_lt_top.ne).trans ((normal_volume (r.frame w) r.reserve).trans_le (mul_le_mul_of_nonneg_left (le_max_right ..) (basic_pos ..).le))
   apply le_trans (mul_le_mul_of_nonneg_left he (mul_nonneg ha hZ.le)); exact le_of_eq (by unfold K bag V; ring) -- h name?
end YM.Contacts.Harvest.Route

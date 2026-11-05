import YM.Next.UV_STRESS.Product
import YM.TraceExtension.Cask.Tidal
import YM.Gauge.MatrixGroup
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker Function Wilson MeasureTheory Next.UVStress
open scoped Classical
section
variable {G:Gauge}{V I:Type*}[Fintype V]
abbrev Rain (V:Type*)(G:Gauge):= V→ G.El
abbrev freq (V:Type*)[Fintype V](G:Gauge):Measure (Rain V G):= Measure.pi (fun _=> G.probHaar)
def rule (Z:Finset V)(f : Rain V G→ℂ) := Draws (· ∈ Z) f
lemma harvest (S:Finset I) (D:I→ Finset V) (f:I→Rain V G→ℂ) (H:(S:Set _).PairwiseDisjoint D) (hf:∀ i∈S, rule (D i) (f i)) :
  (∫ u:Rain V G,∏ i∈S,f i u ∂ freq V G) =∏ i∈S,∫ u,f i u ∂freq V G:=by
    induction S using Finset.induction_on with
    | empty=> simp
    | @insert i s hi IH=>
       have hp:= hf i (mem_insert_self ..); let g := fun u:Rain V G=> ∏ j∈s,f j u
       have ht: Draws (fun j=> j ∉ D i) g:=by
          intro a b h; refine Finset.prod_congr rfl (fun k hk=> hf _ (mem_insert_of_mem hk) _ _ ?_)
          intro v hv; exact h v (fun hz=> disjoint_left.mp (H (mem_insert_self ..) (mem_insert_of_mem hk) (fun he=> hi (he.symm ▸ hk))) hz hv)
       simp_rw [prod_insert hi,← IH (H.subset (coe_subset.mpr (Finset.subset_insert ..))) (fun k hk=> hf k (mem_insert_of_mem hk))]; simpa only[scatter, Pi.mul_apply, prod_const_one, one_mul] using scatter_parts (fun x:V=> x∈D i) G.probHaar (fun _ _=>1) hp ht (by intro j;simp)
lemma vortex (t : Rain V G) (f:Rain V G→ℂ)(h:Measurable f):
    (∫ u, f (t*u) ∂freq V G) =∫ u,f u ∂freq V G:=by
    have hp : MeasurePreserving (fun u=>t*u) (freq V G) (freq V G):= measurePreserving_pi _ _ (fun v:V=> measurePreserving_mul_left G.probHaar (t v))
    calc
      _ =∫ u,f u ∂Measure.map (fun u=>t*u) (freq V G):= (integral_map hp.measurable.aemeasurable h.aestronglyMeasurable).symm
      _ = _:=by rw[hp.map_eq]
end
section env
variable {S T:Type*} [MeasurableSpace S]
lemma constV (x:ℂ): Envelope (fun _ : S=>x):= ⟨measurable_const,_,fun _=>le_rfl⟩
lemma fromR {f:S→ℝ}(h:Envelope f):Envelope (Complex.ofReal ∘ f):=by obtain ⟨c,hc⟩:=h.cost; exact ⟨Complex.measurable_ofReal.comp h.meas,c,fun x=>by simpa using hc x⟩
lemma meanN {f:S→ℂ}{H:ℝ} (h:∀ x,‖f x‖≤H)(μ:Measure S)[IsProbabilityMeasure μ]: ‖∫ x,f x∂μ‖ ≤ H:= by
    simpa using norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall h : ∀ᵐ x ∂μ, ‖f x‖ ≤ H)
lemma costNN [Nonempty S] {f:S→ℂ} (h: Envelope f) : ∃ c:ℝ,0 ≤ c ∧ ∀ s, ‖f s‖ ≤ c:=by
   obtain ⟨c,h⟩:= h.cost; obtain ⟨i⟩:= ‹Nonempty S›; exact ⟨c,(norm_nonneg _).trans (h i),h⟩
lemma envUmul {f g:S→ℂ} (h:Envelope f)(hs:Envelope g): Envelope (fun s=>f s*g s):= by
   obtain ⟨a,ha⟩:= h.cost; obtain ⟨b,hb⟩:=hs.cost
   exact ⟨h.meas.mul hs.meas,a*b,fun v=>(norm_mul ..).trans_le (mul_le_mul (ha _) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (ha v)))⟩
lemma envUadd {f g:S→ℂ}(h:Envelope f)(hs:Envelope g):Envelope (fun s=>f s+g s):= by obtain ⟨a,ha⟩:= h.cost; obtain ⟨b,hb⟩:=hs.cost;exact ⟨h.meas.add hs.meas,a+b,fun v=>(norm_add_le ..).trans (add_le_add (ha _) (hb _))⟩
lemma envUsub {f g:S→ℂ}(h:Envelope f)(hs:Envelope g): Envelope (fun s=> f s-g s):=by simp_rw [sub_eq_add_neg]; obtain ⟨c,hc⟩:=hs.cost; exact envUadd h ⟨hs.meas.neg,c,fun x=> (norm_neg _).trans_le (hc x)⟩
lemma envUsum (s:Finset T)(F:T→S→ℂ)(h:∀ i∈s,Envelope (F i)): Envelope (fun V=>∑ i∈s,F i V):=by
   induction s using Finset.induction_on with
   | empty=> simp; exact constV _
   | insert i s hi IH=> simp_rw [sum_insert hi]; exact envUadd (h _ (mem_insert_self ..)) (IH (fun i hi=> h _ (mem_insert_of_mem hi)))
lemma envUprod (s:Finset T)(F:T→S→ℂ)(h:∀ i∈s,Envelope (F i)): Envelope (fun V=>∏ i∈s,F i V):=by
   induction s using Finset.induction_on with
   | empty=> simp; exact constV _
   | insert i s hi IH=> simp_rw [prod_insert hi]; exact envUmul (h _ (mem_insert_self ..)) (IH (fun i hi=> h _ (mem_insert_of_mem hi)))
lemma capped {f:S→ℂ}(h:Envelope f)(μ:Measure S)[IsFiniteMeasure μ]: Integrable f μ:=by obtain ⟨c,hc⟩:= h.cost; exact Integrable.of_bound h.meas.aestronglyMeasurable c (Filter.Eventually.of_forall hc)
variable [MeasurableSpace T]
lemma based {f:S→ℂ}(h: Envelope f)(g:T→ S)(hs:Measurable g): Envelope (f ∘ g):= by obtain ⟨c,hc⟩:=h.cost; exact ⟨h.meas.comp hs,c,fun x=> hc (g x)⟩
lemma sealM {f:S→ T→ℂ}(μ:Measure T)[IsProbabilityMeasure μ](h:Envelope (uncurry f)): Envelope (fun s=> ∫ v,f s v∂μ):=by obtain ⟨c,hc⟩:=h.cost; exact ⟨h.meas.stronglyMeasurable.integral_prod_right.measurable,c,fun s=> meanN (H:=c) (fun t=>hc (s,t)) μ⟩
end env
end YM.Trace.Cask

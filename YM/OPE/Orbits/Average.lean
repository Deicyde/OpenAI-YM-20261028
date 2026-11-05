import YM.OPE.Orbits.Spin

/-! Equivariant readout through Haar averaging. Single-field inputs
are fixed through each sufficient output horizon (a key exact fact for
constructing compatible readouts). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Filter Set MeasureTheory Extraction Table Word Prescription
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
attribute [local instance] measO borelO YM.Work.A15.compact_ortho
local instance : SecondCountableTopology Ortho := by
    haveI:SecondCountableTopology M4:= inferInstanceAs (SecondCountableTopology Lines)
    exact inferInstanceAs (SecondCountableTopology ↥(Matrix.unitaryGroup Axis ℝ : Set M4))
local instance hH : haar.IsHaarMeasure:= by unfold haar; infer_instance
local instance hP : IsProbabilityMeasure haar := by unfold haar; apply IsProbabilityMeasure.mk; apply Measure.haarMeasure_self

variable {G:Gauge}{L:Register G}{S:Table L}{Q:DiffPlan S}{P:Prescription Q}{X:Rotation S}{ρ:S.RealSpin}
variable {I J:Type}[Fintype I]{d:I→ℕ} (hX:X.Laws Q ρ) (hS:S.Hierarchy)
variable (m:ℕ)(w:Labels S d){x:I→E4}{o:E4}

def averageV (P:Prescription Q)(X:Rotation S)(n:ℕ)(x:I→E4)(o:E4)(w:Labels S d): S.Field n:= if orbitMargin P n x o then ∫ k,spinning P X n x o k w ∂haar else 0

include hS hX in
lemma average_expand (hx:orbitMargin P m x o):averageV P X m x o w= ∑ i∈ bands Q m,∫ k,bears X P i m x o w k ∂haar:=by
    rw [averageV,if_pos hx]; simp_rw [Orbits.scatter P hS m]; exact integral_finsetSum _ (fun i hi=>integrable_bears P hX hS m x o i w (hx i hi))
lemma margin_open : IsOpen {z:(I→E4)×E4|orbitMargin P m z.1 z.2}:=by
    apply isOpen_iff_mem_nhds.mpr; intro z hz; change ∀ᶠ z':(I→E4)× E4 in 𝓝 z,orbitMargin P m z'.1 z'.2
    unfold orbitMargin; exact (eventually_all_finset _).mpr fun i hi=> ((compact_dock P i).mem_nhds (hz i hi))
include hS hX in
lemma average_smooth (hx:orbitMargin P m x o):ContDiffAt ℝ ∞ (fun p:(I→ E4)×E4=> averageV P X m p.1 p.2 w) (x,o):=by
    refine (ContDiffAt.sum (f:=fun i (z:(I→E4)×E4)=> ∫ k,bears X P i m z.1 z.2 w k ∂haar) (s:=bands Q m) ?_).congr_of_eventuallyEq ?_
    · intro i hi; exact smooth_orbit_row P hX hS m x o i w (hx i hi)
    filter_upwards [(margin_open (P:=P) (I:=I) m).mem_nhds hx] with z hz; exact average_expand (hS:=hS) hX _ w hz -- arg order

private lemma bears_ite (i:I)(q:Mode Q)(k:Ortho) (a:S.Field (d i)) : bears X P q m x o (update w i a) k =
    checkRow P q (Ortho.move k⁻¹ ∘ x) (Ortho.move k⁻¹ o) (update (roll X k⁻¹ w) i (X.act _ k⁻¹ a)) • X.act m k (P.loaded q m):=by
    unfold bears; congr 2; funext j
    by_cases he:j=i; subst j; · rw [update_self]; exact congr_arg _ (update_self ..)
    erw [update_of_ne he]; apply congr_arg (X.act _ k⁻¹); exact update_of_ne he ..
def readMap (P:Prescription Q) (X:Rotation S) (hX:X.Laws Q ρ) (hS:S.Hierarchy)(m:ℕ) (x:I→ E4)(o:E4): MultilinearMap ℂ (fun i=>S.Field (d i)) (S.Field m) := by
    classical
    refine ⟨averageV P X m x o,?_,?_⟩
    · intro K; have : K=Classical.decEq _:=Subsingleton.elim _ _; subst K; intro v i a b
      by_cases ht:orbitMargin P m x o; swap; simp [averageV,ht]
      simp_rw [average_expand hX hS m _ ht,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro q hq
      rw [← integral_add (integrable_bears P hX hS m _ _ _ _ (ht q hq)) (integrable_bears P hX hS m _ _ _ _ (ht q hq))]; apply integral_congr_ae; filter_upwards with k
      rw [bears_ite m, map_add,MultilinearMap.map_update_add,add_smul,bears_ite m,bears_ite m]
    intro K; have : K=Classical.decEq _:=Subsingleton.elim _ _; subst K; intro v i a b
    by_cases ht:orbitMargin P m x o; swap; simp [averageV,ht]
    simp_rw [average_expand hX hS m _ ht, Finset.smul_sum]; apply Finset.sum_congr rfl; intro q hq
    rw [← integral_smul]; apply integral_congr_ae; filter_upwards with k
    rw [bears_ite m, map_smul,MultilinearMap.map_update_smul, bears_ite m,← smul_assoc]
-- fix singleton syntax
lemma old_fixes {d:ℕ}(hInc:Q.Inclusions S)(hP:P.Coherent)(hS:S.Hierarchy)(v:S.Field d)(he:d≤ m):
    shadow P m (sole (0:E4)) (sole (quoteTag (⟨d,v⟩:S.Tag))) 0=Q.rise he v:=by
    unfold shadow; have hi i: P.ope i (sole (0:E4)) (sole (quoteTag (⟨d,v⟩:S.Tag))) 0=P.test i m (Q.rise he v) :=by
         rw [quoteTag,P.insertOne d _ hS,P.affinity hS.laws.toSymmetric hInc i v he,S.rep]
    simp_rw [hi]; exact (hP m).rebuilds _

lemma centerMargin (P:Prescription Q) (m:ℕ) : orbitMargin P m (sole (0:E4)) 0:=by
    intro i h k e he; have hi : Ortho.move k 0=0:= map_zero (Ortho.motion k)
    have hw : away (Ortho.move k ∘ sole (0:E4)) (Ortho.move k 0)= sole (0:E4):=funext (fun i=>by rw [hi]; unfold away; change Ortho.move k (0:E4)-0=0; rw [hi,sub_zero])
    rw [hw]; exact bearing_clear e
include hS hX in
lemma average_fixes {j:ℕ}(v:S.Field j)(hi:Q.Inclusions S)(hp:P.Coherent)(he:j≤ m):
    averageV P X m (sole 0) 0 (d:=fun _=>j) (sole v)=Q.rise he v:=by
    rw [averageV,if_pos (centerMargin P m)]
    have hv(k:Ortho): spinning P X m (sole 0) (0:E4) k (d:=fun _=>j) (sole v)= Q.rise he v:=by
       unfold spinning; have hx:Ortho.move k⁻¹ 0=0:=map_zero (Ortho.motion k⁻¹)
       have hh : Ortho.move k⁻¹ ∘ sole (0:E4)=sole (0:E4):= by funext; exact hx
       have hg : (names (roll X k⁻¹ (fun i=> (sole v i:S.Field j))))=sole (quoteTag (⟨j,X.act j k⁻¹ v⟩:S.Tag)):=rfl
       rw [hh,hx,hg,old_fixes m hi hp hS _ he, hX.filtered,← hX.group]; rw [mul_inv_cancel,hX.fixes]
    simp_rw [hv]; simp
omit [Fintype I] in
lemma move_margin (a:Ortho): orbitMargin P m (Ortho.move a ∘ x) (Ortho.move a o) ↔ orbitMargin P m x o:=by
    unfold orbitMargin Dock; simp only [← Function.comp_assoc,show ∀ k:Ortho, Ortho.move k ∘ Ortho.move a=(Ortho.move (k*a)) from (fun k=>funext fun z=> (Ortho.move_mul k _ _).symm),← Ortho.move_mul]; constructor
    · intro h i hi k; rw [← div_mul_cancel k a]; exact h i hi _
    exact fun h i hi k=> h i hi (k*a)
include hX in
lemma average_rotation (a:Ortho) : averageV P X m (Ortho.move a ∘ x) (Ortho.move a o) (roll X a w)=X.act _ a (averageV P X m x o w):=by
    classical
    unfold averageV; simp_rw [move_margin m a]; split; swap; exact (map_zero _).symm
    let f:=fun k:Ortho=>spinning P X m (Ortho.move a ∘ x) (Ortho.move a o) k (roll X a w); let g:=fun k:Ortho=>spinning P X m x o k w
    have hf(k): f (a*k) = X.act m a (g k):=by
       have he:(a*k)⁻¹*a=k⁻¹ := by group
       have hz: Ortho.move (a*k)⁻¹ ∘ (Ortho.move a ∘ x)=Ortho.move k⁻¹ ∘ x:= funext fun i=>by simp only [comp_apply,← Ortho.move_mul,he]
       have ht:roll X (a*k)⁻¹ (roll X a w)=roll X k⁻¹ w := funext fun i=>by change X.act _ (a*k)⁻¹ (X.act _ a _)=_; rw [← hX.group,he]; rfl
       unfold f g spinning; rw [hz,ht,← Ortho.move_mul,he]; exact hX.group ..
    have ht:=measurePreserving_mul_left haar a
    have he:=ht.integral_comp (g:=f) (show MeasurableEmbedding (a * ·) from (Homeomorph.mulLeft a).measurableEmbedding)
    change (∫ k,f k ∂haar) = _; rw [← he]
    have hb := (X.act m a).toContinuousLinearEquiv.antilipschitz
    have hW:= (X.act m a).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm' (μ:=haar) hb g
    exact Eq.trans (integral_congr_ae (Eventually.of_forall hf)) hW
end YM.OPE.Orbits

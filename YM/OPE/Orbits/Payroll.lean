import YM.OPE.Orbits.Quotes

/-! Upper-rate controls for finite tensors with moving positions/label
components. Self-contained finite-dimensional consequences of OPE.Exchange
and Viewer estimates, leaving the nonperturbative numbers unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Set Filter Extraction MeasureTheory Table
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge} {S₀:Register G}{S:Table S₀}{I J L:Type}[Fintype I][Fintype J] {d:I→ ℕ}
    {A:L→ℝ}{φ:Filter L}{a b c u:ℝ}(hA:Tendsto A φ atTop)

include hA in
lemma pay_lin {V W:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][NormedAddCommGroup W][NormedSpace ℝ W]
      {F : L → V→L[ℝ] W}{x : L→V}(hF:RateLE φ A (fun i=>‖F i‖) a)(hx:RateLE φ A x b): RateLE φ A (fun i=>F i (x i)) (a+b) := ((hF.mul hx.norm).of_norm_le (Eventually.of_forall (fun _=> ContinuousLinearMap.le_opNorm ..)))
include hA in
lemma pay_fixed {V W:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V][NormedAddCommGroup W][NormedSpace ℝ W]
      (F:V→ₗ[ℝ]W){x:L→V}(hx:RateLE φ A x a): RateLE φ A (fun i=>F (x i)) a:=by
      have h:=(pay_lin (F:=fun _=>LinearMap.toContinuousLinearMap F) hA (RateLE.const _ hA) hx)
      rw [zero_add] at h; exact h


include hA in
lemma contract {V : I → Type}[∀i,NormedAddCommGroup (V i)][∀i,NormedSpace ℂ (V i)] [∀i,NormedSpace ℝ (V i)] [∀i,IsScalarTower ℝ ℂ (V i)] [∀i,FiniteDimensional ℂ (V i)] {W:Type}[NormedAddCommGroup W][NormedSpace ℂ W]
    (f:L→ MultilinearMap ℂ V W)(hf:∀ w, RateLE φ A (fun i=>(f i) w) a) (v:L→∀i,V i) (b:I→ℝ) (hb:∀ i:I, RateLE φ A (fun s=>v s i) (b i)) : RateLE φ A (fun i=> (f i) (v i)) (a+∑ i,b i):=by
    let E j:=Fin (Module.finrank ℂ (V j)); let e j : Module.Basis (E j) ℂ (V j) := Module.finBasis _ _
    let c (j:I)(k:E j): V j→ₗ[ℂ] ℂ:= (e j).coord k
    have he(i:L): f i (v i) = ∑ t:((j:I)→ E j), (∏ j, c j (t j) (v i j)) • f i (fun j=> e j (t j)) := by
       have hx:v i= fun j=>∑ k, c j k (v i j) • e j k:=funext fun _=> ((e _).sum_repr ..).symm
       conv_lhs=> rw [hx,MultilinearMap.map_sum_finset]; simp only [MultilinearMap.map_smul_univ]
       apply Finset.sum_congr (by ext; simp) fun _ _=>rfl
    letI (j:I): FiniteDimensional ℝ (V j) := Module.Finite.trans ℂ _
    simp_rw [he,add_comm a]; refine RateLE.sum hA fun t _=>?_ ; exact (RateLE.prod hA fun j _=>pay_fixed hA ((c j _).restrictScalars ℝ) (hb j)).smul (hf _)

variable {x:L→I→ E4}{y:L→J→E4}{o:L→ E4}
include hA in
lemma swings_kept {x':L→J→E4} (k:L→Ortho) (hk:Kept φ A c y)(hx:Intervals φ A b (centerless L) y)(hh:∀ j l,x' l j=o l+ Ortho.move (k l) (y l j)): Kept φ A c x' ∧ Intervals φ A b (fun l=>sole (o l)) x':=by
   have he(i j l): ‖x' l i-x' l j‖ = ‖y l i-y l j‖:=by rw [hh,hh,add_sub_add_left_eq_sub]; change ‖Ortho.motion _ _ - Ortho.motion _ _‖ = _; rw [← show Ortho.motion (k l) (y l i-y l j)= _ from map_sub ..]; exact LinearIsometryEquiv.norm_map ..
   have ht(i l): ‖o l - x' l i‖ = ‖(0:E4)-y l i‖:=by rw [hh,sub_add_cancel_left, zero_sub,norm_neg,norm_neg,Ortho.move_norm]
   exact ⟨fun u hu=>(hk u hu).mono (fun i hi p q e=> (hi p q e).trans_eq (he ..).symm), fun u hu=> (hx u hu).mono (fun i hi ⟨⟩ q=> (hi () q).trans_eq (ht ..).symm)⟩

end YM.OPE.Orbits

import YM.RG08.Wax.Balance
/-! # Join product evaluation measures, charge norm with cost 1.
Unital log cumulants in products of roots need no multimultiplication
operator estimate with same-slot repeated tags: only disjoint qualify.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Lattice Filter Set MeasureTheory MeasureTheory.Measure Scores CompactlySupported
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} [Fintype I] [DecidableEq I] {R : ℝ} {D : ℕ} {U V T : Finset I}

private def por (U : Finset I) (a b : Patch I D R) : Patch I D R:= ⟨xor a.1 b.1, fun i=> if i∈U then a.2 i else b.2 i⟩
private lemma por_c (U : Finset I): Continuous (uncurry (por (D:=D) (R:=R) U)) := by
  refine Continuous.prodMk ?_ (continuous_pi (fun i=>?_))
  · exact (continuous_of_discreteTopology (f:=fun p: Bool×Bool=> xor p.1 p.2)).comp (continuous_fst.fst.prodMk continuous_snd.fst)
  change Continuous fun x:Patch I D R × Patch I D R => if i∈ U then x.1.2 i else x.2.2 i; split_ifs <;> fun_prop
private lemma tray_power (A: Finset I)(a:I→Sight D R)(x : Patch I D R) : paid (speak A a) x=sign x.1* ∏ i∈A,(a i).val (x.2 i).1 (x.2 i).2:= by
  rw [reads,← Finset.prod_coe_sort A]
private lemma trayC (h:T=U∪V) (hp : Disjoint U V)(v:I→Sight D R)(a b:Patch I D R) : paid (speak T v) (por U a b)= paid (speak U v) a * paid (speak V v) b := by
  have hh : sign (por U a b).1=sign a.1*sign b.1 := by unfold por sign; cases a.1 <;> cases b.1 <;> norm_num
  have he (i) (hi:i∈U): (por U a b).2 i=a.2 i:= if_pos hi
  have hv (i) (hi:i∈V): (por U a b).2 i=b.2 i:= if_neg fun hz=>Finset.disjoint_left.mp hp hz hi
  rw [h,tray_power,tray_power,tray_power,Finset.prod_union hp, hh,mul_mul_mul_comm]; congr 2
  · exact Finset.prod_congr rfl (fun i hi=> by rw [he i hi])
  exact Finset.prod_congr rfl (fun i hi=> by rw [hv i hi])

lemma trades (A:Poise U D R)(B:Poise V D R)(he:T=U∪V)(hd:Disjoint U V)(hp:0≤R) : ∃ P: Poise T D R, ‖P‖≤‖A‖*‖B‖ ∧ ∀ a, P (speak T a)=A (speak U a)* B (speak V a) := by
  obtain ⟨μ,hμ,hY,H⟩:=buys A hp; obtain ⟨ν,hν,hW,Z⟩:=buys B hp; let f:= μ.prod ν
  let Q (x:Scouts T D R)(v:Patch I D R× Patch I D R):ℝ:= paid x (por U v.1 v.2)
  haveI : BorelSpace (Patch I D R × Patch I D R):= Prod.borelSpace (α:=Patch I D R) (β:=Patch I D R)
  haveI : IsFiniteMeasure f:= inferInstanceAs (IsFiniteMeasure (μ.prod ν))
  have hi x: Integrable (Q x) f:= ((paid_c x).comp (por_c U)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let l: Scouts T D R→ₗ[ℝ] ℝ := {
    toFun x:=∫ v,Q x v∂f
    map_add' x y:= by
       rw [← integral_add (hi x) (hi y)]
       apply integral_congr_ae; refine Eventually.of_forall fun z=> ?_
       change sign _*(x.val _+y.val _)=sign _*x.val _+sign _*y.val _; ring
    map_smul' c x:= by
       rw [show (RingHom.id ℝ) c=c from rfl, ← integral_smul]
       apply integral_congr_ae; refine Eventually.of_forall fun z=> ?_
       change sign _*(c*x.val _)=c*(sign _*x.val _); ring }
  have hl (x:Scouts T D R): ‖l x‖≤(‖A‖*‖B‖)*‖x‖ := by
    apply (norm_integral_le_of_norm_le (μ:=f) (f:=Q x) (integrable_const ‖x‖) (Eventually.of_forall fun z=> price x _)).trans_eq
    rw [integral_const]; unfold f; rw [show Measure.real (μ.prod ν) Set.univ=μ.real Set.univ*ν.real Set.univ from by rw [← Set.univ_prod_univ, measureReal_prod_prod],hY,hW,smul_eq_mul]
  refine ⟨_, LinearMap.mkContinuous_norm_le l (by positivity) hl,fun a=>?_⟩ -- f?
  change l _= _; change (∫ z,Q _ z ∂f)=_; rw [H,Z,← integral_prod_mul]; exact integral_congr_ae (Eventually.of_forall fun i=>trayC he hd a i.1 i.2)

def sale (A:Poise U D R)(B:Poise V D R)(T:Finset I) : Poise T D R:= if h:T=U∪V∧Disjoint U V ∧ 0≤R then (trades A B h.1 h.2.1 h.2.2).choose else 0
lemma sale_cost (A:Poise U D R)(B:Poise V D R)(T:Finset I): ‖sale A B T‖ ≤ ‖A‖*‖B‖ := by
    unfold sale; split; next h=>exact (trades A B h.1 h.2.1 h.2.2).choose_spec.1
    rw [norm_zero]; positivity
lemma sells (A:Poise U D R)(B:Poise V D R)(he:T=U∪V)(hp:Disjoint U V)(hx:0≤R)(a): sale A B T (speak T a)=A (speak U a)*B (speak V a):= by
   unfold sale; rw [dif_pos (show _ from ⟨he,hp,hx⟩)]; exact (trades A B he hp hx).choose_spec.2 a
end YM.RG08.Wax

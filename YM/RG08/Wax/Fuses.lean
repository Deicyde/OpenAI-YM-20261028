import YM.RG08.Wax.Laminate
import YM.RG08.Scores.PageFees
/-! # Address inflation with a bounded carrier. Derivatives held through D. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Wax
open Function Lattice Filter Set MeasureTheory MeasureTheory.Measure Scores CompactlySupported Pages
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} [Fintype I] [DecidableEq I] (T: Finset I)(D:ℕ){R w : ℝ}
-- simple slot polar
lemma spoke_eq {U:Finset I}{R:ℝ}{a b : I→Sight D R}(h:∀ i∈U,a i=b i) : speak U a=speak U b := by
   unfold speak; apply congr_arg; refine Subtype.ext (ContinuousMap.ext ?_); intro x; exact Finset.prod_congr rfl fun i _=> by rw [h (i.val) i.property]

variable (a : I → E4)(δ : I→ℝ) (h: ∀ i,Stays (a i) (δ i) R)
private def raceP (x:Zelt I D R): Zelt I D R:= fun i=> ⟨(x i).1,⟨a i+δ i • (x i).2.val,(h i).covers (x i).2.property⟩⟩
private lemma raceC : Continuous (raceP D a δ h) := by
   apply continuous_pi; intro i; apply Continuous.prodMk ((continuous_apply i).fst) (Continuous.subtype_mk ?_ _); fun_prop
private def candles (x:Zelt I D R):= ∏ i∈T, δ i^ ((x i).1.1.val)
private lemma candles_c : Continuous (candles T D (R:=R) δ) := by
   unfold candles; apply continuous_finsetProd; intro i hi
   exact (continuous_of_discreteTopology (f:=fun x:Sheet D=> δ i^x.1.val)).comp (continuous_apply i).fst
private def travelZ : C(Zelt I D R,ℝ) →ₗ[ℝ] C(Zelt I D R,ℝ) := {
    toFun A:= ⟨fun x=> candles T D δ x*A (raceP D a δ h x), (candles_c T D δ).mul (A.continuous.comp (raceC D a δ h))⟩
    map_add' p q:= ContinuousMap.ext fun x=> mul_add ..
    map_smul' c p := ContinuousMap.ext fun x=> mul_left_comm .. }
private lemma travel_live (x:I→Sight D R) : travelZ T D a δ h (profileP T x)= profileP T (fun i=> scroll (a i) (δ i) D (h i) (x i)) := by
   refine ContinuousMap.ext fun y=>?_
   have hl (z)(x:I→Sight D R): profileP T x z = ∏ i∈T,(x i).val (z i).1 (z i).2:= by change (∏ i:T, _) = ∏ _∈_,_; rw [← Finset.prod_coe_sort T]
   change (∏ _∈_, _)* profileP T x (raceP D a δ h y)=_
   simp_rw [hl]; rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl (fun i _=>?_)
   obtain ⟨u,hu⟩:= doors D R (x i); rw [← hu,(scroll_leaf ..).2]
   have he (t:Sheet D) (w:Scores.Close R) : δ i^t.1.val * mark D R u t ⟨a i+(δ i)•w.val,(h i).covers w.property⟩=mark D R (roll (a i) (δ i) u) t w := by
    obtain ⟨⟨j,hj⟩,b⟩:=t
    change δ i ^ j * iteratedFDeriv ℝ j u.val (a i + (δ i) • w.val) (basis ∘ b)=iteratedFDeriv ℝ j (roll (a i) (δ i) u).val w.val (basis ∘ b); rw [Pages.facades (h:=by omega)]; rfl
   exact he (y i).1 (y i).2
-- All T including empty
private lemma allowed (x:Scouts T D R): travelZ T D a δ h x.val ∈ Spun T D R := by
   let V:=Spun T D R
   let f:=travelZ T D a δ h
   have he : V ≤ V.comap f:= Submodule.span_le.mpr fun _ ⟨i,hx⟩=>hx ▸ (show f _∈ V from (travel_live T D a δ h i).symm ▸ Submodule.subset_span (Set.mem_range_self _))
   exact he (Scouts.tie T D R x).property
-- def avoiding coercion Diamonds
private def rose : Scouts T D R →ₗ[ℝ] Scouts T D R where
    toFun x:= (Scouts.tie T D R).symm ⟨travelZ T D a δ h x.val,allowed T D a δ h x⟩
    map_add' x y:= (Scouts.tie T D R).injective (Subtype.ext (map_add (travelZ T D a δ h) x.val y.val))
    map_smul' c x:= (Scouts.tie T D R).injective (Subtype.ext (map_smul (travelZ T D a δ h) c x.val))
private lemma lends (x: Scouts T D R): ‖rose T D a δ h x‖≤1*‖x‖ := by
   change ‖travelZ T D a δ h x.val‖≤ 1*‖x‖; refine (ContinuousMap.norm_le _ (by positivity)).mpr fun i=>?_
   apply (norm_mul _ _).trans_le (mul_le_mul ?_ (ContinuousMap.norm_coe_le_norm x.val (raceP D a δ h i)) (norm_nonneg _) zero_le_one)
   unfold candles; rw [norm_prod]; apply Finset.prod_le_one (fun i _=>norm_nonneg _) (fun i _=>?_); rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ((Real.norm_of_nonneg (h i).nonneg).trans_le (h i).short)
def mottle:= (rose T D a δ h).mkContinuous _ (lends T D a δ h)
lemma mote : ‖mottle T D a δ h‖ ≤ 1:= LinearMap.mkContinuous_norm_le _ zero_le_one _
lemma moto (X:I→ Sight D R): mottle T D a δ h (speak T X)=speak T (fun i=> Pages.scroll (a i) (δ i) D (h i) (X i)):= (Scouts.tie _ _ _).injective (Subtype.ext (travel_live T D a δ h X))
end YM.RG08.Wax

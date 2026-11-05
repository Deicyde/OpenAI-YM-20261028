import YM.PCalc.Loop

/-!
# Parameter-independent slice collar. True Haar!

Wiping on S then T maps the quotient bijectively (even for subsided
components). Gauge with block identity at every root, not ANY local gauge. Can
select other orientations separately. Local determinant equation after Leg only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Precision
open Filter Function Set Lattice RG Wilson Matrix Exterior Finset Tree MeasureTheory
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Pointwise
variable {c f : Side} {G : Gauge} {g : Ratio c f}

namespace Profiles

def wiped (F : Forest g) (U : Config G f) := Lattice.gauge (F.foldAt U) U

def wick (F : Forest g) (U : Config G f) : F.Slice G := fun i => wiped F U i

variable (F H : Forest g)

lemma wears (U : Config G f) : F.drape (wick F U)=wiped F U := by
  funext i; by_cases h : i∈F.trunks
  · exact (F.on_tree _ ⟨i,h⟩).trans (F.compress U i h).symm
  exact F.off_tree _ ⟨i,h⟩
lemma wick_root (U : F.Slice G) : wick F (F.drape U)=U := by
  have he i : F.foldAt (F.drape U) i=1 := by
    induction i using Forest.hike.induct F with
    | case1 i hi ih =>
      have hs : (F.up i).used i∈F.trunks := (F.trunk_mem_iff _).mpr ⟨_,hi,rfl⟩
      have hk := F.fold_step (F.drape U) hi; rw [ih,Step.read,show F.drape U ((F.up i).used i)=1 from F.on_tree _ ⟨_,hs⟩] at hk
      simpa only [inv_one,ite_self,mul_one] using hk
    | case2 i hi => rw [show i=g.embed (g.parent i) from Classical.not_not.mp hi, Forest.fold_root]
  ext1 i; simp only [wick,wiped,Lattice.gauge,he,F.off_tree,one_mul,inv_one,mul_one]

lemma wick_gauge (U : Config G f) (t : Site f→G.El) (h : ∀ x : Site c,t (g.embed x)=1) : wick F (Lattice.gauge t U)=wick F U := by
  have he i : F.foldAt (Lattice.gauge t U) i=F.foldAt U i*(t i)⁻¹ := by
    simp only [Forest.foldAt,travel_gauge,F.hike_root,h,inv_one,mul_one,_root_.mul_inv_rev]
  funext i; unfold wick wiped; rw [Lattice.gauge, Lattice.gauge]; simp_rw [he]; unfold Lattice.gauge; group
@[fun_prop] lemma continuous_wick : Continuous (wick F (G:=G)) := by
  apply continuous_pi; intro x; simp only [wick,wiped,Lattice.gauge]; fun_prop

lemma rehomes (U : F.Slice G) : wick F (H.drape (wick H (F.drape U)))=U := by
  rw [wears,wiped,wick_gauge F _ _ (fun x => H.fold_root _ _),wick_root]

def reroute (G : Gauge) : F.Slice G ≃ₜ H.Slice G where
  toFun x := wick H (F.drape x)
  invFun x := wick F (H.drape x)
  left_inv := rehomes F H
  right_inv := rehomes H F
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma spending (G : Gauge) : MeasurePreserving (reroute F H G) (F.order G) (H.order G) := by
  let W := reroute F H G
  refine ⟨W.continuous.measurable,?_⟩
  ext x hx
  rw [Measure.map_apply W.continuous.measurable hx]
  have he : MeasurableSet ((wick H) ⁻¹' x) := (continuous_wick H).measurable hx
  let Z := (x.indicator (fun _ => (1:ℝ))) ∘ (wick H)
  have ht : Integrable Z (prior G f) := by
    simpa only [Z, indicator_comp_right] using! ((integrable_const (1:ℝ)).indicator he : Integrable (((wick H) ⁻¹' x).indicator (fun _ => (1:ℝ))) (prior G f))
  have hw k hk u : Z (Lattice.gauge k u)=Z u := congr_arg (x.indicator _) (wick_gauge H u k hk)
  have hi := (F.pack Z ht hw).symm.trans (H.pack Z ht hw)
  have hc : MeasurableSet (W ⁻¹' x) := W.continuous.measurable hx
  have h1 : (fun y => Z (F.drape y))=(W ⁻¹' x).indicator (fun _ => (1:ℝ)) := by
    funext i
    change x.indicator _ (W i)=_
    by_cases hh : W i∈x <;> simp [hh]
  have h2 : (fun y => Z (H.drape y))=x.indicator fun _ => (1:ℝ) := by ext i; simp [Z,wick_root]
  rw [h1,h2,integral_indicator hc,integral_indicator hx,setIntegral_const,setIntegral_const] at hi
  change (F.order G) (W ⁻¹' x) = _
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  simpa only [smul_eq_mul,mul_one] using! hi
end Profiles
end YM.Precision

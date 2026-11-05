import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Fine

/-!
# Arrays of arguments: actual U and the uncut forecast

Work in Local hill gauge. Permit extra deterministic rotations of each
occasion, so can test in units of a supplied reference frame. See e.g.
Reoriented to tie gauges WHEN needed, we don't rotate the tags here. Keep the
three different laws distinct (the actual physical step's Gaussian price, first order
fluctuation on local window, canonical curl law on uncut metric).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546.Curved
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Rows Tree Bid
open UVNext.PricedKernels Extra.Iteration Extra.Iteration.Scales YM.AnalyticBridge.LocalGaussianLaws Current Lift Remote Local
open MeasureTheory SectorTools.PhysicalGaussianSwitch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

open FreeResolvent (treeInverse insertion ix flatten tensor)
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S}
  {I : Type} {F : Forest S.ratio} {x : ℝ}

variable (P : I → Occasion G f) (r : I → G.El)

def Looks (X : Support f) (l : ℕ) (x : ℝ) :=
    ∀ i : I, (P i).place ⊆ X ∧ (P i).link.length ≤ stride l x

/-- Common physical probes in units of g (not coupling reset). -/
def sampled (g : ℝ) (U : Config G f) : Gaussian.Vec I := fun i =>
  (G.adjoint (r i) (g⁻¹ • (P i).link.atSite U (P i).location)) (P i).color

def forecast (H L : Bed) (T : Tube G S) (g : ℝ) (V : Config G c) : Gaussian.Vec I := fun i =>
    (G.adjoint (r i) (g⁻¹ • flow S H L T (look V) (P i).coordFace)) (P i).color

def wind {W : Finset (Bond f)} (z : Gaussian.Vec (SlotsW A F x W G)) : Gaussian.Vec I := fun i =>
    (G.adjoint (r i) (sectionCurl z (P i).coordFace)) (P i).color

def analyze : Gaussian.Vec (FreeResolvent.Slot G f 2) →ₗ[ℝ] Gaussian.Vec I where
  toFun z i := (G.adjoint (r i) (WithLp.toLp 2 (fun k => z (ix (P i).coordFace k)))) (P i).color
  map_add' x y := funext fun i => by
    let Z := fun (x : Gaussian.Vec _) => WithLp.toLp 2 (fun k : G.ColorIndex => x (ix (P i).coordFace k))
    change G.adjoint (r i) (Z (x+y)) _ = G.adjoint (r i) (Z x) _ + G.adjoint (r i) (Z y) _
    rw [show Z (x+y)=Z x+Z y from rfl,map_add]; rfl
  map_smul' t x := funext fun i => by
    let Z := fun (x : Gaussian.Vec _) => WithLp.toLp 2 (fun k : G.ColorIndex => x (ix (P i).coordFace k))
    change G.adjoint (r i) (Z (t • x)) _ = t • (G.adjoint (r i) (Z x) _)
    rw [show Z (t • x)=t • Z x from rfl,map_smul]; rfl
lemma analyzed (x : Curvature G f) (i) : analyze P r (flatten x) i =
    G.adjoint (r i) (x (P i).coordFace) (P i).color := rfl

variable [Fintype I]

omit [Fintype I] in
lemma sampled_cont (g : ℝ) : Continuous (sampled P r g) := by
  unfold sampled; apply continuous_pi; intro i
  have h := (G.adjoint (r i)).continuous_of_finiteDimensional
  let L (U : Config G f) := (P i).link.atSite U (P i).location
  have hh : Continuous L := by unfold L Slot.atSite expandAt; fun_prop
  exact (PiLp.continuous_apply _ _ _).comp (h.comp (hh.const_smul (c:=g⁻¹)))

/-- True even off the guard. Does not transfer to arbitrary polynomial
local field before the other budgets are paid. -/
lemma sampled_bound {g : ℝ} (h : 0<g) (V : Config G f) : ‖sampled P r g V‖ ≤ 2/g := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i =>
    (color_component _ _).trans ?_
  rw [G.norm_adjoint,norm_smul,Real.norm_of_nonneg (by positivity),← div_eq_inv_mul]
  exact div_le_div_of_nonneg_right (Slot.eval_norm ..) h.le

lemma wind_cost {W : Finset (Bond f)} {X : Support f} {l x} {o : Site c} (hh : Clears A x o (radiusB x))
    (h : Looks P X l x) (hp : Covers X W) (hw : Reachable S o x W) (z : Gaussian.Vec (SlotsW A F x W G)) :
    ‖wind P r z‖ ≤ 4*((Fintype.card G.ColorIndex:ℝ)*‖z‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => (color_component _ _).trans ?_)
  rw [G.norm_adjoint]; exact inputsCurl (P i) z hh ((h i).1) hp hw

variable {P r}
open Gaussian

/-- Bounds on arrays on the very same guard. Looks carries true slots. -/
theorem Central.sighted (P : I → Occasion G f) (r : I → G.El) {t g x : ℝ} (hg : 0<g) (hx : 1≤x) (ht : 0<t)
    {T : Tube G S} {v : Dir G c} {H L : Bed} {o : Site c} {V : Config G c} {Y : LinkArray G (Frozen A x F)}
    {X : Support f} {W : Finset (Bond f)} {l : ℕ} (hP : Looks P X l x)
    {a Z : Vec (In x A F (G:=G))} (h : Central (o:=o) v V T H L a Z Y X W g t l) :
    let U := physical A F V Y (tape (a+g • Z))
    let m := forecast P r H L T g V; let B := sampled P r g U
    let z := wind P r (rebase T v a g W Z)
    ‖m‖ ≤ t/g ∧ ‖B‖ ≤ t/g ∧ ‖B - (m + z)‖ ≤ x^(-(1/8):ℝ) := by
  intro U m B z
  have hp : 0 ≤ t/g := div_nonneg ht.le hg.le
  have hf (b : G.Color) (j : I) (H : ‖b‖ ≤ t) : |G.adjoint (r j) (g⁻¹ • b) (P j).color| ≤ t/g := by
    apply (color_component ..).trans; rw [G.norm_adjoint, norm_smul,Real.norm_of_nonneg (by positivity),← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right H hg.le
  refine ⟨(pi_norm_le_iff_of_nonneg hp).mpr (fun i => hf _ i (((h.prediction _ (hP i).1 (hP i).2).1).trans (by linarith))),
    (pi_norm_le_iff_of_nonneg hp).mpr (fun i => hf _ i (h.prediction _ (hP i).1 (hP i).2).2.1),?_⟩
  have hX : 0<x := by linarith only [hx]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  obtain ⟨-, -, he⟩ := h.prediction (P i) (hP i).1 (hP i).2
  let A' := g⁻¹ • (P i).link.atSite U (P i).location
  let B' := g⁻¹ • flow S H L T (look V) (P i).coordFace
  let Z' := sectionCurl (rebase T v a g W Z) (P i).coordFace
  have heq : (B-(m+z)) i = G.adjoint (r i) (A'-(B'+Z')) (P i).color := by
    rw [map_sub,map_add]; rfl
  rw [heq]; exact (color_component _ _).trans ((G.norm_adjoint ..).trans_le he)



variable [DecidableEq I]
def analyzer (P : I → Occasion G f) (r : I → G.El) := LinearMap.toMatrix' (analyze P r)
def sky (P : I → Occasion G f) (r : I → G.El) (H L : Bed) (T : Tube G S) :=
    covView (analyzer P r) (tensor G (fConditional S H L T.R))

omit [Fintype I] [DecidableEq I] in
lemma read_wind (P : I → Occasion G f) (r : I → G.El) {W : Finset (Bond f)}
    (z : Gaussian.Vec (SlotsW A F x W G)) :
    wind P r z = (analyzer P r*Current.plane S F * insertion (loading A F x W G)) *ᵥ z := by
  rw [← mulVec_mulVec,← mulVec_mulVec,analyzer,LinearMap.toMatrix'_mulVec]
  rw [show plane S F *ᵥ (insertion (loading A F x W G) *ᵥ z) = flatten (sectionCurl z) from
    (authentic (S:=S) (plantW S z)).symm]; rfl
omit [Fintype I] [DecidableEq I] in
lemma wind_section (P : I → Occasion G f) (r : I → G.El) {W : Finset (Bond f)} {X : Support f}
    {l x} {o : Site c} (hx : Clears A x o (radiusB x)) (h : Looks P X l x)
    (hp : Covers X W) (hu : Reachable S o x W) (z : Vec (FreeResolvent.Active G F)) :
    wind P r (z ∘ loading A F x W G)=view (analyzer P r * Current.plane S F) z := by
  rw [view,← mulVec_mulVec,analyzer,LinearMap.toMatrix'_mulVec,← authentic (S:=S) z]
  funext i
  let p := (P i).face
  rw [analyzed]; unfold wind
  rw [show sectionCurl (z ∘ loading A F x W G) (P i).coordFace=liftedCurl (S:=S) z (P i).coordFace from
    reads_curl (W:=W) z p hx (hp.flags p ⟨_,(h i).1 (P i).face_mem, Work.E01.base_touched _⟩) hu]


end YM.PhysicalNext.PhysicalGuard7f546.Curved

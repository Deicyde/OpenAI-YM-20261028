import YM.Next.FOUNDATIONS.LinkBounds
import YM.Push.FREE_RESOLVENT.Gap
import YM.Work.B04
import YM.Work.E02
import YM.Work.F01




/-!
# The periodic free block precision in the tree used by the RG step

`fullMatrix`: K + κ Qrᵗ Qr, expanded in orthonormal `G.Color`
coordinates (literal counting, no volume normalization, no extra Frobenius
price factor). `Qr` = actual rooted `Precision.probe`. Sides on the given
periods, in particular include response to harmonic arguments. See
`YM.Push.predictor` for the derivation from the predictor (Branches input).

`treeMatrix`: precision on the tree slice with roots pinned in every
block. Exact vertical Hessian of the unmasked stationary calculation when
using the matched path data; expressed here conditional on `Prismatic` and
`Comptroller` (F03 produces them upon path inputs, *not* estimates on the
inverse). Only gap & width of the **forward** two-form metric are needed
for our inverse calculation; none of that path data or advanced Towers needed
there! In particular don't consume inverse fields of Rack in the estimate.

Use same counting conventions for arbitrary forests (even no translation
symmetry). `r` spectral parameter in Gap is positive in applications;
notation `u` for the additive shift for principal compressions later.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {n c f : Side} {S : StepData c f} {G : Gauge} {r s : ℕ}

/-- PAC = site, direction, color. No multiplicities omitted. -/
abbrev PAC (G : Gauge) (r : ℕ) := TypeFace r × G.ColorIndex
abbrev Slot (G : Gauge) (n : Side) (r : ℕ) := Co n (PAC G r)
abbrev Vec (G : Gauge) (n : Side) (r : ℕ) := Slot G n r → ℝ

/-- Pin a basis coordinate over a Body. -/
def ix (b : Body r n) (i : G.ColorIndex) : Slot G n r := (b.1,b.2,i)
def component (u : Vec G n r) (i : G.ColorIndex) (b : Body r n) : ℝ := u (ix b i)

def flatten (x : fieldDir G n r) : Vec G n r := fun i => x (i.1,i.2.1) i.2.2
lemma component_flat (x : fieldDir G n r) (i : G.ColorIndex) : component (flatten x) i = parts G r x i := rfl

/-- dots in color, not on unscaled matrices. -/
lemma color_dot (x y : G.Color) : dotProduct x.ofLp y.ofLp = inner ℝ x y := by
  rw [PiLp.inner_apply]
  unfold dotProduct; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma component_dot (u v : Vec G n r) : dotProduct u v = ∑ i : G.ColorIndex, dotProduct (component u i) (component v i) := by
  unfold dotProduct
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm (f:=fun (i : G.ColorIndex) (x : Site n) => ∑ j : TypeFace r, component u i (x,j)*component v i (x,j))]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_comm

lemma flat_dot (x y : fieldDir G n r) : dotProduct (flatten x) (flatten y) = ∑ i, inner ℝ (x i) (y i) := by
  rw [component_dot]; unfold dotProduct
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => ?_
  exact color_dot (G:=G) (x i) (y i)

/-- Promote the scalar matrix without reindex assumptions. -/
def tensor (G : Gauge) (A : Matrix (Body r n) (Body s f) ℝ) : Matrix (Slot G n r) (Slot G f s) ℝ :=
  of fun i j => if i.2.2=j.2.2 then A (i.1,i.2.1) (j.1,j.2.1) else 0

lemma component_mul (A : Matrix (Body r n) (Body s f) ℝ) (u : Vec G f s) (i : G.ColorIndex) :
    component (tensor G A *ᵥ u) i = A *ᵥ component u i := by
  funext b
  simp only [component,mulVec,dotProduct,tensor,ix,of_apply]
  simp_rw [Fintype.sum_prod_type]; simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,if_true]

lemma tensor_transpose (G : Gauge) (A : Matrix (Body r n) (Body s f) ℝ) : (tensor G A).transpose = tensor G A.transpose := by
  ext i j; simp [tensor,eq_comm]

abbrev FaceRow := Row (TypeFace 2) (TypeFace 2)
def baseMatrix (S : StepData c f) (H : FaceRow) :=
  Precision.K (H.acts f) + S.kernel.penalty • ((probe S).transpose * probe S)
def fullMatrix (G : Gauge) (S : StepData c f) (H : FaceRow) := tensor G (baseMatrix S H)

/-- cost still independent of tree. -/
def curlCharge (H : FaceRow) (x y : Dir G f) :=
  ∑ i : G.ColorIndex, dotProduct (parts G 1 x i) (Precision.K (H.acts f) *ᵥ parts G 1 y i)

lemma fiscal_eq (S : StepData c f) (H : FaceRow) (x y : Dir G f) :
    dotProduct (flatten x) (fullMatrix G S H *ᵥ flatten y) =
      curlCharge H x y + S.kernel.penalty * ∑ b, inner ℝ (bills S x b) (bills S y b) := by
  rw [← flat_dot, component_dot, component_dot, curlCharge, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [fullMatrix, component_mul, baseMatrix, component_flat]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    ← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec]
  congr 2
  exact dotProduct_comm _ _

lemma fiscal_gap (S : StepData c f) (H : FaceRow) (x : Dir G f) {a : ℝ} (ha : Gap (H.acts f) a) :
    a * (∑ b, ‖dColor G f 1 x b‖^2) + S.kernel.penalty * (∑ b, ‖bills S x b‖^2) ≤
      dotProduct (flatten x) (fullMatrix G S H *ᵥ flatten x) := by
  rw [fiscal_eq]
  simp_rw [← real_inner_self_eq_norm_sq, ← flat_dot, component_dot,component_flat, Finset.mul_sum,add_le_add_iff_right]
  apply Finset.sum_le_sum
  intro i _
  rw [Precision.K, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm ((H.acts f) *ᵥ _)]
  exact ha.lower (d 1 f *ᵥ parts G 1 x i)

section tree
-- S parameter infer? avoid reconstruct StepData via projection via specifying (S := ...)
variable {g : Ratio c f}

/-- match the actual free coordinates of the slice -/
abbrev Active (G : Gauge) (T : Forest g) := T.Free × G.ColorIndex

def plant (T : Forest g) : Active G T → Slot G f 1 := fun j => ix (j.1.val.1, coord j.1.val.2) j.2
lemma plant_inj (T : Forest g) : Function.Injective (plant T (G := G)) := by
  rintro ⟨x,i⟩ ⟨y,j⟩ he
  simp only [plant,ix,Prod.mk.injEq,coord_iff] at he
  exact Prod.ext (Subtype.ext (Prod.ext he.1 he.2.1)) he.2.2

/-- on independent free bond coordinates. -/
def treeMatrix (G : Gauge) (S : StepData c f) (T : Forest S.ratio) (H : FaceRow) :=
  (fullMatrix G S H).submatrix (plant T) (plant T)

def active (T : Forest g) (v : AxisChart G T) : Active G T → ℝ := fun i => v i.1 i.2
def profile (T : Forest g) (v : Active G T → ℝ) : AxisChart G T := fun i => WithLp.toLp 2 (fun j => v (i,j))
lemma active_profile (T : Forest g) (v : Active G T → ℝ) : active T (profile T v) = v := rfl


lemma active_dot (T : Forest g) (x y : AxisChart G T) :
    dotProduct (active T x) (active T y) = ∑ i, inner ℝ (x i) (y i) := by
  unfold dotProduct active; rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_; exact color_dot (G:=G) (x i) (y i)


lemma chart_flow (S : StepData c f) (T : Forest S.ratio) (x : AxisChart G T) :
    insertion (plant T) *ᵥ active T x = flatten (stretch (S:=S) T (0,x)) := by
  funext i
  rcases i with ⟨u,a,k⟩
  obtain ⟨b,hb⟩ := axisEquiv.surjective a
  rw [coord_map] at hb; subst a
  let e : Pressure.Bond f := (u,b)
  have hh := Work.F01.collect_vertical T x e (S:=S)
  change _ = collect G (stretch (S:=S) T (0,x)) e k
  rw [hh]
  split <;> rename_i H
  · refine Finset.sum_eq_zero fun j _ => ?_
    change (if plant T j = (u,coord b,k) then 1 else 0) * _ = 0
    rw [if_neg, zero_mul]; intro he
    apply j.1.property
    rw [show j.1.val=e from
      Prod.ext (congr_arg (fun i : Slot G f 1 => i.1) he) ((coord_iff ..).mp (congr_arg (fun j : Slot G f 1 => j.2.1) he))]
    exact H
  let t : Active G T := (⟨e,H⟩,k)
  change (insertion (plant T)*ᵥ active T x) (plant T t) = active T x t
  simp [mulVec,dotProduct,insertion,(plant_inj T).eq_iff]

lemma tree_qf (S : StepData c f) (T : Forest S.ratio) (H : FaceRow) (x y : AxisChart G T) :
    dotProduct (active T x) (treeMatrix G S T H *ᵥ active T y) =
      dotProduct (flatten (stretch T (0,x))) (fullMatrix G S H *ᵥ flatten (stretch T (0,y))) := by
  rw [treeMatrix,← insertion.dot_compress,chart_flow,chart_flow]

/-- Vertical Fréchet Hessian in *distinct* counting directions (conditional
path match). No volume scalars from passing through a normed-space Hessian.
Proof uses actual foundational jet calculus, so only need analytic germ. -/
lemma tree_hessian (S : StepData c f) (T : Forest S.ratio) (B : Bed) (k : S.Choices)
    (p : Clip) (W : PathData G) (hf : Prismatic T p W) (hc : Comptroller T B p W)
    (x y : AxisChart G T) :
    iteratedFDeriv ℝ 2 (tested T k p W 0) 0 ![x,y] = dotProduct (active T x) (treeMatrix G S T B.metric *ᵥ active T y) := by
  let F := Function.uncurry (tested T k p W)
  let L := ContinuousLinearMap.inr ℝ (Dir G c) (AxisChart G T)
  change iteratedFDeriv ℝ 2 (F ∘ L) 0 _ = _
  rw [Next.Foundations.jets_linear L (f:=F) ((hf k).of_le le_top), ContinuousMultilinearMap.compContinuousLinearMap_apply,
      tree_qf, fiscal_eq]
  have hy : iteratedFDeriv ℝ 2 F 0 (fun i : Fin 2 => L (![x,y] i)) =
      iteratedFDeriv ℝ 2 F 0 ![(0,x),(0,y)] := by congr 1; funext i; fin_cases i <;> rfl
  rw [show _ = _ from hy]; unfold F
  rw [(hc k).2.2]
  simp only [crop,gaugeFiscal,curlCharge,zero_sub,Pi.neg_apply,inner_neg_neg]

end tree

/-- Fixed-L test calibration in the normalization of F01, using only E02
(no path-data or inverse assumptions). Thresholds independent of period. -/
def macroCost (G : Gauge) (L : Side) (j : ℕ) (K : KernelChoices) := (Work.E02.answer G L j K).choose

def treeFare (G : Gauge) (P : Patch) (K : KernelChoices) (a : ℝ) :=
  let β := Work.F01.curlFactor P.L (box (Pressure.macroR P)) (macroCost G P.L P.J K)
  let γ := Work.F01.probeFactor P.L
  min a K.penalty / (1+β+γ)
lemma treeFare_pos (G : Gauge) (P : Patch) (K : KernelChoices) {a : ℝ} (ha : 0 < a) :
    0 < treeFare G P K a := by
  apply div_pos (lt_min ha K.penalty_pos)
  unfold Work.F01.curlFactor Work.F01.probeFactor; positivity

lemma tree_gap (S : StepData c f) (T : Forest S.ratio) (H : FaceRow) (hS : Larger (G:=G) S)
    {a : ℝ} (ha : 0 < a) (hg : Gap (H.acts f) a) : Gap (treeMatrix G S T H) (treeFare G S.patch S.kernel a) := by
  let K := S.kernel
  let C := macroCost G S.patch.L S.patch.J S.kernel
  obtain ⟨hC,e⟩ := (Work.E02.answer G S.patch.L S.patch.J S.kernel).choose_spec
  let β := Work.F01.curlFactor S.patch.L (box (Pressure.macroR S.patch)) C
  let γ := Work.F01.probeFactor S.patch.L
  have hβ : 0 ≤ β := by unfold β Work.F01.curlFactor; positivity
  have hγ : 0 ≤ γ := by unfold γ Work.F01.probeFactor; positivity
  let r := treeFare G S.patch K a
  have hr : 0 < r := treeFare_pos _ _ _ ha
  have he : r*(1+β+γ)=min a K.penalty := div_mul_cancel₀ _ (by positivity)
  have h1 : r*β ≤ a := ((mul_le_mul_of_nonneg_left (show β ≤ 1+β+γ by linarith) hr.le).trans_eq he).trans (min_le_left ..)
  have h2 : r*γ ≤ K.penalty := ((mul_le_mul_of_nonneg_left (show γ ≤ 1+β+γ by linarith) hr.le).trans_eq he).trans (min_le_right ..)
  constructor; intro v
  let x := stretch (S:=S) T (0,profile T v)
  have ht : ∀ i ∈ T.trunks, collect G x i = 0 := fun i h => (Work.F01.collect_vertical T (profile T v) i (S:=S)).trans (dif_pos h)
  let k := Classical.arbitrary S.Choices
  have hp := fun i => Work.F01.link_bound S hS.1 T k x ht C hC.le i fun U hu hw =>
    e _ _ S rfl rfl rfl hS.2.1 hS.2.2 T U hu 1 i k hw
  let D := ∑ b, ‖dColor G f 1 x b‖^2
  let Q := ∑ b, ‖bills S x b‖^2
  have hd : 0 ≤ D := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq : 0 ≤ Q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hh : dotProduct v v ≤ β*D + γ*Q := calc
    _ = ∑ i, ‖profile T v i‖^2 := by
      simpa only [active_profile, real_inner_self_eq_norm_sq] using active_dot T (profile T v) (profile T v)
    _ ≤ ∑ i, ‖collect G x i‖^2 := by
      have he (i : T.Free) : collect G x i.val = profile T v i := (Work.F01.collect_vertical (S:=S) T (profile T v) i.val).trans (dif_neg i.property)
      simp_rw [← he]; exact Cost.sum_comp_le (f:=fun i : T.Free => i.val) Subtype.val_injective (fun i => ‖collect G x i‖^2) fun _ => sq_nonneg _
    _ ≤ _ := Work.F01.sum_estimate S.ratio _ (fun b => ‖dColor G f 1 x b‖) (fun b => ‖bills S x b‖)
      (fun i => ‖collect G x i‖) C (fun i => norm_nonneg _) hp
  apply (mul_le_mul_of_nonneg_left hh hr.le).trans
  calc
    _ ≤ a*D + S.kernel.penalty*Q := by
      rw [mul_add, ← mul_assoc, ← mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_right h1 hd) (mul_le_mul_of_nonneg_right h2 hq)
    _ ≤ dotProduct (flatten x) (fullMatrix G S H *ᵥ flatten x) := fiscal_gap S H x hg
    _ = _ := (tree_qf S T H (profile T v) (profile T v)).symm
end YM.FreeResolvent

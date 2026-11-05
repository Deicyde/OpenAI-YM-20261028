import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Price

/-!
# On the committed cloud

Keep true hypotheses on real argument functions (unprofiled nonlinear
logarithms are not default functions here). Generic quantitative theorem, also
using only the genuine submoments at the chosen markers. One source engine,
occurrences may share some or every coordinate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC.Common
open MeasureTheory ProbabilityTheory Function Filter Finset Marker
open YM.Multi.Vacuum.Gauss Probe Moment Expansion Price Fused  Connector Charge
open YM.Next.SectorChange YM.Extra.Trajectories Grove Lattice
open Schur Wisps Gaussian
open scoped Topology BigOperators MatrixOrder
variable {V I : Type} [DecidableEq V] [DecidableEq I] [Fintype I]
variable {R : Census V} (C : Gaussian.Table I) (v : Probes V I)

def cable : GCC.Rows V I I := fun _ => ((CFC.sqrt (A:=Gaussian.Table I) C):Gaussian.Table I)
lemma paid_one : MeasurePreserving (mapRows ((CFC.sqrt (A:=Gaussian.Table I) C):Gaussian.Table I)) (standard I) (cloud C) :=
    ⟨(map_cont _).measurable, paid C⟩

omit [DecidableEq V] in
lemma price_eq (h : C.PosSemidef) (i j : V) : gram (cable C) i j=C := by
  have he : (CFC.sqrt C).transpose=CFC.sqrt C := Matrix.isHermitian_iff_isSymm.mp (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)).isHermitian
  ext a b; unfold gram crossed; rw [Matrix.of_apply]
  change ∑ k,CFC.sqrt C a k * CFC.sqrt C b k=C a b
  have hm : CFC.sqrt C * (CFC.sqrt C).transpose=C := by rw [he]; exact CFC.sqrt_mul_sqrt_self _ h.nonneg
  exact congr_fun (congr_fun hm a) b
omit [DecidableEq V] in
lemma common_due (h : C.PosSemidef) (s : Finset V) (w : V → Row I) :
    due s (cable C) w = ∑ i∈s,∑ a,w i a*C a a := by
  refine sum_congr rfl fun i _ => sum_congr rfl fun a _ => ?_
  rw [← crossed_self]
  exact congr_arg (w i a * ·) (congr_fun (congr_fun (price_eq C h i i) a) a)






/-- Coupled envelope budget. Pay moderate growth over the ENTIRE selection
including at sites of many-valence. This is sufficient, not an input on an
interacting conditional expectation. -/
def pool (T : Finset V) (q : Gaussian.Table I) (w : V → Row I) :=
    (∀ i∈T, ∀ a,0≤ w i a) ∧ ∀ a,∑ b,(∑ i∈T,w i b)* |q a b| ≤ 1/8

omit [DecidableEq V] in
lemma pool_enough (h : C.PosSemidef) {T : Finset V} {w} (hv : pool T C w) : base (cable C) T w := by
  apply base.of hv.1; intro i hi a
  have he (j : V) (b : I) : crossed (cable C i a) (cable C j b)=C a b :=
    congr_fun (congr_fun (price_eq C h i j) a) b
  simp_rw [he]; rw [sum_comm]; simp_rw [← sum_mul]; exact hv.2 a

omit [DecidableEq V] in
lemma capital (h : C.PosSemidef) {n : Side} (p : I → Site n) {σ K : ℝ} (hσ : 0≤σ) (hl : Pours C p p σ K)
    (T : Finset V) : Bank T (cable C) p σ K := ⟨hσ,hl.pos,fun i hi j hj => by rw [price_eq C h]; exact hl⟩

omit [DecidableEq V] [DecidableEq I] in
lemma scaled (K : ℝ) {T : Finset V} {w : V → Row I}
    (hk : 0≤K) (he : ∀ a, ∑ b,|C a b| ≤ K)
    (h : ∀ i∈T,∀ a,0 ≤ w i a) (ht : ∀ a, ∑ i∈T,w i a ≤ (8*(1+K))⁻¹) : pool T C w := by
  refine ⟨h,fun a => ?_⟩
  let M := (8*(1+K))⁻¹
  have hh : 0 ≤ M := by unfold M; positivity
  calc
    _ ≤ ∑ b,M*|C a b| := sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (ht b) (abs_nonneg _)
    _ ≤ M*K := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (he a) hh
    _ ≤ _ := by unfold M; rw [inv_mul_eq_div,div_le_iff₀ (by positivity)]; linarith

variable [Fintype V]




end YM.Primitives.GCC.Common

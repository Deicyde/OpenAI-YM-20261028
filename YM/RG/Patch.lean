import YM.Lattice.Box
import YM.Lattice.Scale
import YM.Wilson.Law

/-!
Kernel frame and finite tags on a patch.

`mass` is relative to finite **counting** measure in this presentation.

Existence of a common branch cutoff for which minimizing branches have UNIQUE
minimizers and fallback is nonempty is a proof obligation, not assumed
of any Gauge.

In these uses the classical choices on minimizing branches
select those actual points.

Frames in neighboring patches use ONE choice per
physical coarse-site.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG

open Lattice Wilson
open scoped Topology Matrix.Norms.Frobenius

/-- One shape, used also in pre-block-ratio analytic contracts. -/
structure Patch where
  L : Side
  J : ℕ
  order_cut : 4 ≤ J
  coarse : 3 ≤ L.val
  odd_side : Odd L.val

/-- Chosen once. No sampling/measurability is implicit in these choices. -/
structure KernelChoices where
  penalty : ℝ
  frame_cut : ℝ
  predictor_cut : ℝ
  axial_factor : ℝ
  penalty_pos : 0 < penalty
  frame_cut_pos : 0 < frame_cut
  predictor_cut_pos : 0 < predictor_cut
  axial_factor_pos : 0 < axial_factor

namespace Patch
variable (P : Patch) {G : Gauge}

/-- rounded up: side `(2J+6)L+1`. -/
def radius := (P.J + 3) * P.L.val

def sites := box P.radius
abbrev Points := ↥P.sites
abbrev Small := ↥(box (P.L.val/2))

def center : P.Points := ⟨0,center_box _⟩
instance : Nonempty P.Points := ⟨P.center⟩
instance : Nonempty P.Small := ⟨⟨0,center_box _⟩⟩

abbrev Rolls := Fin P.J → P.Small

theorem roll_sites (z : P.Rolls) : ∑ i, (z i).val ∈ P.sites := by
  have hs (i : Fin P.J) : (z i).val ∈ box (P.L.val / 2) := (z i).property
  have hr : P.J * (P.L.val / 2) ≤ P.radius := Nat.mul_le_mul (by omega) (Nat.div_le_self ..)
  unfold sites
  rw [box_test]
  constructor
  · intro i
    rw [Finset.sum_apply]
    calc
      _ ≤ -((P.J * (P.L.val/2) : ℕ) : ℤ) := by exact neg_le_neg (by exact_mod_cast hr)
      _ = ∑ _ : Fin P.J, -((P.L.val/2 : ℕ) : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ ↦ ((box_test.mp (hs j)).1 i)
  · intro i
    rw [Finset.sum_apply]
    calc
      _ ≤ ∑ _ : Fin P.J, ((P.L.val/2 : ℕ) : ℤ) :=
        Finset.sum_le_sum fun j _ ↦ ((box_test.mp (hs j)).2 i)
      _ = ((P.J * (P.L.val/2) : ℕ) : ℤ) := by simp
      _ ≤ _ := by exact_mod_cast hr

def addRoll (z : P.Rolls) : P.Points := ⟨_, P.roll_sites z⟩

/-- J-fold convolution of the uniform weight on one centered fine L-block.
Domain is patch at scale L. -/
def weight (x : P.Points) : ℝ :=
  ∑ i : P.Rolls, if P.addRoll i = x then (Fintype.card P.Rolls : ℝ)⁻¹ else 0

theorem weight_sum : ∑ x, P.weight x = 1 := by
  have he : 0 < (Fintype.card P.Rolls : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold weight; rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ he.ne']

theorem weight_nonneg (x : P.Points) : 0 ≤ P.weight x := by
  apply Finset.sum_nonneg; intro _ _; split <;> positivity

abbrev Frame (G : Gauge) := P.Points → G.El
abbrev FrameTag := P.Points × Lattice.Order

def axial (U : CoverConfig G) (r : P.FrameTag) (x : P.Points) :=
  travel U r.1.val (route r.1.val x.val r.2)

def via (h : P.Frame G) (U : CoverConfig G) (x y : P.Points) (l : Lattice.Order) :=
  h x * travel U x.val (route x.val y.val l) * (h y)⁻¹

/-- open branch. -/
def usesMin (C : KernelChoices) (U : CoverConfig G) : Prop :=
  ∀ l k x y, G.chord (P.via (P.axial U (P.center,l)) U x y k) < C.frame_cut

def average {n : Type*} [Fintype n] (f : n → ℝ) : ℝ := (Fintype.card n : ℝ)⁻¹ * ∑ i, f i

def score (U : CoverConfig G) (h : P.Frame G) : ℝ :=
  average fun x => average fun y => average fun l => G.price (P.via h U x y l)

@[fun_prop] theorem score_cont : Continuous fun v : CoverConfig G × P.Frame G => P.score v.1 v.2 := by
  unfold score average via; fun_prop

 
def minimizing (U : CoverConfig G) (h : P.Frame G) :=
  h P.center = 1 ∧ ∀ h' : P.Frame G, h' P.center = 1 → P.score U h ≤ P.score U h'

theorem min_exists (U : CoverConfig G) : ∃ h : P.Frame G, P.minimizing U h := by
  have hs : Nonempty P.Points := inferInstance
  have he : IsClosed { h : P.Frame G | h P.center = 1 } := isClosed_eq (continuous_apply _) continuous_const
  exact he.isCompact.exists_isMinOn ⟨1, rfl⟩ ((P.score_cont.comp (continuous_const.prodMk continuous_id)).continuousOn)

def selected (U : CoverConfig G) : P.Frame G := (P.min_exists U).choose

def facesum (U : CoverConfig G) : ℝ :=
  ∑ x : P.Points, ∑ p : PlaqAxes,
    if (∀ y ∈ visits x.val (square p.val.1 p.val.2), y ∈ P.sites)
    then G.chord (faceValue U (x.val,p)) else 0

/-- Sum over internal positive links. -/
def axialCost (U : CoverConfig G) (t : P.FrameTag) :=
  ∑ x : P.Points, ∑ i : Axis,
    if h : x.val + step i ∈ P.sites then
      G.chord (P.axial U t x * U (x.val,i) * (P.axial U t ⟨x.val + step i,h⟩)⁻¹)
    else 0

def eligible (C : KernelChoices) (U : CoverConfig G) : Finset P.FrameTag := by
  classical
  exact Finset.univ.filter fun t =>
    P.axialCost U t ≤ C.axial_factor * (2*P.radius+1) * P.facesum U

def frameMass (C : KernelChoices) (U : CoverConfig G) (t : P.FrameTag) : ℝ := by
  classical
  exact if P.usesMin C U then (Fintype.card P.FrameTag : ℝ)⁻¹ else
    if t ∈ P.eligible C U then ((P.eligible C U).card : ℝ)⁻¹ else 0

def frame (C : KernelChoices) (U : CoverConfig G) (t : P.FrameTag) : P.Frame G := by
  classical
  exact if P.usesMin C U then P.selected U else fun x => (P.axial U t P.center)⁻¹ * P.axial U t x

abbrev Connector (G : Gauge) := P.Points → G.El

def bondCost (Y : P.Connector G) (u : G.El) : ℝ := ∑ x, P.weight x * G.price (Y x * u⁻¹)

@[fun_prop] theorem bondCost_cont : Continuous fun v : P.Connector G × G.El => P.bondCost v.1 v.2 := by
  unfold bondCost; fun_prop

theorem bond_min (Y : P.Connector G) : ∃ u, ∀ v, P.bondCost Y u ≤ P.bondCost Y v := by
  have h : Continuous fun u => P.bondCost Y u := by fun_prop
  obtain ⟨u,-,hu⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty h.continuousOn
  exact ⟨u, fun v => hu (Set.mem_univ v)⟩

def best (Y : P.Connector G) := (P.bond_min Y).choose

def usesBest (C : KernelChoices) (Y : P.Connector G) : Prop := P.bondCost Y (P.best Y) < C.predictor_cut

def predict (C : KernelChoices) (Y : P.Connector G) (r : P.Points) : G.El := by
  classical
  exact if P.usesBest C Y then P.best Y else Y r

def predictorMass (C : KernelChoices) (Y : P.Connector G) (r : P.Points) : ℝ := by
  classical
  exact if P.usesBest C Y then (Fintype.card P.Points : ℝ)⁻¹ else P.weight r

/-- These hypotheses need proofs for this patch/kernel. -/
structure Branches (C : KernelChoices) (G : Gauge) : Prop where
  frame_unique : ∀ U : CoverConfig G, P.usesMin C U → ∃! h, P.minimizing U h
  predictor_unique : ∀ Y : P.Connector G, P.usesBest C Y → ∃! u, ∀ v, P.bondCost Y u ≤ P.bondCost Y v
  axial_exists : ∀ U : CoverConfig G, (P.eligible C U).Nonempty
end Patch
end YM.RG

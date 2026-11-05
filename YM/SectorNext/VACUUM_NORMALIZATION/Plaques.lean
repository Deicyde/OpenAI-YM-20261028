import YM.SectorNext.VACUUM_NORMALIZATION.Scheme
import YM.SectorNext.VACUUM_NORMALIZATION.Station


/-!
# Strict positivity for cut no-hole flat D stacked bills

Sufficient shape: *contains* the compulsory direct plaquette and
noise tangent rows on the real keys, with given positive coefficients;
other rows (e.g., cut transported inputs, all other symmetry channels)
can be arbitrary and ALL are included. Uses the actual PriceGap and
Comptroller (no assumptions on the determinant of this stack or thermal
at nonstationary points). Can change/eliminate identity-completed
coordinates via `identity_price` in subsequent file, retain tree/gauge.
No control here on a genuinely holey/frozen matrix – needs Sector inputs,
esp. analytic/log neighborhoods of actual affine rules.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum.FlatTree
open Lattice Tree RG Wilson Precision Matrix Filter Function Exterior Bloch Bid
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical ContDiff
variable {c f : Side} (S : StepData c f) (F : Forest S.ratio) {X : Type*} {G : Gauge}

/-- Color column of the physically stretched fine field in the chart
with **zero coarse input**: exactly the counting vector with tree links
zeroed. -/
def leg (x : Key F G → ℝ) (i : G.ColorIndex) : form 1 f := fun j => blank F (fun a => x (a,i)) ((wheel f).symm j)

lemma slots (x : Key F G → ℝ) (i : G.ColorIndex) : leg S F x i=parts G 1 (stretch (S:=S) F (0,keys F x)) i := by
  funext ⟨j,k⟩; obtain ⟨l,rfl⟩ := axisEquiv.surjective k
  rw [leg,parts,stretch]; rw [show axisEquiv.symm (axisEquiv l)=l from axisEquiv.symm_apply_apply _,show (wheel f).symm (j,axisEquiv l)=(j,l) from (wheel f).symm_apply_apply (j,l)]
  have h y : linearCopy S.ratio (collect G 0) y=0 := by unfold linearCopy collect; split <;> rfl
  rw [h,zero_add,blank]
  split <;> simp [keys_at]

lemma lines (D : Matrix X (Body 1 f) ℝ) (x : Key F G → ℝ) (k : X) (i : G.ColorIndex) :
    (slips F (lined G.ColorIndex D) *ᵥ x) (k,i)=(D *ᵥ leg S F x i) k := by
  rw [slip_price]
  unfold mulVec dotProduct; rw [Fintype.sum_prod_type,← Equiv.sum_comp (wheel f) (fun j : Body 1 f=> D k j*_) ]; apply Finset.sum_congr rfl; intro j _
  unfold lined; simp only [Matrix.of_apply,ite_mul,zero_mul]
  rw [Finset.sum_ite_eq']; simp [leg] -- uses wheel_app -> rewrite inverse with helper if needed
  left; rw [← wheel_app,Equiv.symm_apply_apply]



/-- Data port for the cut no-hole stacked D: compulsory subset
including identities displayed. All keys non-tree counted once. Here D
on FULL common coordinates; restrict by actual S and F. Allows all further
rows including the actual ell cuts. For tree independence ALSO verify
`negatives` on the extra rows.
-/
structure Tickets (D : Matrix X (AllKeys G.ColorIndex f) ℝ) (a b : ℝ) where
  direct : Body 2 f × G.ColorIndex ↪ X
  heat : Body 1 c × G.ColorIndex ↪ X
  apart (i j) : direct i ≠ heat j
  first (i j) : D (direct i) j=a*lined G.ColorIndex (d 1 f) i j
  next (i j) : D (heat i) j=b*lined G.ColorIndex (probe S) i j


variable [Fintype X]










end YM.SectorNext.Vacuum.FlatTree

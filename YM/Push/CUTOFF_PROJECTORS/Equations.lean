import YM.Next.FOUNDATIONS.JetReads
import YM.Push.CUTOFF_PROJECTORS.Frame
import YM.Work.C25

/-!
# Equation coordinates and cutoff presentation

Specify here the missing finite input.

There is *not* currently a producer of the Wilson equation transfers on the
family in the Lean library.

This interface works from actual link vector
fields and their equation-cylinder `Coefficient` chains (on the *same*
Family; transfer to `C.ref d`).

Choice of their stencils/filtered-gradients,
representation and bounds is for RDuets, NOT dictated uniquely by physical
measures nor by label vectors.

In particular neither `C.Makes` nor the
accepted G09 alone gives the chain for an equation cylinder.

Take these as
inputs, not the projections, projector bounds, tested rank, etc.

`ComesFrom` below gives exact requirements for using this data as equation
coordinates, all of them *finite regulator* (including actual unnormalized
density equality, no change of RG kernel). This file doesn't need spectral
assumptions; also no claim that these inputs already say the maps are
injective, or that these equations are all the relations. Additional
(noncollapse) estimates used for rank & inverse use of the columns are
separate. A degenerate equation family, though still having a perfectly
good orthogonal projection, won't serve via those estimates!

The cylinder itself elsewhere uses literal
translation; *further* transfers for other offsets, Woke and array bounds,
etc. as needed down the road belong to other producers. State locality
here as actual dependence on the fixed endpoint stencil, not a bound on
reader/algorithm costs or choices of masks when setting up a Duet. No IBP or
all-copy `close` estimate is assumed or proved by the projection procedure.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.CutoffProjectors
open Function Filter Labels Lattice RG Wilson Source MeasureTheory Next.Extract Extraction
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius

variable {G : Gauge} {d N p : ℕ} (F : Labels.Frame G d)

/-- The actual Maxwell equation parameter space, in the family's
coordinate frame. -/
def equationSpace : Submodule ℂ F.Coeff :=
  (Maxwell.equationIdeal G d).map F.coords.toLinearMap

def parameterEquiv : (Maxwell.equationIdeal G d) ≃ₗ[ℂ] equationSpace F :=
  LinearEquiv.submoduleMap _ _

theorem equation_dim : Module.finrank ℂ (equationSpace F) = Module.finrank ℂ (Maxwell.equationIdeal G d) :=
  (parameterEquiv F).finrank_eq.symm

/-- Compute the input space by the genuine free linear constraints. No
assumption that this gives all free or interacting separated nulls. -/
theorem equation_iff {v : F.Coeff} : v ∈ equationSpace F ↔ ∀ X : Maxwell.TaylorTower G,
    Labels.read (fun i => Maxwell.gaugeJet (X i)) (F.coords.symm v).val = 0 := by
  rw [← Maxwell.ideal_meaning]
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := Submodule.mem_map.mp hv
    simpa using hw
  exact fun h => Submodule.mem_map.mpr ⟨_,h,F.coords.apply_symm_apply _⟩

lemma scaled_mem (t : ℝ) {x : F.Coeff} (h : x ∈ equationSpace F) : F.scaled t x ∈ equationSpace F := by
  rw [equation_iff] at h ⊢
  intro X
  rw [Next.Foundations.read_frame_scaled]
  convert h (t • X) using 2
  ext1 i; simp; rfl

def scaledEquations (t : ℝ) : equationSpace F →ₗ[ℂ] equationSpace F :=
  ((F.scaled t).comp (equationSpace F).subtype).codRestrict _ fun x => scaled_mem F t x.2

variable {n : Side} {C : Family G}

/-- A link vector field (complexified in the physical color frame; coordinates
for the LEFT increments, positive links). -/
abbrev Vectors (G : Gauge) (n : Side) := Config G n → Edge (Site n) → G.ColorIndex → ℂ

/-- The finite data used to compute the map. `m` is level in the chain;
allow any values where not using a chain (pad linearly for the `.x`). -/
structure Packet (C : Family G) (d N p : ℕ) where
  weights : equationSpace (C.labels.level d) →ₗ[ℂ] Vectors G (C.side N p)
  chain (m : ℕ) : equationSpace (C.labels.level d) → Coefficient (C.labels.level d) (C.side m p)
  linear_x (m : ℕ) : IsLinearMap ℂ fun v => (chain m v).x

namespace Packet
variable (E : Packet C d N p)

/-- Includes the `t_N^{-l}` factor of  (l = slot degree of that
component). No extra G adjoint, color trace factors or conjugations across
the two entries of this formula. -/
def X := E.weights.comp (scaledEquations (C.labels.level d) (C.path.levels.clock.threshold N)⁻¹)

def forward (e : Edge (Site n)) (j : G.ColorIndex) : RG.Directions G n :=
  Pi.single e ((EuclideanSpace.basisFun G.ColorIndex ℝ) j)

variable (v : equationSpace (C.labels.level d))

def derivative {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : Config G n → Y)
    (e : Edge (Site n)) (j : G.ColorIndex) (U : Config G n) := leftDerivs f [forward e j] U

/-- `energy` counts positive plaquettes exactly once, with the
normalized trace price. `RG.increment` exponentiates in `G.Color`'s
normalization. The minus sign is for `bare β = exp (-β * energy)`;
divergence differentiates the **whole** component. This definition is to
be used with genuine derivative hypotheses and β>0. -/
def Jorigin : Config G (C.side N p) → ℂ :=
  fun U => ((C.S.a N : ℂ)^d)⁻¹ * ∑ (e : Edge (Site (C.side N p))), ∑ j : G.ColorIndex,
    (E.X v U e j * (derivative energy e j U : ℝ) -
      ((C.beta N p : ℂ))⁻¹ * derivative (fun V => E.X v V e j) e j U)

def J (o : Site (C.side N p)) (U : Config G (C.side N p)) := E.Jorigin v (translate o U)

-- This need NOT be the factory's transfer of the equation
-- cylinder's top x coordinate: that would forget its remainder.
def matrixAt (m : ℕ) : equationSpace (C.labels.level d) →L[ℂ] C.label d :=
  (IsLinearMap.mk' _ (E.linear_x m)).toContinuousLinearMap

def reference := E.matrixAt (C.ref d)

def topEquation := E.matrixAt N

/-- Top coordinates of the PRIMARY matched to J at the *reference*. -/
def costMatrix : equationSpace (C.labels.level d) →L[ℂ] C.label d :=
  (C.factory d N p).terminal.symm.toLinearMap.toContinuousLinearMap.comp E.reference

abbrev subspace : Submodule ℂ (C.label d) := LinearMap.range E.reference.toLinearMap

/-- Constraint-row form of the matrix. Use the same H-invariant Hermitian
form (conj only on column, linear in x). Its kernel is the **retained**
space, not the kernel of step. Even use only finrank many rows. -/
def row (w : equationSpace (C.labels.level d)) : C.label d →L[ℂ] ℂ :=
  ((innerSL ℂ) (chart (C.labels.level d) (E.reference w))).comp (chart (C.labels.level d))

def finiteRows :=
  let b := Module.finBasis ℂ (equationSpace (C.labels.level d))
  (LinearMap.pi fun i => (E.row (b i)).toLinearMap).toContinuousLinearMap

set_option maxRecDepth 4000 in
theorem rows_kernel : LinearMap.ker E.finiteRows.toLinearMap = normal (C.labels.level d) E.subspace := by
  let F := C.labels.level d
  let b := Module.finBasis ℂ (equationSpace F)
  ext x
  rw [normal_iff, LinearMap.mem_ker]
  change E.finiteRows x = 0 ↔ _
  have app (i) : E.finiteRows x i = pair F (E.reference (b i)) x := by
    dsimp only [finiteRows]
    rfl
  constructor
  · intro h y hy
    obtain ⟨z,rfl⟩ := LinearMap.mem_range.mp hy
    have hu (i) : inner ℂ (chart F (E.reference (b i))) (chart F x) = 0  := by
      change pair F _ _ = 0
      rw [← app, h]; rfl
    change inner ℂ (chart F (E.reference z)) (chart F x) = 0
    rw [← b.sum_repr z, map_sum, map_sum, sum_inner]
    simp only [map_smul, inner_smul_left, hu, mul_zero, Finset.sum_const_zero]
  intro h
  ext1 i
  rw [app, h (E.reference (b i)) (LinearMap.mem_range.mpr ⟨b i,rfl⟩)]; rfl

/-- All formulas interpreted on the same cutoff family. These premises for
*physical* use of the finite matrix are intentionally not postulated as
always available. `Stencil` is in microscopic sites. `cap` takes the
literal remBound, allowing a regulator-dependent bound; does *not* enforce
the WEbud pre-L payments. -/
def sites (n : Side) (S : Finset Cover) : Support n := S.image (wrap n)

/-- C¹ in each of the used left directions (just enough here to use
`derivative` with a genuine continuous value). -/
structure Along {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : Config G n → Y) : Prop where
  continuous : Continuous f
  exact (e : Edge (Site n)) (j : G.ColorIndex) (U : Config G n) :
    HasDerivAt (fun t : ℝ => f (increment U (t • forward e j))) (derivative f e j U) 0
  rate (e : Edge (Site n)) (j : G.ColorIndex) : Continuous (derivative f e j)

structure ComesFrom (S : Finset Cover) : Prop where
  fit : C.ref d ≤ N
  spatial : 0 ∈ S
  fits : ∀ x ∈ S, ∀ i : Axis, 20*((x i).natAbs + 1) ≤ (C.side N p).val
  coupling : 0 < C.beta N p
  action : Along (energy (G:=G) (n:=C.side N p))
  coefficients (w : equationSpace (C.labels.level d)) (e : Edge (Site (C.side N p))) (j) :
    Along fun U => E.X w U e j
  depends w : LocalOn (sites (C.side N p) S) (E.X w)
  moves w U e j : E.X w U e j ≠ 0 → e.1 ∈ sites (C.side N p) S ∧
    e.1 + step e.2 ∈ sites (C.side N p) S
  reads w : LocalOn (sites (C.side N p) S) (E.Jorigin w)
  gauge w : GaugeInvariant (E.Jorigin w)
  format (m : ℕ) : C.ref d ≤ m → m ≤ N → ∀ w,
    (E.chain m w).Format 0 C.params (C.path.rep N p m)
  cap (m : ℕ) : C.ref d ≤ m → m ≤ N → ∀ w, ∃ b : ℝ,
    (E.chain m w).remBound 0 (C.path.rep N p m) (Real.sqrt (C.path.levels.clock.forcedAllowance m)) b
  encode w U : (E.chain N w).density 0 (C.localSection d) (C.path.rep N p N) U =
    ((C.S.a N : ℂ)^d) * ((C.path.rep N p N).eval U : ℂ) * E.Jorigin w U
  transfer m : C.ref d ≤ m → m < N → ∀ w,
    (E.chain m w).density 0 (C.localSection d) (C.path.rep N p m) =
      ((C.S.block m).val : ℂ)^d • (C.path.levels.clock.op m p).push (C.path.β N p (m+1))
        ((E.chain (m+1) w).density 0 (C.localSection d) (C.path.rep N p (m+1)))

variable {E} {S : Finset Cover}

theorem ComesFrom.continuous (h : E.ComesFrom S) : Continuous (E.Jorigin v) := by
  unfold Jorigin
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Continuous.sub ?_ ?_)
  · exact ((h.coefficients v i j).continuous).mul (Complex.continuous_ofReal.comp (h.action.rate i j))
  exact continuous_const.mul ((h.coefficients v i j).rate i j)

/-- Even though `deriv` uses junk values when not differentiable, here J
really extends linearly. -/
theorem ComesFrom.linear (h : E.ComesFrom S) : IsLinearMap ℂ E.Jorigin := by
  have hs (a b : equationSpace (C.labels.level d)) (U : Config G (C.side N p)) (e j) :
      derivative (fun V => E.X (a+b) V e j) e j U = derivative (fun V => E.X a V e j) e j U +
        derivative (fun V => E.X b V e j) e j U := by
    simp only [map_add, Pi.add_apply]
    exact (((h.coefficients a e j).exact e j U).add ((h.coefficients b e j).exact e j U)).deriv
  have ht (c : ℂ) (w : equationSpace (C.labels.level d)) (U : Config G (C.side N p)) (e j) :
      derivative (fun V => E.X (c • w) V e j) e j U = c * derivative (fun V => E.X w V e j) e j U := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact (((h.coefficients w e j).exact e j U).const_mul c).deriv
  constructor
  · intro a b; ext1 U
    unfold Jorigin
    -- rewrite derivative first
    simp_rw [hs]
    simp only [map_add, Pi.add_apply, add_mul, mul_add, add_sub_add_comm, Finset.sum_add_distrib]
  intro c a; ext1 U
  unfold Jorigin
  simp_rw [ht]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm _ c, ← mul_sub,
    ← Finset.mul_sum]

/-- Check the reference readout really uses the family's transfer and full
normalization. Equality here is of reference coordinates, not of density
functions of J and its primary. -/
theorem ComesFrom.matched (h : E.ComesFrom S) (hc : C.Makes) :
    ((C.factory d N p).entries (C.ref d) (E.costMatrix v)).x = (E.chain (C.ref d) v).x :=
  C.normalized hc h.fit (E.reference v)

theorem matched_field (E : Packet C d N p) :
    C.O N p (d:=d) (E.reference v) = initial (C.localSection d) C.path N p (E.costMatrix v) := rfl

theorem ComesFrom.density_int (h : E.ComesFrom S) (hc : C.Makes) (m : ℕ) (hr : C.ref d ≤ m) (hm : m ≤ N) :
    Integrable ((E.chain m v).density 0 (C.localSection d) (C.path.rep N p m)) (prior G (C.side m p)) := by
  obtain ⟨b,hb⟩ := h.cap m hr hm v
  have he := Coefficient.envelope (C.localSection d) (hc.wilson.represents N p m hm).good hb (h.format m hr hm v)
  obtain ⟨K,hk⟩ := he.cost
  exact Integrable.of_bound he.meas.aestronglyMeasurable K (Eventually.of_forall hk)

/-- A downstream normalization check on an authentic packet. Includes the
partition, nothing divided by a hypothetical new normalization. -/
theorem ComesFrom.integral (h : E.ComesFrom S) (hc : C.Makes) (m : ℕ) (hr : C.ref d ≤ m) (hm : m ≤ N) :
    (∫ U, (E.chain m v).density 0 (C.localSection d) (C.path.rep N p m) U ∂prior G (C.side m p)) =
      (C.S.a m : ℂ)^d * (partition G (C.side N p) (C.beta N p) : ℂ) *
        moment (C.beta N p) (E.Jorigin v) := by
  induction hm using Nat.decreasingInduction with
  | self =>
    have hi := continuous_integrable (C.beta N p) (h.continuous v)
    rw [moment_formula _ _ hi]
    have hz : (partition G (C.side N p) (C.beta N p) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (partition_pos _).ne'
    simp_rw [h.encode, (hc.wilson.starts N p).2, mul_assoc]
    rw [integral_const_mul]; simp [hz]
  | of_succ k hk Hk =>
    simp_rw [h.transfer k hr hk]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, StepData.push_integral (C.path.levels.transition_mass ..) _
      (h.density_int v hc _ (hr.trans k.le_succ) hk), Hk (hr.trans k.le_succ), C.S.a_step]
    have he := (C.S.block k).property.ne'
    simp only [Complex.ofReal_div, Complex.ofReal_natCast]
    rw [← mul_assoc, ← mul_assoc, ← mul_pow, mul_comm ((C.S.block k).val : ℂ), div_mul_cancel₀ _ (by exact_mod_cast he)]

end Packet

/-- One way to commission the finite inputs (which for physical use are
needed at sufficiently fine cutoffs). Even allow p dependence for start of
chain proofs. E proposes stronger eventual receipts. No spectral promises in
this structure. Ordinary data like oriented readout or budget promises if
needed will be separate inputs. Not an existence assertion for a campaign
serving the estimates. -/
structure Campaign (C : Family G) where
  cutoff : C.Makes
  packet (d N p : ℕ) : Packet C d N p
  box (d : ℕ) : Finset Cover
  start (d p : ℕ) : ℕ
  uses (d N p : ℕ) : start d p ≤ N → (packet d N p).ComesFrom (box d)

namespace Campaign
variable (A : Campaign C)

abbrev spaces : Subspaces C := fun d i => (A.packet d i.1 i.2).subspace

def presentation : Presentation C := present A.spaces

/-- Explicitly d, every pair (N,p). -/
theorem cost (d N p : ℕ) : ‖A.presentation.step d (N,p)‖ ≤ fee (C.labels.level d) := retain_le_fee ..

theorem costs (f : Extraction.Order) : Affordable A.presentation f := affordable A.spaces f

theorem projected (x : C.label d) :
    A.presentation.step d (N,p) (A.presentation.step d (N,p) x) = A.presentation.step d (N,p) x :=
  retain_retain ..

/-- exact at the finite coordinates instead of already at any
limit. -/
theorem ker (d N p : ℕ) :
    LinearMap.ker (A.presentation.step d (N,p)).toLinearMap = (A.packet d N p).subspace := retain_ker ..

theorem range (d N p : ℕ) :
    LinearMap.range (A.presentation.step d (N,p)).toLinearMap =
      LinearMap.ker (A.packet d N p).finiteRows.toLinearMap :=
  (retain_range _ _).trans (A.packet d N p).rows_kernel.symm

theorem equation_iff_zero (x : C.label d) : A.presentation.step d (N,p) x = 0 ↔
    ∃ w : equationSpace (C.labels.level d), (A.packet d N p).reference w = x := by
  change x ∈ LinearMap.ker _ ↔ _
  rw [A.ker]
  exact LinearMap.mem_range

theorem auth_rows (d p : ℕ) (f : Extraction.Order) : ∀ᶠ j : ℕ in atTop,
    (A.packet d (f.mesh j) p).ComesFrom (A.box d) := by
  filter_upwards [f.mesh.cofinal.eventually (eventually_ge_atTop (A.start d p))] with j hj
  exact A.uses _ _ _ hj

theorem auth_late (d : ℕ) (f : Extraction.Order) : f.late (fun N p => (A.packet d N p).ComesFrom (A.box d)) :=
  Eventually.of_forall fun _ => auth_rows ..
end Campaign
end YM.Push.CutoffProjectors

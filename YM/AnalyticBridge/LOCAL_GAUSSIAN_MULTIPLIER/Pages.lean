import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Sleeves
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Tier

/-!
# Kernels/payments to local letters

`Slices` tracks exact (untruncated) identities before pricing a letter,
including coupling, V, and at the *same* tags. Producers for a dictionary
with short diagonal letters plus ordered chain tails still needed. There is
an expensive (nonlocal) fallback dictionary of no quantitative interest.
Here, in particular, no assumption on estimates of `logdet`; see consumer
for buying the needed individual letter prices afterwards.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Matrix Tree Precision Exterior Bloch MeasureTheory Next.SectorChange Next.SectorChange.Gaussian
open Next.SectorChange.Rows YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open Next.Fluctuations.Sector
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff InnerProductSpace Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S}
namespace Spot
variable (u : Spot d)

/-- Addresses retain row names in E's convention (in particular orientations
that share a U or V argument). -/
abbrev Shape (c f : Side) := Cell f ⊕ Bond c ⊕ Cell c ⊕ Co c Gain ⊕ Cell c ⊕ Cell c
abbrev RowPosts (c f : Side) := Signed × Shape c f

def material (V : Config G c) (p : u.Visual) := u.m V p.1+d.g • p.2

def bolt (V : Config G c) (p : u.Visual) := residual d.tube d.betaHat V u.k u.stencils u.A u.F d.broadCut
  d.radius p.1 (u.hard V p) (u.material V p)

def impression (i : Shape c f) (s : Signed) (V : Config G c) (p : u.Visual) :=
    let P := pull s 0 (u.hard V p); let Q := S.prediction P (choice s u.k)
    let v := pull s 0 V; let T := d.tube
    let x := d.betaHat; let t := temp x; let r := till x
    match i with
    | .inl i => T.workF r P v (fiery G x S.patch.L) t i - ∑ j : Bool,
        chargedUp T x V u.k u.stencils u.A u.F d.broadCut d.radius p.1 (u.material V p) s (i,j)
    | .inr (.inl i) => T.workI r Q v t i -
        chargedSide T x V u.k u.stencils u.A u.F d.broadCut d.radius p.1 (u.material V p) s i
    | .inr (.inr (.inl i)) => T.workC r v t i
    | .inr (.inr (.inr (.inl i))) => T.workN r v t i
    | .inr (.inr (.inr (.inr (.inl i)))) => T.workL r P Q v t i
    | .inr (.inr (.inr (.inr (.inr i)))) => T.workD r v t i

def residualFee (V : Config G c) (p : u.Visual) (i : RowPosts c f) : ℝ :=
    -d.input.beta * ((Fintype.card Signed:ℝ)⁻¹ * u.impression i.2 i.1 V p)

lemma written_rows (s : Signed) (V : Config G c) (p : u.Visual) :
    (∑ i : Shape c f,u.impression i s V p) = u.bolt V p s := by
  simp_rw [Shape,Fintype.sum_sum_type]; rw [bolt, at_residual]
  simp only [impression]; abel

lemma tallies (V : Config G c) (p : u.Visual) : HasSum (u.residualFee V p)
    (-d.input.beta*averaged (u.bolt V p)) := by
  convert! (hasSum_fintype (u.residualFee V p)) using 1
  rw [Fintype.sum_prod_type]
  unfold averaged residualFee
  simp_rw [← Finset.mul_sum]
  simp_rw [u.written_rows]

/-- Reusable Gaussian/determinant ports. The Nat alphabet can e.g.
subindex window/log terms of the paired comparators then their chain tails.
Quadratic ports additionally indexed by physical ordered endpoints even if
revisiting links. Need only identities on matching Flags and licensed
real kernels; see edits later for keeping agreement on intact support and
local extension requirements. No appeal to a common counting-field precision
to discard holes or to change the window in the quadratic correction. -/
structure Slices where
  paired : Config G c → ℕ → ℝ
  limitPay : Config G c → ℕ → ℝ
  difference : Config G c → u.InKey → u.InKey → ℕ → ℝ
  common V : u.Clearing V → HasSum (paired V) (Real.log (u.shiftGram V).det-Real.log u.H.det)
  logarithm V : u.Clearing V → HasSum (limitPay V) (Real.log (1+(u.shiftGram V*u.C V-1)).det)
  correction i j V : u.Clearing V → HasSum (difference V i j) (((u.C V)⁻¹-u.shiftGram V) i j)

/-- **Not** claiming local data on such a dictionary. -/
def entire : u.Slices where
  paired V := Pi.single 0 (Real.log (u.shiftGram V).det-Real.log u.H.det)
  limitPay V := Pi.single 0 (Real.log (1+(u.shiftGram V*u.C V-1)).det)
  difference V i j := Pi.single 0 (((u.C V)⁻¹-u.shiftGram V) i j)
  common := fun _ _ => hasSum_pi_single ..
  logarithm := fun _ _ => hasSum_pi_single ..
  correction := fun _ _ _ _ => hasSum_pi_single ..

abbrev Relative := u.FrozenKey ⊕ ℕ ⊕ ℕ

def book (D : u.Slices) (V : Config G c) : u.Relative → ℝ
  | .inl _ => -Real.log (spare d.chart d.input.beta)
  | .inr (.inl i) => -(1/2)*(D.paired V i)
  | .inr (.inr i) => (1/2)*(D.limitPay V i)

lemma balanced (D : u.Slices) (V : Config G c) (h : u.Clearing V) : HasSum (u.book D V) (u.receipt V) := by
  have he := (D.common V h).mul_left (-(1/2 : ℝ))
  have hl := (D.logarithm V h).mul_left (1/2:ℝ)
  let f := fun _ : u.FrozenKey => -Real.log (spare d.chart d.input.beta)
  convert! HasSum.sum (f:=u.book D V) (hasSum_fintype f) (HasSum.sum he hl) using 1
  simp [f,receipt,neg_mul]; ring

abbrev Correction := Slots S ⊕ u.ActiveKey ⊕ u.ActiveKey × u.ActiveKey × ℕ

def thin (V : Config G c) (p : u.Visual) := Rows.direct d.tube d.betaHat V u.k u.stencils u.A u.F d.broadCut
    d.radius p.1 (u.m V p.1)

def sourceFee (V : Config G c) (p : u.Visual) := eta d.tube d.betaHat V u.k u.stencils u.A u.F d.broadCut
    d.radius p.1 (u.m V p.1) d.g

def affinity (V : Config G c) (p : u.Visual) := adjustment d.tube d.betaHat V u.k u.stencils u.A u.F d.broadCut
    d.radius p.1 (u.C V) (u.m V p.1) d.g p.2

/-- One address retains the full endpoints' color sum (indicators in
direct rows untouched). Apply the `exp`/Mayer to this letter, not
per-color. Covariance under block conjugations, numbering Slices in
a way that retains gauge symmetries, etc. are separate requirements
when reconstructing output species; not granted by the identity. -/
def cardCost (D : u.Slices) (V : Config G c) (p : u.Visual) : u.Correction → ℝ
  | .inl i => ∑ j:G.ColorIndex,-((u.thin V p (i,j))^2/2)/d.g^2
  | .inr (.inl i) => ∑ a:G.ColorIndex,u.sourceFee V p (i,a) * p.2 (i,a)
  | .inr (.inr (i,j,N)) => ∑ a:G.ColorIndex, ∑ b:G.ColorIndex,(p.2 (i,a) * (D.difference V (i,a) (j,b) N * p.2 (j,b))) / 2

lemma rectifies (D : u.Slices) (V : Config G c) (h : u.Clearing V) (p : u.Visual) : HasSum (u.cardCost D V p) (u.affinity V p) := by
  let I i := u.cardCost D V p (.inl i)
  let H i := u.cardCost D V p (.inr (.inl i))
  let L i := u.cardCost D V p (.inr (.inr i))
  let Q := (u.C V)⁻¹-u.shiftGram V
  let x := u.thin V p; let z := p.2
  let f i j := z i*(Q i j*z j)/2
  let g i j := ∑ a:G.ColorIndex, ∑ b:G.ColorIndex, f (i,a) (j,b)
  have he i j : HasSum (fun l => L (i,j,l)) (g i j) := hasSum_sum (s:=Finset.univ)
    (fun a _ => hasSum_sum (s:=Finset.univ) (fun b _ => (((D.correction (i,a) (j,b) V h).mul_right _).mul_left _).div_const _))
  have ht : HasSum L (∑ i,∑ j,g i j) := addresses fun i => addresses fun j => he i j
  have hh : u.affinity V p= ∑ i,I i + ((∑ i,H i)+(∑ i,∑ j,g i j)) := by
    change -((x ⬝ᵥ x)/2)/_ + (_ ⬝ᵥ z) + (z ⬝ᵥ (Q *ᵥ z))/2 = _
    have hj : (∑ i,I i)=-((x ⬝ᵥ x)/2)/d.g^2 := by
      change (∑ i : Slots S, ∑ j : G.ColorIndex, -((x (i,j))^2/2)/d.g^2)=_
      unfold dotProduct; simp_rw [Fintype.sum_prod_type]
      simp_rw [Finset.sum_div,← Finset.sum_neg_distrib]; simp only [sq,Finset.sum_div]
    have hp : (∑ i,H i)=u.sourceFee V p ⬝ᵥ z := by unfold dotProduct; rw [Fintype.sum_prod_type]; rfl
    rw [hj,hp,add_assoc]; congr 1
    unfold g f dotProduct mulVec; simp_rw [dotProduct,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_div]
    refine congr_arg₂ HAdd.hAdd rfl ?_
    apply Finset.sum_congr rfl; intro i hi
    exact Finset.sum_comm
  rw [hh]; exact HasSum.sum (hasSum_fintype I) (HasSum.sum (hasSum_fintype H) ht)
end Spot
end YM.AnalyticBridge.LocalGaussian

import YM.UVNext.PRICED_KERNELS.Assembly
import YM.UVNext.PRICED_KERNELS.Basin
import YM.UVNext.PRICED_KERNELS.Elliptic
import YM.UVNext.PRICED_KERNELS.Trees



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Offering the real active precision inverse uniformly on this j,L & Permit

Actual `hessian` in `FiniteBound`, relative slice chart on ANY of
these forests (not just an equivariant choice). Includes full gap price from
the issuance—not a spectral input about a polynomial truncation. Provide an explicit post-L after
kernel consumer: assertions at any N,m,p do not cost p, N, or coupling
at this L,j. No assumption of density analytic branch continuation to
those rates. Does not price the quantum wave discrepancy or the actual
successor arrays in Remaining.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Set Function Lattice Wilson RG RG.Supply Precision Pressure Laurent Exterior Bloch Matrix Tree Bid
open Push.PriceCompiler
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio}

/-- Keys per fine physical site (could compress below instead of this price).
-/
def multiplicity (G : Gauge) := (Fintype.card ((TypeFace 1) × G.ColorIndex) : ℝ)





section Hess
variable (S : StepData c f)
-- pre-L coefficients in the `unitHess` estimates. For A = Ω j, η = α j (width rate, not Hessian gap!).
def critProbe (L : ℝ) (j : ℕ) (s : ℝ) := L*(1+dC 0 s*2)*stepC j s


def billFlip (ι : Type*) [Fintype ι] (s C : ℝ) := C*Fintype.card ι * Real.exp (s/2) * basin (s/2)


-- cost at t/L for `d^T` and d (again can project to any lower width). d^T output row cardinal TypeFace(k+1) vs D uses k

def plusdC (k : ℕ) (s : ℝ) := Fintype.card (TypeFace (k+1)) * (Next.Free.delta_budget k s).choose


def unitPrice (L : ℝ) (j : ℕ) (κ s A : ℝ) :=
    plusdC 1 s*((Fintype.card (TypeFace 2):ℝ)*A)*dC 1 s + |κ| * (billFlip (TypeFace 1) s (critProbe L j s) * critProbe L j s)




end Hess

/-- The actual price on the issued Hessian and all these uses of It. Works
on every path choice with the given premises. Use with Π kernels of the earlier
construction by `fixed_steps` below. **No** need for pre-existing Paid
estimates on the inverse/absolute matrix Hessian conditions at each period.
  Stage rate s from Kernel Maps, not the Θ after choice.
-/
def activePrice (G : Gauge) (L : ℝ) (j : ℕ) (κ s A : ℝ) :=
    1 + Fintype.card G.ColorIndex * unitPrice L j κ s A



def inverseWidth (L s η C : ℝ) := cautious (s/2/L) η C / 2
def inversePrice (G : Gauge) (L s η C : ℝ) := (2/η)*multiplicity G*basin (inverseWidth L s η C)


section Fixed
open RG.Supply
variable {P : Before} {f₀ : ℕ → ℕ} {D : Rolls (P.sheet G f₀)}
    {M : Preparations P D} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
    {a : Levels G} (h : Permit M I a) {V : Horizon a} (hv : Motor P a V)
    {Q : ℕ → ℕ → PathData G} (hi : Installed P a V Q)

def stamp (D : Rolls (P.sheet G f₀)) (j : ℕ) : ℝ :=
    let K := P.frozen G
    activePrice G (D.L j).val j (P.kernelChoice G).penalty (K.α j) (K.Ω j)



def fare {D : Rolls (P.sheet G f₀)} (M : Preparations P D) (j : ℕ) : ℝ :=
    inversePrice G (D.L j).val ((P.frozen G).α j) (M.gap j) (stamp D j)

include h hv hi

end Fixed
end YM.UVNext.PricedKernels

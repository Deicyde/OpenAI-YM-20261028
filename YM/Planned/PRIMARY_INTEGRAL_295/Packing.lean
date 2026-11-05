import YM.Extra.SOURCE_HISTORIES.Clusters
import YM.Next.FREE_KERNELS.Lifts
import YM.Push.LOCAL_SPLITTING.Funding



/-!
# Funding a real primary build

Unpaid other E component income on certifying this actual raw build,
not its canonical/projection error. Anchor funcs true domains B (incl
boundary), unmasked. All at ONE beta. Use with own stationary prices
on 0. Do not use the smaller mask support with a recovered coefficient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Packing
open Function Filter Set Lattice Labels Source RG Wilson Next.Foundations Extra.Histories
open Push.Local
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {n : Side} {A : Hol G} {T : SectionData F}
variable {R : Rep G n} {o : Site n} {X : ℕ→Support n} {u w v : ℝ}

/-- Unscaled extra budget on raw NON-leading terms, required from the
primary step producer re sector etc, including (here before carving out
any canonical components) true scores, not forgetting component 0
c(re) in `kappa`. The cap `u` used at `L^d δ`. -/
structure Other (M : Raw F n) (R : Rep G n) (X : ℕ→Support n) (o : Site n) (κ u : ℝ) : Prop where
  pay : ∃ e:ℕ→ℝ, (∀ i,R.p.supBounds o (X (i+1)) (M.bulk (i+1)) (e i)) ∧ SumBudget (fun i=> reservedMass R.p (X (i+1)) (e i)) u
  lanes : ForceCost R.p R.activities M.forced (κ*u)

variable {M : Raw F n}




def canvas (a : ℝ) (K : ℕ) := Real.exp ((a+2)*K)



def unitRaw (a : ℝ) (K : ℕ) (C : ℝ) := 2*canvas a K*C+1

def unitOutput (A : Hol G) (T : SectionData F) (a : ℝ) (K : ℕ) (C w : ℝ) := 2*factor A T a w * unitRaw a K C + 1

def tol (d : ℕ) (L : Side) (δ : ℝ) := (L.val:ℝ)^d*δ

section
variable (L : Side) (i : F.Index) (A T M) {δ : ℝ}
variable (hr : M.Format o X R) (h : Readable A T R.p n w) {K : ℕ} (hp : coverNumber R.p.B (X 0)≤K)
include hr h hp



omit hp

end
end YM.Planned.PrimaryIntegral295.Packing

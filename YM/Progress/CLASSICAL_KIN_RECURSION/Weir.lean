import YM.Progress.CLASSICAL_KIN_RECURSION.Counter

set_option warningAsError false

/-!
# Static completed real matrix and response map. Native c for the CURRENT
height. Sign unimportant in square penalty, here Δ*+L²P^T. No inverse
assumed; totalization unused off Pins. pre-L norm estimates further work.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin.Tent
open Lattice RG Exterior Wilson Precision Tree Bid Bloch Matrix
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {M : Bed}

/-- positive convention Lg in square. -/
def clog (S : StepData c f) (G : Gauge) : Hall G c f →ₗ[ℝ] Frame G f:=
    (paint G (d 0 f).transpose).comp (LinearMap.fst _ _ _) + ((S.patch.L.val : ℝ)^2) • ((paint G (plaque S).transpose).comp (LinearMap.snd _ _ _))


def dam (S : StepData c f) (M : Bed) (G : Gauge): Hall G c f→ₗ[ℝ] Hall G c f→ₗ[ℝ] ℝ:= mainCounter S M G + (counts G 0 f).compl₁₂ (clog S G) (clog S G)


def Pin (S : StepData c f) (M : Bed) (G : Gauge): Prop:= ∀ x:Hall G c f,x≠0→0<dam S M G x x


lemma dammed (h : Pin S M G) : Bijective (dam S M G):= by
  have hh:Injective (dam S M G):=(injective_iff_map_eq_zero _).mpr fun x hx=>by by_contra he; have hy:=h x he; rw [hx] at hy; exact lt_irrefl 0 hy
  exact ⟨hh,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Module.finrank_linearMap_self])).mp hh⟩

abbrev Note (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]:= X→L[ℝ] ℝ
open scoped Classical in
def sluice (S : StepData c f) (M : Bed) (G : Gauge): Note (Hall G c f) →L[ℝ] Hall G c f:= if h: Pin S M G then
  (LinearMap.toContinuousLinearMap ((LinearEquiv.ofBijective _ (dammed h)).symm.toLinearMap.comp (LinearMap.toContinuousLinearMap.symm.toLinearMap))) else 0






variable (h : Pin S M G)
include h





variable (hh : (M.metric.acts f).transpose=M.metric.acts f)
include hh


end YM.Progress.ClassicalKin.Tent

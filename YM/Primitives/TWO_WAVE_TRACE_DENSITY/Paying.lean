import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Period
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Quadrature

/-!
# Use a *true* publication, all C12 errors quantitative and posted
independently of the torus. Non-determinant scalar terms agree EXACTLY
with infinite-volume kernels on the two external mesh momenta.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave
open Lattice Laurent Bloch Matrix Complex RG
open scoped BigOperators Topology Classical
variable {α β ι τ : Type} [Fintype α] [Fintype β] {n : Side} {k : ℕ}

namespace SceneLedger

variable (L:SceneLedger α β)
/-- signed extra scalar q-independent limit. Holds both momenta as given,
delta supplied separately. -/
def sideAmp (p t:Momentum) (v w:α→ℂ):ℂ:=
    let a:=L.riseAmp p v; let b:=L.riseAmp t w
    (a ⬝ᵥ drive (colors L.tail₂ ![t]) ![b]) +
      (L.arc p t v w ⬝ᵥ drive (colors L.tail₁ (fun _=>0)) (fun _=>0))
def litBill (p t : Momentum) (v w:α→ℂ):ℂ:=
    L.sideAmp p t v w + (1/2:ℂ)*zoneMean (quote p (headSymbol L.cov) (L.stamp p v) (L.stamp t w) (L.stamp₂ p t v w))

def riseCost (α β:Type) [Fintype α] [Fintype β] (C:ℝ):ℝ:=1+(Fintype.card β:ℝ)*(C*((Fintype.card α:ℝ)*C))
def vertexCost (α β:Type) [Fintype α] [Fintype β] (C:ℝ):ℝ:= badgeFare (α⊕β) C (riseCost α β C) 1
def arcCost (α β:Type) [Fintype α] [Fintype β] (C:ℝ) : ℝ :=
    (Fintype.card β:ℝ)*(C*badgeFare (α⊕β) C (riseCost α β C) 2)
def pairCost (α β : Type) [Fintype α] [Fintype β] (C:ℝ):ℝ:=
    badgeFare (α⊕β) C (riseCost α β C) 2 + badgeFare (α⊕β) C (arcCost α β C) 1

def cellCost (α β:Type) [Fintype α] [Fintype β] (C:ℝ):=siteCost β C (vertexCost α β C) (vertexCost α β C) (pairCost α β C)
def fee (α β : Type) [Fintype α] [Fintype β] (η C:ℝ):ℝ:= (1/2:ℝ)*quadCost (η/2) (cellCost α β C)

variable {η C:ℝ} {I:Invoices α β n ℝ} {L}





namespace Credits
variable (H: Credits L η C)
include H





end Credits
namespace Published
open Invoices
variable (H:Published L I) (hc:Credits L η C)
include H hc



end Published
end SceneLedger
end YM.Primitives.TwoWave

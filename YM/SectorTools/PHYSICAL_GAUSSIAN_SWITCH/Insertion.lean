import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Local
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Potential
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Weighted


/-!
# An explicit physical insertion

Independent of whether end/mid windows happen to give the same table at
this sector. Heat factor at selected physical regular Z coordinates (can
use one or all colors at a link, or any finite set), for example useful
in a comparison with ratio exponent contributions such as those around
Softening sign; cannot promise integrability just by looking at
the unperturbed positive precision. This consumer earns pricing directly
also on a `Sector_Covariance_Jets.Sky` (correct V with common geometry), no
Directed etc. and no `Larger` needed beyond Sky's side test. This is a
mathematical *insertion under the conditional Gaussian*, not claiming to
have grouped or identified any actual Mayer selections there. All entries
remain physical and part of the full support bills.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch.Insertion
open Function Filter Matrix MeasureTheory Set
open Next.SectorChange.Gaussian
open scoped Topology BigOperators ENNReal Classical
local notation "Covar" => Next.SectorChange.Gaussian.Table

variable {I : Type} [Fintype I] [DecidableEq I] {D : Covar I} {r K p : ℝ}

def cost (X : Finset I) (r : ℝ) (i : I) := if i∈X then r else 0
def forge (X : Finset I) (r : ℝ) : Covar I := diagonal (fun i => -(2*cost X r i))
def heat (X : Finset I) (r : ℝ) (x : Vec I) := Real.exp (r*∑ i∈X,x i^2)



omit [Fintype I] in
lemma local_heat (X : Finset I) (r : ℝ) : Support.SquareOn (Embedding.subtype (·∈X)) (forge X r) := by
  intro i j ht; have he {i : I} (hi : i∉Set.range (⇑(Embedding.subtype (·∈X)))) : i∉X := fun h => hi ⟨⟨i,h⟩,rfl⟩
  by_cases h : i=j
  · subst j; have hi := ht.elim (fun h => h) (fun h => h); simp [forge,cost,he hi]
  exact diagonal_apply_ne _ h
omit [Fintype I] in
lemma symmetric (X : Finset I) (r : ℝ) : (forge X r).IsSymm := by unfold Matrix.IsSymm forge; simp

def savings (p K r : ℝ) (n : ℕ) := Real.exp ((p+1)*Weighted.spend p K (n*r) 0)

-- expose both actual likelihood and integral identity on centered cloud
structure Absorbs (D : Covar I) (X : Finset I) (p K r : ℝ) : Prop where
  main : D.PosDef
  altered : (Potential.system D (forge X r) 1).PosDef
  moment : (Potential.system D (forge X r) p).PosDef
  lp : let A:=Potential.tilted D (forge X r)
       (mixed A D p).PosDef ∧ price A D p 0 ≤ savings p K r X.card
  actual : let e:=Embedding.subtype (·∈X); let B:=forge X r; let A:=Potential.tilted D B
           let a:=Potential.bill (D.submatrix e e) (B.submatrix e e) (0:Vec X) 1
           (0<a) ∧ (∀ z, likelihood A 0 D 0 z=heat X r z/a) ∧
           (cloud D).withDensity (fun z => ENNReal.ofReal (heat X r z/a))=cloud A
  changed : (X.Nonempty ∧ 0<r) → Potential.tilted D (forge X r) ≠ D



section sky
open Lattice Wilson RG Precision Exterior Bloch Tree Pressure
open Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Motion Next.SectorChange.Rows

variable {G : Gauge}


end sky
end YM.SectorTools.PhysicalGaussianSwitch.Insertion

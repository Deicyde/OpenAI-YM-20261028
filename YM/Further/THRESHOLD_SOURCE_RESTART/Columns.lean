import YM.Extra.MULTISOURCE_BOUNDS.LogTerms
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.Push.ABSOLUTE_SUMS.Ursell

/-!
# Recombined scalar-vacuum cut of the restart first-system

In this route specify a restricted hard-exclusion system with all
of its masked vertices. Each reclosed hard record at this cut
must still carry its earlier ban list, before summing interchangeable
histories. NEED still the first-system expansion for the actual integral
with scalar reclosures (including commuting their choices with the later
marked omission move here); no proof that an arbitrary scalar-only
procedure could deliver this. As elsewhere additional variants must be
priced. This producer derives the occurrence identities and computes the
weights for the unscaled *marked log*, rather than assuming its form as
part of a kernel. Does not change meter currency to derivatives, nor assert
any prices on the underlying kernels/vac.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart
open Function Filter Set MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Extra.Multi LogTerms Prepare Width
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {V α : Type*} [DecidableEq V] [Fintype V]
variable {P : Rep G n} {o : V → Site n}

/-- Multiplicative kernel port: all these terms after any reorganization
of SCALAR families necessitated by the first-system derivation. `bans`
rectangular condition (per hard address). If d- and source histories force a
different ban pattern they need distinct hard addresses; whether already
present in *one* common reclosed P is physics input. Here the unforced gas itself uses only disjointness – include overlaps for all earlier shared data in
those supports, or get the identity by a compatible reformat. `quantum`
will divide by the quiet part of THIS unforced gas including the appropriate
avoid s (already counted at the unmarked reset). Not dividing by a hard K
at all even here. -/
structure Grey (P : Rep G n) (o : V → Site n) (α : Type*) where
  box : Vault P o (Marks.all V)
  mark : α → Finset V
  sites : α → Support n
  heft i : (sites i).Nonempty
  roots i : ∀ v∈mark i, o v∈sites i
  bans : α → ℕ → Prop
  physical i j : bans i j → ∃ x∈sites i,x∈oldSites P j
  force : α → Config G n → ℂ
  borel i : Measurable (force i)
  law i : LocalOn (sites i) (force i)
  hue i : GaugeInvariant (force i)

namespace Grey
open Push.AbsoluteSums.Ursell Repeated  
variable (A : Grey P o α)
def black (i : α) (U) := Poly.send (Marks.mode (A.mark i)) (masked P.p.threshold (A.sites i) (A.force i) U)








def rare (p : Tuple α) := (nameSet A.mark p).Nonempty
abbrev Fielding := {p : Tuple α // A.rare p}

-- as an addressing type, includes collisions and untouched records

def charge (p : Tuple α) := Push.AbsoluteSums.Ursell.coefficient (blocked A.sites) p.2 / (p.1+1).factorial
def mounted (p : Tuple α) (U : Config G n) := if legal A.mark p then
    (A.charge p:ℂ) * ∏ i, A.force (p.2 i) U else 0

-- In particular includes p with all mark=empty


def reg : Atoms P.p (Marks.all V) o G A.Fielding where
  sites p := numbered A.sites p.val
  tag p := Marks.mode (nameSet A.mark p.val)
  H p := A.mounted p.val
  proper p := p.property
  pin p i hi := by
    have hx : ∃ j,i∈ A.mark (p.val.2 j) := by simpa [nameSet,Marks.mode] using! hi
    obtain ⟨j,hj⟩ := hx
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,A.roots _ _ hj⟩
  borel i := by
    unfold mounted; split; exact measurable_const.mul (Finset.measurable_fun_prod _ fun _ _ => A.borel _); exact measurable_const
  footprint p := by
    intro U W he; unfold mounted; split; swap; rfl
    exact congr_arg (HMul.hMul (A.charge p.val:ℂ)) <| Finset.prod_congr rfl
      (fun i hi => A.law _ U W (agrees_mono he (Finset.subset_biUnion_of_mem (fun j => A.sites (p.val.2 j)) hi)))
  gauge p t U := by unfold mounted; simp_rw [A.hue _ t U]









variable {w : V → ℝ}

-- includes all masked terms and blocked or unoccupied placements
structure Hits (M : ℕ) (a b : ℝ) (w : V → ℝ) : Prop where
  pos : 0 ≤ a
  small : 0 ≤ b ∧ 8*((M+M+1:ℕ):ℝ)^4*b ≤ 1
  controlled : ∃ g : α → ℝ, (∀ j,0 ≤ g j ∧ ∀ U,2*Poly.price w (A.black j U)≤g j) ∧ Ac.Hit A.sites M g (a+1) b

variable {M : ℕ} {a b : ℝ} {B : Finset ℕ} {U : Config G n}




end Grey
end YM.Further.ThresholdSourceRestart

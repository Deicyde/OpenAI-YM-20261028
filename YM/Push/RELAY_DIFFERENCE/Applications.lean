import YM.Next.EXTRACTION.Basis
import YM.Next.EXTRACTION.Relay
import YM.Push.RELAY_DIFFERENCE.Lanes

/-!
# Applying signed comparison estimates to the RelayCosts

No assumption of a relay bill/limit/derivative system as comparison input.

All comparisons operate at the literal finite normalized Family. w<d
re-presentations and the finite difference need their own encodings.

For a
mark, inputs on the ACTUAL cutoff-row space with hypotheses for any row
in the chosen projector kernel paid by `dollar`.

Note E.L.15617 case
specifically uses projection rows, but `D04` also uses projected parts
with costs tested after row scaling, so keep the stated scope.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Lattice Cells Marker Overlay Stock Bid Mix
open scoped Topology Matrix.Norms.Frobenius BigOperators
open Next.Extract
variable {G : Gauge} {C : Family G} {N p d : ℕ} {W : Worth} {f : Extraction.Order} {F : Trial C} {b : Presentation C}

/-- Shared requisites from prior producers, with C.Makes for links and
primary normalization. Use same Worth even if asking both e=d1 and e=d2. -/
structure Shop (C : Family G) (W : Worth) : Prop where
  simple : G.Simple
  frame : C.Makes
  tabs : Tabs C.path.levels
  floors : roomCost C.path.levels W
  book : Bank W C.path.levels

/-- All data about finite coefficients and unnormalized labelled source
representations on the SAME Wilson history.

`Prices` flexible (costs
before/after steps to be afforded on that same history).

Not a limit input. -/
structure Provisions (S : Solo C F d) (W : Worth) (f : Extraction.Order) : Prop where
  fees : S.Priced W f
  ensemble : ∃ P : Prices, Grids S P f ∧ ∀ᶠ i in atTop, P.buys C i

namespace Provisions
variable {S : Solo C F d}

/-- Version with dollar and quantitative rents. Use any fixed
`0 < γ < 1/8` for close. `every` strengthening to both kinds in Placement. -/
theorem complete (h : Shop C W) (H : Provisions S W f) (hF : Stencilled f F) :
    dollar C f S.row ∧ ∀ γ : ℝ, γ < gamma → CenterRents S.diff (flight C (-γ)) f := by
  obtain ⟨P,hP,hQ⟩ := H.ensemble
  have hc := grid_centers h.frame h.simple h.tabs hP H.fees h.floors h.book hQ hF
  exact ⟨H.fees.cost h.frame h.floors h.book, fun _ hγ => hc.earn h.frame (Solo.uniform_slow H.fees.initial)
    ((Stencilled.upper h.frame _).sub hF) hγ⟩




end Provisions

/-- At same weight no discrepancy; no paid array needed. -/
theorem constant_vet (h : C.Makes) (x : C.label d) : vet C f d (Bid.visits C d x) := by
  let P := Bid.visits C d x
  have ht : tight C f (fun _ : Cutoffs => x) := ⟨‖x‖,Eventually.of_forall fun _ => Eventually.of_forall fun _ => le_rfl⟩
  refine ⟨_,Work.D01.answer C h d f _ ht,fun _ _ => 0, tendsto_const_nhds,fun j m => ?_⟩
  refine ⟨m,le_rfl,Eventually.of_forall fun i => ?_⟩
  filter_upwards [f.mesh.cofinal.eventually_ge_atTop m] with k hk
  refine ⟨hk,fun T hT _ y hY => ?_⟩
  let N := f.mesh k; let p := f.per i
  have he (F : Config G (C.side N p) → ℂ) (ha : F=0) : Interior (T.chamber 0) F ∧ T.rootTest (C.beta N p) F ≤ 0 := by
    rw [ha]; refine ⟨Interior.constant _ 0,?_⟩
    have hv := Next.Extract.root_smul T (C.beta N p) F 0
    simp only [zero_smul,norm_zero,zero_mul] at hv; exact hv.le
  exact he _ (sub_self _)

/-- Inputs on D04's actual calls, incorporating equation partner from an
IBP producer for the same C. The matching equality is only a *finite*
reference coordinate equality: `S.row` is exactly the singleton entry
at the new weight ref. Could require it across all periods once N is
large; late is enough here. No reference retune after the call.
-/
structure Calls (b : Presentation C) (f : Extraction.Order) (W : Worth) (d : ℕ) : Prop where
  erase (x : Rowe C d) : (∀ j,b.step d j (x j) = 0) → dollar C f x →
    ∃ F : Trial C, Stencilled f F ∧ exactOnSep C f F ∧
      ∃ S : Solo C F d, (S.row =ᶠ[f.fuse] x) ∧ Provisions S W f
  lift (v : ℕ) : v < d → ∀ x : C.label v, ∃ S : Solo C (Bid.visits C v x) d, Provisions S W f
  farther (x : C.label d) (b : Axis) : ∃ S : Solo C (Bid.heighten C d x b) (d+1), Provisions S W f


end YM.Push.RelayDifference

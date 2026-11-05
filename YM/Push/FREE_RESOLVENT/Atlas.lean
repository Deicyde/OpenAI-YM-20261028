import YM.Push.FREE_RESOLVENT.Views

/-!
# Comparing stencils in different ambient spaces

Indexed, possibly rectangular matrices (even each leg on its own numbering
and with its own Ledger). Views always restrict to nonwrapping in their
*coarse positions*. Still charge all copies outside the geometry here in
the exponential prices when using full inverses. Plain germ congruence with
price-free arithmetic here; not standalone direction estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine.View
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set
open Work.F08 Lifted
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f f' c c' n : Side} {S : StepData c f} {r : ℕ} {s : Signed} {z : Cover} {P : Patch} {K : KernelChoices}
variable {ι κ μ X α β ξ : Type*}
variable {o : Site c} {o' : Site c'}

abbrev Atlas (c : Side) (ι α : Type*) := ι ≃ Co c α

def place (A : Atlas c ι α) (o : Site c) (z : Cover) (t : α) := A.symm (addr o z,t)
def position (A : Atlas c ι α) (x : ι) := (A x).1

lemma place_inject (A : Atlas c ι α) (o : Site c) {z v : Cover} {t u : α} (R : ℕ)
    (hp : size z ≤ R) (ht : size v ≤ R) (hr : 2*R<c.val) (h : place A o z t=place A o v u) :
    z=v ∧ t=u := by
  have he : (addr o z,t)=(addr o v,u) := A.symm.injective h
  refine ⟨?_,congr_arg Prod.snd he⟩
  have hh : wrap c z=wrap c v := add_left_cancel (congr_arg Prod.fst he)
  exact ((size_centers _ _ hp hr).symm.trans (congr_arg lift hh)).trans (size_centers _ _ ht hr)


-- Summation list here only covers a whole patch, used AFTER the data are
-- evaluated; no retrimming Gram in that patch.



section arithmetic
variable {X' ι' κ' μ' : Type*} [TopologicalSpace X]

/-- On one ambient space, near the chosen test, numerical support. -/
def Lives {n : Side} (a : ι → Site n) (b : κ → Site n) (R : ℕ) (F : X → Matrix ι κ ℝ) (x : X) : Prop :=
  ∀ i j, R < separation (a i) (b j) → (fun y => F y i j)=ᶠ[𝓝 x] (fun _ => 0)

-- All address coincidences are geometric, not period-independent Taylor input prices.
def Lines (x : X) (o : Site c) (o' : Site c') (A : Atlas c ι α) (A' : Atlas c' ι' α) (B : Atlas c κ β) (B' : Atlas c' κ' β)
    (F : X → Matrix ι κ ℝ) (F' : X → Matrix ι' κ' ℝ) (R : ℕ) := ∀ z v : Cover, size z ≤ R → size v ≤ R →
      ∀ (a : α) (b : β), (fun y => F y (place A o z a) (place B o v b)) =ᶠ[𝓝 x]
        fun y => F' y (place A' o' z a) (place B' o' v b)

variable {R r : ℕ} {x : X} {A : Atlas c ι α} {B : Atlas c κ β} {T : Atlas c μ ξ}
variable {F : X → Matrix ι κ ℝ} {G : X → Matrix κ μ ℝ} {H : X → Matrix ι κ ℝ}
variable {A' : Atlas c' ι' α} {B' : Atlas c' κ' β} {T' : Atlas c' μ' ξ}
variable {F' : X → Matrix ι' κ' ℝ} {G' : X → Matrix κ' μ' ℝ} {H' : X → Matrix ι' κ' ℝ}




namespace Lines
lemma lower (h : Lines x o o' A A' B B' F F' R) (hm : r ≤ R) : Lines x o o' A A' B B' F F' r :=
  fun z v hx hy => h z v (hx.trans hm) (hy.trans hm)
lemma add (h : Lines x o o' A A' B B' F F' R) (h' : Lines x o o' A A' B B' H H' R) :
    Lines x o o' A A' B B' (fun y => F y+H y) (fun y => F' y+H' y) R := fun z v hx hy a b =>
  (h z v hx hy a b).add (h' z v hx hy a b)

lemma scale (h : Lines x o o' A A' B B' F F' R) (k : ℝ) :
    Lines x o o' A A' B B' (fun y => k • F y) (fun y => k • F' y) R :=
  fun z v hx hy a b =>
    (show (fun _ : X => k)=ᶠ[𝓝 x] (fun _ => k) from EventuallyEq.rfl).mul (h z v hx hy a b)
lemma all (s : Finset ξ) {F : ξ → X → Matrix ι κ ℝ} {F' : ξ → X → Matrix ι' κ' ℝ}
    (h : ∀ i ∈ s, Lines x o o' A A' B B' (F i) (F' i) R) :
    Lines x o o' A A' B B' (fun y => ∑ i ∈ s, F i y) (fun y => ∑ i ∈ s,F' i y) R := by
  classical
  induction s using Finset.induction_on with
  | empty => intro z v hz hv a b; filter_upwards with x; simp
  | @insert i t he ih =>
    simp_rw [Finset.sum_insert he]
    apply Lines.add (h i (by simp)); exact ih (fun i hi => h i (by simp [hi]))




end Lines
end arithmetic













end YM.FreeResolvent.Affine.View

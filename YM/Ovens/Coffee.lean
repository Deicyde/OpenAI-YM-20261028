import YM.Ac.Tree
import YM.Pressure.Seeds


/-!
# Obligations for forced startup packets

Let IE differ by some already oriented, budgeted scalar-phase additions
paid by NewCap. For any *choice of compulsory output* `Pipes`, with those
same base E & Flags & Paths, glue a signed-coverage expansion of attachments
to an accountable gas. Evaluate at ANY U. Designed for E:, reusable
after P:Ctx, etc. There is no synthetic link-measure sigma here. Keep real
phases and probabilities outside. Need poses for C.K across forced Beta band.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Ovens
open Filter Function Set RG Wilson Lattice Supply Shoot Pressure
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators NNReal ENNReal
variable {G : Gauge} {n : Side}

/-- geometry skeleton path. Attachments with nonempty sets, occurring with an actual flag. -/
structure Pipes (G : Gauge) (n : Side) where
  reg : ℕ → RegularAddress n
  kernel : ℕ → ForcedAddress G n
  softer : ℕ → Support n
  sites i : (softer i).Nonempty

-- Let OLD be a proper labelled gas (disjoint, exact), even if K,F not both nonzero when accessed.
-- Extra attachments `logarithm` merged by exponential decomposition.
abbrev Code (G : Gauge) (n : Side) := ℕ → Config G n → ℝ
structure Tap (G : Gauge) (n : Side) where
  regular : Code G n
  forced : Code G n
  logarithm : Code G n

abbrev Label := ℕ⊕ℕ

def lefts (x : Finset Label) := x.toLeft

def rights (x : Finset Label) := x.toRight

namespace Pipes
variable (X : Pipes G n)

def pours (d : Tap G n) : Activities G n := ⟨X.reg,X.kernel,d.regular,d.forced⟩

def reach (d : Tap G n) (l : Label) (u : Config G n) := l.elim (fun i => d.forced i u) (fun i => Real.exp (d.logarithm i u)-1)

def patch : Label → Support n := Sum.elim (fun i => (X.kernel i).support) X.softer

def skin (s : Finset Label) : Support n := s.biUnion X.patch

def plot (s : Finset Label) := (lefts s).biUnion fun i => (X.kernel i).inventory

-- (Can use old K.Learns.e directly)
def contains (s : Finset Label) := (lefts s).Nonempty ∧
    Ac.Spark X.patch s ∧ ((lefts s:Set ℕ)).Pairwise (fun i j => Disjoint (X.kernel i).support (X.kernel j).support)

abbrev Pellet := {s : Finset Label // X.contains s}
lemma plot_ne (p : X.Pellet) : (X.plot p).Nonempty := by
  obtain ⟨i,hi⟩ := p.property.1
  obtain ⟨j,hj⟩ := (X.kernel i).inventory_ne; exact ⟨j,Finset.mem_biUnion.mpr ⟨_,hi,hj⟩⟩
lemma plot_sub (p : X.Pellet) : X.plot p⊆X.skin p := by
  intro i hi; obtain ⟨j,hj,hq⟩ := Finset.mem_biUnion.mp hi
  exact Finset.mem_biUnion.mpr ⟨Sum.inl j,by simpa [lefts] using hj,(X.kernel j).inventory_sup hq⟩

variable {X} (F : ℕ ≃ X.Pellet)

def condition (P : BudgetPoint) (i : ℕ) (U : Config G n) := ∀ j∈lefts (F i).val,(X.kernel j).eligible P.threshold U

def addr (P : BudgetPoint) (i : ℕ) : ForcedAddress G n := ⟨X.skin (F i),X.plot (F i),X.plot_ne (F i),X.plot_sub (F i), condition F P i⟩

open scoped Classical in
def solid (P : BudgetPoint) (d : Tap G n) (i : ℕ) (U : Config G n) := if (addr F P i).eligible P.threshold U then
    ∏ j∈ (F i).val,reach d j U else 0

def fused (P : BudgetPoint) (d : Tap G n) : Activities G n := ⟨X.reg,addr F P,d.regular,solid F P d⟩

variable (X)
structure Digests (t : Tap G n) (P : BudgetPoint) (δ b : ℝ) : Prop where
  stamp : (X.pours t).Valid P δ b
  visits i : ∀ U : Config G n,t.logarithm i U≠0 → ¬Healthy P.threshold (X.softer i) U
  pays : Dominated t.logarithm
  steady i : Lattice.GaugeInvariant (t.logarithm i)
  looks i : UsesFinal P.threshold (X.softer i) (t.logarithm i)
  reads i : Measurable (t.logarithm i)
  carries (s : Signed) (b : Site n) : ∃ v : Equiv.Perm ℕ,
    (∀ i, X.softer (v i) = (X.softer i).image (affine s b)) ∧
    ∀ U i, t.logarithm (v i) U=t.logarithm i (pull s b U)

/-- extra exponent one even at top (use H_j). Reserves: here f matrix independent i.
            prim packets can be given λ=p_*^2µ. Price EXPLICIT. -/
structure Buys (t : Tap G n) (P : BudgetPoint) (κ γ : ℝ) : Prop where
  margin : 0 ≤ γ ∧ 0≤κ ∧ (P.B+P.B+1:ℕ)^4*γ ≤ 1
  certificate : ∃ f : Label → ℝ,(∀ i, 0 ≤ f i) ∧ (∀ i U,
    |reach t i U| ≤ i.elim (fun _ => Real.exp (-κ)) (fun _ => 1)*f i) ∧
      Ac.Hit X.patch P.B f (P.supportExponent+1) γ

/-- continuum in β; no continuity of flag surfaces in field, only prices.

Not needed for projection proof.

Root.K clock intercept. -/
def invariantJet (_ : BudgetPoint) (f : ℝ→Tap G n) (x : Set ℝ) : Prop :=
    ∀ a ∈ x, ∀ j,∀ ε : ℝ, 0<ε → ∀ᶠ b in nhdsWithin a x,
        ∀ U, |reach (f b) j U - reach (f a) j U| ≤ ε

def little (P : BudgetPoint) (f : ℝ→Tap G n) (x : Set ℝ) :=
    ∃ κ γ c,(P.B+P.B+1:ℕ)^4*γ ≤ (1:ℝ) ∧ 0≤γ ∧ (0:ℝ)≤κ ∧ (∀ i, 0≤c i) ∧ (∀ a∈x,∀ i U,
    |reach (f a) i U| ≤ i.elim (fun _ => Real.exp (-κ)) (fun _ => 1)*c i) ∧
        Ac.Hit X.patch P.B c (P.supportExponent+1) γ

variable {X}
def retakes (F : ℕ≃ X.Pellet) (P : BudgetPoint) (f : ℝ→Tap G n) (x : Set ℝ) := ∀ a∈x, ∀ ε : ℝ,0 < ε →
    ∀ᶠ b in nhdsWithin a x,∃ g : ℕ → ℝ, (∀ i,0≤g i) ∧ (∀ U i, ‖solid F P (f a) i U-solid F P (f b) i U‖≤g i) ∧
      SumBudget (fun i => P.mass (addr F P i).support (g i)) ε

variable (X)

lemma encoding : Nonempty (ℕ≃X.Pellet) := by
  classical
  haveI : Infinite X.Pellet := by
    let f := fun i : ℕ => ({Sum.inl i}:Finset Label)
    have he i : X.contains (f i) := by
      constructor
      · exact ⟨i, by simp [f,lefts]⟩
      refine ⟨⟨by simp [f],?_⟩,?_⟩
      · simp only [f,Finset.mem_singleton]; intros v hv q hq; rw [hv,hq]; exact .refl
      simp [f,lefts,Set.Pairwise]
    refine Infinite.of_injective (fun i : ℕ => (⟨f i,he i⟩ : X.Pellet)) (fun i j h => ?_)
    have h' := congr_arg Subtype.val h; simpa [f] using h'
  obtain ⟨d⟩ := nonempty_denumerable X.Pellet; exact ⟨(Denumerable.eqv X.Pellet).symm⟩
end Pipes
end YM.Ovens

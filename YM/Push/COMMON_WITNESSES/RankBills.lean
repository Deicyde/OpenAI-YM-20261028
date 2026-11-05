import YM.Push.COMMON_WITNESSES.Orders

/-!
# Per-family finite rank bills and their transport

Our contribution here isn't `Kroot`, i.e., obtaining the bills *physically*,
but turning bills with finite arity, weights and regulators on compatible
stations into the required common input. In particular instead of asking already `Y.Valid` under
some order for each d, we'll split out the finite estimates from the extraction
and continuum components. No existence assertion without exact hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Filter Function Set Extraction Wilson Next.Extract Cells
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {d : ℕ} {T : Table C.book}
variable {X : Columns C T d} (Y : X.Trials)

/-- The proposed **same** detector family for all k, with gap, widths,
depths, scale, marks and actual lift coordinates, but not claiming any
estimates on the law yet. `later` in Y is IRRELEVANT until the end of the
procedure, when it will be filled by ordered extraction from the lifts.
E comparison scale  in the allowed interpretation of `Valid`.
In particular gap is nonnegative with limit zero, marks tuned to the
actual prescribed limiting rescaled tests (one or two slots), weight
bound d fixed, exact unit. -/
structure Setup : Prop where
  ratios : ∃ b : ℝ, 0 < b ∧ ∀ k, Y.scale k = C.S.a (Y.depth k) * ((C.path.levels.clock.monitor (Y.depth k))^b)
  same_stage k m (hq : Y.width k ≤ m) (hN : m ≤ Y.depth k) :
    C.path.levels.clock.J m=C.path.levels.clock.J (Y.depth k)
  scale_down : StrictAnti Y.scale
  conjugate (k N p i) : star (Y.lift k N p i) = Y.lift k N p i
  unit (k N p) : Y.lift k N p 0 = C.refUnit d
  tuned i : Tendsto (fun k => Y.tested k i) atTop (𝓝 (X.row i).expected)
  seams : ∃ η : ℝ, 0 < η ∧ ∀ k i j a,
    |Y.realPlace k i j a| ≤ C.S.a (Y.width k)*((2:ℝ)⁻¹-η)
  generic (k i) : Y.realPlace k i ∈ YM.generic _

variable (b : Presentation C) (f : Order)

/-- Finite upper numerical rank bound on the comparison projections of
RBin. Intended only if at base with `Projected b` and `Base` identifying
that Bin's kernel with the null space. Will give an exact scope test there as
well; doesn't ask for extra uniformity in d or period. -/
def SizeBill (X : Columns C T d) : Prop :=
  f.late fun N p => Module.finrank ℂ (LinearMap.range (b.step d (N,p)).toLinearMap) ≤ X.dim+1

/-- Input: uniform A k BEFORE picking p, asking just on each mesh tail not
all cutoffs. Observe these bills on one common mesh extraction ALSO give
sufficient outer compactness. No prior assumption of any `responds` limits. -/
def LiftBill (k p : ℕ) (A : ℝ) : Prop :=
  ∀ᶠ j : ℕ in atTop, ∀ i, ‖Y.lift k (f.mesh j) p i‖ ≤ A

/-- Input for now: true corrected root bound on ordered regulator tails, for
**one k and tolerance**, same specified budget `gap`. Real normalized
`rootTest` uses the full reflected tilings with hand/star convention; all
nonempty subsets asked here. `subtract1` = `F-a`, `subtract2` =
`(F-a)(G-b)-c` (even for repeated labels at distinct slots), c free *second
cumulant*, rounded scale. No terrain of estimates on moments with coincident
points is assumed. -/
def CheapBill (k : ℕ) (ε : ℝ) : Prop :=
  f.late fun N p => ∃ h : Y.depth k ≤ N,
    let Z := center C.S p ((Y.window k).trans h) 0
    ∀ i c s,
      Interior (Z.chamber 0) (Y.weigh k N p i c s) ∧
      Z.rootTest (C.beta N p) (Y.subtract1 k N p i c s) ≤ Y.gap k + ε ∧
      ∀ t, s<t → Z.rootTest (C.beta N p) (Y.subtract2 k N p i c s t) ≤ Y.gap k + ε

/-- One request (none = rank, false = norm, true = root). Norm across all
basis labels for X *only*, finite. Each d can have its own cost. -/
def rankInvoice (A : ℕ → ℝ) : Option (Bool × ℕ × ℕ) → Order → Prop
  | none, u => SizeBill b u X
  | some (false,k,p), u => LiftBill Y u k p (A k)
  | some (true,k,l), u => CheapBill Y u k (toll l)

lemma pay (A : ℕ → ℝ) (i) {f g : Order} (h : Tails g f) (w : rankInvoice Y b A i f) : rankInvoice Y b A i g := by
  rcases i with _|⟨e,k,p⟩
  · unfold rankInvoice SizeBill at *
    exact h.late w
  cases e
  · exact h.mesh.holds (fun N => ∀ i, ‖Y.lift k N p i‖ ≤ A k) w
  unfold rankInvoice CheapBill at *
  exact h.late w



abbrev ProbeID (X : Columns C T d) := ℕ × Fin (X.dim+1)


/-- Both-stage coordinate receipt, even `z` on every p kept. This and the
bills will give Valid. -/
abbrev Response (z : ProbeID X → ℕ → C.label d) : Prop := Keeps (X:=fun _=>C.label d)
  f (fun (_ : ProbeID X) _ => True) (fun ⟨k,i⟩ N p => Y.lift k N p i) z (fun ⟨k,i⟩ => Y.later k i)

def decoded (y : ProbeID X → C.label d) : X.Trials := { Y with later := fun k i => y (k,i) }


end YM.Push.Common

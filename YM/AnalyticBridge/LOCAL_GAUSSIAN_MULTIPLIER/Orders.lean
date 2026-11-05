import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Exponent
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Tariff

/-!
# Per-entry bills in a common kernel evaluation ⇒ one multiplier bill

Pointwise analytic algebra for the CURRENT label supports.
`Reading` later instantiates `Varying`'s three functions (`Reading.ret`, compulsory logs and logarithms of still-direct Mayer factors).
No continuity prediction about a tag, nor claiming any setting of the
budgets relative to the upstream steps.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice Wilson RG Next.SectorChange Next.SectorChange.Gaussian Moments
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators RealInnerProductSpace ContDiff

variable {α β γ ι : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι] [DecidableEq β]
    {b : Tariff α β γ ι}

/-- The three classes of multiplier factors. Logs are log letters at
`kept` and pre-Mayer value at `optional`. Other selected gates (e.g.
the mandatory broad patches of a region) at `first` directly.
Do not rearrange signed K/gas as logs.
-/
structure Varying (α β γ P : Type) where
  first : α → P → ℝ
  kept : β → P → ℝ
  optional : γ → P → ℝ

namespace Varying
variable {X : Type} (p : Varying α β γ X)
def beginning : X → ℝ := ∏ i, p.first i
def closure : X → ℝ := Real.exp ∘ (∑ i,p.kept i)
def list : X → ℝ := ∏ i, ((Real.exp ∘ p.optional i)-1)
def volumeMark : X → ℝ := p.beginning*p.closure*p.list
end Varying

namespace Tariff
variable {X : Type}
def committed (b : Tariff α β γ ι) (z : Vec ι) := Real.exp (b.value + ∑ i∈b.coreᶜ,b.invoice i z)

/-- In particular may be buying no derivative on a flagged-output
sector. Does NOT implicitly infer `Earn` from prices on a
preselected Store with certain untouched global profiles. Consume at
this point (after proving whether prerequisite guards remain). -/
structure Earn (p : Varying α β γ X) (x : X) (b : Tariff α β γ ι) (z : Vec ι) : Prop where
  here i : ‖p.first i x‖ ≤ b.portal i z
  kids i : ‖p.optional i x‖ ≤ b.quota i z
  home : ∑ i∈b.core,p.kept i x ≤ b.value
  after : ∀ i:β,i∉b.core → p.kept i x ≤ b.invoice i z
  extra : b.Event z

namespace Earn
variable {p : Varying α β γ X} {x : X} {z : Vec ι}
omit [Fintype α] [Fintype γ] [Fintype ι] in
lemma aggregate (h : Earn p x b z) : p.closure x ≤ b.committed z := by
  unfold Varying.closure Function.comp
  apply Real.exp_monotone
  rw [Finset.sum_apply,← Finset.sum_add_sum_compl]
  exact add_le_add h.home (Finset.sum_le_sum fun i hi => h.after i (Finset.mem_compl.mp hi))

end Earn

variable {G : Gauge} {n : Side}

/-- A point calculus test (all the estimates AT ONCE). f,p refers
later to Extended/Shelter; in particular not dropping a charge because
some coordinates participate in several parents. `z` can be a different
reference Z (for tag stability); must then pass *these* stronger
cross tests. The ordinary use is always with the single law's Z.
-/
structure Stack (p : Varying α β γ (Config G n)) (D : Directions G n → Prop) (k : ℕ) (V : Config G n)
    (b : Tariff α β γ ι) (z : Vec ι) : Prop extends Earn p V b z where
  first i : Ticket D k V (b.portal i z) (b.grow z) (p.first i)
  allKept i : Charge D k V (b.grow z) (p.kept i)
  priced i : Ticket D k V (b.quota i z) (b.grow z) (p.optional i)

def mainRate (α β γ : ℕ) (k : ℕ) : ℝ := α + ((k:ℝ)+1)*((β:ℝ)+1) + ((γ:ℝ)*((k:ℝ)+1)*2)

def across (α β γ : ℕ) (k : ℕ) (r : ℝ) : ℝ := mainRate α β γ k*r^2

namespace Stack
variable {p q : Varying α β γ (Config G n)} {D : Directions G n → Prop}
    {k : ℕ} {V : Config G n} {z : Vec ι}

omit [Fintype β] [DecidableEq β] [Fintype γ] in
lemma fronts (h : Stack p D k V b z) : Ticket D k V (∏ i, b.portal i z) (Fintype.card α*b.grow z) p.beginning := by
  convert! Ticket.stack (fun i _ => h.first i) using 1; simp

lemma beams (h : Stack p D k V b z) (he : b.Lease) : Charge D k V ((Fintype.card β+1)*b.grow z) (∑ i,p.kept i) := by
  have ht := Charge.total (I:=Finset.univ) fun i _ => h.allKept i
  apply ht.radius
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  linarith only [he.pays_grow z]

lemma ceiling (h : Stack p D k V b z) (he : b.Lease) : Ticket D k V (b.committed z) (climbing k ((Fintype.card β+1)*b.grow z)) p.closure :=
  (h.beams he).bill_exp h.toEarn.aggregate

lemma quota_le (_h : Stack p D k V b z) (he : b.Lease) (i : γ) (k : ℕ) :
    climbing k ((1+b.quota i z)*b.grow z) ≤ climbing k (2*b.grow z^2) := by
  have hr := he.pays_grow z
  have hl := he.born i z
  unfold climbing
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  nlinarith only [hr,hl]

lemma last (h : Stack p D k V b z) (he : b.Lease) (i : γ) :
    Ticket D k V (b.slide i z) (climbing k (2*b.grow z^2)) ((Real.exp ∘ p.optional i)-1) :=
  ((h.priced i).mayer).mono (he.earmark i z) (h.quota_le he i k)

lemma tails (h : Stack p D k V b z) (he : b.Lease) : Ticket D k V (∏ i,b.slide i z) (↑(Fintype.card γ) * climbing k (2*b.grow z^2)) p.list := by
  convert! Ticket.stack (fun i _ => last h he i) using 1; simp

lemma rateEnough {a e f : Type} [Fintype a] [Fintype e] [Fintype f]
    (x : Tariff a e f ι) [DecidableEq e] (z : Vec ι) (he : x.Lease) (k : ℕ) :
    (Fintype.card a*x.grow z)+ climbing k ((Fintype.card e+1)*x.grow z) +
        (↑(Fintype.card f) * climbing k (2*x.grow z^2)) ≤ across (Fintype.card a) (Fintype.card e) (Fintype.card f) k (x.grow z) := by
  let A := (Fintype.card a:ℝ); let B := (Fintype.card e:ℝ); let C := (Fintype.card f:ℝ)
  let r := x.grow z; let u : ℝ := k+1
  have hi : 1≤ r := he.pays_grow z
  have hf : r ≤ r^2 := by nlinarith
  change A*r + u*((B+1)*r) + C*(u*(2*r^2)) ≤ (A+u*(B+1)+C*u*2)*r^2
  rw [add_mul _ (C*u*2) (r^2),add_mul A _ (r^2),show C*(u*(2*r^2))=C*u*2*r^2 by ring, ← mul_assoc u (B+1)]
  have ha : 0 ≤ A := Nat.cast_nonneg _
  have hu : 0 ≤ u := by unfold u; positivity
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hf ha) (mul_le_mul_of_nonneg_left hf (mul_nonneg hu (by unfold B; positivity)))) le_rfl

lemma buy (h : Stack p D k V b z) (he : b.Lease) : Ticket D k V (b.codex z) (across (Fintype.card α)
    (Fintype.card β) (Fintype.card γ) k (b.grow z)) p.volumeMark :=
  (((h.fronts.mul (h.ceiling he)).mul (h.tails he))).mono (he.paid z h.extra) (rateEnough b z he k)
end Stack
end Tariff
end YM.AnalyticBridge.LocalGaussian

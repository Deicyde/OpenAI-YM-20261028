import YM.AnalyticBridge.RESET_INCOME_PORT.Split
import YM.SectorNext.VACUUM_NORMALIZATION.Bulk


set_option warningAsError false

/-!
# Head reassembled at the Income probes (local test version)

Optional, sometimes preferable to raw coupons in `Split`. A quite different
regime: only after spending the ACTUAL component estimates on an allocation
regrouping. Not assuming the log identity on the head: terms issued on
`sleeves` and spent per (first gas) address using this normalization. Prove
the local-to-extensive and log implications. STILL requires numerical
estimates and the regrouping data to be same-family, incl winds and flags.

In applications use on each all-good probe. Keep *every* address even
zeros, and prove (not asserted here) the emission and recombination of
localized integrals exactly with the masks, predicates and tags of that
regrouping. No assumption all stores can be localized separately from
independent tag sections. Profile-complement cancellations may be internal
to this assembly. The log is that of genuine positive deletion evaluations
after assembling the signed integrals; masked/dead logs outside those tests
are not used. NOT an application-ready physical price theorem, not claiming
that a uniform Share bound holds or that dropping any complement in this
regime is free. No hypothesis `Income` or `Split` here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome

open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Next.SectorChange UVNext.CouplingReset Input RG.Supply RG.Shoot Pressure.Testing
open SectorNext.Vacuum.ReLog
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {e : Plate G S} {R : Rep G f} {V : Config G c} {κ u δ : ℝ}

/-- `flight` is removed from the head exponent (still needs its own
forecast/local error estimates vs beta,alpha,loop). Normalize components to
THIS, inside the common ledger. No claims that claims below could be issued
for arbitrary flight, nor buying the unmarked estimates by a vacuum lower
bound in a different currency. -/
structure HeadGas (e : Plate G S) where
  chosen : Finset (Stores S)
  flight : Config G c → ℝ
  reads : ℕ → Support c
  atoms : ℕ → Config G c → ℝ
  slips (A : Stores S) : Config G c → S.Choices → Finset ℕ → (e.Sample A → ℝ)

namespace HeadGas
variable (d : HeadGas e)

/-- Only on matches; recombining on the actual V would need proving the
zero case wasn't improperly used. -/
def receive (R : Rep G f) (A : Stores S) (V : Config G c) (k : S.Choices) (J : Finset ℕ) := if e.matched A V then
    Real.exp (e.cost R A V k-d.flight V)*(∫ z, d.slips A V k J z ∂ (e.law A V k)) else 0

/-- Balance per address. Permit even integration-variable-change differences
already INSIDE the emission (e.g., summing two profile partners against the
stated true marginal); no assertion of absolute bound / costing from this
alone. See `Handover` for one straightforward source of the first proof via
pointwise-integrand reconstruction. -/
structure Balance (R : Rep G f) (V : Config G c) : Prop where
  leg A : A∈d.chosen → e.matched A V → ∀ k,
    (∀ J, Integrable (d.slips A V k J) (e.law A V k)) ∧
      HasSum (fun J => ∫ z, d.slips A V k J z ∂ (e.law A V k)) (∫ z,e.color R A V k z ∂ (e.law A V k))
  enters J : ∑ A ∈ d.chosen, ∑ k, d.receive R A V k J =
      note d.reads (fun i => d.atoms i V) Finset.univ J

/-- Check summability before reordering or evaluating the cluster sums.
This stronger version requires actual summability even in L¹. -/
structure Handover (R : Rep G f) (V : Config G c) : Prop where
  entry A : A∈d.chosen → e.matched A V → ∀ k,
    (∀ J, Integrable (d.slips A V k J) (e.law A V k)) ∧
      Summable (fun J => ∫ z, ‖d.slips A V k J z‖ ∂ (e.law A V k)) ∧
      ∀ᵐ z ∂ (e.law A V k), HasSum (fun J => d.slips A V k J z) (e.color R A V k z)
  part J : ∑ A ∈ d.chosen, ∑ k, d.receive R A V k J =
      note d.reads (fun i => d.atoms i V) Finset.univ J



lemma Balance.collected (h : d.Balance R V) : let Z := fumes d.reads (fun i => d.atoms i V) Finset.univ
    e.head R V d.chosen = Real.exp (d.flight V)*Z := by
  intro Z
  have hx A (ha : A∈d.chosen) k : HasSum (d.receive R A V k) (Real.exp (-d.flight V)*e.value R A V k) := by
    unfold receive Plate.value
    split <;> rename_i he
    · rw [←mul_assoc, ← Real.exp_add, add_comm, ← sub_eq_add_neg]
      exact ((h.leg A ha he k).2).mul_left _
    simp
  have hw := hasSum_sum (f:=fun A j => ∑ k, d.receive R A V k j) (fun A (hv : A∈d.chosen) =>
    hasSum_sum (s:=Finset.univ) (fun k hh => hx A hv k))
  simp_rw [h.enters,← Finset.mul_sum] at hw
  change HasSum _ (Real.exp _ * e.head R V _) at hw
  unfold Z fumes; rw [hw.tsum_eq, ← mul_assoc, ← Real.exp_add,add_neg_cancel, Real.exp_zero,one_mul]

/-- Local prices still to produce at honest supports. At V with external
flags, these tags include hypothetical unmasked extensions on their *own*
domains (not asserting reconstruction there). Some constructions may have
to retain stricter near-root supports to make those proofs with `reads`. -/
structure Token where
  wages : ℕ → ℝ
  width : ℝ
  quota : ℝ
  rate : ℝ

structure Token.Paid (hd : Token) (d : HeadGas e) : Prop where
  tags : Tags d.reads e.point d.atoms hd.wages
  hit : Fund d.reads e.point.B hd.width hd.quota hd.rate hd.wages

def press (V : Config G c) := ∑ i : Support c, raw d.reads d.atoms i V



lemma receive_log {t : Token} (ht : t.Paid d) (hV : RG.flags e.point.threshold V = ∅) (h : d.Balance R V) :
    e.head R V d.chosen = Real.exp (d.flight V - d.press V) ∧ |d.press V| ≤ sites c * t.quota := by
  have hi := intake d.reads ht.tags _ ht.hit
  let L (i : Support c) := locked d.reads e.point d.atoms i V
  let Z := fumes d.reads (herald d.reads e.point d.atoms V)
  have hx : (Finset.univ : Support c).powerset = Finset.univ := by ext; simp
  have hp : Z Finset.univ = Real.exp (- ∑ i,L i) := by rw [←hx]; exact (hi.2.2.2 V Finset.univ).2.1
  have hk (i : Support c) : L i = raw d.reads d.atoms i V := masked_eq _ _ _ _ (by simp [Healthy,hV])
  have hf : herald d.reads e.point d.atoms V = (fun i => d.atoms i V) := funext (fun i => masked_eq _ _ _ _ (by simp [Healthy,hV]))
  have he := h.collected d
  simp_rw [hk] at hp
  constructor
  · rw [he, ← hf, show fumes d.reads _ Finset.univ = _ from hp, ← Real.exp_add,←sub_eq_add_neg]; rfl
  have hh := extensive d.reads ht.tags _ ht.hit V
  change ∑ i, |L i| ≤ _ at hh; simp_rw [hk] at hh
  exact (Finset.abs_sum_le_sum_abs _ _).trans hh

lemma base_load {t : Token} (ht : t.Paid d) (hV : RG.flags e.point.threshold V=∅) (hR : e.Receipt R)
    (h : d.Balance R V) : let r := e.outside R V + d.flight V
    (∑ A∈d.chosen, cutEntry e.book e.forest e.tube R A V) = Real.exp (r-d.press V) ∧
      |d.press V| ≤ sites c*t.quota := by
  intro r; obtain ⟨hf,hv⟩ := d.receive_log ht hV h; refine ⟨?_,hv⟩
  rw [Plate.cut_sum hR, hf,← Real.exp_add]; unfold r; congr 1; ring


end HeadGas
end YM.AnalyticBridge.ResetIncome

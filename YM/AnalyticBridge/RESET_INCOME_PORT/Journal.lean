import YM.AnalyticBridge.RESET_INCOME_PORT.HeadGas
import YM.Next.MULTISOURCE.Germs
import YM.Next.UV_STRESS.Dimension
import YM.Next.UV_STRESS.SpanQ
import YM.UVNext.COUPLING_RESET.Regular


set_option warningAsError false

/-!
# All-good reassembly to an early activity family of CouplingReset

An option for when the larger per-label (but local!) receipts from the
allocation and second log are available. The estimate on the *jets of the
difference* is separate and important: prices which would pay logs at a
first reorganized gas need NOT pay this. Keep wind/address supports at
`reg` through that match. Nothing about actually producing these receipts
on this history, and final template/E/forced bookkeeping remains extra.
See the report regarding earlier separation/indicator corrections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome

open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Next.SectorChange UVNext.CouplingReset Input RG.Supply RG.Shoot Pressure.Testing
open SectorNext.Vacuum.ReLog Multi.Puff
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {e : Plate G S} {R : Rep G f} {V : Config G c} {κ u δ : ℝ}

/-- `glass` are local-log columns routed (possibly split,
use absolute convergence) after the *exact* head assembly.

`fixes` are
pre-reset alignment terms, including the residual common scalar and the
prediction at α * secondTerm.

No new beta present.

Reg support is at full
price, and derivatives at the same BudgetPoint.

Forced fields can be filled
arbitrarily here only because Prereset tests unforced values only; this
Journal isn't a full-output split, not claiming its issued Activities are a
`Valid` trial of Reset. -/
structure Journal (e : Plate G S) where
  gas : HeadGas e
  origin : ℕ → Support c
  reg : ℕ → RegularAddress c
  delivery i : origin i ⊆ (reg i).support
  glass : ℕ → Config G c → ℝ
  fixes : ℕ → Config G c → ℝ
  obliged : ℕ → ForcedAddress G c
  payload : ℕ → Config G c → ℝ

namespace Journal
variable (j : Journal e)

def prints : Activities G c := ⟨j.reg,j.obliged,fun i => j.glass i+j.fixes i,j.payload⟩

/-- `cc`: forecast function (ell(V) = u*sites-prediction(V)), full log
units. No target present on the RHS of `curse`: a scattering of just the
outstanding orbit terms, ledger differences etc AFTER the gas direction
`flight`, not buying their post-cancellation estimates from any unrelated
criterion. Each column must supply true smooth local error estimates (see
Rates); exports absolute results for all-good, not attempting to do flag
attachments. Require log pieces conservatively issued per full support from
the same atoms, on the domain of actual prices. This version uses
Healthy(original) to pair their sum; `glass/fixes` derivatives and final E
readings use full destination support, with genuine extensions at its
boundary. For use at all-good, census equality need only hold there, but
don't use price facts obtained by masks coinciding only on an interior. -/
structure Read (R : Rep G f) (cc : Config G c → ℝ) (t : HeadGas.Token) : Prop where
  full : j.gas.chosen=Finset.univ
  token : t.Paid j.gas
  ballet (V : Config G c) : RG.flags e.point.threshold V=∅ → j.gas.Balance R V
  census (P : Support c) V : Healthy e.point.threshold P V →
    HasSum (fun i => if j.origin i=P then j.glass i V else 0) (raw j.gas.reads j.gas.atoms P V)
  curse V : RG.flags e.point.threshold V=∅ → HasSum (fun i => j.fixes i V) (cc V-e.outside R V-j.gas.flight V)

/-- Support-priced cancellation in orders (not assuming EBound). These
are local quantitative inputs and also need authentic regularity on the
actual formulas comparing them (not differentiating indicators). -/
structure Rates (b : ℕ → ℝ) (δ : ℝ) : Prop where
  prime i : e.point.Regular (j.reg i).support (j.glass i)
  added i : e.point.Regular (j.reg i).support (j.fixes i)
  nonneg i : 0 ≤ b i
  jets i U : Healthy e.point.threshold (j.reg i).support U → ∀ l, List.length l ≤ e.point.order →
      (∀ A∈l, e.point.dirBound (j.reg i).site A) → ‖leftDerivs (j.glass i) l U + leftDerivs (j.fixes i) l U‖ ≤ b i
  budget x : SumBudget (fun i => if (j.reg i).site=x then e.point.mass (j.reg i).support (b i) else 0) δ

lemma Rates.earns {b : ℕ → ℝ} (h : j.Rates b δ) : j.prints.EBound e.point δ := by
  refine ⟨b,fun i => ⟨h.nonneg i,fun V hv l hl he => ?_⟩, h.budget⟩
  unfold prints; dsimp only
  rw [Crest.sum_at l hl V (into _ _ ((h.prime i).smooth V hv)) (into _ _ ((h.added i).smooth V hv))]
  exact h.jets i V hv l hl he



variable {cc : Config G c → ℝ} {t : HeadGas.Token}
lemma Read.merged (h : j.Read R cc t) (hV : RG.flags e.point.threshold V=∅) :
    j.prints.additive e.point V = j.gas.press V + (cc V-e.outside R V-j.gas.flight V) := by
  have ht : HasSum (fun i => j.glass i V) (j.gas.press V) := by
    have hh P := h.census P V (by simp [Healthy,hV])
    simpa [HeadGas.press] using (hasSum_sum (s:=Finset.univ) (fun i hi => hh i))
  have hu (i : ℕ) : j.prints.regularOccurrence e.point i V=j.glass i V+j.fixes i V :=
    masked_eq _ _ _ _ (by simp [Healthy,hV])
  unfold Activities.additive; simp_rw [hu]; exact (ht.add (h.curse V hV)).tsum_eq

lemma emits (h : j.Read R cc t) (he : e.Receipt R) (hV : RG.flags e.point.threshold V=∅) :
    (∑ A : Stores S, cutEntry e.book e.forest e.tube R A V) = Real.exp (cc V - j.prints.additive e.point V) := by
  rw [← h.full,(j.gas.base_load h.token hV he (h.ballet V hV)).1,h.merged j hV]
  congr 1; ring




end Journal

section live
variable {b : Sheet G} {D : Rolls b} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Directed G I Z K P)
    {s : Set ℝ} {g a E : ℕ → ℕ → ℝ} {N m p : ℕ}

/-- Consume in the financially issued Directed. Pre-reset valuation /
projection comparisons would prove `Read.curse` and `Rates` etc on these
same data, not by choosing a new flight after a beta correction. In
particular the proposed u is in per-site OUTPUT units. -/
theorem prepares (hW : Ringing K g W) (hc : Cosmos Z K W g a E) (hm : m < N) (Q : UVNext.CouplingReset.In B.a m p)
    (hL : ∀ x∈s, Lives B.bake N (m+1) p (Q x)) (hb : ∀ x∈s,(Q x).beta∈band B.a (m+1))
    (F χ u k) (q : ResetPrices) :
    let e := assigned B N m p g a F χ u k
    ∀ (J : ℝ → Journal e) (v : ℝ → ℝ) (t : ℝ → HeadGas.Token) (l : ℝ → ℕ → ℝ),
      (∀ x∈s,(J x).Read (Q x) (fun V => v x * sites (B.a.S.side m p) - demand B N (Q x) V) (t x)) →
      (∀ x∈s,(J x).Rates (l x) (funds B.a m q / 4)) → Prereset B q s N m p Q v (fun x => (J x).prints) := by
  intro e J v t l hT hJ; refine ⟨fun x hx => (hJ x hx).earns _,fun x hx V hv => ?_⟩
  have hp := purchased B F χ u k hW hc hm (Q x) (hL x hx) (hb x hx)
  obtain ⟨_,_,_,_,_,_,_,κ,_,H⟩ := committed B hW hc N m p hm (Q x) (hL x hx) (hb x hx)
  have ht := (H u F χ).1.total
  unfold target; rw [ht V]; exact (J x).emits (hT x hx) hp hv
end live
end YM.AnalyticBridge.ResetIncome

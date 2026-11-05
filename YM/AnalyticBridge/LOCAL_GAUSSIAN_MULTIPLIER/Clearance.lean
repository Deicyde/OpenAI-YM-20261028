import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Score

/-!
# Preflight: EVERY prerequisite at the same snapshot

Inputs about components refer to (1) Needed (their closed chart test)
(2) kernel estimates on this *marginal* of the given fog/protocol and a
single set of anchor directions (3) support survival of every named gate
at this point, even near a differentiated zero (4) row action estimate,
only on genuinely retained residual rows after the indicated subtractions.

Preflight before paying products. For producers of (3), may have to keep
all test/assignment guards with that word, even where the tag likelihood
is zero or fallback Q is selected. Don't identify it with Plot tests on the
unopened multiplier, nor assume the joint estimates just from separately
integrated sector/det bills. See guard constructors later.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision MeasureTheory Next.SectorChange Next.SectorChange.Gaussian
open Next.SectorChange.Rows YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open Curtain Tariff Spot.Programme Spot Notice
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S} {u : Spot d}
  {H R K α β γ : Type} [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R]
  [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
  {X : Support c} {l : Viewport u X H R K} {D : u.Slices} {b : Finset ℕ} {q : Programme D b}
  {n : q.Run α β γ} {a : Notice l}

namespace Reading
variable (B : Reading a n) {Ω : Set (Config G c)} {r t : ℝ} {V : Config G c} {p : Reel G H R K}

/-- Demand each needed purchase on the common view. The local context may
be output-flagged (value usage only). It still has to prove every prerequisite
of a test it invokes. -/
def awakeAtom (p : Reel G H R K) : α ⊕ γ → Config G c → ℝ :=
    Sum.elim (B.turning p).first (fun i => (B.turning p).optional i)
def Wakes (p : Reel G H R K) (V : Config G c) :=
    ∀ i : α ⊕ γ, ∃ᶠ W in nhds V, B.awakeAtom p i W ≠ 0

omit [DecidableEq H] [DecidableEq R] [DecidableEq β] in
lemma fails {i : α ⊕ γ} (h : B.awakeAtom p i V=0) : B.unmasked V p=0 := by
  unfold Reading.unmasked Reading.word
  cases i with
  | inl i => rw [Finset.prod_eq_zero (Finset.mem_univ i) h]; ring
  | inr i =>
    rw [show (∏ i : γ,(Real.exp (B.delta i V (p.1, a.imprint V p))-1))=0 from Finset.prod_eq_zero
      (Finset.mem_univ i) (by rw [show B.delta i V (p.1,a.imprint V p)=0 from h,Real.exp_zero,sub_self]), mul_zero]

omit [DecidableEq H] [DecidableEq R] [DecidableEq β] in
lemma stale (h : ¬ B.Wakes p V) : (fun W => B.unmasked W p) =ᶠ[𝓝 V] (fun _ => 0) := by
  obtain ⟨i,hi⟩ := not_forall.mp h
  filter_upwards [not_frequently.mp hi] with W hW
  exact B.fails (Classical.not_not.mp hW)

omit [DecidableEq H] [DecidableEq R] [DecidableEq β] [Fintype α] [Fintype β] [Fintype γ] in
/-- Derive a guard handshake from persistence. `q₀` is e.g. an unmetered
neighborhood validity (off-chart continuation choices frozen), not a hard
seed partition; any shrinking applies to all queried factors. -/
lemma require (h : B.Wakes p V) {q₀ : Set (Config G c)} (he : q₀∈ nhds V)
    {Ω : Set (Config G c)} (hΩ : IsClosed Ω) (i : α ⊕ γ)
    (ht : ∀ W ∈ q₀,B.awakeAtom p i W ≠ 0 → W∈Ω) : V∈Ω := by
  by_contra hv; have hz := hΩ.isOpen_compl.mem_nhds (Set.mem_compl hv)
  obtain ⟨W, hw, hi, hs⟩ := ((h i).and_eventually ((show ∀ᶠ x in nhds V,x∈q₀ from he).and (show ∀ᶠ x in nhds V,x∈Ωᶜ from hz))).exists
  exact hs (ht W hi hw)

/-- Only actual row slots in the kept subset can bid on a combined
row price in `Tariff.Earn.home`. All OTHER price slots count
per-entry, so this isn't replacing the combined multiplier estimate with a
log bound on everything. E.g. permit negative `b.value` earned on OWN
mandatory CorePackets on the same `W` neighborhood's seeds (checked on
`Wakes`); see Affine deployments. -/
def Residues (n : q.Run α β γ) (T : Tariff α β γ (Component G H R)) :=
    ∀ i:β,i∈T.core → ∃ x : RowPosts c f,n.settled i=.inl x

/-- Primitive input. For given V on the committed good domain: cost
on *actual retained projections/extensions*. For germ-dominated-
differentiation uses at nearby W: unmasked extensions still pass
these tests (can commission with much weaker care parameters; don't
pretend will be under the same quantitative bill). `Needs` forward
preconditions reside on THIS step in the lens; the chart and profile
haven't been rescaled. Directions in the cost predicate usually
`d.out.dirBound` with connected anchor - not per-letter basis. -/
structure Clearance (t : ℝ) (T : Tariff α β γ (Component G H R))
    (V : Config G c) (W : Directions G c → Prop) (k : ℕ) : Prop where
  pane : (a.C V).PosDef
  bought : Peak (a.C V) T.capacity -- for endpoint budget
  leased : T.Lease
  action : Residues n T
  opens p : Needed l t V p → B.Wakes p V →
    Stack (B.turning p) W k V T (a.imprint V p) ∧ a.Score p V k W (T.grow (a.imprint V p))

namespace Clearance
variable {W : Directions G c → Prop} {k : ℕ} {B} {T : Tariff α β γ (Component G H R)}

/-- Called before even applying a differentiated upper bound. Either
entire term is zero (estimate derivatives by actual germ equality), or
all pre-tests enable at same V and chart (without assuming flags still true
in a neighborhood). -/
lemma preflight (h : Clearance B t T V W k) (hr : Ready d.chart d.g r)
    (hV : Ω∈ nhds V) (hk : t<r) (hs : B.Shutter Ω t) (p : Reel G H R K) :
    let u W := B.endorsed r W p
    let f := B.turning p; let z := a.imprint V p
    u =ᶠ[𝓝 V] 0 ∨
      (Needed l t V p ∧ Had (l:=l) r V p ∧ B.Wakes p V ∧
      (u =ᶠ[𝓝 V] (fun W => a.wideStrip W p * f.volumeMark W)) ∧
      a.Score p V k W (T.grow z) ∧ Stack f W k V T z) := by
  intro u f z
  by_cases hp : Needed l t V p
  swap
  · left
    filter_upwards [hV, exterior hp] with w hw hv
    exact Classical.not_not.mp fun ht => hv (B.shrinks hr hs w hw ht)
  by_cases hh : B.Wakes p V
  swap
  · left
    filter_upwards [B.stale hh] with w hw
    change a.strip _ w p*B.unmasked w p=0
    rw [show B.unmasked w p=0 from hw,mul_zero]
  right
  have hx := escape hp hk
  refine ⟨hp,hx,hh,?_,(h.opens p hp hh).2,(h.opens p hp hh).1⟩
  filter_upwards [B.guarded_near hr hx] with w hw
  rw [show u w=a.wideStrip w p * _ from hw]; change _=_* (B.turning p).volumeMark w; rw [turning_mark]



def degrees (k A B C I H : ℕ) : ℝ := mainRate A B C k + climbing k (scoreScale I H)
lemma degrees_pos (k A B C I H : ℕ) : 0 < degrees k A B C I H := by
  unfold degrees climbing mainRate; have := scoreScale_pos I H; positivity

lemma degrees_le (A B C I H k : ℕ) (r : ℝ) (hr : 1 ≤ r) :
    climbing k (scoreScale I H*r^4)+across A B C k r ≤ degrees k A B C I H*r^4 := by
  have hh : 0 ≤ mainRate A B C k := by unfold mainRate; positivity
  unfold degrees across climbing
  rw [add_mul (mainRate ..),mul_assoc ((k:ℝ)+1),add_comm ((k+1:ℝ)*(scoreScale .. * _))]; exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (by norm_num)) hh) le_rfl

/-- The core jet theorem includes the moving density bill.

Every
ordered derivative bounded simultaneously; direction order costs grow
polynomially with variance-read size. -/
theorem success (h : Clearance B t T V W k) (hr : Ready d.chart d.g r)
    (hV : Ω∈ nhds V) (hk : t<r) (hs : B.Shutter Ω t) (p : Reel G H R K) :
    let z := a.imprint V p; let r₀ := T.grow z
    let η := degrees k (Fintype.card α) (Fintype.card β) (Fintype.card γ)
      (Fintype.card (Component G H R)) (Fintype.card H)
    Ticket W k V (a.strip r V p * T.codex z) (η*r₀^4) (fun V => B.endorsed r V p) := by
  intro z r₀ η
  rcases h.preflight hr hV hk hs p with he|⟨ht,hi,hw,hE,hK,hP⟩
  · have hx : 0 ≤ η*r₀^4 := mul_nonneg (degrees_pos ..).le (by positivity)
    exact (((Ticket.pure hx (0:ℝ)).agree (EventuallyEq.symm he)).mono
      (by rw [norm_zero]; exact mul_nonneg (a.absolute V p r) (h.leased.fair z)) le_rfl)
  rw [a.pricey hi]
  have hq := (hK.currency (h.leased.pays_grow _) le_rfl).mul (hP.buy h.leased)
  exact (hq.mono le_rfl (degrees_le _ _ _ _ _ _ r₀ (h.leased.pays_grow z))).agree hE.symm
end Clearance
end Reading
end YM.AnalyticBridge.LocalGaussian

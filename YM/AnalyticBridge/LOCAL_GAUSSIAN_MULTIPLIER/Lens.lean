import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Programme
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.ShiftChart
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen


/-!
# Choose the local window ONCE across the multiplier

Do not implicitly insert identities in the precision. A viewport is for keeping
the Gaussian endpoints of the selected letters (with all exposed
colors) and all K, held hard and frozen U arguments and Y tag bindings
required by the terms. `Reading` outputs extended pre-mask letters
with checks against their *particular* full coefficients. Here this is
at fixed coverage / forest / tags. Footprint X is for these functional
estimates; to retain ALSO actual query support and eligibility
bookkeeping/tags for integrated gas overlap, etc., would need corresponding
construction from RECONNECTED_LOCALITY. In particular, not saying other
tags give the same answer just because the expansion at this tag reads
only these fields.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision MeasureTheory Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows
open YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S} {u : Spot d}

open Curtain Spot

abbrev Display (G : Gauge) (H R K : Type) := LinkArray G K × Coordinates G H R

structure Viewport (u : Spot d) (X : Support c) (H R K : Type) where
  read : H ⊕ R ↪ ActiveKey u
  held : K ↪ FrozenKey u
  activePos i : Next.SectorChange.points S (read i).val.val ⊆ X
  heldPos i : Next.SectorChange.points S (held i).val.val ⊆ X

variable {H R K : Type} {X : Support c}
namespace Viewport
variable (l : Viewport u X H R K)

def slot (j : (H⊕R) × G.ColorIndex) : InKey u := (l.read j.1,j.2)
lemma slot_inj : Injective l.slot := by
  intro i j he
  exact Prod.ext (l.read.injective (congr_arg Prod.fst he)) (show (l.slot i).2=(l.slot j).2 from congr_arg Prod.snd he)

def info (p : Visual u) : Display G H R K := (p.1 ∘ l.held,p.2 ∘ l.slot)

def cropped (V : Config G c) : Curtain.Chart G H R := (u.C V).submatrix l.slot l.slot

def edges (i : H ⊕ R) : Bond f := (l.read i).val.val
def bars (i : K) : Bond f := (l.held i).val.val

def copyAt (V : Config G c) : LinkArray G (H ⊕ R) := fun i => replica S.ratio V (l.edges i)

def copy (V : Config G c) : LinkArray G H := l.copyAt V ∘ Sum.inl

lemma uses (X : Support c) (e : Bond f) (he : Next.SectorChange.points S e ⊆ X) :
    LocalOn X (fun V : Config G c => replica S.ratio V e) := by
  intro v w hv; unfold replica; split
  · rfl
  next hx =>
    apply hv
    · exact he (mem_insert ..)
    have hp := S.ratio.parents_hop S.patch.odd_side e.1 e.2
    split at hp
    · rw [← hp]; exact he (Set.mem_insert_of_mem _ rfl)
    exact (hx hp).elim



@[fun_prop] lemma continuous_copyAt : Continuous l.copyAt := by
  refine continuous_pi fun i => ?_
  unfold copyAt replica; split <;> fun_prop
@[fun_prop] lemma continuous_copy : Continuous l.copy := by
  refine continuous_pi fun i => (continuous_apply (Sum.inl i)).comp (l.continuous_copyAt)

variable [Fintype H] [Fintype R] [Fintype K] [DecidableEq H] [DecidableEq R]



/-- Cost of a local marginal: dims from actual endpoints, even near the
seam. Can subsequently pay this from cover costs, don't use if prices
actually need only the much smaller number of exp-tested endpoints. -/
def frameCost (S : StepData c f) (X : Support c) := X.card * S.patch.L.val^4 * Fintype.card Axis

private lemma fitsPrice {Y : Type} [Fintype Y] (L : Y → Bond f) (h : Injective L)
    (he : ∀ i,Next.SectorChange.points S (L i) ⊆ X) : Fintype.card Y ≤ frameCost S X := by
  let f i := (
    (⟨S.ratio.parent (L i).1, he i (Set.mem_insert ..)⟩ : X), S.ratio.residue (L i).1, (L i).2)
  have hx : Injective f := by
    intro i j hx; apply h; apply Prod.ext
    · have hp := congr_arg (fun x => (x.1:↥X).1) hx
      have hr := congr_arg Prod.fst (congr_arg Prod.snd hx)
      rw [← S.ratio.unpack_at (L i).1, ← S.ratio.unpack_at (L j).1]
      rw [(show S.ratio.parent (L i).1 = S.ratio.parent (L j).1 from hp), (show S.ratio.residue (L i).1=S.ratio.residue (L j).1 from hr)]
    have he := congr_arg Prod.snd (congr_arg Prod.snd hx); exact he
  have hh := Fintype.card_le_of_injective f hx
  change _ ≤ Fintype.card ((↥X) × Site S.ratio.count × Axis) at hh
  simp_rw [Fintype.card_prod,Fintype.card_coe,Lattice.site_card] at hh; exact hh.trans (le_of_eq (mul_assoc ..).symm)

include l
omit [DecidableEq H] [DecidableEq R] [Fintype K] in
lemma frameRoom : Fintype.card ((H⊕R) × G.ColorIndex) ≤ frameCost S X * Fintype.card G.ColorIndex := by
  have ht := fitsPrice l.edges (fun a b h => l.read.injective (Subtype.ext (Subtype.ext h))) l.activePos
  rw [Fintype.card_prod]; exact Nat.mul_le_mul_right _ ht
omit [DecidableEq H] [DecidableEq R] [Fintype H] [Fintype R] in
lemma heldRoom : Fintype.card K ≤ frameCost S X :=
  fitsPrice l.bars (fun _ _ h => l.held.injective (Subtype.ext (Subtype.ext h))) l.heldPos
end Viewport

variable [Fintype H] [Fintype R] [Fintype K] [DecidableEq H] [DecidableEq R]

variable {l : Viewport u X H R K}
/-- Local field-read requirements, NOT estimates or asserting existence.
Geometry is fixed outside uses (assembly must also price the possible-tag
reads in these proofs; here we retain the *whole* choice/table, not doing
decoupling or claiming a function only of some partial sector).

At true uses with flags must read the genuine coefficients even if some
other optional factor vanished (agreement with *edited* values).
`LocalOn` required even off this guard, for these extensions.
-/
structure Notice (l : Viewport u X H R K) where
  C : Config G c → Curtain.Chart G H R
  m : Config G c → LinkArray G K → Coordinates G H R
  stores : LocalOn X C
  views : LocalOn X m
  meet V : u.Clearing V → l.cropped V=C V
  arrive V Y : u.Clearing V → m V (Y ∘ l.held)=u.m V Y ∘ l.slot
  recorded : ∀ i j, Measurable fun V => C V i j
  marks : Measurable (Function.uncurry m)

namespace Notice
variable (a : Notice l)
def law (V : Config G c) : Measure (Display G H R K) := (piHaar G K).prod (cloud (a.C V))
instance (V : Config G c) : IsProbabilityMeasure (a.law V) := by unfold law; infer_instance

omit [DecidableEq H] [DecidableEq R] [Fintype H] [Fintype R] [Fintype K] in
lemma principal (V : Config G c) (h : u.Clearing V) : (a.C V).PosDef := a.meet V h ▸ h.kernel.submatrix l.slot_inj
omit [DecidableEq H] [DecidableEq R] [Fintype K] in
lemma priceCap (V : Config G c) (h : u.Clearing V) {Q : ℝ} (hQ : Peak (u.C V) Q) : Peak (a.C V) Q := by
  rw [← a.meet V h]; exact hQ.project ⟨l.slot,l.slot_inj⟩

def givenU (V : Config G c) (p : Display G H R K) : LinkArray G (H ⊕ R) :=
    release (l.copyAt V) (tape (a.m V p.1+d.g • p.2))

omit [DecidableEq H] [DecidableEq R] [Fintype K] in
lemma givenU_here (V : Config G c) (h : u.Clearing V) (p : Visual u) (i : H ⊕ R) :
    a.givenU V (l.info p) i = u.hard V p (l.edges i) := by
  unfold hard physical returned thaw; rw [show u.F.drape _ (l.edges i) = _ from u.F.off_tree _ (l.read i).val, freeze_regular]
  unfold givenU Viewport.info; rw [a.arrive V _ h]; unfold release
  have he : tape ((u.m V p.1) ∘ l.slot + d.g • (p.2 ∘ l.slot)) i = displaced (u.m V p.1) d.g p.2 (l.read i) := by
    ext; rfl
  rw [he]; rfl

-- Actual frozen binding as well. Does not require flags.
omit [Fintype H] [Fintype R] [Fintype K] [DecidableEq H] [DecidableEq R] in
lemma hold_here (l : Viewport u X H R K) (V : Config G c) (p : Visual u) (i : K) :
    (l.info p).1 i = u.hard V p (l.bars i) := by
  unfold hard physical returned thaw; rw [show u.F.drape _ (l.bars i) = _ from u.F.off_tree _ (l.held i).val, freeze_held]
  rfl
end Notice

section read
open Spot.Programme
variable {α β γ : Type} {D : u.Slices} {b : Finset ℕ} {q : Programme D b}
    {n : q.Run α β γ} {a : Notice l}

/-- Supplier: the extended pre-mask records of the *selected* local
product of this step. No integrability or smoothness implied on their
whole field domain. -/
structure Reading (a : Notice l) (n : q.Run α β γ) where
  ret : α → Config G c → Display G H R K → ℝ
  logs : β → Config G c → Display G H R K → ℝ
  delta : γ → Config G c → Display G H R K → ℝ
  retMeas i : Measurable (Function.uncurry (ret i))
  logsMeas i : Measurable (Function.uncurry (logs i))
  deltaMeas i : Measurable (Function.uncurry (delta i))
  retSees i : LocalOn X (ret i)
  logsSee i : LocalOn X (logs i)
  deltaSees i : LocalOn X (delta i)
  retReached i V p : u.Clearing V → ret i V (l.info p) = q.visit (n.entry i) V p
  logsReached i V p : u.Clearing V → logs i V (l.info p) = q.posted (n.settled i) V p
  deltaReached i V p : u.Clearing V → delta i V (l.info p) = q.posted (n.marks i) V p

namespace Reading
variable (R₀ : Reading a n)
variable [Fintype α] [Fintype β] [Fintype γ]

/-- The multiplier of these selections, after querying the primitive
local letters, but before differentiation, charging or gathering.
Hang any good-set/flag inventory mask outside. -/
def word (V : Config G c) (p : Display G H R K) :=
    (∏ i, R₀.ret i V p) * Real.exp (∑ i, R₀.logs i V p) * ∏ i,(Real.exp (R₀.delta i V p)-1)

omit [DecidableEq H] [DecidableEq R] [Fintype H] [Fintype R] [Fintype K] in
theorem real_word (V : Config G c) (p : Visual u) (h : u.Clearing V) : R₀.word V (l.info p) = n.complete V p := by
  unfold Reading.word; simp_rw [fun i => R₀.retReached i V p h,fun i => R₀.logsReached i V p h,fun i => R₀.deltaReached i V p h]; rfl

omit [DecidableEq H] [DecidableEq R] [Fintype H] [Fintype R] [Fintype K] in
lemma stands : Measurable (Function.uncurry R₀.word) := by
  unfold Reading.word uncurry
  exact ((Finset.measurable_fun_prod _ (fun i _ => R₀.retMeas i)).mul (Finset.measurable_fun_sum _ (fun i _ => R₀.logsMeas i)).exp).mul
    (Finset.measurable_fun_prod _ (fun i _ => (R₀.deltaMeas i).exp.sub measurable_const))

omit [DecidableEq H] [DecidableEq R] [Fintype H] [Fintype R] [Fintype K] in
lemma member (V : Config G c) : Measurable (R₀.word V) := R₀.stands.comp (measurable_prodMk_left (x:=V))

omit [DecidableEq H] [DecidableEq R] [Fintype H] [Fintype R] [Fintype K] in
lemma windowed : LocalOn X R₀.word := by
  intro x y h
  unfold Reading.word; simp_rw [fun i => R₀.retSees i x y h, fun i => R₀.logsSee i x y h, fun i => R₀.deltaSees i x y h]






end Reading
end read
end YM.AnalyticBridge.LocalGaussian

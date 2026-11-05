import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Lens
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Orders


/-!
# Every hard argument stays held for the one component calculus

`Shutter` is a per-held-link demand on the *selected atoms* (through
U copies, gates or log parents). Keep the corresponding γ/protectors
before opening at any other locations. We use a slightly larger open
chart. Thus the product extends by zero beyond the carried patch even
around equality at the moving open boundary. Not inferred from overall
sector support once defaults dropped.

`Pays` results later also cost **inside** the shutter: tests of
smoothness along a V movement are actual germ tests (possibly with
cutoff profile), never differentiate χ across branch predicates or the
final inventory indicator. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision MeasureTheory Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows
open YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented Metric
open Curtain Spot Spot.Programme
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S} {u : Spot d}
  {H R K : Type} [Fintype H] [Fintype R] [Fintype K] [DecidableEq H] [DecidableEq R]
  {X : Support c} {l : Viewport u X H R K}

/-- The integrand on this domain extends by zero
outside moving chart; pay ONLY that extension.

Need Borel and domination
along any queried increments before integrating a derivative. -/
abbrev Reel (G : Gauge) (H R K : Type) := LinkArray G K × Curtain.Pair G H R

def pullLaw (G : Gauge) (H R K : Type) [Fintype H] [Fintype R] [Fintype K] : Measure (Reel G H R K) :=
    (piHaar G K).prod (Curtain.measure G H R)
instance (G : Gauge) (H R K : Type) [Fintype H] [Fintype R] [Fintype K] : SigmaFinite (pullLaw G H R K) := by unfold pullLaw; infer_instance

namespace Notice
variable (a : Notice l)

def tide (V : Config G c) (p : LinkArray G K) : Prices G H := closeHalf (a.m V p)

def imprint (V : Config G c) (p : Reel G H R K) := poured d.g (a.tide V p.1) (l.copy V) p.2

def strip (r : ℝ) (V : Config G c) (p : Reel G H R K) :=
    coverFee d.chart d.g r (a.tide V p.1) (l.copy V) (a.C V) p.2

def wideStrip (V : Config G c) (p : Reel G H R K) :=
    fare d.chart d.g (a.tide V p.1) (l.copy V) (a.C V) p.2

def bought (V : Config G c) (p : Display G H R K) := issued (a.tide V p.1) d.g p.2

def Had (r : ℝ) (V : Config G c) (p : Reel G H R K) := validBack r (l.copy V) p.2

def Needed (l : Viewport u X H R K) (r : ℝ) (V : Config G c) (p : Reel G H R K) :=
    ∀ i : H,p.2.2 i*(l.copy V i)⁻¹∈G.lieExp '' closedBall 0 r

omit [Fintype K] [DecidableEq H] [DecidableEq R] in
@[fun_prop] lemma readable (V : Config G c) : Measurable (a.tide V) :=
  measurable_snd.comp (separate.measurable.comp (a.marks.comp measurable_prodMk_left))

omit [Fintype K] [DecidableEq H] [DecidableEq R] in
lemma eaten (V : Config G c) (p : Reel G H R K) (hg : 0 < d.g) : a.bought V (p.1,a.imprint V p)=unlit (l.copy V) p.2.2 := by
  unfold imprint poured bought issued; rw [close_join,attends _ _ hg]

-- `Had` must have l as parameter. Bring back real U exactly on this chart.
omit [Fintype K] [DecidableEq H] [DecidableEq R] in
lemma stalls {r : ℝ} (hr : Ready d.chart d.g r) (V : Config G c) (p : Reel G H R K) (hp : Had (l:=l) r V p) (i : H) :
    a.givenU V (p.1,a.imprint V p) (.inl i) = p.2.2 i := by
  have hx : a.bought V (p.1,a.imprint V p) i=tape (a.m V p.1+d.g • a.imprint V p) (.inl i) := rfl
  unfold givenU release; rw [← hx, a.eaten V p hr.heat]
  exact congr_fun (read_unlit _ hr.ins hp) i

omit [Fintype K] [Fintype R] [DecidableEq H] [DecidableEq R] in
lemma still {V : Config G c} {p : Reel G H R K} {r : ℝ} (hr : r ≤ firstRadius G) (hi : Had (l:=l) r V p) :
    ∀ᶠ W : Config G c in nhds V, Had (l:=l) r W p := by
  refine eventually_all.mpr fun i : H => ?_
  let f (W : Config G c) := p.2.2 i*(l.copy W i)⁻¹
  exact (show Continuous f by unfold f; fun_prop).continuousAt (geom_pay hr |>.1 |>.mem_nhds (hi i))

omit [Fintype K] [Fintype R] [Fintype H] [DecidableEq H] [DecidableEq R] in
lemma exterior {V : Config G c} {p : Reel G H R K} {r : ℝ} (h : ¬ Needed l r V p) :
    ∀ᶠ W : Config G c in nhds V, ¬ Needed l r W p := by
  unfold Needed at h; push Not at h; obtain ⟨i,hi⟩ := h
  let f (W : Config G c) := p.2.2 i*(l.copy W i)⁻¹
  have hp : IsClosed (G.lieExp '' closedBall 0 r) := ((isCompact_closedBall _ _).image G.lieExp_cont).isClosed
  have hx : f V ∈ (G.lieExp '' closedBall 0 r)ᶜ := hi
  filter_upwards [(show Continuous f by unfold f; fun_prop).continuousAt (hp.isOpen_compl.mem_nhds hx)] with y hy
  exact fun ht => hy (ht i)

omit [Fintype K] [Fintype R] [Fintype H] [DecidableEq H] [DecidableEq R] in
lemma escape {V : Config G c} {p : Reel G H R K} {r t : ℝ} (hi : Needed l t V p) (he : t < r) : Had (l:=l) r V p :=
    fun i => image_mono (closedBall_subset_ball he) (hi i)

omit [Fintype K] in
lemma absolute (V : Config G c) (p : Reel G H R K) (r : ℝ) : 0 ≤ a.strip r V p := cover_nonneg ..
omit [Fintype K] in
lemma pricey {V : Config G c} {p : Reel G H R K} {r : ℝ} (h : Had (l:=l) r V p) : a.strip r V p=a.wideStrip V p := if_pos h
end Notice

variable {α β γ : Type} {D : u.Slices} {b : Finset ℕ} {q : Programme D b}
  {n : q.Run α β γ} {a : Notice l}

namespace Reading
open Notice

variable [Fintype α] [Fintype β] [Fintype γ] (B : Reading a n)

def turning (p : Reel G H R K) : Varying α β γ (Config G c) :=
  ⟨fun i V => B.ret i V (p.1,a.imprint V p),fun i V => B.logs i V (p.1,a.imprint V p),fun i V => B.delta i V (p.1,a.imprint V p)⟩

def marked (V : Config G c) : Varying α β γ (Display G H R K) :=
  ⟨fun i => B.ret i V,fun i => B.logs i V,fun i => B.delta i V⟩

omit [Fintype H] [Fintype R] [Fintype K] [DecidableEq H] [DecidableEq R] in
lemma retreat (V : Config G c) : B.word V=(B.marked V).volumeMark := by
  ext x; simp only [Varying.volumeMark,Varying.beginning,Varying.closure,Varying.list,
    Function.comp_apply,Pi.mul_apply,Finset.sum_apply,Finset.prod_apply,marked,Pi.sub_apply]; rfl

/-- Unmasked local product in *held* coordinates, all sharing the same
V-dependent read of `z` (totalized germs). -/
def unmasked (V : Config G c) (p : Reel G H R K) := B.word V (p.1, a.imprint V p)

def endorsed (r : ℝ) (V : Config G c) (p : Reel G H R K) := a.strip r V p * B.unmasked V p

omit [Fintype K] [DecidableEq H] [DecidableEq R] in
lemma turning_mark (V : Config G c) (p : Reel G H R K) :
    (B.turning p).volumeMark V = B.unmasked V p := by
  simp only [turning,Varying.volumeMark,Varying.beginning,Varying.closure,Varying.list,
    Function.comp_apply,Pi.mul_apply,Finset.sum_apply,Finset.prod_apply,Pi.sub_apply]; rfl

/-- Either a carried gate/variant or an optional log delta may protect
hard reads. This does not demand that each multiplicative occur's U uses
be disjoint. -/
def HeldAt (V : Config G c) (p : Display G H R K) :=
    (∀ i : α,B.ret i V p ≠ 0) ∧ (∀ i : γ,B.delta i V p ≠ 0)

omit [Fintype H] [Fintype R] [Fintype K] [DecidableEq H] [DecidableEq R] in
lemma unopened {V : Config G c} {p : Display G H R K} (h : B.word V p ≠ 0) : B.HeldAt V p := by
  constructor
  · intro i hi; apply h; unfold Reading.word; rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]; ring
  intro i hi; apply h; unfold Reading.word; rw [show (∏ j,(Real.exp (B.delta j V p)-1))=0 from
    Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi,Real.exp_zero]; ring),mul_zero]

def Shutter (S : Set (Config G c)) (t : ℝ) := ∀ V∈S, ∀ p : Display G H R K,
    B.HeldAt V p → ∀ i, ‖a.bought V p i‖ ≤ t

variable {r t : ℝ} {Ω : Set (Config G c)}



omit [Fintype K] in
/-- CLOSED smaller support, important for equality about the MOVING
open chart. This condition is at any nonzero point. -/
lemma shrinks {p : Reel G H R K} (hr : Ready d.chart d.g r) (h : B.Shutter Ω t) (V : Config G c) (hv : V∈Ω)
    (hp : B.endorsed r V p ≠ 0) : Needed l t V p := by
  have hw : Had (l:=l) r V p := by
    by_contra hh; apply hp; unfold endorsed Notice.strip coverFee; rw [if_neg (show ¬validBack _ _ _ from hh),zero_mul]
  have hh := B.unopened (V:=V) (p:=(p.1, a.imprint V p)) (right_ne_zero_of_mul hp)
  intro i
  have hI := h V hv (p.1, a.imprint V p) hh i
  let x := unlit (l.copy V) p.2.2
  rw [a.eaten V p hr.heat] at hI
  refine ⟨x i, by simpa only [mem_closedBall, dist_zero_right] using hI, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]; exact congr_fun (read_unlit _ hr.ins hw) i

omit [Fintype K] in
lemma guarded_near (hr : Ready d.chart d.g r) {p : Reel G H R K} {V : Config G c} (hx : Had (l:=l) r V p) :
    (fun W => B.endorsed r W p)=ᶠ[𝓝 V] (fun W => a.wideStrip W p * B.unmasked W p) := by
  filter_upwards [Notice.still hr.ins hx] with i hi
  rw [endorsed,a.pricey hi]
end Reading
end YM.AnalyticBridge.LocalGaussian

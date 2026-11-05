import YM.Ac.Tree
import YM.Bid.Fetch
import YM.Next.EXTRACTION.Raw

/-!
# Preparing the finite premises for the arrival

The proof-bid D04 is conditional. Its application needs discrepancy / Ward
identity estimates on the cutoff family (RBin), not implied here by the
centered estimates. Also, rank detection estimates (RShort) will be needed --
see the detector module. Here are the RBin inputs as *finite-cutoff* estimates,
separating limit existence out from `RelayBin`. Only the step projection data
(not its convergence) is required alongside these estimates. Pick projections
on the family indexed by exactly `(N,p)` as for the Wilson moments. Keep them
in the same extraction as the moments. `Presentation` below includes no
hierarchy data.

There is a subtlety even for an ordinary further mesh refinement: the `mark`
estimate must work for **more** rows `x : Rowe C d` on the refinement, because
`dollar` assumes a bound along the regulator tails only. We show even this
estimate transports. Extend each new such `x` by zero away from the new grid
of indices to use the old estimate. Only its actual values at cutoffs being
used enter the test. Uses no uniformity in the number of rows.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Next.Extract
open Set Function Filter Extraction Extraction.Lease Dash Bid
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {S : Table C.book} {f g : Order}

abbrev CoordMap (C : Family G) (d : ℕ) := C.label d →L[ℂ] C.label d

/-- At this interface only require a projection, not already its exact
continuum kernel. Convention: equations belong to the **kernel**. Idempotent
at *every* (N,p) (can use arbitrary projections where not yet fitting). -/
structure Presentation (C : Family G) where
  step (d : ℕ) : ℕ × ℕ → CoordMap C d
  projected (d u v) : step d u (step d u v) = step d u v

/-- Sufficient bounds for including the full finite matrix data in the
extraction. Inner bound covers each period. Use the usual operator norms. E.g.
fixed-metric orthogonal projections are bounded. -/
structure Affordable (b : Presentation C) (f : Order) : Prop where
  rows (d p : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ j : ℕ in atTop, ‖b.step d (f.mesh j,p)‖ ≤ D
  outer (d : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ f.late fun N p => ‖b.step d (N,p)‖ ≤ D

lemma Tails.affordable {b : Presentation C} (h : Tails g f) (H : Affordable b f) : Affordable b g := by
  constructor
  · intro d p
    obtain ⟨D,hD,hv⟩ := H.rows d p
    exact ⟨D,hD,h.mesh.holds (fun N => ‖b.step d (N,p)‖ ≤ D) hv⟩
  intro d
  obtain ⟨D,hD,hv⟩ := H.outer d
  exact ⟨D,hD,h.late hv⟩

/-- A bin with exactly the given finite projection data and **both-stage**
limits of them. `z d p` are the inner (mesh) limits. -/
structure Projected (b : Presentation C) (f : Order) (R : Bin S) (z : ∀ d : ℕ, ℕ → CoordMap C d) : Prop where
  same (d) : (R d).step = b.step d
  keeps : Keeps (X := CoordMap C) f (fun _ _ => True) (fun d N p => b.step d (N,p)) z (fun d => (R d).trueP)

lemma Projected.approaches {b : Presentation C} {R : Bin S} {z} (h : Projected b f R z) (d : ℕ) : Bin.Matrix R d f := by
  change Tendsto (R d).step f.fuse (𝓝 (R d).trueP)
  rw [h.same]
  exact Order.along (Y := CoordMap C d) (L := fun N p => b.step d (N,p)) (h.keeps.limits d)

lemma projected_limit {d : ℕ} {X : Type*} {h : Filter X} [h.NeBot]
    (p : X → CoordMap C d) (q : CoordMap C d)
    (H : ∀ i x, p i (p i x) = p i x) (he : Tendsto p h (𝓝 q)) (x : C.label d) : q (q x) = q x := by
  have hx := Dash.arcing he (tendsto_const_nhds (x := x))
  exact tendsto_nhds_unique_of_eventuallyEq (Dash.arcing he hx) hx (Eventually.of_forall fun i => H i x)

lemma Projected.inner_projection {b : Presentation C} {R : Bin S} {z} (h : Projected b f R z) (d p : ℕ) (x : C.label d) :
    z d p (z d p x) = z d p x :=
  projected_limit (fun j => b.step d (f.mesh j,p)) (z d p) (fun _ => b.projected d _) (h.keeps.rows d p trivial) x

lemma Tails.projected {b : Presentation C} {R : Bin S} {z} (h : Tails g f) (H : Projected b f R z) : Projected b g R z :=
  ⟨H.same,h.keeps H.keeps⟩

/-- Construct the common refinement for *all* these matrices. At application,
any limiting kernels/auxiliary data already picked along `f` are retained by
`Tails`. `S` is just a parameter for the `Bin` type. -/
theorem include_projections (S : Table C.book) (b : Presentation C) (h : Affordable b f) :
    ∃ g : Order, ∃ R : Bin S, ∃ z, Projected b (f.refine g) R z := by
  have he : Reserve (X := CoordMap C) f (fun _ _ => True) (fun d N p => b.step d (N,p)) :=
    Reserve.of_norm (fun _ => Eventually.of_forall fun _ => trivial) (fun d p _ => h.rows d p) h.outer
  obtain ⟨g,z,y,H⟩ := he.gather
  let R : Bin S := fun d =>
    ⟨b.step d, y d, b.projected d, projected_limit (b.step d) (y d) (b.projected d) (Order.along (H.limits d))⟩
  exact ⟨g,R,z,fun _ => rfl,H⟩

/-- The remaining finite-family estimates from `Bid.RelayBin`.

* `dollar` bounds inverse terminal coordinate norm by
  `exp (ε * C.S.scale N)` for each fixed `ε>0`, eventually (`f.late`). For
  each such x annihilated by the step projection, `mark` needs the measurable
  bounded (at the cutoff, `sober`) comparison cylinder with actual normalized
  Wilson moment equalities (`exactOnSep`: zero with every finite separated
  spectator test at cutoff positions, any fixed positive separation). These
  are on ordered tails. It needs `close` *from* the cylinder in the actual
  physical `upper` family: root bounds (`Lease.rents` -- tests all specified
  translated tilings, relative margins, actual link orientations/copies and
  supports) by some `y N p` going to zero on ordered tails.
* `transit`, `pace` request `vet` (actual cutoff matching with `dollar`-paid
  vector and `close` difference bounds). Includes identity transport even at
  equal weights; `heighten` uses `a_N⁻¹` times translated **forward**
  difference with given positive-axis step.

Rates and thresholds use exactly these existing Lean types, with the same
`Order` -- in particular no sequential convergence claim about a hierarchy is
an input through this gate. -/
structure RelayCosts (b : Presentation C) (f : Order) (d : ℕ) : Prop where
  mark (x : Rowe C d) : (∀ j, b.step d j (x j) = 0) → dollar C f x →
    ∃ z, sober C z f ∧ exactOnSep C f z ∧ Bid.close C f (upper C x-z)
  transit (w : ℕ) : w ≤ d → ∀ x : C.label w, vet C f d (visits C w x)
  pace (x : C.label d) (a : Axis) : vet C f (d+1) (heighten C d x a)

lemma Tails.cost {P : Trial C} (h : Tails g f) (H : Bid.close C f P) : Bid.close C g P := by
  obtain ⟨y,hv,hp⟩ := H
  refine ⟨y,hv.mono_left h.fused,?_⟩
  intro i j
  obtain ⟨m,hm,hr⟩ := hp i j
  exact ⟨m,hm,h.late hr⟩

lemma close_change {P Q : Trial C} (h : Bid.close C g P) (H : g.late fun N p => P N p = Q N p) : Bid.close C g Q := by
  obtain ⟨y,hv,hp⟩ := h
  refine ⟨y,hv,?_⟩
  intro i j
  obtain ⟨m,hm,hr⟩ := hp i j
  refine ⟨m,hm,?_⟩
  unfold Order.late at *
  filter_upwards [hr,H] with k hk hk'
  filter_upwards [hk,hk'] with l hl hl'
  simpa only [hl'] using hl

lemma Tails.vets {P : Trial C} {d : ℕ} (h : Tails g f) (H : vet C f d P) : vet C g d P := by
  obtain ⟨w,hc,hv⟩ := H
  exact ⟨w,fun ε hε => h.late (hc ε hε),h.cost hv⟩

/-- Preserve the actual `mark` cost, *including* for rows newly satisfying a
bound just on the extracted regulator grid. -/
lemma Tails.relay {d : ℕ} {b : Presentation C} (h : Tails g f) (H : RelayCosts b f d) : RelayCosts b g d := by
  classical
  refine ⟨?_,fun w hw x => h.vets (H.transit w hw x),fun x a => h.vets (H.pace x a)⟩
  intro x hx he
  let w : Rowe C d := fun j => if picks g j.1 j.2 then x j else 0
  have hw : dollar C f w := by
    intro ε hε
    have he' := localize g f (he ε hε)
    unfold Order.late at *
    filter_upwards [he'] with k hk
    filter_upwards [hk] with i hi
    dsimp only [w]
    split_ifs with hp
    · exact hi hp
    rw [map_zero, norm_zero]
    exact (Real.exp_pos _).le
  have hh j : b.step d j (w j) = 0 := by
    unfold w; split
    · exact hx j
    rw [map_zero]
  obtain ⟨z,hz,ho,hq⟩ := H.mark w hh hw
  refine ⟨z,h.late hz, fun n q l δ hδ => h.late (ho n q l δ hδ),close_change (h.cost hq) ?_⟩
  unfold Order.late
  refine Eventually.of_forall fun k => Eventually.of_forall fun j => ?_
  let N := g.mesh j
  let p := g.per k
  have hp : w (N,p) = x (N,p) := if_pos (picks_self g j k)
  funext t
  change C.O N p (d := d) (w (N,p)) t - z N p t = C.O N p (d := d) (x (N,p)) t - z N p t
  rw [hp]

variable {b : Presentation C} {R : Bin S} {z : ∀ d : ℕ, ℕ → CoordMap C d}

lemma Projected.ready (h : Projected b f R z) (d : ℕ) (he : RelayCosts b f d) : RelayBin C R f d := by
  refine ⟨h.approaches d,?_,he.transit,he.pace⟩
  intro x hx hq
  exact he.mark x (by simpa only [h.same d] using hx) hq

def Presentation.ofBin (R : Bin S) : Presentation C := ⟨fun d => (R d).step,fun d => (R d).projection⟩

lemma costs_of_relay {d : ℕ} (h : RelayBin C R f d) : RelayCosts (Presentation.ofBin R) f d :=
  ⟨h.mark, h.transit, h.pace⟩

lemma Tails.relayBin {d : ℕ} (h : Tails g f) (H : RelayBin C R f d) : RelayBin C R g d := by
  have hr := h.relay (costs_of_relay H)
  exact ⟨H.P.mono_left h.fused,hr.mark,hr.transit,hr.pace⟩
end YM.Next.Extract

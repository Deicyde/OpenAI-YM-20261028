import YM.Extra.MULTISOURCE_TRAJECTORIES.Geometry
/-!
# Actual Lanes at fixed cutoff and a uniform producer criterion

It asks for strong spatial/smooth estimates on an
explicit choice (localized connected conditional moments, real unmasked,
also pricing their complements using the actual unmarked gas).

It may be a
much worse route numerically than a joint small/large-field expansion as in
the candidate.

Exactness, convergence, smoothness and existence of *some*
radii do not depend on these uniform post-L estimates.

Same C, reps, exact
origin stencil normalizations, tags, signed transformed values and physical
bump at every step in both statements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Wilson RG Lattice Overlay Marker Mix Function Filter MeasureTheory Stock
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {C : Family G} {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {R : Census V}
    {N p : ℕ}

namespace Probes
variable (R) (Q : Probes C V N p) (W : ∀ j,Windows (C.side j p))

def lane : Lane C.path R N p where
  sites j := (Q.layers R (W j)).bands
  load := Q.d
  uses := Q.eval

lemma signal_eq (h : C.Makes) {j : ℕ} (ho : Aperture (C.path.rep N p j)) (hj : j≤N) (s : R.Mode) :
    (Q.lane R W).signal j s = Q.toInsertions.total s j ∘ matrixField := funext fun U =>
  Q.toInsertions.fragments_exact R _ _ _ h.wilson ho (Q.anchored h _) hj U s

lemma first (h : C.Makes) (ho : Aperture (C.path.rep N p N)) (s : R.Mode) (U : Config G (C.side N p)) :
    (Q.lane R W).signal N s U = Ride.bump (C.S.a N) s Q.d * (bare (C.beta N p) U:ℂ) * Ride.Product (H:=C.path) Q.eval s U := by
  rw [Q.signal_eq R W h ho le_rfl s,Insertions.total_top,comp_apply,Q.toInsertions.source_eq, funext Q.physical]; rfl

lemma transition (h : C.Makes) {j : ℕ} (ho : Aperture (C.path.rep N p j)) (ho' : Aperture (C.path.rep N p (j+1))) (hj : j<N) (s : R.Mode) :
    let L := Q.lane R W
    L.signal j s = (Ride.bump (C.S.block j).val s L.load) •
      (C.path.levels.clock.op j p).push (C.path.β N p (j+1)) (L.signal (j+1) s) := by
  dsimp only
  rw [Q.signal_eq R W h ho hj.le, Q.signal_eq R W h ho' hj, Insertions.total_step Q.toInsertions s j hj]
  funext U; exact congrArg (Ride.bump (C.S.block j).val s Q.d • ·) (Insertions.step_push _ (Q.toInsertions.smooth_total s hj).continuous U)

omit [Fintype V] [Nonempty V] in
lemma integrable_product (s : R.Mode) : Integrable (Ride.Product (H:=C.path) Q.eval s) (law G _ (C.beta N p)) := by
  rw [← funext Q.physical]; apply continuous_integrable
  exact continuous_finsetProd _ fun i _ => (Q.toInsertions.smooth i).continuous.comp matrixField_cont




end Probes

variable {n : Side} {P : Rep G n}
namespace Layers
variable {α : Type*} {X : Layers P R α}

/-- Sufficient sales at ONE level (evaluated on exact localized functions,
not a theorem that the signed inclusion/exclusions satisfy them). Same-support
order/derivative norms at the displayed budget; also asks for a *higher*
support exponent for the K hit estimates where Ac.forest is used. -/
def Sale (Q : X.Prices) (w δ : ℝ) (mixed : Bool) := 0 ≤ δ ∧ 0 < w ∧
    (∀ i : V,SumBudget (fun j => if ranked (X.tag j)=mixed ∧ i∈(X.tag j).val then Poly.toll (fun _ => w) (X.tag j)*
      loaf P.p (X.region j) δ (Q.jet j) else 0) 1) ∧
    ∃ γ : ℝ,0 ≤ γ ∧ Real.exp γ - 1 ≤ 1 ∧ (P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ) ≤ 1 ∧
      Ac.Hit X.area P.p.B (rental Q (fun _ => w) mixed) (P.p.supportExponent+δ+1) γ

def Expenses (X : Layers P R α) (w : ℝ) :=
  (∀ i,w * ‖X.units i‖ ≤ 1) ∧ ∃ Q : X.Prices,Sale Q w 0 false ∧
      ∃ t δ : ℝ, w ≤ t*Real.exp (δ*P.p.B/64) ∧ Sale Q t δ true

variable [DecidableEq α] [Countable α]
omit [Fintype V] in
lemma funding {Q : X.Prices} {w δ : ℝ} {mixed : Bool} (h : Aperture P) (hr : X.Ready) (he : Sale Q w δ mixed) :
    Q.stubs.funded (fun _ => w) δ mixed 1 := by
  obtain ⟨hδ,hw,hc,γ,hg,hu,hv,hh⟩ := he
  exact financed Q h hr.toAnchored _ (fun _ => hw) _ _ _ _ hδ hg hu hv hc hh

omit [Fintype V] in
theorem holds {w : ℝ} (h : Aperture P) (hr : X.Ready) (hK : P.activities.ForcedFamily P.p)
    (hs : Stubs.far (A:=X.bands)) (he : X.Expenses w) : Stubs.Holds X.bands w := by
  obtain ⟨hi,Q,hq,t,δ,hw,hSale⟩ := he
  exact ⟨hi,X.active ‹Aperture P› hr hK,hs,Q.stubs,funding ‹Aperture P› hr hq,
    Or.inr ⟨fun _ => t,δ,hSale.1,fun _ => ⟨hSale.2.1,hw⟩, funding ‹Aperture P› hr hSale⟩⟩
end Layers

variable {d : ℕ} {u : ℝ}
/-- Proposed (strong, speculative) criterion using real conditional moments.
ALL periods with a ticket, every opened m,i, eventual cutoff N. Windows may
use any genuine blocks, but support prices are on complete unions. Backward
physical and direct/provisional payment requests *before* the gathering.
The conclusion (`circle` below) uses no altered family or schedule. -/
def Offers (C : Family G) (d : ℕ) (u : ℝ) := ∃ a t k, 0 < a ∧ (1:ℝ) ≤ t ∧ ∀ m i, C.ref d ≤ m → Tabs.opens C.path.levels t m i →
    ∀ᶠ N in atTop, ∃ h : m ≤ N, i ≤ N ∧ ∀ p, ticket C t N p m i h → ∀ v : C.label d, ‖v‖ ≤ u →
      ∃ W : ∀ j,Windows (C.side j p), ∀ j,i ≤ j → j ≤ N → Aperture (C.path.rep N p j) ∧ 8 ≤ C.path.levels.clock.coverSize j ∧
        ((Probes.center C p h v).layers (census _) (W j)).Expenses (width C a k j)

lemma book_story (H : C.Makes) {N m i p : ℕ} (h : m ≤ N) (hi : i≤N) {t : ℝ} (ht : 1 ≤ t) (hop : Tabs.opens C.path.levels t m i)
    (hh : ticket C t N p m i h) (v : C.label d) (W : ∀ j,Windows (C.side j p)) (a : ℝ) (k : ℕ) (hs : ∀ j,i ≤ j → j ≤ N →
      Aperture (C.path.rep N p j) ∧ 8 ≤ C.path.levels.clock.coverSize j ∧
      ((Probes.center C p h v).layers (census _) (W j)).Expenses (width C a k j)) :
    Story (m:=m) (i:=i) C ((Probes.center C p h v).lane (census _) W) v (fun a => width C a k) a := by
  classical
  let Q := Probes.center C p h v
  let R := census (Site (C.side m p))
  refine ⟨hop.1,hi,fun x => ⟨rfl,Probes.center_eq C p h v x⟩,fun j hj hj' x => Probes.center_positions C p h v (hop.1.trans hj) hj' x,
    fun j hj hj' => ?_,Q.integrable_product R,Q.first R W H (hs N hi le_rfl).1,fun j s hj hN => ?_⟩
  · obtain ⟨ho,hB,hS⟩ := hs j hj hj'
    exact Layers.holds ho (Q.ready _ _ H hj') (H.wilson.represents _ _ j hj').good.labels.forced
      (Probes.center_far (W j) h v H ht hh hB hj (hop.1.trans hj) hj') hS
  exact Q.transition R W H (hs j hj hN.le).1 (hs _ (hj.trans (Nat.le_succ _)) hN).1 hN s

theorem circle (H : C.Makes) (h : Offers C d u) : Circle C d u := by
  obtain ⟨a,t,k,ha,ht,h⟩ := h
  refine ⟨a,t,k,ha,ht,fun m i hm hi => ?_⟩
  filter_upwards [h m i hm hi] with N hN
  obtain ⟨hm,hN,h⟩ := hN
  refine ⟨hm, fun p he v hv => ?_⟩
  obtain ⟨W,h⟩ := h p he v hv
  exact ⟨_,book_story H hm hN ht hi he v W a k h⟩

open Extraction

end YM.Extra.Trajectories

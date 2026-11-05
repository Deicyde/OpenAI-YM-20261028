import YM.Next.UV_STRESS.Birth
import YM.Push.SECTOR_MEASURE.Output


set_option warningAsError false

/-!
# The old and old/new source transfer we need *before* any estimates

Produce the old lane's **signals** (not its representation) on all
subsets. One reason to do this again rather than assume Lane.Works
is that that apparently innocuous assumption for this application would
already require, inter alia, Active and existence of Radial prices on a
SIMULTANEOUS product trajectory in the *earlier* N:k integrations. Here
we drive those integrations to the signed join with no estimates hypothesis
at all on old histories (and no Representability assumption). The red
representation hypotheses in later files can thus be confined entirely to
the k:ell portion, including the birth **there**. Also expose actual sector
columns for use at any individual push. Never renormalize by a sector mass.
-/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PhaseCoarse
open Function Filter Set MeasureTheory Analysis Extraction Lattice RG Wilson Overlay Marker Cells
open YM.Next.UVStress Push.SectorMeasure
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} (C : Family G) {N p h k m d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Sector column identities for source signals need gauge invariance.
All statements equality of actual functions (not a.e.). -/
theorem push_invariant {f c : Side} (S : StepData c f) (H : S.patch.Branches S.kernel G)
    (β : ℝ) (F : Config G f → ℂ) (hf : Integrable F (prior G f)) (hi : GaugeInvariant F) :
    GaugeInvariant (S.push β F) := by
  intro t V
  let u : Site f → G.El := t ∘ S.ratio.parent
  have hu : u ∘ S.ratio.embed=t := by
    funext x; exact congr_arg t (S.ratio.embed_parent x)
  let fct (U : Config G f) := S.density β U (Lattice.gauge t V) • F U
  have q := prior_gauge u
  have e := integral_map (f:=fct) q.aemeasurable (by rw [q.map_eq]; exact
    (StepData.push_slice (S.isKernel H β) (Lattice.gauge t V) F hf).aestronglyMeasurable)
  rw [q.map_eq] at e
  change (∫ U, fct U ∂prior G f) = ∫ U, _ ∂ prior G f
  rw [e]
  apply integral_congr_ae
  filter_upwards with U
  dsimp only [fct]
  rw [← hu, S.covary H, hi u U]

/-- Top functions in this file need only be envelope and gauge invariant
(no smoothness). No Radial at any level requested. `copies` application below. -/
abbrev Scan (p N : ℕ) (ι : Type) := ι → Config G (C.side N p) → ℂ

abbrev fireSet (s : Finset ι) := chooseMode s
variable {C} (a : ι → ℕ) (O : Scan C p N ι)

def shelf {Ω : Type*} (O : ι → Ω → ℂ) (s : Finset ι) (U : Ω) := ∏ i ∈ s, O i U

def topLaw (s : Finset ι) (U : Config G (C.side N p)) :=
  Ride.bump (C.S.a N) (fireSet s) a * (bare (C.beta N p) U : ℂ) * shelf O s U

/-- Raw density coefficient on all subsets, incl exact vacuum. All
densities are RELATIVE TO probability Haar; physical scale factors in
bump, positive bare Wilson factor, partition not divided out. -/
def signal (s : Finset ι) (m : ℕ) (hm : m≤N) : Config G (C.side m p) → ℂ :=
    Nat.decreasingInduction (motive:=fun m _ => Config G (C.side m p) → ℂ)
      (fun k _ F => Ride.bump (C.S.block k).val (fireSet s) a •
        (operation C p k).push (C.path.β N p (k+1)) F)
      (topLaw (C:=C) a O s) hm

lemma signal_top (s : Finset ι) : signal (C:=C) a O s N le_rfl = topLaw (C:=C) a O s := Nat.decreasingInduction_self ..
lemma signal_step (s : Finset ι) (hm : m<N) : signal (C:=C) a O s m hm.le =
    Ride.bump (C.S.block m).val (fireSet s) a •
      (operation C p m).push (C.path.β N p (m+1)) (signal (C:=C) a O s (m+1) hm) := Nat.decreasingInduction_succ_left ..

omit [Fintype ι] [DecidableEq ι] in
lemma shelf_env {α : Type*} [MeasurableSpace α] {O : ι → α → ℂ} (s : Finset ι) (he : ∀ i, Envelope (O i)) : Envelope (shelf O s) := by
  refine ⟨Finset.measurable_fun_prod _ fun i _ => (he i).meas, ∏ i ∈ s,(he i).cost.choose, fun x => ?_⟩
  simp only [shelf, norm_prod]; exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (he i).cost.choose_spec x)

lemma envL1 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℂ} (h : Envelope f) : Integrable f μ := by
  obtain ⟨M,hM⟩ := h.cost
  exact (integrable_const (c:=(M:ℝ))).mono' h.meas.aestronglyMeasurable (Eventually.of_forall hM)

variable (s : Finset ι) (he : ∀ i, Envelope (O i)) (hg : ∀ i, GaugeInvariant (O i))
include he in
lemma signal_int (hm : m≤N) : Integrable (signal (C:=C) a O s m hm) (prior G _) := by
  induction hm using Nat.decreasingInduction with
  | self =>
    rw [signal_top]
    unfold topLaw; simp_rw [mul_assoc]
    have hp := (bare_cont (G:=G) (n:=C.side N p) (C.beta N p))
    exact (final_mul (prior G _) (fun U => ↑(bare (C.beta N p) U)) (shelf O s)
      (Env.compact (Complex.continuous_ofReal.comp hp)) (envL1 _ (shelf_env s he))).const_mul _
  | of_succ i hi ih => rw [signal_step a O _ hi]; exact (StepData.push_integrable (C.path.levels.transition_mass ..) _ ih).smul _

include he hg in
lemma signal_inv (hm : m≤N) : GaugeInvariant (signal (C:=C) a O s m hm) := by
  induction hm using Nat.decreasingInduction with
  | self =>
    rw [signal_top]
    intro t x; simp only [topLaw,shelf,bare_gauge]; simp_rw [hg _ t x]
  | of_succ i hi ih =>
    rw [signal_step a O _ hi]
    have H := push_invariant (operation C p i) (step_approved C p i) (C.path.β N p (i+1)) _
      (signal_int a O s he hi) ih
    intro t V; rw [Pi.smul_apply,H,Pi.smul_apply]

include he hg in
/-- Any of these rows can instead be computed with the true sector-resolved
push. No overlap error. Useful for next birth & step tests. Does NOT
mean we can afford to take norms before summing the columns. -/
theorem signal_columns (hm : m<N) {x w : ℝ} (D : Allocation G (operation C p m) x w)
    (T : Tree.Forest (operation C p m).ratio) (V : Config G (C.side m p)) :
    signal (C:=C) a O s m hm.le V = Ride.bump (C.S.block m).val (fireSet s) a *
      ∑ A, output D T (C.path.β N p (m+1)) (signal (C:=C) a O s (m+1) hm) A V := by
  rw [push_columns D T _ _ (step_approved C p m) (signal_int a O s he hm) (signal_inv a O s he hg hm) V,
    signal_step a O _ hm]; rfl

include he in
lemma signal_dual (hk : k≤m) (hm : m≤N) (f : Config G (C.side k p) → ℂ) (hf : Envelope f) :
    (∫ V, stack C p N k m f hk V * signal (C:=C) a O s m hm V ∂prior G _) =
      Ride.bump (C.S.a m) (fireSet s) a * (partition G (C.side N p) (C.beta N p) : ℂ) *
        moment (C.beta N p) (fun U => stack C p N k N f (hk.trans hm) U * shelf O s U) := by
  induction hm using Nat.decreasingInduction with
  | self =>
    rw [signal_top]
    let g := stack C p N k N f hk
    have hi := final_mul (law G _ (C.beta N p)) g (shelf O s) (stack_envelope C p N k N f hk hf)
      (envL1 _ (shelf_env s he))
    rw [moment_formula _ _ hi, mul_assoc,mul_inv_cancel_left₀ (by exact_mod_cast (partition_pos (G:=G) (n:=C.side N p) (C.beta N p)).ne'), ← integral_const_mul]
    apply integral_congr_ae; filter_upwards with x; unfold topLaw; ring
  | of_succ i hi ih =>
    let T := signal (C:=C) a O s (i+1) hi
    let Q := (operation C p i).push (C.path.β N p (i+1)) T
    let g := stack C p N k i f hk
    let b := Ride.bump (C.S.block i).val (fireSet s) a
    have e (V) : g V * signal (C:=C) a O s i hi.le V = b*(g V * Q V) := by
      rw [signal_step a O _ hi]; change _*(b*Q V)=_; ring
    specialize ih (hk.trans (Nat.le_succ _)); rw [stack_step C p N k i _ hk] at ih
    change (∫ V, g V * signal (C:=C) a O s i _ V ∂prior G _) = _
    simp_rw [e]
    unfold Q
    rw [integral_const_mul,reads_joint C _ _ (stack_envelope C p N k i f hk hf) T (signal_int a O s he hi)]
    unfold T; rw [ih,bump_steps C i]; unfold b; ring

/-- Use just the already verified stack distributivity convenience for all
subsets (`acquire_all`) with such a scan. No Bands.Works. -/
private def formatOnly : Lane C.path (Stock.census ι) N p :=
  ⟨fun _ => ⟨0,0,fun _ => ∅,fun _ => (Stock.census _).quiet,0,fun _ _ => (Stock.census _).quiet,0⟩,
    (fun _ => 0),O⟩

variable (J : Scan C p k ι)

def test (hk : k≤N) (U : Config G (C.side N p)) :=
    stack C p N k N (fun V => ∏ i ∈ s,(J i V-O i U)) hk U

/-- Signs: NEW minus OLD. New isn't multiplied by old for the same
marker (one shared copy index). -/
def blend (hk : k≤N) (V : Config G (C.side k p)) :=
    ∑ q ∈ s.powerset, (-1:ℂ)^q.card *
      (Ride.bump (C.S.a k) (fireSet (s\q)) a * shelf J (s\q) V) * signal (C:=C) a O q k hk V

variable (hk : k≤N) (hz : ∀ i, Envelope (J i))
include he hz
lemma blend_law :
    Integrable (test (C:=C) O s J hk) (law G _ (C.beta N p)) ∧
      Integrable (blend (C:=C) a O s J hk) (prior G _) ∧
      (∫ V, blend (C:=C) a O s J hk V ∂prior G _) = Ride.bump (C.S.a k) (fireSet s) a *
        (partition G (C.side N p) (C.beta N p) : ℂ) * moment (C.beta N p) (test (C:=C) O s J hk) := by
  let b (q : Finset ι) := (-1:ℂ)^q.card
  let g (q : Finset ι) := shelf J (s\q)
  let Q (q : Finset ι) := shelf O q
  let H (q : Finset ι) U := stack C p N k N (g q) hk U * Q q U
  let I (q : Finset ι) V := g q V * signal (C:=C) a O q k hk V
  let w (q : Finset ι) := Ride.bump (C.S.a k) (fireSet q) a
  let D := s.powerset
  have e : test (C:=C) O s J hk = fun U => ∑ q ∈ D,b q * H q U :=
    funext (fun U => acquire_all C (formatOnly O) s J hk U hz)
  have e' : blend (C:=C) a O s J hk = fun V => ∑ q ∈ D,(b q*w (s\q))*I q V := by
    funext V; apply Finset.sum_congr rfl; intro q _; unfold I w g b; ring
  have hH q := (final_mul (law G _ (C.beta N p)) (stack C p N k N (g q) hk) (Q q)
    (stack_envelope C p N k N (g q) hk (shelf_env _ hz)) (envL1 _ (shelf_env q he))).const_mul (b q)
  have hI q := (final_mul (prior G _) (g q) _ (shelf_env _ hz) (signal_int a O q he hk)).const_mul (b q*w (s\q))
  rw [e,e']; refine ⟨integrable_finsetSum _ fun _ _ => hH _,integrable_finsetSum _ fun _ _ => hI _,?_⟩
  rw [moment, integral_finsetSum _ (fun q _ => hH q), integral_finsetSum _ (fun q _ => hI q), Finset.mul_sum]
  apply Finset.sum_congr rfl; intro q hq
  have e := signal_dual a O q he (m:=k) le_rfl hk (g q) (shelf_env _ hz); rw [stack_origin] at e
  have hw : w (s\q)*w q=w s := by
    rw [mul_comm]; unfold w Ride.bump; dsimp only [fireSet,chooseMode]
    rw [← Finset.prod_union Finset.disjoint_sdiff,Finset.union_sdiff_of_subset (Finset.mem_powerset.mp hq)]
  rw [integral_const_mul, integral_const_mul]
  rw [e, show Ride.bump (C.S.a k) (fireSet s) a=w s from rfl,← hw]
  unfold moment Q w; ring

omit he hz in
def old (v : C.book.Token) (t : h≤N) : Scan C p N (Site (C.side h p)) :=
  fun i => (center C.S p t 0).copy i (C.seen v (0:Site (C.side N p)))
omit he hz in
def fresh (t : h≤k) (E : Config G (C.side k p)→ℂ) : Scan C p k (Site (C.side h p)) :=
  fun i => (center C.S p t 0).copy i E

omit he hz in
lemma copy_interior_all {c : Side} (T : Tiling c) (E : Config G c→ℂ) (hE : Interior univ E) (i : T.Cell) :
    Interior univ (T.copy i E) := by
  classical
  have H : Interior univ (E ∘ Lattice.pull (T.omega i) (T.translateBy i)) :=
    hE.unchanged _ _ (mapsTo_univ ..)
  by_cases h : T.hand i
  · rw [show T.copy i E=(fun U => star ((E ∘ Lattice.pull (T.omega i) (T.translateBy i)) U)) from funext fun _ => if_pos h]
    exact H.real
  rw [show T.copy i E=E ∘ Lattice.pull (T.omega i) (T.translateBy i) from funext fun _ => if_neg h]; exact H

omit he hz in
lemma old_inv (v : C.book.Token) (t : h≤N) (hc : C.Makes) (i : Site (C.side h p)) :
    Interior univ (old (C:=C) v t i) := by
  unfold old; apply copy_interior_all _ _ _ _
  obtain ⟨d,v⟩:=v
  change Interior _ (C.O N p v 0)
  have hp : Envelope (C.O N p (d:=d) v (0:Site _)) := Env.compact (C.continuousO N p d v 0)
  have H : Interior (↑((C.localSection d).footprint (0:Site (C.side N p))) : Set (Site (C.side N p))) (C.O N p (d:=d) v 0) := 
    ⟨C.invariant hc N p d v 0,hp.meas,C.localO N p d v 0,hp.cost⟩
  exact H.enlarges (subset_univ _)

omit he hz in
/-- If supplied only the *k→ell portion* of Stair, with the k densities
reading these integrals (e.g., exact function equality of the density at
signed birth), can pay by `lifted_spine` just as for an entire Lane input. -/
theorem cash (C : Family G) {h k ℓ d N p : ℕ} (X : Stair C (trays C h p) N p)
    (hk : k ≤ N) (hc : C.Makes) (t : h ≤ k) (v : C.label d) (E : Config G (C.side k p) → ℝ)
    (hE : Envelope (paint E)) (W : ℝ) (hW : 0 < W)
    (init : ∀ s : (trays C h p).Mode, X.echo C k s=blend (C:=C) (fun _ => d)
      (old ⟨d,v⟩ (t.trans hk)) s.val (fresh t (paint E)) hk)
    (run : X.Limit C k ℓ (fun _ => d))
    (stop : (X.representation ℓ).Radial (fun _ => W) 1 2 2 1) :
    Integrable (retrieve C t hk (paint E) (C.seen ⟨d,v⟩ (0:Site (C.side N p)))) (law G _ (C.beta N p)) ∧
      ‖moment (C.beta N p) (retrieve C t hk (paint E) (C.seen ⟨d,v⟩ (0:Site (C.side N p))))‖^
        ((Fintype.card (Site (C.side h p)):ℝ)⁻¹) ≤ Real.exp (Stock.expPrice C h ℓ d W 1 2 2 1) := by
  let O := old (p:=p) (C:=C) ⟨d,v⟩ (t.trans hk)
  let J := fresh t (paint E)
  let q (s : (trays C h p).Mode) := moment (C.beta N p) (test O s.val J hk)
  have e (s : (trays C h p).Mode) := blend_law (C:=C) (fun _ => d) O s.val
    (fun i => borel_bounded (old_inv _ _ hc i)) J hk (fun i => copy_safe (G:=G) (center C.S p t 0) (paint E) hE i)
  have hr : X.Lit C k (fun _ => d) q := by intro s; rw [init]; exact (e s).2.2
  let s := Stock.final (Site (C.side h p))
  exact ⟨(e s).1,lifted_spine (h:=h) C hc run hr stop hW⟩
end YM.UVNext.PhaseCoarse

import YM.Extra.WILSON_STARTUP.Store
import YM.Further.ITERATION_RECIPE_PRODUCER.Kin
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.DIRECTED_RECIPE.Recipe
import YM.Progress.DIRECTED_RECIPE.Symmetry


set_option warningAsError false

/-!
# Loading that very kinetic worksheet into the directed oven

At startup, literal Wilson β before and after the common widened-address
merger.

Thus `Bid.Oust` for a non-dummy `Recipe`, AND literal UV-shape
identities when requiring the additional exact-origin test within the recipe
(`safe`); first only, no `BatchPay` assumed to earn these.

`Approved`
itself would require syntactically different paths and predicates; we don't
transfer Oust through an arbitrary denotational equality.

Our test always
keeps the origin raw data, even though the same-period invoices support a
looser test too.

Extra path-dependent restrictions can be imposed by the
suppliers (needs proofs of their actual startup approval, in addition to
`BatchPay.permit` at advances).

All-curve β resolution still conditional on
genuine step estimates; see Bands.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Further.IterationRecipe
open Function Lattice Wilson RG RG.Supply RG.Shoot Precision Bid Pressure Exterior Extra.Iteration
open WilsonStartup Start Next.Scheduling Progress.DirectedRecipe Ovens Ovens.Pipes Input
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {a : Levels G} {O : ChartRatio G} {M : Horizon a} {k : Kin M O}
    {N p : ℕ} {e : ℕ → ℕ → Exchange} {u : ℕ → ℕ → Postage}

abbrev pipe (a : Levels G) (N p : ℕ) := dictionary G (a.S.side N p)
abbrev ink (a : Levels G) (N p : ℕ) := payload (a.params N).clip (a.budget N) G (a.S.side N p)
abbrev serving (k : Kin M O) (N p : ℕ) (β : ℝ) := fromTop k N p β (pipe a N p) (ink a N p β)

def Policy (r : Permissions a) := ∀ N p β, β∈band a N → r.starts N p β (pipe a N p) (ink a N p β)

def screen (r : Permissions a) : Permissions a := { r with
    starts := fun N p β X d => r.starts N p β X d ∧ X=pipe a N p ∧ d=ink a N p β }





variable (hk : ∀ N, k.path N N=crown G (a.params N).clip) (h : Start.Allows a N)
    {r : Permissions a} (hp : Policy r)
include hk h hp


omit hk h hp in
lemma atTop {R : Rep G (a.S.side N p)} (hR : (recipe k e u (screen r)).first N p R) : R=serving k N p R.beta := by
  obtain ⟨hb,X,d,hh,H⟩ := hR
  rw [H]; obtain ⟨-,rfl,rfl⟩ := hh.permit; rfl
omit hk h hp in
lemma begins_exact {R : Rep G (a.S.side N p)} (hR : PeriodFuture k e u (screen r) N p N R) :
    R.beta ∈ band a N ∧ SurfacePay k (screen r) N p R.beta (pipe a N p) (ink a N p R.beta) ∧ R=serving k N p R.beta := by
  cases hR with
  | begin hw he => obtain ⟨-,hv,ht⟩ := he.permit; subst_vars; exact ⟨hw,he,rfl⟩
  | struck hn _ _ _ => omega

omit hk h hp in
lemma grows_wide {R : Rep G (a.S.side N p)} (hR : PeriodFuture k e u (screen r) N p N R) : WilsonStartup.Wide R := by
  obtain ⟨hb,H,hx⟩ := begins_exact hR
  let n := a.S.side N p
  have he : Readdress (a.budget N) _ _ (Start.layout a N p R.beta).activities R.activities := Eq.mpr (congr_arg
    (fun R' => Readdress (a.budget N) _ _ (Start.layout a N p R.beta).activities (Rep.activities R')) hx) (H.ingredients.address (k.path N N) (a.params N).clip R.beta 0 (enumeration G n))
  refine ⟨fun i U hi => ?_⟩
  obtain ⟨j,rfl⟩ : i ∈ Set.range _ := of_not_not fun h => hi (congr_fun (he.restK _ h) U)
  rw [he.sup,he.inv,hR.pockets.2.1]
  rw [he.kernels] at hi
  exact (Start.wide ..).footprints _ U hi

variable {s : Survey G} {K : MapPrices} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
  {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y} {B : Beam K D}
  {k' : Kin M s.B.chart} (paid : Paid I a) (tax : Regime B e u W) (hm : M.Suffices K)
  {A : ClassicalCosts} {U : Apertures} (hs : Engine U A B u k')
omit hk h hp
include hs paid hm


end YM.Further.IterationRecipe

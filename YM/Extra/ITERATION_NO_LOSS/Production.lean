import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.ITERATION_NO_LOSS.Planned

/-!
# The common path worksheet, priced with the pressure grants

No quantification over a future re-extracted family to *produce* costs. Must
still anticipate the sufficient width, kernel, loop, gas and marker estimates
with this dependency order, and prove (among many others) the two dynamical
hypotheses in `Production.directed` on the actual paid Levels. The estimate
behind `Rates.quantum` in particular cannot price its slope only after L.

The placeholder initial `Sheet` is used to choose K; actual RRack must work
with the finally reserved choices (and clip `.direct` from this provisional
sheet). It's not enough just to buy one neighboring output at which some
remaining-data proof works. See ledger in report.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Production
open Filter Function Lattice Wilson RG RG.Supply Precision Pressure Pressure.Testing Tree Bloch Bid Craft Input 
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}



variable {P : Sheet G} {D : Rolls P} {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y}
variable {a : Levels G} {M : Horizon a} {K X : MapPrices} {U : Apertures} {A : ClassicalCosts} {H : QuantumCosts}
    {Q : PostCost D} {O : ChartRatio G} (hc : Before P U A H K) (hw : Warm H W) (hp : Paid I a)
    (hg : GapQuote D K Q) (hO : LocalRatio O)

include hc hw hp hg hO

/-- Select exactly one unmasked trajectory bundle and use a supplied
path-dependent recipe factory (subsequent unmarked/marked tasks still need
proofs about this selection).

`hpin` can come from the first output of menus,
not a new pre choice. -/
theorem directed (hpin : ∀ M : Horizon a, Rack a X M → ∃ T, Retained T M ∧ T.Suffices K)
    (hM : Rack a X M) (hN : ∀ N m, m < N → Harmonic (M.towers N m))
    (hR : ∀ T, Retained T M → T.Suffices K → Rates T K U A H Q O)
    (make : (M : Horizon a) → Kin M O → Shoot.Recipe a) (hm : ∀ M F,(make M F).path=F.path) :
    ∃ (T : Horizon a) (F : Kin T O) (B : Input.Directed G I O K Q), Retained T M ∧ T.Suffices K ∧ F.Planned Q ∧
      B.a=a ∧ HEq B.M T ∧ HEq B.kin F ∧ HEq B.bake (make T F) ∧
      ∀ N m, m≤N → Ticket B.M K U A N m (B.kin.path N m) := by
  obtain ⟨T,h1,h2⟩ := hpin M hM
  obtain ⟨F,hF,ht⟩ := planned hc hw hp h2 hg hO (fun N m he p => by rw [h1.1]; exact hM.oath N m _ he) (fun N m hm => by
    have he := (h1.2 N m hm).2
    exact fun r s b c => show (∑' z, (T.towers N m).T (r,b) c z)=_ from he ▸ hN N m hm r s b c) (hR T h1 h2)
  exact ⟨T,F,⟨a,hp,hO,T,F,h2,hF,make T F, hm T F⟩,h1,h2,hF,rfl,HEq.rfl,HEq.rfl,HEq.rfl,ht⟩
end YM.Extra.Iteration.Production

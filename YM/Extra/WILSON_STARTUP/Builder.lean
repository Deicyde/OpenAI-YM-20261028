import YM.Extra.WILSON_STARTUP.Fast
import YM.Extra.WILSON_STARTUP.Roll


/-!
# Startup-compatible inputs from parameterized loop producers (conditional!)

Freeze the retargetted MapPrices BEFORE L. The pressure pricing order can
still be used alongside startup asks for that quote before commissioning
levels. If RLoops fulfilled at a qualifying schedule (NOT established), there
are M' and `Kin M'` with the stated **top**, still meeting exactly the
`Directed` trajectory-independent kinetic ports. Must use the NEW objects, not
retarget after constructing actual recursions. Only the described pricing
asks anticipated; `RRequirements` may need substantially more for advances
on the new inputs. Keep those advances & retainer choices as distinct producer
tasks. Result for the basic retain/next predicates in particular doesn't allow
choosing more restrictive invariants ex post.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Builder
open RG Shoot Lattice Design Wilson Bid Input Precision Start Source Pressure
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge} {C : Supply.Sheet G} {D : Supply.Rolls C} {T : Supply.Protection D} {W : Supply.Delays T} {Y : Supply.Bar W}
    {I : Supply.Wait Y} {S : Labels.Frames G} {X : ∀ d, SectionData (S.level d)}

/-- Quote independent of later delays, all L, particular RLoops witnesses
and all Gate choices. Can use the simpler `Change.same_steps` if G.Simple,
Floor payments etc as there and the top linear root already aligned on curl. -/
def quote (C : Supply.Sheet G) (K : MapPrices) := (Change.retarget C K).choose



variable (C)



variable {C} {O : ChartRatio G} {Q : PostCost D} {K : MapPrices} {a : Levels G} {H : Horizon a}
    {kin : Kin H O}

/-- For the actual new PathData; chooser for these extra predicates still
must anticipate which advance estimates will be available in trajectories.
Nothing in Oust will pay an arbitrary extra test automatically. -/
structure Gates (a : Levels G) where
  retain (N m p : ℕ) : Rep G (a.S.side m p) → Prop
  first (N p : ℕ) : Rep G (a.S.side N p) → Prop
  next (N m p : ℕ) : Rep G (a.S.side m p) → Rep G (a.S.side (m+1) p) → Prop

def Gates.bake (R : Gates a) (kin : Kin H O) : Recipe a := ⟨kin.path,R.retain,R.first,R.next⟩

def assign (hI : Supply.Paid I a) (hO : LocalRatio O) (hH : H.Suffices K) (h : kin.Planned Q) (R : Gates a) :=
    tighten (G:=G) (Directed.mk a hI hO H kin hH h (R.bake kin) rfl)

def Gates.Pass (R : Gates a) := ∀ N p β, β∈band a N → R.first N p (layout a N p β) ∧ R.retain N N p (layout a N p β)

variable (hI : Supply.Paid I a) (hO : LocalRatio O) (hH : H.Suffices K) (h : kin.Planned Q) (R : Gates a)

theorem accepted (hr : ∀ N, kin.path N N = top G (a.params N).clip) (hR : R.Pass) (N : ℕ) :
    Approved (assign hI hO hH h R) N := approved_tight _ _ ⟨hr _,hR _⟩

theorem launched (hG : G.Simple) (hr : ∀ N, kin.path N N=top G (a.params N).clip) (hR : R.Pass)
    (H₀ : Timing.funded S X C W.betaEntry) : ∀ N p, Oust (assign hI hO hH h R) N p := fun N p =>
    oust _ N p (accepted hI hO hH h R hr hR N) (Timing.receive S X hG H₀ hI N).1







end YM.WilsonStartup.Builder

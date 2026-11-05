import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Timetable




/-!
# Alternate boot, scheduling the literal startup horizon BEFORE Before

Billing Kg for Oust and also for unmasked iteration (vs doing those on
M.K and only transforming afterwards; no apparent automatic continuation
of that theorem to our Cook needs). In particular K' does **not** depend
on the fitted comparison/import widths/relaxations nor future L calendar!
Only keep the same direct charge. T and A0 preserved as well as Sworn
H below, top Sworn is produced. No need assume the possibly wrong
positivity references for an arbitrary retained M across path changes.
Second boot, chemical variants can price RSetup statistics on this K'.

Mathematics from accepted code WilsonStartup.{Polar,Change}, Extra.Iteration;
rework some for dependent compat and keep keys not returned there. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.World
open Matrix Function Set Filter RG Wilson Lattice Bid Precision Exterior Bloch Tree Work
    WilsonStartup Change Design F08 Extra.Iteration Supply Pressure
open scoped BigOperators Topology Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {a : Levels G} {M H : Horizon a} {K U : MapPrices}
  {c c' : Clip} (ha : c'.direct=c.direct)

include ha





-- Quotes before any further Stage consumers. `prices` here are weaker
-- data requests, more general estimates consumers must be able to spell
-- entrances for the resulting depths BEFORE usage.
structure Grant (K U : MapPrices) : Prop where
  eta i : U.η i ≤ K.η i
  alpha i : U.α i ≤ K.α i
  reserve i : K.Ω i ≤ U.Ω i

omit ha
lemma concedes (h : Grant K U) {a : Levels G} {M : Horizon a} (T : M.Suffices K) : M.Suffices U :=
  ⟨fun _ _ hi => covered_mono (T.rows _ _ hi) (h.alpha _) (h.reserve _),fun _ _ hi b => floor_mono (T.all _ _ hi b) (h.eta _) (h.reserve _),
    fun _ _ hi => deep_mono _ (T.costs _ _ hi) (h.alpha _) (h.reserve _),T.crossings,T.stack,T.top⟩

structure Tour (a : Levels G) (H M : Horizon a) : Prop extends Overlay H M where
  links N m : m<N → (H.towers N m).T=(M.towers N m).T


end YM.Further.PhysicalPeriodLimitF933.World

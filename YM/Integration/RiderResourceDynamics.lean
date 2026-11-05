import YM.Integration.RiderWorkloadEnvelope

/-! A concrete resource calendar, separated from any theorem selecting a
physical Family.  This is the native `Unveiled.console` constructor alone:
its positive hearth is one and its lighting uses the original `Rider.atEra`.
The fixed zero workload supplies only default resource slots; the purchased
family still contains every workload through `Rider.calendar`.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.RiderResourceDynamics
open Lattice RG Wilson
open RemainderComparison RemainderComparison.Hymnal
open RemainderComparison.Placement

def fromWorkload (G : Gauge) (P : Rider.Workload) : Dynamics G where
  ν _ _ _ _ := 1
  tall _ _ _ _ := zero_lt_one
  lighting := @fun _ _ D X _ _ _ _ Y _ _ _ _ i j t =>
    Rider.atEra P D Y i j
      (Rider.scope P (X i j |>.halo) ((max t.val (j + 1)) + 1))

def defaultDynamics (G : Gauge) : Dynamics G :=
  fromWorkload G (RiderWorkloadEnvelope.workload (0, 0, 0, 0, 0))

theorem fromWorkload_nu (G : Gauge) (P : Rider.Workload)
    (j i : ℕ) (E E' : RG.Stage) :
    (fromWorkload G P).ν j i E E' = 1 := rfl


theorem calendar_hearth (G : Gauge) (P : Rider.Workload)
    (j i : ℕ) (E E' : RG.Stage) :
    (Rider.calendar P (defaultDynamics G)).cultivate.hearth j i E E' =
      min 1 (min 1 (Seasons.portion G E')) := rfl

end YM.Integration.RiderResourceDynamics

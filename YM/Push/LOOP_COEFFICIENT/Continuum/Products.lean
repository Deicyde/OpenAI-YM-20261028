import YM.Push.LOOP_COEFFICIENT.Continuum.Curls

/-!
# Alternating to full corner counting. Orbital and transverse identities
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Continuum
open Matrix Function Filter Set Lattice Laurent Bloch Wilson RG Work.F02 Complex Paths 
open scoped BigOperators
variable {G : Gauge} (k : Momentum)






def momentumSq := ∑ i, k i ^ 2




def needle (T : CColor G) : Polarization G := fun i => if i.1=1 then T i.2 else 0










-- Direction and color pair, on fixed orbitals.








variable (p : Momentum)










end YM.Push.Loops.Continuum

import YM.Push.LOOP_COEFFICIENT.Continuum.Matrix
import YM.Push.LOOP_COEFFICIENT.Fine.Root


/-!
# Continued unscaled fine gauge operator and its principal vertex
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Fine
open Matrix Set Lattice Laurent Exterior Bloch RG Wilson Work.F02 Function Filter Paths Complex Metric Continuum
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {G : Gauge} {q p s : Momentum}


lemma root_base_entry (G : Gauge) (i j k) : (root G).base k i j = if i.2=j then 1-cexp (Continuum.freq k i.1) else 0 := by simp [root,longitudinal,Exterior.q,Continuum.freq]
lemma root_one_entry (q p : Momentum) (v : Polarization G) (i j) : (root G).one q p v i j = cexp (Continuum.freq q i.1) * ((coupling G).lin (shaft i.1 v)) i.2 j := rfl
lemma root_two_entry (q p s : Momentum) (v w : Polarization G) (i j) : (root G).two q p s v w i j = cexp (Continuum.freq q i.1) * ((coupling G).quad (shaft i.1 v) (shaft i.1 w)) i.2 j := rfl
lemma freq_period (k : Momentum) (i : Axis) (z : Cover) : cexp (Continuum.freq (k+reciprocal z) i) = cexp (Continuum.freq k i) := by simp_rw [Continuum.freq, ← wind_step]; change mode _ _ = mode _ _; simp
lemma root_lit (G : Gauge) (η : ℝ) : Lit (root G) η := by
  constructor
  · intro k hk; simp_rw [show (root G).base = fun k => of fun i j => if i.2=j then 1-cexp (Continuum.freq k i.1) else 0 from funext fun _ => Matrix.ext fun i j => root_base_entry ..]; refine ⟨analyticMatrix (fun i j => ?_),fun z => by simp only [freq_period]⟩
    simp only [Matrix.of_apply]; split <;> first | exact contDiffAt_const | (unfold Continuum.freq; fun_prop)
  · intro k p v _ _; exact ⟨analyticMatrix (fun i j => by simp_rw [root_one_entry, Continuum.freq]; fun_prop), fun z w => Matrix.ext fun i j => by rw [root_one_entry,freq_period,root_one_entry]⟩
  intro k p s v w _ _ _; exact ⟨analyticMatrix (fun i j => by simp_rw [root_two_entry, Continuum.freq]; fun_prop), fun z u t => Matrix.ext fun i j => by rw [root_two_entry,freq_period,root_two_entry]⟩






end YM.Push.Loops.Fine

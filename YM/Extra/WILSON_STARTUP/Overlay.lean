import YM.Extra.WILSON_STARTUP.Engine
import YM.Work.C02

/-!
# Alignment of the horizon's unmodified and local top stack (positive root case)

Here don't even have to change the mf,mn,o! For E top symmetric positive
root on the exact two-forms the *linear* full*d columns coincide. Only use
this at the top as input, not on the complement in each diagonal/metric
prop at lower steps. New nonlinear path and behavior of prices on arbitrary
U unaffected by this LINEAR assertion. Handles harmonic directions. Strict
direct <1 for the pos-root alignment calculation.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Change
open Matrix Function Filter RG Wilson Lattice Bid Precision Exterior Bloch Tree Work Design
open scoped BigOperators Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {a : Levels G} {M H : Horizon a} {K : MapPrices}
variable {n f : Side} {S : StepData n f} {U : Towers S.patch.L}
variable {B C : Bed} {p q : Clip} {η Ω : ℝ}

def mapped (H : Horizon a) : Horizon a where
  H N m := if m=N then bed (a.params N).clip else H.H N m
  towers := H.towers

theorem overlaid (H : Horizon a) : Overlay (mapped H) H :=
  ⟨fun _ => if_pos rfl,fun _ _ h => if_neg h.ne,fun _ _ _ => rfl⟩

lemma metric_coincide (h : Floor B p n η Ω) (hh : B.diagonal.acts n = 1) :
    B.metric.acts n * d 1 n = (bed p).metric.acts n * d 1 n := by simp only [bed,spike_acts,one_smul,h.same,hh]

lemma top_diagonal (hU : Towers.Diagonal S B C U) (h : Floor B p f η Ω) (hh : B.diagonal.acts f = 1) :
    Towers.Diagonal S (bed p) C U := by
  have hk : Precision.K ((bed p).metric.acts f) = Precision.K (B.metric.acts f) := by rw [Precision.K,Precision.K,Matrix.mul_assoc,Matrix.mul_assoc,metric_coincide h hh]
  exact ⟨⟨hk ▸ hU.trial.primal,hU.trial.dual⟩,hU.transport, by rw [hU.stays]; simp only [bed,spike_acts,one_smul,hh]⟩



structure Aligned (M : Horizon a) (K : MapPrices) : Prop where
  full N n : (M.H N N).full (a.params N).clip n * d 1 n = (bed (a.params N).clip).full (a.params N).clip n * d 1 n
  η N : K.η (a.clock.J N) ≤ 1
  Ω N : 1 ≤ K.Ω (a.clock.J N)
  direct N : (a.params N).clip.direct ≤ 1





section root
variable {ι τ : Type} [Fintype ι] (P : Matrix ι ι ℝ)



end root






end YM.WilsonStartup.Change

import YM.Planned.PRIMARY_INTEGRAL_295.Barges
import YM.Planned.PRIMARY_INTEGRAL_295.Night
/-!
# Covariant actual Gram across gauged Kw.µ paths

Preserves K representative at V even for negative directed Q coords.
Here all g transforms arbitrary. DOES use exact normalized Q identities
from Branches and K.ratio.Forest. Doesn't assert clamped vs true
kernel fit. Doesn't assume group-equivariance of global plog (uses
curvature at Q before converting fderiv at the identity).

-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Hoods
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks Night Hives Candles Barges
open Next.Fluctuations Work.E03
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G:Gauge} {c f : Side} {S:StepData c f}
variable (K:Core G S) (V:Config G c)(z: Site c→G.El)
section
variable (s:Signed)
-- true sign transforming positive representative, root at ZERO always odd

def push_gauge (z: Site c → G.El)(s:Signed) : Site c → G.El:= z ∘ affine s 0
def flatten (z:Site c→ G.El)(i:Bond f):G.El:= z (S.ratio.parent i.1)

lemma breath (a:Temps G f)(i:Bond f): collect G (K.reachable (harvest.burn (flatten (S:=S) z) a)) i =
   G.adjoint (flatten (S:=S) z i) (collect G (K.reachable a) i) :=by
   -- including G.ColorIndex empty!
   rw [Bosom.count_root, Bosom.count_root]; split <;> rename_i h
   · rw [map_zero]
   let p:=flatten (S:=S) z
   apply PiLp.ext; intro j; rfl
-- physical coarse pull at centered rotation
lemma pulls (s:Signed):pull s 0 (Lattice.gauge z V)=Lattice.gauge (push_gauge z s) (pull s 0 V):=by
    exact Push.Local.pull_gauge s 0 V z
lemma lit (a:Temps G f):upload K (Lattice.gauge z V) (harvest.burn (flatten (S:=S) z) a) = Lattice.gauge (z ∘ S.ratio.parent) (upload K V a):=by
    funext i; unfold upload increment; rw [← copied S.ratio S.patch.odd_side,breath]
    unfold Lattice.gauge constantGauge flatten; simp only [Function.comp_apply]
    have he (x:G.El)(v:G.Color):G.lieExp (G.adjoint x v) = x*G.lieExp v*x⁻¹:=by apply G.mat_injective; simp [G.mat_adjoint, G.exp_conjugate]; rfl
    rw [he]; group

lemma glows (a:Temps G f): owl K s (Lattice.gauge z V) (harvest.burn (flatten (S:=S) z) a) = Lattice.gauge (push_gauge z s ∘ S.ratio.parent) (owl K s V a):=by
    have he : push_gauge (z ∘ S.ratio.parent) s= push_gauge z s ∘ S.ratio.parent:=by
       funext i; unfold push_gauge; simp [affine,S.ratio.parent_signed S.patch.odd_side]
    unfold owl; rw [lit,pulls,he]

lemma bubble (a:Temps G f) (hk:S.patch.Branches S.kernel G):corn K s (Lattice.gauge z V) (harvest.burn (flatten (S:=S) z) a)=Lattice.gauge (push_gauge z s) (corn K s V a):=by
   unfold corn; rw [glows]; funext i; unfold StepData.prediction; rw [S.updateGauged hk,(S.patch.bond_gauge (h:=hk) ..).2]; unfold Lattice.gauge; rw [Function.comp_apply,Function.comp_apply,S.ratio.embed_parent,S.ratio.embed_parent]
end
end YM.Planned.PrimaryIntegral295.Hoods

import YM.Progress.STATIONARY_SCENES.Frames
import YM.Push.PRICE_COMPILER.Authors

/-!
# Holomorphic q-averaging theorem

Parameter width even after passage to the integral, via paid joint
Fourier series. Weak enough for this route to require periodically resetting
in parameters as well; covers 's application, not arbitrary mixed
representations. Radian + modes on the parameter, unit Haar on internal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave
open Lattice Laurent Bloch Filter Function Topology Matrix
open Work.F07 Set MeasureTheory UnitAddTorus
open scoped Classical BigOperators Topology
variable {k:Type*}[Fintype k]{α β:Type}

/-- Holomorphic + periodic + sup, *scalar*. -/
structure Sold (s C:ℝ)(f:Phase k→ℂ):Prop where
  vane : Vane f s
  nn : 0≤C
  budget : ∀ p∈strip s,‖f p‖≤C

-- Phase coordinates (not scaled); use k⊕Axis for parameters + one internal q

def thread (p:Phase k)(q:Momentum): Phase (k⊕Axis):= Sum.elim p q
omit [Fintype k] in
lemma thread_in {p:Phase k}{q:Momentum}{s:ℝ}(h:p∈strip s)(ht:q∈strip s): thread p q∈strip s:=by rintro (i|i); exact h i; exact ht i
omit [Fintype k] in
lemma zero_in {s:ℝ}(h:0<s):(0:Phase k)∈strip s:= realStrip _ h (by simp)
omit [Fintype k] in
lemma threaded (x:Cover) (p:Phase k)(q:Momentum): thread p (q+reciprocal x)=thread p q+reciprocal (Sum.elim (0:Shift k) x):=by ext1 (i|i); simp [thread,reciprocal]; rfl
omit [Fintype k] in
lemma threaded_param (x:Shift k) (p:Phase k)(q:Momentum): thread (p+reciprocal x) q=thread p q+reciprocal (Sum.elim x (0:Cover)):=by ext1 (i|i); exact rfl; simp [thread,reciprocal]

omit [Fintype k] in
lemma threadD' (p:Phase k)(q:Momentum): DifferentiableAt ℂ (thread p) q:=by
  apply differentiableAt_pi.mpr; rintro (i|i) <;> (unfold thread; simp <;> try fun_prop)


variable {F:Phase (k⊕Axis)→ℂ}{s C:ℝ}(H:Sold s C F)



include H
-- The F integrand is integrable on the internal torus for every external
-- point, despite Choice opaque walk on wrap representatives.



variable (k)


private def string (z:Cover):ℂ:=∫ a:Rim Axis,mFourier z a ∂ globe Axis
omit H in
private lemma string_le (z:Cover):‖string z‖≤1:=by
  have hz (a:Rim Axis): ‖mFourier z a‖ ≤ 1:= (ContinuousMap.norm_coe_le_norm _ _).trans_eq mFourier_norm
  unfold string; apply (norm_integral_le_of_norm_le_const (Eventually.of_forall hz)).trans; simp


variable {k}





  -- only need q real, so can't use congr_arg; integral ae substitute
end YM.Primitives.TwoWave

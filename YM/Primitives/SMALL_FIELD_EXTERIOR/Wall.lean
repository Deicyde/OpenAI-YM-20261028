import YM.Primitives.SMALL_FIELD_EXTERIOR.Shed
import YM.Push.BETA_TRANSPORT.Joint
import YM.Push.STATIONARY_UNIFORM.Paths



/-!
# What costs the complement? (weight relative to a coarse field)

This is an actual energy barrier. Off the chosen domain, at least one
nonlinear expense must be paid, even at seam, even for branch tags (with positive likelihood), on **any**
of the specified trees. Uses E02 on actual `Bid.Cops` and doesn't need a log
expansion outside the chart. Uniform stamp before period (post L).
Does NOT infer volume-independent smallness on the relative contributions
after normalization. See `Dross`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior.Forestage
open Function Set Filter MeasureTheory Metric
open Lattice Precision Wilson RG Tree Pressure Pressure.Stores Next.Fluctuations Push.Uniform
open YM.Push.BetaTransport
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} (B : Forest S.ratio) {r D d β W J : ℝ}

def windowCount (P : Patch) := ((box (macroR P)).card:ℝ) * Fintype.card PlaqAxes

private lemma walls (i : Site c) (U : Config G f) (h : energy U ≤ d^2/2) (hd : 0 ≤ d) : port S i U ≤ windowCount S.patch * d := by
  let w := S.ratio.embed i
  let X := box (macroR S.patch)
  have he (x : Site f) (p : PlaqAxes) : G.chord (faceValue U (x,p)) ≤ d := by
    have hv : G.price (faceValue U (x,p)) ≤ energy U := Finset.single_le_sum
      (f:=fun p => G.price (faceValue U p)) (fun p _ => (G.price_range _).1) (Finset.mem_univ _)
    apply (sq_le_sq₀ (G.chord_nonneg _) hd).mp
    rw [G.chord_price]; linarith
  have hf (x : Cover) (p : PlaqAxes) : Axial.face X (expandAt w U) x p ≤ d := by
    unfold Axial.face; split_ifs
    · unfold faceValue; simp only [travel_at]; exact he _ _
    exact hd
  calc
    _ ≤ ∑ _x∈X, ∑ _p : PlaqAxes,d := Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun p _ => hf x p
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,windowCount,X]; ring





-- Relative log links small force inclusion in the literal event.


-- post-L. Uniform in these tori using the E02 charge.
structure Barrier (G : Gauge) (P : Patch) (Q : KernelChoices) (r D : ℝ) : Prop where
  positive : 0 < D
  energy {c f : Side} (S : StepData c f) (e : S.patch=P) (q : S.kernel=Q) (h : Bid.Larger (G:=G) S) :
    ∀ B : Forest S.ratio, ∀ x : Positions (Primary c G), ∀ a : B.Slice G, a∉shed B x r →
    ∀ t : S.Choices, 0 < S.likelihood (B.drape a) t → D < totalEnergy S t (B.drape a,roof G x)





end YM.Primitives.SmallFieldExterior.Forestage

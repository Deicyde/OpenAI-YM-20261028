import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Jets
import YM.Extra.SOURCE_HISTORIES.Retained
import YM.Next.UV_STRESS.Aligned
import YM.PhysicalNext.ORDERED_AFFINE_2B.Fixed
import YM.Push.RELAY_DIFFERENCE.SingleMajorant


/-!
# E units for the real affine reading with one centered Gaussian

Normalized arbitrary V directions with a prescribed polynomial growth,
*all positions*, arbitrary origin (e.g. that of a larger support).
The scalar subtraction is priced by the LOCATION of each of its
physical affine rows (summing other labels later does not get to assume
an O(1) bound on the value of an extensive scalar). The mean-shift
is that used in the same integrand, not a comparison of matrix powers on
a flat or reshaped field. Additional invoices for using a moving, hard
chart read or integrating the Gaussian are different obligations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B
open Function Filter Lattice Wilson RG Precision Pressure Tree Matrix
open Next Next.Fluctuations Next.SectorChange Push.SectorMeasure
open WardBin.Lies AnalyticBridge.SectorAffine
open AnalyticBridge.LocalGaussian (Ticket add_parts linear_parts)
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {V : Config G c} {n P : ℕ} {t d C : ℝ}
  {o : Site c} {l : List (Directions G c)}

section units
variable {ι : Type} [Fintype ι] {H : Config G c → ι → ℝ} {a : ι → Site c} {M : ℕ → ℝ}
lemma BundleQuote.smooth (h : BundleQuote n a d M H V) : Germ n H V :=
  contDiffAt_pi.mpr (fun i => (h i).smooth)

lemma BundleQuote.component (h : BundleQuote n a d M H V) (hl : l.length≤n) (i : ι) :
    leftDerivs (fun v => H v i) l V = leftDerivs H l V i :=
  linear_parts (ContinuousLinearMap.proj i) h.smooth hl

def weight (o p : Site c) (P l : ℕ) := (((1+(separation p o:ℝ))^P)^l)⁻¹

def Earned (o : Site c) (P : ℕ) (M : ℝ) (l : List (Directions G c)) (V : Config G c) (a : ι → Site c) (H : Config G c → ι → ℝ) :=
    ∀ i, weight o (a i) P l.length * |leftDerivs H l V i| ≤ M

lemma BundleQuote.earn (h : BundleQuote n a d (orderedCost G t C) H V)
    (hl : l.length≤n) (ha : Afford t P o l) (hd : 0<d) (ht : 0<t) :
    Earned o P (sumCost G d P l.length*C) l V a H := by
  intro i; have hh := (h i).authenticated hd ht P hl ha
  rwa [h.component hl i] at hh


end units

variable {S : StepData c f} {T : Tube G S} {x ε s M : ℝ}
    {k : S.Choices} {A : Stores S} {F : Forest S.ratio} {q : Chi}

namespace Fixed.Fees
variable (h : Fees T x A F k q ε V n s d M) (hd : 0 < d) (ht : 0 < temp x)
  (hl : l.length ≤ n) (ha : Afford (temp x) P o l) (Y : LinkArray G (Frozen A x F))
  {g : ℝ} (hg : 0 < g) (z : Prices G (Active A x F))

include h hd ht hl ha hg





omit hg ht in
/-- Both full exponential Schur prices at  argument; amount for
positive orders `l` still has (temp x)^l. Apply `Fixed.pricing`: t'≤1
and t' ≤ 2 * fiery G x P.L, so the same C_L * fine-t is available. -/
lemma assets (hh : 0≤temp x) :
    let p := Wisps.front A F (G:=G) (x:=x); let e := FreeResolvent.native c
    let a := Wisps.down S (G:=G); let u := (temp x)^l.length * sumCost G (SelectedOrderedKernels.narrow n d) P l.length
    let v := M*Real.exp (-s*radiusB x); let w := FreeResolvent.Mark.radial (Directions G c) e o P
    FreeResolvent.Mark.Bill w e a p l d (u*M) (leftDerivs (D T x A F k) l V) ∧
    FreeResolvent.Mark.Bill w e p p l d (u*M) (leftDerivs (precision T x A F k) l V) ∧
    FreeResolvent.Mark.Bill w e p p l d (u*M) (leftDerivs (Fixed.covariance T x A F k) l V) ∧
    FreeResolvent.Mark.Bill w e p p l d (u*v) (leftDerivs (distortion T x A F k) l V) ∧
    FreeResolvent.Mark.Bill w e p p l d (u*v) (leftDerivs (mismatch T x A F k) l V) := by
  have hd := SelectedOrderedKernels.narrow_pos n hd
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := h.matrices
  exact ⟨matrix_pays h₁ hd P hh hl ha,matrix_pays h₂ hd P hh hl ha,matrix_pays h₃ hd P hh hl ha,
    matrix_pays h₄ hd P hh hl ha, matrix_pays h₅ hd P hh hl ha⟩

end Fixed.Fees
end YM.PhysicalNext.OrderedAffine2B

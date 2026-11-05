import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Leases
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Survey


/-!
# Pricing quadratic rationals from actual endpoint Co/C geometry

Give component jet/change tests for insertions at endpoints identified by
these physical reads.

`dual`'s coefficient x,i,j,n is *after* paying its
window/route cost; only use with the primitive ordered inverse and kernel
estimates.

No resolvent/log-det conclusion granted here.

Very similar
for per-guide-row negative terms or linear sources; all evaluated in the
same ReadPack, NOT substituting a vacuum comparator.

We do not absorb an
extensive flat log into a local amplitude.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson ProjectorNext.Equivariance Next.SectorChange
  Next.SectorChange.Gaussian Next.SectorChange.Rows YM.Push.SectorMeasure
  YM.Next.Foundations Precision MeasureTheory Metric Curtain Notice Moments
open scoped Topology BigOperators Matrix.Norms.Frobenius YM.Push.SectorMeasure ContDiff Classical

section move
variable {G : Gauge} {c f : Side} {S : StepData c f} {d : Desk G S} {u u' : Spot d}
    {H R K : Type} [Fintype H] [Fintype R] {X X' : Support c} {l : Viewport u X H R K} {l' : Viewport u' X' H R K}
    {a : Notice l} {a' : Notice l'} {p : Reel G H R K} {W : Directions G c → Prop}
    {Y : Finset (Component G H R)} {z : Prices G (H⊕R)} {ρ r : ℝ} {x : ℝ} {V : Config G c} {k : ℕ}

-- Compare roots to z, allowing held-Z shifts. Choose B=1 when exact.
def ballast {G : Gauge} {I : Type} (C : ℝ) (Y : Finset (I×G.ColorIndex)) (z : Prices G I) := C*Real.sqrt (floorPrice Y z)
lemma buoy {G : Gauge} {I : Type} (Y : Finset (I×G.ColorIndex)) (z : Prices G I) {C : ℝ} (he : 1 ≤ C) :
    1 ≤ ballast C Y z := by
  refine one_le_mul_of_one_le_of_one_le he ?_
  exact le_trans (le_of_eq Real.sqrt_one.symm) (Real.sqrt_le_sqrt (inPrice ..))
lemma ballast_sq {G : Gauge} {I : Type} (Y : Finset (I×G.ColorIndex)) (z : Prices G I) (C : ℝ) :
    ballast C Y z^2=C^2* floorPrice Y z := by
  unfold ballast; rw [mul_pow,Real.sq_sqrt (zero_le_one.trans (inPrice ..))]
lemma buoys {G : Gauge} {I : Type} (Y : Finset (I×G.ColorIndex)) (z : Prices G I) {C : ℝ} {i}
    (hi : i∈Y) (hc : 1 ≤ C) : ‖z i‖ ≤ ballast C Y z := by
  rw [← sq_le_sq₀ (norm_nonneg _) (zero_le_one.trans (buoy Y z hc)),ballast_sq,Real.norm_eq_abs,sq_abs]
  exact le_trans (b:=load Y z) (Finset.single_le_sum (fun i _ => sq_nonneg (z i)) hi) <|
    le_trans (b:=floorPrice Y z) (le_add_of_nonneg_left zero_le_one)
      (le_mul_of_one_le_left (zero_le_one.trans (inPrice ..)) (one_le_pow₀ hc))

omit [Fintype H] [Fintype R] in
/-- Simultaneous two-version use in Outlook; mean change in `u` units. -/
lemma ballast_moves {X : ℝ} {v t' : Prices G (H⊕R)} (hq : ∀ i∈Y, ‖v i - t' i‖ ≤ X)
    (hi : 0 ≤ X) {z : Prices G (H⊕R)} (hz : z=v ∨ z=t') : ∀ i∈Y,‖v i‖ ≤ ballast (1+X) Y z ∧ ‖t' i‖ ≤ ballast (1+X) Y z := by
  intro i h
  have he (s w z : ℝ) (hs : 1≤z) (hz : ‖w‖ ≤ z) (hh : ‖s-w‖ ≤ X) : ‖s‖ ≤ (1+X)*z := by
    have hh := add_le_add hh hz
    have hx := norm_add_le (s-w) w; rw [sub_add_cancel] at hx
    exact (hx.trans hh).trans (by nlinarith)
  let y := Real.sqrt (floorPrice Y z)
  have hp : 1≤ y := by simpa only [ballast,one_mul] using buoy Y z (le_refl 1)
  have hy : ‖z i‖ ≤ y := by simpa [ballast,y] using buoys Y z h (le_refl 1)
  rcases hz with heq|heq <;> subst z
  · exact ⟨buoys _ _ h (by linarith),he _ _ _ hp hy (by rw [norm_sub_rev]; exact hq i h)⟩
  exact ⟨he _ _ _ hp hy (hq i h),buoys _ _ h (by linarith)⟩

variable {i j : H⊕R}

/-- Coefficients on given (i,j) at all colors, e.g. from
`u.price:cardCost`. User commits identity on flags for their particular
`a.movement z` and actual address. The budget tests cost the whole
extension of these coefficients BEFORE `par` is invoked. They can also
use the centered criteria there about this very `p`. -/
def dual (F : G.ColorIndex → G.ColorIndex → Config G c → LinkArray G K → ℝ)
    (i j : H⊕R) (V : Config G c) (q : Display G H R K) : ℝ :=
    ∑ k:G.ColorIndex,∑ b:G.ColorIndex,(q.2 (i,k)*(F k b V q.1*q.2 (j,b)))/2

def lin (F : G.ColorIndex → Config G c → LinkArray G K → ℝ)
    (i : H⊕R) (V : Config G c) (q : Display G H R K) : ℝ :=
    ∑ k:G.ColorIndex,F k V q.1*q.2 (i,k)

variable {F F' : G.ColorIndex → G.ColorIndex → Config G c → LinkArray G K → ℝ}
    {E E' : G.ColorIndex → Config G c → LinkArray G K → ℝ}
open Spot

-- These certify such Reads only with the indicated *diagonal address
-- synchronization* of the coefficients.
omit [Fintype H] [Fintype R] in
lemma happens (D : u.Slices) (N : ℕ) (P : u.Visual) (hi : ∀ k b,F k b V (l.info P).1=D.difference V (l.slot (i,k)) (l.slot (j,b)) N) :
    dual F i j V (l.info P)=u.cardCost D V P (.inr (.inr (l.read i,l.read j,N))) := by
  unfold dual; simp_rw [hi]; rfl
omit [Fintype H] [Fintype R] in
lemma one_way (D : u.Slices) (P : u.Visual) (hi : ∀ k,E k V (l.info P).1=u.sourceFee V P (l.slot (i,k))) :
    lin E i V (l.info P)=u.cardCost D V P (.inr (.inl (l.read i))) := by unfold lin; simp_rw [hi]; rfl

/-- Registration tariffs use at BOTH snapshots if forecasting. -/
lemma endpoint (ht : ∀ t∈Y, Charge W k V r (a.movement p t)) (he : 1 ≤ ρ) (hx : ∀ t∈Y, ‖a.imprint V p t‖ ≤ ballast ρ Y z) (J : Component G H R) (Hj : J∈Y) :
    Ticket W k V (ballast ρ Y z) r (a.movement p J) := (ht J Hj).with_one (hx J Hj) (buoy Y z he)

-- If using individual per-party debts, can sum at this point instead of counting colors.
lemma line {C : ℝ} (hx : ∀ b:G.ColorIndex,(i,b)∈Y) (he : 0≤r)
    (hh : ∀ t∈Y, Ticket W k V (ballast ρ Y z) r (a.movement p t))
    (hf : ∀ b:G.ColorIndex, Ticket W k V C r (fun U => E b U p.1)) :
    Ticket W k V (Fintype.card G.ColorIndex*(C*ballast ρ Y z)) (2*r) (fun U => lin E i U (p.1,a.imprint U p)) := by
  have ht := Ticket.sum (I:=Finset.univ) (add_nonneg he he) (fun b _ => (hf b).mul (hh _ (hx b)))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← two_mul] at ht
  convert! ht using 1
  ext x; simp only [lin,Finset.sum_apply,Pi.mul_apply]; rfl

private def half (a : Notice l) (i j : H⊕R) (F : G.ColorIndex → G.ColorIndex → Config G c → LinkArray G K → ℝ)
    (p : Reel G H R K) (w : G.ColorIndex×G.ColorIndex) (U : Config G c) : ℝ :=
    (1/2:ℝ) * (a.movement p (i,w.1) U * (F w.1 w.2 U p.1 * a.movement p (j,w.2) U))
private lemma duality (i j : H⊕R) :
    (fun U => dual F i j U (p.1,a.imprint U p))=∑ w:G.ColorIndex×G.ColorIndex,half a i j F p w := by
  ext x; simp only [dual,Finset.sum_apply,half,Fintype.sum_prod_type,Notice.movement]; apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j hj; ring

lemma par {C : ℝ} (hx : ∀ b:G.ColorIndex,(i,b)∈Y ∧ (j,b)∈Y) (he : 0 ≤ r)
    (hh : ∀ t∈Y, Ticket W k V (ballast ρ Y z) r (a.movement p t))
    (hf : ∀ b b':G.ColorIndex, Ticket W k V C r (fun U => F b b' U p.1)) :
    Ticket W k V (Fintype.card G.ColorIndex^2*(C*ρ^2)* floorPrice Y z) (3*r)
      (fun U => dual F i j U (p.1,a.imprint U p)) := by
  have hg : Ticket W k V 1 0 (fun _ => (1/2:ℝ)) := (Ticket.pure le_rfl _).mono (by norm_num) le_rfl
  let b := ballast ρ Y z
  have hu (t : G.ColorIndex × G.ColorIndex) : Ticket W k V (b*(C*b)) (3*r) (half a i j F p t) := by
    obtain ⟨x,y⟩ := t; exact (hg.mul ((hh _ (hx x).1).mul ((hf x y).mul (hh _ (hx y).2)))).mono (by rw [one_mul]) (by linarith)
  rw [duality]; refine (Ticket.sum (by positivity) (fun i _ => hu i)).mono ?_ le_rfl
  refine le_of_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Nat.cast_mul]
  rw [show b*(C*b)=C*b^2 by ring, show b^2=_ from ballast_sq Y z ρ]; ring



-- Does NOT have to interpolate through an ill-defined sector/flag,
-- but still need both leases in ONE comparison budget.

end move
end YM.AnalyticBridge.LocalGaussian

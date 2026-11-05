import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Shutter

/-!
# Pay the score of the SAME conditional kernel

The trajectory variation of a print at a held position costs also; do
not just estimate at fixed Z. Use entrywise inverse/log tickets on the
actual *marginal*, including its normalization, not the pre-local
inverse. Later integrate including the resulting dimension and Z
polynomials. `κ` logarithm of a single Haar read is actual chosen
B70 χ(J) data; supply budgets about the moving base within this REAL
extension region. This theorem never purports to bound a derivative
OF a hard chart switch.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision MeasureTheory Next.SectorChange Next.SectorChange.Gaussian
open Next.SectorChange.Rows YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open Curtain
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S} {u u' : Spot d}
  {H R K : Type} [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R]
  {X X' : Support c} {l : Viewport u X H R K}

namespace Notice
variable (a : Notice l)
abbrev Component (G : Gauge) (H R : Type) := (H⊕R) × G.ColorIndex

def inverseSlot (i j : Component G H R) (V : Config G c) := (a.C V)⁻¹ i j

def movement (p : Reel G H R K) (i : Component G H R) (V : Config G c) := a.imprint V p i

def jacket (l : Viewport u X H R K) (p : Reel G H R K) (i : H) (V : Config G c) :=
    -Real.log (d.chart.scale * d.chart.J (unlit (l.copy V) p.2.2 i))

def dressing (V : Config G c) := -Real.log (coat (a.C V))

private def halfLeg (p : Reel G H R K) (i j : Component G H R) : Config G c → ℝ :=
    (fun _ => (-1/2:ℝ)) * (a.movement p i * (a.inverseSlot i j * a.movement p j))

def stamps (p : Reel G H R K) (V : Config G c) := tab d.chart d.g (a.tide V p.1) (l.copy V) (a.C V) p.2

theorem printed (p : Reel G H R K) : a.stamps p = (fun _ : Config G c => -Real.log (d.g ^ Fintype.card (H × G.ColorIndex))) +
    (∑ i,jacket l p i) + a.dressing + ∑ k : Component G H R × Component G H R,a.halfLeg p k.1 k.2 := by
  funext V
  unfold stamps tab dressing jacket
  simp only [Pi.add_apply,Finset.sum_apply,Fintype.sum_prod_type,Finset.sum_neg_distrib]
  unfold halfLeg movement inverseSlot imprint force Matrix.mulVec dotProduct
  simp only [Pi.mul_apply]; simp_rw [← Finset.mul_sum,Fintype.sum_prod_type]; ring

structure Score (p : Reel G H R K) (V : Config G c) (k : ℕ) (D : Directions G c → Prop) (r : ℝ) : Prop where
  paving i j : Ticket D k V r r (a.inverseSlot i j)
  pressed i : Ticket D k V r r (a.movement p i)
  suit i : Charge D k V r (jacket l p i)
  global : Charge D k V r a.dressing

def scoreScale (N P : ℕ) : ℝ := (P+1:ℝ)+(1+N^2:ℝ)*6

lemma scoreScale_pos (N P : ℕ) : 0 < scoreScale N P := by unfold scoreScale; positivity

namespace Score
variable {D : Directions G c→Prop} {k : ℕ} {V : Config G c} {r : ℝ}
    {a} {p : Reel G H R K}

private lemma node (h : a.Score p V k D r) (hr : 1 ≤ r) (i j : Component G H R) :
    Charge D k V (6*r^4) (a.halfLeg p i j) := by
  have hh : Ticket D k V 1 0 (fun _ : Config G c => (-1/2:ℝ)) := (Ticket.pure le_rfl _).mono (by norm_num) le_rfl
  have hl := (hh.mul ((h.pressed i).mul ((h.paving i j).mul (h.pressed j)))).tip
  refine hl.radius ?_
  have ht : 1 ≤ r^3 := one_le_pow₀ hr
  change (1+1*(r*(r*r)))*(0+(r+(r+r))) ≤ _
  nlinarith only [hr,mul_le_mul_of_nonneg_right ht (zero_le_one.trans hr)]

lemma places (h : a.Score p V k D r) (hr : 1 ≤ r) : Charge D k V
    (scoreScale (Fintype.card (Component G H R)) (Fintype.card H)*r^4) (a.stamps p) := by
  rw [printed]
  have he := Charge.total (I:=Finset.univ) (fun (i : Component G H R × Component G H R) _ => h.node hr i.1 i.2)
  have hh := Charge.total (I:=Finset.univ) (fun i _ => h.suit i)
  apply Charge.radius ((((Charge.freeze _ (le_refl 0)).add hh).add h.global).add he)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,zero_add]
  let N := (Fintype.card (Component G H R):ℝ); let M := (Fintype.card H:ℝ)
  have hi : r ≤ r^4 := by simpa only [pow_one] using (pow_le_pow_right₀ hr (show 1≤4 by norm_num))
  have hx : M*r ≤ M*r^4 := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)
  rw [Fintype.card_prod (α:=Component G H R),Nat.cast_mul]; unfold scoreScale
  change M*r+r+N*N*(6*r^4) ≤ ((M+1)+(1+N^2)*6)*r^4
  linarith only [hi,hx,pow_nonneg (zero_le_one.trans hr) 4]

lemma currency (h : a.Score p V k D r) (hr : 1 ≤ r) {w : ℝ} (hw : a.wideStrip V p ≤ w) :
    Ticket D k V w (climbing k (scoreScale (Fintype.card (Component G H R)) (Fintype.card H)*r^4))
      (fun W => a.wideStrip W p) := (h.places hr).bill_exp hw
end Score

/-- Inputs for moving snapshots. Price the ACTUAL reference means and
marginal normalizers also. κ may include powers of distances and volume
of the tested neighborhoods; formula keeps it unexponentiated. -/
structure Meets {l' : Viewport u' X' H R K} (a' : Notice l') (p : Reel G H R K)
    (V : Config G c) (k : ℕ) (D : Directions G c→Prop) (r κ : ℝ) : Prop where
  paving i j : Ticket D k V (κ*r) r (a.inverseSlot i j-a'.inverseSlot i j)
  velocity i : Ticket D k V (κ*r) r (a.movement p i-a'.movement p i)
  settle : Ticket D k V (κ*r) r (a.dressing-a'.dressing)

namespace Meets
variable {l' : Viewport u' X' H R K} {a' : Notice l'} {D : Directions G c → Prop}
    {p : Reel G H R K} {V : Config G c} {κ r : ℝ} {k : ℕ} {a}


end Meets
end Notice
end YM.AnalyticBridge.LocalGaussian

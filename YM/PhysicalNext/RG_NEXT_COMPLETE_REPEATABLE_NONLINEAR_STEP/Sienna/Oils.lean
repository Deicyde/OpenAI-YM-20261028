import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Diap
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Palette
/-!
# Voucher for POLY seam. Includes explicit bounds meeting `polar` & solar
 (-gap/8 tails). Reserve evaluation on same ALL tags and shapes.
 independent of F (any maximizer). Keeps R0 . Clipping costs!
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sienna
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {f w : ℝ→ℝ} {p C η σ l : ℝ} {n : ℕ} {Q : KernelChoices} {c g : Side}
variable (L : Side) (O : ChartRatio G) (ho : LocalRatio O) (P : Patch) (b : Clip) (A : Before G σ C P.J Q (n+3)) (E : FiberFee O ((n+3)+1))
    (h : Bolt G L f) (d r a : ℝ)
local notation "V" => A.tables b P
local notation "D" => wick G L
local notation "M" => (Delay.fineMonitor G L)
local notation "W" => (fun t=> pam n O b P A (f t) (f t) E (ConnectedActivityE6.loopBill G L t))
local notation "Z" => (fun t=> betaF G t L)
local notation "U" => eaves G L
local notation "F" => (fun t=> Pressure.fiery G t L)
variable (hm : 0<(A.tables b P).gap) (hd : 0<d)
include hm hd h ho
lemma compass (c' C' : ℝ) : ∀ᶠ t in atTop, ∀ h' β : ℝ, 1≤ f t → 0<β → β ≤ 2*Z t →
    ∀ k:ℝ, 0≤k→ k ≤ f t → ∀ B:BudgetPoint, B.threshold=F t → ∀ A:BudgetPoint,A.threshold≤ 2*F t → ∀ x:ℝ,0≤x → x ≤ U t →
      h'=β*(f t*c'*x^5+f t*(C'*A.threshold^3+C'*A.threshold^4))+(W t+tapir V (f t)+f t*a/2) →
         let e:= (V).gap*(D d t)^2/4
         let y:= - k*Real.log (measure_g O β) - e +f t*PathData.loopsPrice B β C (ConnectedActivityE6.loopBill G L t) + W t+tapir V (f t)
         y+h' +2 ≤ -e/2 ∧ y ≤ -e/2 := by
  let j t:=tapir (V) (f t); have hJ:Bolt G L j:= (h.nod 2).times (Bolt.still _)
  obtain ⟨-,v,w,h',h'',hh⟩ := posts L P O b A E h; obtain ⟨R,hR,hV⟩:= Coat.scaled O ho L
  let q t:= f t*(R*Delay.bill G L t); have hQ : Bolt G L q:= h.times ((Bolt.still _).times (gift _ _)) -- gift args
  let g:=(V).gap*d^2/8; have hg:0<g:=by unfold g; positivity
  let y t:=q t+1+v t+j t; let s' t:= 1+(v t+j t+ f t*a*2⁻¹)
  have hy : Bolt G L y:= ((hQ.joins (Bolt.still _)).joins h').joins hJ; have hs : Bolt G L s':= (Bolt.still _).joins ((h'.joins hJ).joins ((h.times (Bolt.still _)).times (Bolt.still _)))
  filter_upwards [fires G L hg hy h'', fires G L hg ((hy.joins hs).joins (Bolt.still 2)) (h''.joins h''),hV, minted L C h, crayon L G c' C' h] with t hv hX hr hx H h₀ β ht hβ hb k hk hf B hB B' hB' x hK hU hv' e z
  have hz:= hh t; have he:= hx β hβ.le hb B hB ht; have hp:= H β hβ.le hb B' hB' ht x hK hU
  have hb : - k*Real.log (measure_g O β) ≤ q t:= by rw [neg_mul_comm]; apply le_trans (mul_le_mul_of_nonneg_left (hr β hβ hb) hk) (mul_le_mul_of_nonneg_right hf (mul_nonneg hR.le (zero_le_one.trans (Delay.bill_ge ..)))) -- maybe neg_mul_comm opposite
  have hE : g*(M t)^2=e/2:= by unfold e g wick; ring
  change y t+w t*M t ≤ g*(M t)^2 at hv; rw [hE] at hv hX; unfold z; dsimp only at hz; rw [hv',hz]; dsimp only [y,s',j] at hv hX; constructor <;> linarith only [hb,hv,hX,he,hp]

omit ho E hm hd in
lemma pressures (r : ℝ) (hr : 0<r) : ∀ᶠ t in atTop,∀ β:ℝ, 0<β → betaF G t L /2 ≤ β → 1≤ f t → ∀ x : ℝ, 0 ≤ x → x≤ U t →
    β*meterQ V n (f t)*x + (V).gap/4*(D d t)^2 ≤ β*r:= by
  have hp : Bolt G L (fun t=> meterQ V n (f t)):= (((h.nod _).times (Bolt.still _)).times (Bolt.still _))
  have he := (Brim.absolut hp.uses).mul (edge G L)
  have hh:= (((gen G L d).pow 2).mul_left ((V).gap/4))
  filter_upwards [he.below (by rw [zero_add]; exact vow_ok) _ (half_pos hr), contraction G L (a:=1) (b:=r/4) (by positivity) (f:=fun t=> (V).gap/4*(D d t)^2) hh (show (0:ℝ)* ↑(2:ℕ)<1 by norm_num)] with t ht hv β hb hV hf x hx hX
  simp only [Real.rpow_one] at hv
  have hr₀ : meterQ V n (f t)*x ≤ r/2 := (mul_le_mul (le_abs_self _) hX hx (abs_nonneg _)).trans ((le_abs_self _).trans ht)
  nlinarith only [mul_le_mul_of_nonneg_left hr₀ hb.le,hv,mul_le_mul_of_nonneg_left hV hr.le]
end YM.PhysicalNext.Repeat.Sienna

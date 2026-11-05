import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Embroidery

/-! # Calibrate Taylor-budget receipts for UNFORCED pre-log marks. Prereconstruction.

Actual all-k derivative majorants on tubes, not a logical alias for accepting
 findings as an input. Yet still need affine grades/cubics/history.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained Gas Ursell Trees
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B e i: ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
open Captain

def salary (Q : YM.ConnectedActivityE6.Target G P) (L : Side) (μ C s : ℝ) (j k : ℕ) := (1+2^j*C)* Q.overture L μ s k

def collars (_G : Gauge) (η : ℝ) (s : ℝ) (j m: ℕ) := (shiftG s)^(m*j)*Reserves.polyPrice η (m*j)
structure Armada (Q : YM.ConnectedActivityE6.Target G P) (L : Side) (μ a s d B : ℝ) (j k : ℕ) : Prop where
  gain : 0≤a
  delta : 0<d
  little : a+d+d≤Q.exp
  earned : 0<Q.overture L μ s k
  safe : degreePrice (radiusB s) (salary Q L μ B s j k) d ≤ 1/2

namespace Armada
variable (T' : Armada Q L μ a s i B j k) (N : Captain H j C' d v Y A b r B q k χ)
include N T'
lemma purchases : Trees.Ready H.smallAt (radiusB s) N.stone (a+i) (salary Q L μ B s j k) i (1/2) := by
  have hB:=N.balance; have ha:=T'.earned
  have he : 0<salary Q L μ B s j k := by unfold salary; positivity
  refine ⟨he,T'.delta,T'.safe,by norm_num,N.stone_pos,fun x=> ?_⟩
  have hh:= budget_pull (fun i:H.ThinP=> Subtype.val i) Subtype.val_injective (N.conduit.paid k x)
  let t:= 2^j*B; have ht : 0≤t := mul_nonneg (by positivity) hB
  refine budget_loosen (budget_mono (budget_scale ht hh) (fun z=> ?_) (fun z=> ?_)) ?_
  · split_ifs; next => exact mul_nonneg (N.stone_pos _) (Real.exp_pos _).le
    exact le_rfl
  · split
    next hz=> dsimp only; rw [if_pos (show x∈H.unionP z.val from hz), ← mul_assoc,show t*N.conduit.meant z.val k=N.stone z by rw [Captain.stone, (show t=2^j*B from rfl),mul_assoc]]
              exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right T'.little (Nat.cast_nonneg _))) (N.stone_pos z)
    exact (budget_scale ht hh).1 z
  apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) ha.le
lemma applies (p n : ℕ) : Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=> if n≤z.fst then N.markΦ z p else 0) a
    (collars G i s j p*(salary Q L μ B s j k*(1/2:ℝ)^n*(1-1/2)⁻¹)) := by
  intro x; let P:= H.smallAt; let D:=radiusB s
  have hh:=log_hit_tail _ _ _ H.testS (T'.purchases N) (add_nonneg T'.gain T'.delta.le) n x
  have hs : 0≤shiftG s:= by unfold shiftG; positivity
  have hi:=T'.delta; have hp : 0≤collars G i s j p:= by unfold collars Reserves.polyPrice; positivity
  refine budget_mono (budget_scale hp hh) (fun z=> ?_) fun z=> ?_
  · dsimp only; split_ifs
    next => exact mul_nonneg (show 0≤N.markΦ z p from mul_nonneg (pow_nonneg (by positivity) _) (N.pvc z)) (Real.exp_pos _).le
    next => simp
    exact le_rfl
  have hf:= mul_nonneg hp (hh.1 z); dsimp only; split
  next hx =>
    by_cases hz : n≤z.fst
    swap; · rw [if_neg hz,zero_mul]; exact hf
    rw [if_pos hz,if_pos (show n ≤ z.fst ∧ x∈unionOf H.smallAt z.snd from ⟨hz,hx⟩)]
    let t:ℝ := coverNumber D (unionOf P z.snd)
    have hg : 0≤t:= Nat.cast_nonneg _
    change (shiftG s*(1+t))^(p*j)*N.design z * Real.exp (a*t)≤ _ * (N.design z * Real.exp ((a+i)*t))
    rw [mul_pow]; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (polynomial_cost hi hg _) (pow_nonneg hs _)) (pvc N z)) (Real.exp_pos _).le).trans
    unfold collars Reserves.polyPrice; rw [add_mul, Real.exp_add]; apply le_of_eq; ring
  exact hf

omit T' N
lemma ensemble (Q : YM.ConnectedActivityE6.Target G P) (L : Side) {μ : ℝ} (hμ : 0<μ) (a : ℝ) (ha : 0≤a) (hh : a<Q.exp) (j k : ℕ)
    {B : ℝ→ℝ} (hB : Rate G L 0 B) : ∃ i : ℝ,
    (∀ m n:ℕ, Rate G L Q.rate (fun s=> collars G i s j m*(salary Q L μ (B s) s j k*(1/2:ℝ)^n*(1-1/2)⁻¹))) ∧ ∀ᶠ x in atTop,
      Armada Q L μ a x i (B x) j k := by
  let i:=(Q.exp-a)/2
  have hi : 0 < i := half_pos (sub_pos.mpr hh)
  have hp : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
  let f s:= salary Q L μ (B s) s j k
  have hf : Rate G L Q.rate f := by
    let h:= ((Rate.const 1).add (hB.mul_left (2^j:ℝ))).mul (Q.rate_none L hμ 0 k 0); rw [zero_add] at h; exact h
  have ht : Rate G L 0 (fun x=> (Animals.ballCost (radiusB x):ℝ)) := by simpa only [one_mul,add_zero] using! (Census.width_rate G L 1 0)
  let v x:=degreePrice (radiusB x) (f x) i
  have hz:Rate G L Q.rate v := by
    have h:= ht.mul hf; rw [zero_add] at h; simpa only [v,degreePrice,Trees.stretch,div_eq_mul_inv] using! ((h.mul_right i⁻¹).mul_left 4)
  refine ⟨i,fun m n=> ?_,?_⟩
  · simpa only [zero_add,zero_mul] using! ((hp.pow (m*j)).mul_right (Reserves.polyPrice i (m*j))).mul
      ((hf.mul_right ((1/2:ℝ)^n)).mul_right (1-1/2)⁻¹)
  filter_upwards [hz.below Q.stop (1/2) (by norm_num),Delay.shift_pos G L] with x hx hy using
    ⟨ha,hi,by unfold i; linarith,Q.overture_pos x k hy,(le_abs_self (v x)).trans hx⟩
end Armada
end YM.ConnectedActivityE6.Blaze.March

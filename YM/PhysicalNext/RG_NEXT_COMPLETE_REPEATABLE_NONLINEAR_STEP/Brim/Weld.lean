import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Lap
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Gills
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Symbols

/-!
# Size ξ curvature and Guard compound gate

Costs for faithful correction Compare. G simple or not (reserve rank of
stripped coords even when color set empty). Cover nodes pinned from full-height
sieve. Spend all moments. Leg k measured over weight. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism
open WardBin.Lies Push.PriceCompiler Foramen Gate
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {p j n : ℕ} {L : Side}
variable {d A t C' w M N z β W k ε J' L₀ X' : ℝ}

section amount
variable {o : Site c} {I:Type} [Fintype I] {X : Coat T F} (a : Museum F X.x (bareStores S) K Y I) (hz : o∈Y) (hy : coverNumber X.B Y ≤ X.B)
include hy a hz
lemma settlers : Fintype.card I ≤ (Animals.ballCost (radiusD X.x))*(S.patch.L.val^4*Fintype.card Axis) := by
  let S' := withinH (atEdge S) o (radiusD X.x); let b : I ↪ Bond f:= ⟨a.address,a.address_inj⟩; have he (i) : b i∈S':= (joins ..).mpr ((separation_comm ..).trans_le (far a hz hy i))
  calc
    _ = (Finset.univ.map b).card := by simp
    _ ≤ S'.card := Finset.card_le_card fun i h=> by obtain ⟨k,hh,rfl⟩:= Finset.mem_map.mp h; exact he _
    _ ≤ _ := count_near (Census.perch S) ..
omit hy a hz
abbrev colony (L : Side) (x : ℝ) := (Animals.ballCost (radiusD x))*(L.val^4*Fintype.card Axis)
lemma colonies (G : Gauge) (L : Side) : Rate G L 0 (fun x=> (colony L x:ℝ)) := by
  simp_rw [show ∀ x:ℝ, (colony L x:ℝ)= (↑(radiusD x)+↑(radiusD x)+1:ℝ)^4*((L.val^4*Fintype.card Axis:ℕ):ℝ) from fun x=> by unfold colony Animals.ballCost; push_cast; rfl]
  have h:= spanDO G L
  exact (prep ((h.add h).add (Rate.const 1)) _).mul_right _
end amount
section tune
-- Monitor Choose unit. Q's not time variable
variable (G : Gauge) (L : Side) (P : Teller G) (D : Record)

def sliceD (x : ℝ) := (D.ε/(128*((Fintype.card G.ColorIndex:ℝ)+1))) * Delay.fineMonitor G L x
lemma waft (v : ℝ) : Rate G L v (fun x=> Real.exp (-sliceD G L D x)) := by
  have he:=Rate.monitor_cutoff (G:=G) (L:=L) (a:=v) (δ:=D.ε/(128*((Fintype.card G.ColorIndex:ℝ)+1))) (by have := D.guards; positivity) (γ:=1) zero_lt_one
  simpa only [Real.rpow_one,neg_mul] using! he
-- choose post delay L
lemma snip {δ : ℝ→ℝ} (hb : Rate G L (-(1/2)) δ) : ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T : Tube G S)
    (R : Rep G f), S.patch.L=L → Intake P T x R →
    let d:=gStep R.beta; let y:=sliceD G L D x; let t:= R.p.threshold
    0 ≤ y ∧ d*Fintype.card G.ColorIndex*(y+δ x)< (D.ε*t)/8 ∧ (D.ε*t/d/4)⁻¹ ≤ 1 := by
  have he:=D.guards; let p x:=Delay.fineMonitor G L x; let κ:=(Fintype.card G.ColorIndex:ℝ); have hK:0≤κ:=Nat.cast_nonneg _
  let η:= D.ε/(128*(κ+1)); have hη:0<η:= by unfold η; positivity
  have ht: ∀ᶠ x in atTop, 8/D.ε ≤ p x:= by
    filter_upwards [Delay.monitor_pays G L (d:=0) (show 0≤8/D.ε by positivity) zero_lt_one] with x hx
    simpa only [Real.rpow_one,pow_zero,mul_one] using! hx
  filter_upwards [hb.below (by norm_num) (η*(8/D.ε)) (by positivity), ht] with x hx ht c f S T R he hP d y t
  have hh : p x/2 ≤ t*d⁻¹:= by
    unfold t p; rw [hP.received.temp,← he]; exact charge_area S x T R hP
  have hp:0< p x:= Delay.monitor_pos G L x; have hδ : 0<d := inv_pos.mpr (Real.sqrt_pos.mpr hP.positive)
  have hg:= D.guards
  refine ⟨mul_nonneg hη.le hp.le, ?_, inv_le_one_of_one_le₀ ?_⟩
  · have hs : D.ε*(p x/2)≤D.ε * (t/d) := mul_le_mul_of_nonneg_left (by rw [div_eq_mul_inv]; exact hh) hg.le
    rw [mul_assoc, mul_comm d,← lt_div_iff₀ hδ]; change κ*(η*_+_)<_
    have hv : δ x≤η*p x := (le_abs_self _).trans (hx.trans (mul_le_mul_of_nonneg_left ht hη.le))
    have hx' : η*(128*(κ+1))=D.ε:= div_mul_cancel₀ _ (by positivity : 128*(κ+1)≠0)
    calc
      _ ≤ κ*(η*p x+η*p x) := by unfold η p κ at *; gcongr
      _ < D.ε*(p x/2)/8 := by rw [← hx']; nlinarith only [mul_pos hη hp,mul_nonneg hK (mul_nonneg hη.le hp.le)]
      _ ≤ D.ε*(t/d)/8 := by linarith
      _ = _ := by ring
  rw [le_div_iff₀ (by norm_num : (0:ℝ)<4),div_eq_mul_inv,mul_assoc]; linarith only [(div_le_iff₀ hg).1 ht, mul_le_mul_of_nonneg_left hh hg.le]
end tune
end YM.PhysicalNext.Repeat.Brim

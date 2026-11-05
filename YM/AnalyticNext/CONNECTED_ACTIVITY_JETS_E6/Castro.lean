import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Gust
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Rainbowline

/-!
# Tablet issuance persisting under Vol(s)

Token polynomial irrespective of order of Q estimate (pre-lift marker
position). `gain` independent. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Gate
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush Tablet Foramen
variable {v z η r Q S' : ℝ} {k : ℕ} {U : E → Config G c} {x : E}

def carat (D : Patch) (P : Teller G) (L : Side) (w C : ℝ) := let f:=cable P D C; let k:= price0 (P.top.width-w)
    max 0 (max (k*(mentionPrice L*Fintype.card G.ColorIndex:ℕ)*f) (k*tubularPrice G L*f))
lemma replicaM (X : Coat T F) (D : Patch) (hd : S.patch=D) (hL : S.patch.L=L) (h : Room P S T X.x) (hf : Mode U x k v)
    (C : ℝ) (hC : 0<C) (hp : SliceRows.Bounded T P.top.width C) (hr : 0 ≤ r) (hq : r<P.top.width) :
    Tablet k r (carat D P L r C) (kernelGrowth X.B G v) (fun z=> (vary X (U z)).form) (aim S) (along S) x := by
  rw [← hL]
  have hn := hf.pos; have hl:=royalty_ge G; have hh:=scale_pos
  refine Tablet.across (aims S) (entering S) ?_ (fun i j=> whirl X D hd h hf i j C hC hp) hq hr ?_
  · unfold kernelGrowth; positivity
  unfold cable; positivity
lemma plates (X : Coat T F) (D : Patch) (hd : S.patch=D) (hL : S.patch.L=L) (h : Room P S T X.x) (hf : Mode U x k v)
    (C : ℝ) (hC : 0<C) (hp : SliceRows.Bounded T P.top.width C) (hr : 0 ≤ r) (hq : r<P.top.width) :
    let f:=carat D P L r C; let u:=kernelGrowth X.B G v
    Tablet k r (f*f+1) (u+u) (fun z=> (vary X (U z)).plate) (along S) (along S) x := by
  intro f u; have hg := replicaM X D hd hL h hf C hC hp hr hq; have ht := hg.reverse.enjoin hg
  apply ht.joined
    (Tablet.fixed _ (show Price (along S) _ X.sleepy _ _ from density _ _ _ (by simp [sleepy]) (X.sleep_cap _)) hr zero_le_one ht.pos)



lemma jet_growth (G : Gauge) (L : Side) {w : ℝ→ℝ} (h : Rate G L v w) : Rate G L v (fun x=>kernelGrowth (radiusB x) G (w x)) := by
  have he : Rate G L v (fun x=>4*(radiusB x:ℝ)*(w x*royalty G)) := by
    convert (((Rate.radius_price.mul_left 4).mul (h.mul_right _))) using 1; ring
  exact (he.add (h.add h)).add he
lemma polynomial (G : Gauge) (L : Side) (k m : ℕ) (C u : ℝ) : Rate G L 0
    (fun x=> Tablet.facePrice k (radiusB x) m C u) := by
  have ht:= Census.width_rate G L 1 2
  simp only [one_mul] at ht; simp only [facePrice,Nat.cast_mul]
  exact (ht.mul_right _).mul_right _
lemma swims (G : Gauge) (L : Side) {v : ℝ→ℝ} {η : ℝ} (t : ℝ) (h : Rate G L 0 v) (hr : 0<η) (r : ℝ) : Rate G L t
    (fun x=>Foramen.tidal η r (v x) (radiusB x)) := by
  have hh : Rate G L t (fun x=> Real.exp ((η/2-η)*radiusB x)) := by
    apply ((Rate.cutoff (δ:=η/2) (by linarith))).compare
    filter_upwards with x; rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone
    have he : (till x:ℝ) ≤ (radiusB x:ℝ) := by exact_mod_cast Nat.div_le_self ..
    nlinarith
  simpa only [add_zero] using! hh.mul ((h.mul_left r).add (Rate.const 1))
end YM.ConnectedActivityE6.Blaze.Gate

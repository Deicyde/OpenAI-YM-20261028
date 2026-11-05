import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Prism.Sail

/-! # Score difference of TWO densities buys only polynomial rank with tiny v

Use both actual compact marginals. Rational-chip since θ is held. No rank
 relaxation silently dropping edge reads. Tensor tags v etc from SAME turn.
 Contracts compare scaled inverse/log determinants on true V germ! positive
 condition needed on both sides.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Prism
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {n : ℕ} {v d N Q K D w : ℝ}

structure Anthem (n : ℕ) where
  logE : ℝ
  expE : ℝ
  gold : ℝ
  silver : ℝ
  plus : 0 ≤ logE
  escort : 0 ≤ expE
  gems : 0 ≤ gold
  coins : 0 ≤ silver
  cmd (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (p:E) (v w : ℝ) (f:E→ℝ) :
    Brush n v w f p → v ≤ 1 → Brush n (expE*v) w (fun x=>Real.exp (f x)-1) p
  treat (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (p:E) (v : ℝ) (f:E→ℝ) :
    Brush n v 1 (fun x=> f x -1) p → v ≤ 1/2 → Brush n (logE*v) 1 (fun x=> Real.log (f x)) p
  exp_ok : Brush n silver 1 Real.exp 0
  log_ok : Brush n gold 1 Real.log 1

lemma anthems (n:ℕ) : Nonempty (Anthem n) := by
  obtain ⟨G,hG,hb⟩:= Brush.expands n; let g (x:ℝ):=Real.log (x+1)
  obtain ⟨C,hC,hP⟩:= Brush.compact (k:=n+1) (f:=g) (s:=closedBall 0 (1/2)) (isCompact_closedBall ..) fun x hx=> by
    have hx : |x|≤1/2:=mem_closedBall_zero_iff.mp hx; have hx:= abs_le.mp hx
    exact (contDiffAt_id.add contDiffAt_const).log (show x+1≠0 from ne_of_gt (by linarith only [hx.1]))
  obtain ⟨u,hu,he⟩:= Brush.neighborhood (k:=n) 1 (show ContDiffAt ℝ (↑n) Real.log 1 from Real.contDiffAt_log.mpr (by norm_num))
  obtain ⟨v,hv,hv'⟩:= Brush.neighborhood (k:=n) 0 Real.contDiff_exp.contDiffAt -- edit
  refine ⟨C+n.factorial*C,G,u,v,by positivity,hG,hu.le,hv.le,hb,?_,hv'.self_of_nhds,he.self_of_nhds⟩
  intro E _ _ p v f hf hv; let x:=f p-1
  have hh: x ∈ closedBall 0 (1/2):= mem_closedBall_zero_iff.mpr (hf.bound.trans hv)
  have hx: ‖g x‖≤ C*v:= (locate (f:=g) (C:=C) (t:=1/2) (fun z hz=> Malachite.settled.mp (hP z (mem_closedBall_zero_iff.mpr hz))) (show 1≤n+1 by omega) (by simp [g]) (hf.bound.trans hv)).trans
      (mul_le_mul_of_nonneg_left hf.bound hC.le)
  have he:= even hf ((hP _ hh).smaller (show n ≤ n+1 by omega)) (by linarith) hC.le hx
  simp only [g,sub_add_cancel] at *; exact he

section stress
variable [DecidableEq ι] [Fintype ι] {B C : E→ Matrix ι ι ℝ} {Y Y' : E→ Gaussian.Vec ι}

abbrev Moves (x : E) (n:ℕ) (J:E→ Gaussian.Vec ι) (v:ℝ) := ∀ i, Brush n v 1 (fun x=> J x i) x
abbrev rail (n : ℕ) (N p q r:ℝ) := freight n N p (freight n N q r)
omit [DecidableEq ι] in
lemma lineCost (hn : (Fintype.card ι:ℝ) ≤ N) (hv : 0≤ v) (hw : 0 ≤ w) (hd : 0≤d) (h : Moves x n Y v) (hb : EdgePay B n d 1 x) (hk : Moves x n Y' w) :
    Brush n (rail n N v d w) 1 (fun x=>dotProduct (Y x) (B x *ᵥ Y' x)) x := by
  have he i : Brush n (freight n N d w) 1 (fun x=> (B x *ᵥ Y' x) i) x := by
    change Brush _ _ _ (fun x=> ∑ j, B x i j*Y' x j) _
    exact (sail_total hn (mul_nonneg hd hw) (add_nonneg zero_le_one zero_le_one) (fun k=> (hb i k).paints (hk k))).trim
  exact (sail_total hn (mul_nonneg hv (freight_pos hd hw n ((Nat.cast_nonneg _).trans hn))) (add_nonneg zero_le_one zero_le_one) (fun i=> (h i).paints (he i))).trim
variable (hb : Holds B x Q n) (hc : Holds C x Q n) (Δ : EdgePay (C-B) n D 1 x)
    (hn : (Fintype.card ι:ℝ) ≤ N) (hd : 0≤D) (hq : 0≤ Q) (a : ι→ Site c)
    (hL : ∀ᶠ y in 𝓝 x, (B y).PosDef ∧ (C y).PosDef) (ht : Moves x n Y Q) (hh : Moves x n Y' Q) (hy : Moves x n (Y-Y') D)
include hb hc Δ hn hd hq a ht hh hy

def beam (n : ℕ) (N Q D : ℝ) := rail n N Q (revs D Q N n) Q +rail n N D (banner Q N n) Q+ rail n N Q (banner Q N n) D
lemma merits : Brush n (beam n N Q D) 1 (fun x=> Gaussian.force (B x) (Y x)/2 -Gaussian.force (C x) (Y' x)/2) x := by
  let c y:= (C y)⁻¹; have h':= (Nat.cast_nonneg _).trans hn
  have hc':= broken a hc hn hq
  have hf:= banner_pos n hq h'
  have he:0≤revs D Q N n:= freight_pos hf (freight_pos hd hf n h') n h'
  have hu:= ((semi (lineCost hn hq hq he ht (inback hb hc Δ hn hd hq a) ht)).gathering
    (semi (lineCost hn hd hq hf hy hc' ht))).gathering (semi (lineCost hn hq hd hf hh hc' hy))
  refine hu.shimmy ?_; filter_upwards with x
  simp only [Pi.sub_apply, Matrix.sub_mulVec, Matrix.mulVec_sub,sub_dotProduct,dotProduct_sub,force]; ring

include hL
def plumage (A : Anthem n) (N Q D : ℝ) := A.logE*sail D Q N n + beam n N Q D
lemma angle (A : Anthem n) (hg : gear D Q N n ≤ 1) (hk : sail D Q N n ≤ 1/2) (hp : plumage A N Q D ≤ 1) :
    Brush n (A.expE*plumage A N Q D) 1 (fun u=> Density.replace (C u) (B u) (Y' u-Y u) (Y u)-1) x := by
  let f y := Real.log ((B y).det/(C y).det); let t y:=Gaussian.force (B y) (Y y)/2-Gaussian.force (C y) (Y' y)/2
  have hf : Brush n (A.logE*sail D Q N n) 1 f x:= A.treat E _ _ (fun y=> (B y).det/(C y).det) (bays hc Δ hn hd hq a hg) hk
  have hx: Brush n (plumage A N Q D) 1 (fun x=> f x/2+t x) x := (semi hf).gathering (merits hb hc Δ hn hd hq a ht hh hy)
  refine (A.cmd E _ _ _ _ hx hp).shimmy (hL.mono (fun y hy=>?_)); unfold Density.replace
  dsimp only; rw [Density.chip_income _ _ hy.2 hy.1,Density.spice,← Real.exp_add]; unfold f t; rw [add_sub_cancel]; ring_nf
end stress
end YM.PhysicalNext.Repeat.Prism

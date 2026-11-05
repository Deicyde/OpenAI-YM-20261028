import YM.AnalyticNext.QUARTIC_MATCH.Radius.Fruit
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Rove
import YM.Progress.CLASSICAL_KIN_RECURSION.Delta
/-! # Combine perturbation & Plate on the actual chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision
open Pressure Push.SectorMeasure Next.Rank RankCovariance Thirst Pump Ac Pot
open Display Display.Docking Display.Sew Value Flux SectorNext.Vacuum
     Tree PhysicalGuard7f546.Curved Next.SectorChange AnalyticNext.ConnectedActivity
     AnalyticNext.ConnectedActivity.Cab Push.SectorMeasure.Oriented
     AnalyticBridge.LocalGaussianLaws Exterior Dictionary Push.Local Push.AbsoluteSums
     RecursiveSecants079.BothSides
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {v : Dyed G S} {P : Teller G}
    {B T W t a d b s e δ x : ℝ}

lemma affixed (hp : Petty v W v.bp.B a d (Ancestor.gen v (x:=x)))
    (hr : Petals v.source t) (hT : ∀ s i,Nonempty (v.source.activities.Moves s i))
    (hU : Chips (neutral v) P W x) (hd : d≤1) (M : Plate (neutral v) x W)
    (w : Glade c→ℝ) (h₁ :∀ i,0≤w i) (he : 0≤a) (hH : Ac.Hit (fun i:Glade c=>i.val) v.bp.B w a e) (hE : e≤1)
    (hw : ∀ i p, Matched p → |Real.exp (M.aux i p)-1|≤ w i) :
    ∃ (Q : Plate v x W), Q.base=M.base ∧
        ∃ w' : Glade c→ℝ,(∀ i,0≤w' i) ∧ Ac.Hit (fun i:Glade c=>i.val) v.bp.B w' a (e+4*d) ∧ ∀ i p, Matched p→ |Real.exp (Q.aux i p)-1|≤w' i:= by
  obtain ⟨f,b,h,hb,hq,hy,hz,hL,ht⟩:= facing hU hp hr hT
  let Q : Plate v x W := { M with
    aux := fun i p=> M.aux i p + f i p
    tip := fun i=> (M.tip i).plus (hq i)
    mine:=fun i p hp k=>congr_arg₂ HAdd.hAdd (M.mine i p hp k) (hy i p hp k)
    toll := fun e p i=> congr_arg₂ HAdd.hAdd (M.toll e p i) (hz i p e)
    pitch := fun p hx hp=> Eq.trans (upgrade ..) (by
      rw [M.pitch p hx ((costume _).1 hp), ht p hx hp,sum_add_distrib]; ring) }
  let b' i:= w i + ((b i+b i)+(b i+b i))
  refine ⟨Q,rfl,b',fun i=> add_nonneg (h₁ _) (add_nonneg (add_nonneg (hb _) (hb _)) (add_nonneg (hb _) (hb _))),fun i=> budget_loosen (hit_plus hH (hit_plus (hit_plus h h) (hit_plus h h)) i) (by linarith only),?_⟩
  intro i p hx
  have hh: |Real.exp (f i p)-1|≤ 2*b i:= (Real.abs_exp_sub_one_le ((hL i p hx).trans ((hit_one h he hb i i.property).trans hd))).trans (mul_le_mul_of_nonneg_left (hL i p hx) (by norm_num))
  have hH' : Real.exp (M.aux i p)≤ 2 := by linarith only [hw i p hx,le_abs_self (Real.exp (M.aux i p)-1),hit_one hH he h₁ i i.property,hE]
  let E:=Real.exp (M.aux i p); let C:=Real.exp (f i p)-1; have hE: |E|≤ 2:= by unfold E; rwa [abs_of_nonneg (Real.exp_pos _).le]
  calc
    _ = |E*C+(E-1)|:=by rw [show Real.exp (Q.aux i p)=_ from Real.exp_add (M.aux i p) (f i p)]; unfold E C; ring_nf
    _ ≤ |E*C| + |E-1|:= abs_add_le ..
    _ ≤ _ := by unfold b'; rw [abs_mul]; linarith only [mul_le_mul hE hh (abs_nonneg C) (by norm_num:0 ≤ (2:ℝ)),show |E-1|≤ w i from hw i p hx]
end YM.PhysicalNext.InteractingRank.Soft

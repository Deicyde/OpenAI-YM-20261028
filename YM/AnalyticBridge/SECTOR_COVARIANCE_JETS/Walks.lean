import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Marks
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Wall

set_option warningAsError false

/-! D-row tensor bounds per individual path, holding physical stencils.
The full path is charged, not its net displacement. The normalized V-chart
sizes will be priced later from these unscaled slot tests. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix MeasureTheory Pressure
  Pressure.Tube Bid Next.Fluctuations Next.SectorChange Next.SectorChange.Rows
  Next.SectorChange.Wisps Push.SectorMeasure FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent.Affine (Ceiling star_ceiling zero_null)
open scoped Topology Matrix.Norms.Frobenius ContDiff InnerProductSpace BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {k : ℕ}

/-- Single transported direct jet in ℓ_R, before coefficient and cut. -/
def strand (S : StepData c f) (s : Signed) (t : Directions G f) (x : Site f) (m : Slot) (V : Config G c) :=
  G.adjoint (travel (facade S s V 0) x m.walk) (plaquetteJet S V s (Work.F03.slotFace m x) t)

def gray (S : StepData c f) (s : Signed) (p : Cell f) (V : Config G c) (j : Atom G f) (B : Directions G c) :=
  upright (labelFace S s V p) (atom j) B

def line (S : StepData c f) (s : Signed) (V : Config G c) (j : Atom G f) (x : Site f) (m : Slot) (B : Directions G c) :=
  G.adjoint (travel (wall S s V (B,0)) x m.walk) (gray S s (Work.F03.slotFace m x) V j B)

lemma gray_agrees (S : StepData c f) (s : Signed) (p : Cell f) (V : Config G c) (j : Atom G f) {B : Directions G c}
    (hB : ‖B‖ ≤ 1) : gray S s p V j B = plaquetteJet S (increment V B) s p (atom j) := tangent_agrees _ _ _ _ _ hB
lemma line_agrees (S : StepData c f) (s : Signed) (V : Config G c) (j : Atom G f) (x : Site f) (m : Slot)
    {B : Directions G c} (hB : ‖B‖ ≤ 1) : line S s V j x m B=strand S s (atom j) x m (increment V B) := by
  unfold line strand; rw [gray_agrees _ _ _ _ j hB,wall_agrees _ _ _ hB (by simp)]

lemma gray_cap (S : StepData c f) (s : Signed) (p : Cell f) (V : Config G c) (j : Atom G f) :
    Ceiling k (bladeMoney G (k+1)) (gray S s p V j) :=
  upright_ceiling (faces_cap S s V p _) (blade_nn ..) (atom_small j)

private def mulPot (G : Gauge) (k : ℕ) := 2^k*‖ContinuousLinearMap.mul ℝ G.Mat‖


def lineMoney (G : Gauge) (k : ℕ) (σ : ℝ) :=
  let P := G.projectColor.toContinuousLinearMap
  let L := G.colorMat.toContinuousLinearMap
  cents P * (mulPot G k)^2 * cents L * bladeMoney G (k+1) * (wallMoney G k (σ/2))^2
lemma lineMoney_nn (G : Gauge) (k : ℕ) (σ : ℝ) : 0 ≤ lineMoney G k σ := by
  apply mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (cents_nonneg _) (sq_nonneg _)) (cents_nonneg _)) (blade_nn ..)) (sq_nonneg _)

lemma line_cap (S : StepData c f) (s : Signed) (V : Config G c) (j : Atom G f) (x : Site f) (m : Slot)
    (k : ℕ) {σ : ℝ} (hs : 0 < σ) :
    Ceiling k (lineMoney G k σ * Real.exp (σ*m.length)) (line S s V j x m) := by
  let D := ContinuousLinearMap.inl ℝ (Directions G c) (Directions G f)
  let P := G.projectColor.toContinuousLinearMap
  let L := G.colorMat.toContinuousLinearMap
  let M := ContinuousLinearMap.mul ℝ G.Mat
  let R := wallMoney G k (σ/2)
  let E := Real.exp (σ/2*m.walk.length)
  have hD : ‖D‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp [D]
  have hr : 0 ≤ R := wallMoney_nn _ _ (half_pos hs)
  have he : 0 ≤ E := (Real.exp_pos _).le
  have hh := (walking_wall k S s V m.walk x (half_pos hs)).pre D (mul_nonneg hr he) hD le_rfl
  rw [one_pow,mul_one] at hh
  have hp := gray_cap (k:=k) S s (Work.F03.slotFace m x) V j
  have hm := hh.mul (hp.post L) M (mul_nonneg hr he) (mul_nonneg (norm_nonneg _) (blade_nn ..))
  apply ((hm.mul (star_ceiling hh) M (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hr he)) (mul_nonneg (norm_nonneg _) (blade_nn ..)))) (mul_nonneg hr he)).post P).mono
  have ht : E*E=Real.exp (σ*m.walk.length) := by unfold E; rw [← Real.exp_add]; congr 1; ring
  calc
    _ = lineMoney G k σ * (E*E) := by unfold lineMoney E mulPot cents P L M; ring
    _ ≤ _ := by
      rw [ht]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (lineMoney_nn ..)
      apply mul_le_mul_of_nonneg_left _ hs.le; unfold Slot.length; simp

section depend
variable {s : Signed}
lemma replica_near_agree (S : StepData c f) (a : Directions G f) {U V : Config G c} {o : Site c} {r : ℕ}
    (h : Peers o r U V) : AgreeNear S.ratio.parent o r
      (increment (replica S.ratio U) a) (increment (replica S.ratio V) a) := by
  intro e he; unfold increment replica; split
  · rfl
  rw [h (S.ratio.parent e.1,e.2) he]

lemma face_houses (S : StepData c f) (s : Signed) (i : Cell f) (t : Directions G f) :
    Housed (E:=G.El) (s.act (S.ratio.parent i.1)) 5 (fun V => plaquetteJet S V s i t) := by
  intro U V h
  have hh : sourceFace (S:=S) V s i=sourceFace (S:=S) U s i := by
    funext a; unfold sourceFace; apply congr_arg G.curvature
    unfold faceValue
    apply travel_near _ (Work.E03.parent_step S) _ _ _ _ 4 le_rfl
    exact pulled_near _ _ s _ 4 (replica_near_agree S a fun i hi => (h i hi).symm)
  change fderiv ℝ (sourceFace (S:=S) U s i) 0 t = _; rw [← hh]; rfl

lemma strand_houses (S : StepData c f) (s : Signed) (x : Site f) (m : Slot) (t : Directions G f) :
    Housed (E:=G.El) (s.act (S.ratio.parent x)) (m.length+5) (strand S s t x m) := by
  intro U V h
  unfold strand
  let r := m.walk.length; let o := S.ratio.parent x
  let p := Work.F03.slotFace (n:=f) m x
  have hv : travel (facade S s U 0) x m.walk=travel (facade S s V 0) x m.walk := by
    apply travel_near _ (Work.E03.parent_step S) _ _ _ _ r le_rfl
    exact pulled_near _ _ s _ r (replica_near_agree S 0 fun i hi => h i (hi.trans (by unfold r Slot.length; omega)))
  have hp : plaquetteJet S U s p t=plaquetteJet S V s p t := by
    apply face_houses S s p t
    intro j hj
    refine h j ((separation_triangle (s.act o) (s.act (S.ratio.parent p.1)) j.1).trans ?_)
    rw [separation_signed]; have ht := slot_distance (S:=S) m x; unfold Slot.length
    change separation o (S.ratio.parent p.1) ≤ _ at ht; omega
  rw [hv,hp]

lemma face_needs (S : StepData c f) (s : Signed) (p : Cell f) (V : Config G c) (j : Atom G f)
    (h : ¬separation (s.act (S.ratio.parent p.1)) (S.ratio.parent j.1.1) ≤ 5) :
    plaquetteJet S V s p (atom j)=0 := by
  refine (faceJet_dep _ _ _ _ 0 ?_).trans (map_zero _)
  intro e he; unfold atom; rw [on_axis]; have ht : e≠j.1 := fun hx => h (hx ▸ he); rw [Pi.single_eq_of_ne ht]; rfl

lemma strand_needs (S : StepData c f) (s : Signed) (V : Config G c) (j : Atom G f) (x : Site f) (m : Slot)
    (h : ¬separation (s.act (S.ratio.parent x)) (S.ratio.parent j.1.1) ≤ m.length+5) : strand S s (atom j) x m V = 0 := by
  let p := Work.F03.slotFace (n:=f) m x
  unfold strand; rw [face_needs _ _ _ _ _ ?_, map_zero]; intro he
  refine h ((separation_triangle _ (s.act (S.ratio.parent p.1)) _).trans ?_)
  rw [separation_signed]; have hx := slot_distance (S:=S) m x; unfold Slot.length
  dsimp only [p] at *; omega
end depend
end YM.AnalyticBridge.Covariance

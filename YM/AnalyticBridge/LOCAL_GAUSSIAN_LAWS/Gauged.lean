import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Binding
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.CutGerm
import YM.Next.SCHEDULE.GridCost
import YM.Next.SCHEDULE.Postal



/-!
# Coarse gauge change (all placements/tags held)

Actual A,Q,C and b,E:6030; note only under change of the held y too
(treat separately from V differentiation). Show exact transformation of
relative tangents, k and $\Phi,\ell_R$ reads, INCLUDING divergent/default
sum cases using the metric equivalences. All paths retained. Same
`shots` on both sides. Use .Moved only with actual Bounds (for reading
matrix-vector tests). Selection, Γ/j prices not switched. See separate
file for lattice sym changes, which reindexes BOTH U-addresses and rows
and cannot use just this theorem.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix Laurent Bloch
open Bid Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Oriented 
open Next SectorChange SectorChange.Rows SectorChange.Gaussian Wisps Motion
open ColorBook
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {x : ℝ}

namespace GaugeRoute
variable {H β : Type} [Fintype H] [DecidableEq H] [Fintype β] [DecidableEq β]

def pivot (o : H→G.El) := readers (Equiv.refl H) (fun i => adBody (o i))
lemma pivot_val (o : H→G.El) (v : LogArray G H) (i : H) : pivot o v i=G.adjoint (o i) (v i) := rfl

lemma pivot_sum {ι : Type} (z : G.El) (F : ι → G.Color) : G.adjoint z (∑' i,F i)=∑' i,G.adjoint z (F i) :=
    (adBody z).toContinuousLinearEquiv.map_tsum


lemma barrel_gauge (p : PathData G) (U : Config G n) (z : Site n → G.El) (m : ℕ) (a b : Cell n → G.Color)
    (h : ∀ i, b i=G.adjoint (z i.1) (a i)) (i : Cell n) :
    barrel p m (Lattice.gauge z U) b i=G.adjoint (z i.1) (barrel p m U a i) := by
  unfold barrel; rw [pivot_sum]
  refine tsum_congr fun j => ?_; dsimp only; split <;> rename_i hv
  · let s := (p.row i.2 j).2
    have he : stop i.1 s.walk=(Work.F03.slotFace s i.1).1 := by
      unfold Work.F03.slotFace Slot.offset; rw [wrap_stop_cover,map_zero,add_comm]; nth_rw 1 [show i.1=i.1+0 by rw [add_zero]]; rw [Work.E03.stop_add_left]
    change (p.row i.2 j).1 • G.adjoint (travel (Lattice.gauge z U) i.1 s.walk) (b (Work.F03.slotFace s i.1)) = _
    rw [travel_gauge,h,he,map_smul,G.adjoint_mul,G.adjoint_mul,← G.adjoint_mul (z _)⁻¹ _,inv_mul_cancel,G.adjoint_one]
  simp

lemma shorten_flow (p : PathData G) (z : Site n → G.El) (U : Config G n) (m r : ℕ) (i : Cell n) :
    Pressure.shorten p m r (Lattice.gauge z U) i=G.adjoint (z i.1) (Pressure.shorten p m r U i) := by
  unfold Pressure.shorten shortenTerm; rw [pivot_sum]
  refine tsum_congr fun j => ?_; split
  next h =>
    let s := (p.row i.2 j).2
    have he : stop i.1 s.walk=(Work.F03.slotFace s i.1).1 := by
      unfold Work.F03.slotFace Slot.offset; rw [wrap_stop_cover,map_zero,add_comm]; nth_rw 1 [show i.1=i.1+0 by rw [add_zero]]; rw [Work.E03.stop_add_left]
    unfold PathData.ellTerms; rw [Work.F03.atSite_path,Work.F03.atSite_path,map_smul]
    change _ • G.adjoint (travel (Lattice.gauge z U) i.1 s.walk) _ = _
    rw [travel_gauge,face_gauge,G.curvature_conjugate,he,G.adjoint_mul,G.adjoint_mul,← G.adjoint_mul (z _)⁻¹ _,inv_mul_cancel,G.adjoint_one]
  simp

lemma plotted_flow (a : Clip) (p : PathData G) (z : Site n → G.El) (U : Config G n) (m r : ℕ) (i : Twin n) :
    plotted p a m r (Lattice.gauge z U) i=G.adjoint (z i.1.1) (plotted p a m r U i) := by
  unfold plotted; split
  · rw [shorten_flow]
  rw [shoot,shoot,face_gauge,G.curvature_conjugate,map_smul]

lemma thinned_flow (a : Clip) (p : PathData G) (z : Site n → G.El) (U : Config G n) (t : ℝ) (m r : ℕ) (i : Twin n) :
    thinned p a t m r (Lattice.gauge z U) i=G.adjoint (z i.1.1) (thinned p a t m r U i) := by
  unfold thinned; split
  · have h : PathData.kept a t i.1.1 (Lattice.gauge z U) ↔ PathData.kept a t i.1.1 U := by unfold PathData.kept; simp
    simp_rw [h,shorten_flow]; split <;> simp
  rw [toll_gauge,shoot,shoot,face_gauge,G.curvature_conjugate,map_smul,map_smul]

lemma sum_pay {α : Type} (x y : G.El) (F H : α → Pay G)
    (he : ∀ i v,H i (G.adjoint x v)=G.adjoint y (F i v)) (v : G.Color) :
    (∑' i,H i) (G.adjoint x v)=G.adjoint y ((∑' i,F i) v) := by
  let X:= (adBody x).toContinuousLinearEquiv
  let Y:= (adBody y).toContinuousLinearEquiv
  let L := ContinuousLinearEquiv.arrowCongr X Y
  have hh (i) : H i=L (F i) := by
    ext w k; have q := X.apply_symm_apply w
    have h := he i (X.symm w)
    change H i (X (X.symm w)) = Y (F i _) at h
    rw [q] at h; exact congr_fun (congr_arg WithLp.ofLp h) k
  have hf : (∑' i,H i) = L (∑' i,F i) := by simp_rw [hh]; exact L.map_tsum.symm
  rw [hf]
  change Y ((∑' i,F i) (X.symm (X v))) = Y ((∑' i,F i) v); rw [X.symm_apply_apply]

lemma travel_ad (z : Site n → G.El) (V : Config G n) (y : Site n) (w : Walk) (u : G.Color) :
    G.adjoint (travel (Lattice.gauge z V) y w) (G.adjoint (z (stop y w)) u)=G.adjoint (z y) (G.adjoint (travel V y w) u) := by
  rw [travel_gauge,G.adjoint_mul,G.adjoint_mul,← G.adjoint_mul (_⁻¹),inv_mul_cancel,G.adjoint_one]

lemma lane_flow {X Y : Type*} (z : Site n → G.El) (K : Row X Y) (V : Config G n) (m d : ℕ) (x : Co n X) (y : Co n Y) (b : G.Color) :
    Pressure.lane m d (Lattice.gauge z V) K x y (G.adjoint (z y.1) b)=G.adjoint (z x.1) (Pressure.lane m d V K x y b) := by
  unfold Pressure.lane
  apply sum_pay _ _ _ _ _ b
  intro i v
  unfold Pressure.priced; split
  next h =>
    have hh : stop x.1 (route 0 i 1)=y.1 := by rw [h.2]; simpa using Work.E03.stop_route x.1 0 i
    change K _ _ _ • G.adjoint _ _ = G.adjoint _ (K _ _ _ • G.adjoint _ v)
    rw [map_smul,← hh, travel_ad]
  simp

lemma leap_flow (S : StepData c f) (T : Tube G S) (z : Site c → G.El) (V : Config G c)
    (i : Twin f) (j : Twin c) (m : ℕ) (b : G.Color) :
    leap S T.R m (Lattice.gauge z V) i j (G.adjoint (z j.1.1) b)=G.adjoint (z (S.ratio.parent i.1.1)) (leap S T.R m V i j b) := by
  unfold leap; apply sum_pay _ _ _ _ _ b
  intro u y
  unfold casted; dsimp only; split
  next H =>
    let w := (mesh i).1; let g := S.ratio; let R := route (lift (g.residue w)) (S.patch.L.val • u) 1
    have he : g.parent (stop w R) = (mesh j).1 := by unfold R g w; rw [Work.E03.casted_endpoint .., S.ratio.embed_parent]; exact H.2.symm -- defeq g.res etc
    rw [← copied S.ratio S.patch.odd_side]
    change T.R.mf _ _ u • G.adjoint (travel (Lattice.gauge (constantGauge z g) (replica g V)) w R)
      (G.adjoint (z (mesh j).1) y)=G.adjoint (z (g.parent w)) (T.R.mf _ _ u • G.adjoint (travel (replica g V) w R) y)
    rw [map_smul]
    have h := travel_ad (constantGauge z g) (replica g V) w R y
    simp only [constantGauge,Function.comp_apply,he] at h
    erw [h]
  simp

lemma bothStacks (S : StepData c f) (T : Tube G S) (z : Site c → G.El) (V : Config G c) (m : ℕ) (t : ℝ) :
    let W := Lattice.gauge z V
    (∀ i : Twin f, T.Mv m t W i=G.adjoint (z (S.ratio.parent i.1.1)) (T.Mv m t V i)) ∧
      (∀ i : Bond c, T.Mw m t W i=G.adjoint (z i.1) (T.Mw m t V i)) := by
  intro W
  have h j : T.vision m t W j=G.adjoint (z j.1.1) (T.vision m t V j) := thinned_flow ..
  constructor
  · intro i; unfold Mv Pressure.zip
    rw [map_sum]; simp only [h,Φ,W,leap_flow]
  intro i; unfold Mw Pressure.zip; rw [map_sum]; simp only [h]
  apply Finset.sum_congr rfl; intro j hj
  exact lane_flow z T.R.mn V m S.patch.L.val (pole i) (mesh j) _

section sector
variable (S : StepData c f) (T : Tube G S) (z : Site c → G.El) (V : Config G c) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (k : S.Choices)

def fine (i : Bond f) := z (S.ratio.parent i.1)
def rowAt (i : Slots S) : G.El := z ((i.1).act (roots S (i.2.elim (fun p => .inl p.1) Sum.inr)))
def columnAt (i : Active A x F) : G.El := fine S z i.val.val

private lemma motion (s : Signed) (a : Directions G f) :
    facade S s (Lattice.gauge z V) (pivot (fine S z) a)= Lattice.gauge ((z ∘ s.act) ∘ S.ratio.parent) (facade S s V a) := by
  let w := constantGauge z S.ratio
  have he (a : Directions G f) : pivot (fine S z) a=swing w a := rfl
  rw [facade,he, ← copied S.ratio S.patch.odd_side, swing_increment,Work.F05.pull_gauge_zero]
  change Lattice.gauge (fun i => w (affine s 0 i)) (facade S s V a)=_
  have hx : (fun i => w (affine s 0 i))=(z ∘ s.act) ∘ S.ratio.parent := by funext; simp [w,constantGauge,affine,S.ratio.parent_signed S.patch.odd_side]
  rw [hx]

lemma responseP (s : Signed) (i : Cell f) (a : Directions G f) :
    plaquetteJet S (Lattice.gauge z V) s i (pivot (fine S z) a)=G.adjoint (z (s.act (S.ratio.parent i.1))) (plaquetteJet S V s i a) := by
  let w := z (s.act (S.ratio.parent i.1)); let L := (adBody w).toContinuousLinearEquiv
  unfold plaquetteJet
  refine marks (pivot (fine S z)) L _ _ ?_ a
  funext u; dsimp only [Function.comp_apply]
  rw [motion, face_gauge,G.curvature_conjugate]; rfl

private lemma predicting (h : S.patch.Branches S.kernel G) (s : Signed) (i : Bond c) (a : Directions G f) :
    predictGroup (Lattice.gauge z V) k s i (pivot (fine S z) a)=Lattice.gauge (z ∘ s.act) (S.prediction (facade S s V a) (choice s k)) i := by
  rw [predictGroup,motion,(choice_gauge h _ _ _).2]
  have he : (((z ∘ s.act)∘S.ratio.parent)∘S.ratio.embed)=(z ∘ s.act) := by funext; simp [S.ratio.embed_parent,Function.comp_apply]
  rw [he]

lemma responseBond (h : S.patch.Branches S.kernel G) (s : Signed) (i : Bond c) (a : Directions G f) :
    blockJet (Lattice.gauge z V) k s i (pivot (fine S z) a)=G.adjoint (z (s.act i.1)) (blockJet V k s i a) := by
  let w := z (s.act i.1); let H : G.Color ≃L[ℝ] G.Color := (adBody w).toContinuousLinearEquiv
  unfold blockJet
  refine marks (pivot (fine S z)) H _ _ ?_ a
  funext u; dsimp only [Function.comp_apply]; unfold predictorTurn
  rw [show (0:Directions G f) = pivot (fine S z) (0:Directions G f) from (map_zero _).symm,predicting S z V k h,predicting S z V k h]
  change G.curvature _ = G.adjoint w _
  rw [← G.curvature_conjugate]; unfold Lattice.gauge; congr 1
  dsimp only [Function.comp_apply,w]; unfold predictGroup; rw [map_zero]; group

lemma aim (h : S.patch.Branches S.kernel G) (s : Signed) :
    S.prediction (facade S s (Lattice.gauge z V) 0) (choice s k) = Lattice.gauge (z ∘ s.act) (S.prediction (facade S s V 0) (choice s k)) := by
  funext i; change predictGroup _ k s i _ = _
  simpa only [map_zero] using predicting S z V k h s i 0

lemma template (h : S.patch.Branches S.kernel G) (y : Directions G f) :
    base T x (Lattice.gauge z V) k = pivot (rowAt S z) (base T x V k) ∧
      bump T x (Lattice.gauge z V) k (pivot (fine S z) y)=pivot (rowAt S z) (bump T x V k y) := by
  have h0 (s : Signed) : facade S s (Lattice.gauge z V) 0 = Lattice.gauge ((z ∘ s.act) ∘ S.ratio.parent) (facade S s V 0) := by simpa only [map_zero] using motion S z V s 0
  have h1 (s : Signed) : pull s 0 (Lattice.gauge z V)=Lattice.gauge (z ∘ s.act) (pull s 0 V) := by rw [Work.F05.pull_gauge_zero]; congr! 1; funext; simp [affine]
  constructor
  · funext i; rw [pivot_val]; obtain ⟨s,j|j⟩ := i
    · have hh := (bothStacks S T (z ∘ s.act) (pull s 0 V) (till x) (temp x)).1 j
      change faceFixed T x _ _ j=G.adjoint (z (s.act (S.ratio.parent j.1.1))) (faceFixed T x _ _ j)
      rw [faceFixed,h0,h1,hh,Tube.Xf,plotted_flow,faceFixed,map_sub]; rfl
    · have hh := (bothStacks S T (z ∘ s.act) (pull s 0 V) (till x) (temp x)).2 j
      let Z' := z ∘ s.act
      change noiseFixed _ _ _ _ _ (T:=T)=G.adjoint (Z' j.1) (noiseFixed x V k s j (T:=T))
      rw [noiseFixed,noiseFixed,h1,aim S z V k h,hh,map_sub]
      change Z S (Lattice.gauge Z' _) (Lattice.gauge Z' _) j-G.adjoint (Z' _) _= _
      unfold Z
      rw [map_smul,← G.curvature_conjugate]; unfold Lattice.gauge
      congr! 3; group
  funext i; rw [pivot_val]; obtain ⟨s,j|j⟩ := i
  · change faceKick _ _ _ _ _ _=G.adjoint (z (s.act (S.ratio.parent j.1.1))) (faceKick _ _ _ _ _ _)
    unfold faceKick; split
    · rw [h0]; exact barrel_gauge T.up _ ((z∘s.act)∘S.ratio.parent) (till x) _ _ (fun j => responseP S z V s j y) j.1
    · rw [responseP,map_smul]
  change noiseKick _ _ _ _ _=G.adjoint (z (s.act j.1)) (noiseKick V k y s j)
  rw [noiseKick,noiseKick,responseBond S z V k h,map_neg,map_smul]

lemma bands (W : Stencils S) (y : LogArray G (Slots S)) :
    Rows.restrict x W A F (pivot (rowAt S z) y)=pivot (rowAt S z) (Rows.restrict x W A F y) := by
  funext i; unfold Rows.restrict; rw [pivot_val]; split <;> simp [*,pivot_val]

lemma blew (W : Stencils S) (p : LogArray G (Active A x F)) :
    pivot (fine S z) (Rows.fresh x W A F p)=Rows.fresh x W A F (pivot (columnAt S z x A F) p) := by
  funext i; rw [pivot_val]; unfold fresh; split
  · split
    · rfl
    simp
  simp

-- active vectors on *all* links (do not re-root within a plate)
lemma pushed {p : Clip} {σ C Λ : ℝ} (hp : T.up.Bounds p σ C Λ) (h : S.patch.Branches S.kernel G) (W : Stencils S) (v : SectorChange.Gaussian.Vec (In x A F (G:=G))) :
    let E := onPage (Equiv.refl (Active A x F)) (tagColor (fun i => adBody (columnAt S z x A F i)))
    let H := onPage (Equiv.refl (Slots S)) (tagColor (fun i => adBody (rowAt S z i)))
    Rows.move T x (Lattice.gauge z V) k W A F *ᵥ (E *ᵥ v)=H *ᵥ (Rows.move T x V k W A F *ᵥ v) := by
  intro E H
  let c : LogArray G (Active A x F) := tape v
  have he : tape.symm c=v := tape.symm_apply_apply v
  have ht : tape (E *ᵥ v)=pivot (columnAt S z x A F) c := by
    rw [← he,show _ *ᵥ _ = tape.symm _ from onPage_read _ _ c,tape.apply_symm_apply]; rfl -- implicit CLIE
  rw [moved T x (Lattice.gauge z V) k W A F hp,moved T x V k W A F hp,ht]
  unfold H; rw [onPage_read] -- via pivot rfl
  unfold Rows.selected
  rw [← blew,(template S T z V x k h _).2,bands]; rfl

/-- Change also held *group* coordinates (two endpoints!). This is
NOT a color basis movement on y. -/
def sendFrozen (Y : LinkArray G (Frozen A x F)) (i : Frozen A x F) :=
  let e := i.val.val
  fine S z e * Y i * (z (S.ratio.parent (e.1+step e.2)))⁻¹
lemma shells_move (q : YM.Push.SectorMeasure.Chi) (v : ℝ) (Y : LinkArray G (Frozen A x F)) (i : Frozen A x F) :
    autoShell q v (Lattice.gauge z V) (sendFrozen S z x A F Y) i=G.adjoint (fine S z i.val.val) (autoShell q v V Y i) := by
  unfold autoShell
  rw [← patched_covary, ← copied _ S.patch.odd_side]; congr 1
  unfold sendFrozen fine constantGauge Lattice.gauge; dsimp only [Function.comp_apply]; group
lemma fired (q : YM.Push.SectorMeasure.Chi) (v : ℝ) (Y : LinkArray G (Frozen A x F)) :
    input x A F (autoShell q v (Lattice.gauge z V) (sendFrozen S z x A F Y))=pivot (fine S z) (input x A F (autoShell q v V Y)) := by
  funext i; rw [pivot_val]; unfold input; split
  · split
    next hi he => exact shells_move S z V x A F q v Y (⟨⟨i,hi⟩,he⟩ : Frozen A x F)
    simp
  simp

lemma pushed_seed (q : YM.Push.SectorMeasure.Chi) (v : ℝ) (Y : LinkArray G (Frozen A x F)) (h : S.patch.Branches S.kernel G) (W : Stencils S) :
    Rows.source T x (Lattice.gauge z V) k W A F q v (sendFrozen S z x A F Y) =
      onPage (Equiv.refl _) (tagColor (fun i => adBody (rowAt S z i))) *ᵥ Rows.source T x V k W A F q v Y := by
  unfold Rows.source
  rw [onPage_read, fired S z V x A F]
  have hh := template S T z V x k h (input x A F (autoShell q v V Y))
  rw [hh.1,hh.2,← map_add,bands]; rfl

/-- Result for actual Gram, source and both windows incl means on the
same probes. Frozen link ordering unchanged. -/
theorem stays (q : YM.Push.SectorMeasure.Chi) (v : ℝ) (Y : LinkArray G (Frozen A x F))
    {o : Clip} {σ C Λ : ℝ} (hp : T.up.Bounds o σ C Λ) (h : S.patch.Branches S.kernel G) (W : Stencils S) (g : Assembly.Geometry) :
    let Q X := Rows.gram T x X k W A F
    let b X Y := Rows.blame T x X k W A F q v Y
    let L := onPage (Equiv.refl (Active A x F)) (tagColor (fun i => adBody (columnAt S z x A F i)))
    let H := Lattice.gauge z V; let y := sendFrozen S z x A F Y; let X := Density.skim L
    let U := fun M u => pane (Assembly.sectorW G S x A F g) (Q M) u
    Q H=X (Q V) ∧ b H y=L *ᵥ b V Y ∧ ∀ u, U H u=X (U V u) ∧
      mirror (U H u)=X (mirror (U V u)) ∧
      offCenter (U H u) (b H y)=L *ᵥ offCenter (U V u) (b V Y) ∧
      (mirror (U H u)).det=(mirror (U V u)).det := by
  intro Q b L H y X U
  let M s := Rows.move T x s k W A F
  let E := fun i => adBody (columnAt S z x A F i)
  let N := fun i => adBody (rowAt S z i)
  obtain ⟨he,hb⟩ := weaves (Equiv.refl _) E (Equiv.refl _) N (M V) (M H) (Rows.source T x H k W A F q v y)
    (Rows.source T x V k W A F q v Y) (pushed S T z V x A F k hp h W) (congr_arg _ (pushed_seed S T z V x A F k q v Y h W))
  change Q H=_ at he; change b H y=_ at hb
  refine ⟨he,hb,fun u => ?_⟩
  let T (i : Active A x F) : Set (Active A x F) := {j | Assembly.rel S g (radiusB x) i.val.val j.val.val}
  have hh : Assembly.sectorW G S x A F g=sheet (k:=G.ColorIndex) T := by cases g <;> rfl
  unfold U; rw [hh]
  exact moves _ E (Q V) (Q H) _ _ T T u rfl he hb
end sector
end GaugeRoute
end YM.AnalyticBridge.LocalGaussianLaws

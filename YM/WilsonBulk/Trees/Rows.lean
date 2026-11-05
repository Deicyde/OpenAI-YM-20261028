import YM.WilsonBulk.Trees.Repeat
import YM.WilsonBulk.Grid.Paper

/-! The EXACT rows of the localized projector. Consume **post**-size costs;
width can be picked before block. Printed Rows use `clothe`/`unitSplit` order
and are in real `Laurent.Width`. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Finset Precision Exterior Stationary Audience Matrix FreeResolvent Tree
open Work.F08 Lifted Primitives.TwoWave
open Primitives.TwoWave.RealSlice (three)
open Progress.ClassicalKin Progress.ClassicalKin.Tent
open scoped Topology BigOperators Matrix -- deq

variable {α β γ A B : Type} {c f L : Side} {P : Patch} {K : KernelChoices}
  {g : Ratio c f}

def slot0 (F : α→β→ℝ) : Row α β := fun i j x => if x=0 then F i j else 0
lemma Stamped.site [Fintype α] [Fintype β] (F : α→β→ℝ) : Stamped (slot0 F) := by
  rintro σ h; apply Draw.ready_strip
  intro i j s; refine ⟨‖F i j‖,norm_nonneg _,fun x=> by positivity [Real.exp_pos (s * size (x:Cover)), norm_nonneg (slot0 F i j x)],?_,?_⟩
  · apply summable_of_ne_finset_zero (s:={0}); intro v hv; simp [slot0, (show v ≠ 0 by simpa using hv)]
  rw [tsum_eq_single (0 : Cover) (fun i hi=>by simp [slot0, hi])]; simp [slot0,size]
lemma slot0_acts (F : α→β→ℝ) (c : Side) (x y) : (slot0 F).acts c x y =
    if y.1=x.1 then F x.2 y.2 else 0 := by
  unfold Row.acts; rw [Matrix.of_apply, tsum_eq_single 0 (fun i hi => by simp [slot0, hi])]; simp [slot0]

-- scalar parent and trail
variable (L)
def copyRow : Row (Co L (TypeFace 0)) (TypeFace 0) := slot0 (fun i j => if j=i.2 then 1 else 0)
variable {L}
lemma copy_acts (S : StepData c f) : Seen c (splitCo S.ratio _) (Equiv.refl _) (copyRow S.patch.L) (sitesCopy S) := by
  unfold Seen; ext ⟨x,i⟩ ⟨y,j⟩
  simp only [Matrix.submatrix_apply,copyRow,split_co,sitesCopy,Matrix.of_apply,Equiv.refl_apply, Prod.mk.injEq]; erw [slot0_acts]; aesop

def hikeRows (T : Model P K) : Row (Co P.L (TypeFace 0)) (Co P.L (TypeFace 1)) :=
  fun i => Draw.path P.L (lift i.1) (T.hike ((dock P K three).ratio.assemble (0,i.1)))
lemma Stamped.hikeRows (T : Model P K) : Stamped (hikeRows T) := fun s _ => Draw.ready_strip (fun _ => Draw.path_ready _ _) s
lemma hike_seen (G : Gauge) (T : Model P K) (v : f.val=c.val*P.L.val) :
    Seen c (splitCo (data v K).ratio _) (splitCo (data v K).ratio _)
      (hikeRows T) (hiking G _ (spreadForest T v)) := by
  unfold Seen; let S := data v K; let g:=S.ratio
  ext ⟨x,i⟩ ⟨y,j⟩
  rw [hiking,LinearMap.toMatrix'_apply,Matrix.submatrix_apply,split_co (data v K).ratio ⟨x,i⟩] -- arguments?
  simp only [LinearMap.pi_apply]
  let X := T.hike ((dock P K three).ratio.assemble (0,g.residue x))
  change integralLink x _ _ = Draw.spot g (Draw.path g.count (lift (g.residue x)) X) (g.parent x) (y,j)
  erw [Draw.spot_path]; rw [add_comm (wrap f _), Ratio.unpack_at]; rw [copied_hike]

-- rectangular color order
variable (G : Gauge)
lemma Seen.fine {r t} {F : Row (Co g.count (TypeFace r)) (Co g.count (TypeFace t))}
    {M : Matrix (Body r f) (Body t f) ℝ} (h : Seen c (splitCo g _) (splitCo g _) F M) :
    Seen c (splitCo g _) (splitCo g _) (fineColor G F) (patron G M) := by
  unfold Seen; rw [see_fineColor]; exact congrArg (patron G) h
lemma Seen.coarse {r t} {F : Row (Co g.count (TypeFace r)) (TypeFace t)} {M : Matrix (Body r f) (Body t c) ℝ}
    (h : Seen c (splitCo g _) (Equiv.refl _) F M) : Seen c (splitCo g _) (Equiv.refl _) (bondColor G F) (patron G M) := by
  unfold Seen; exact Eq.trans (congrArg (patron G) h) (see_bondColor ..).symm
lemma Seen.fromFine {r t} {F : Row (TypeFace r) (Co g.count (TypeFace t))} {M : Matrix (Body r c) (Body t f) ℝ}
    (h : Seen c (Equiv.refl _) (splitCo g _) F M) : Seen c (Equiv.refl _) (splitCo g _) (marketColor G F) (patron G M) := by
  unfold Seen; exact Eq.trans (congrArg (patron G) h) (see_marketColor ..).symm

section summands
-- `clothe` includes actu frame degrees. one-cell range
variable {S : StepData c f}
-- need classical deq on expanded finite types: choose on full statements and compare
open scoped Classical
def leftBound (L : Side) : Row (Co L (Loc G 1)) (ParcelG G L) := slot0 (fun i j=> if j=Sum.inl i then 1 else 0)
def rightBound (L : Side) : Row (Loc G 0) (ParcelG G L) := slot0 (fun i j=> if j=Sum.inr i then 1 else 0)
lemma sees_left (S : StepData c f) : Seen c (splitCo S.ratio _) (clothe G S) (leftBound G S.patch.L) (butt G c f) := by
  unfold Seen; rw [helmet_butt]; ext i (j|j)
  · rw [submatrix_apply, inflowL, leftBound]; erw [slot0_acts]
    by_cases h : i=j
    · subst j; simp [shardX, LinearMap.toMatrix'_apply, unitSplit]; rfl
    by_cases h₁ : (unitSplit G S 1 j).1=(unitSplit G S 1 i).1
    · have hx : (unitSplit G S 1 j).2 ≠ (unitSplit G S 1 i).2 := fun e => h ((unitSplit G S 1).injective (Prod.ext h₁ e).symm)
      simp [show (splitCo S.ratio (Loc G 1))=(unitSplit G S 1) from rfl,h₁,h,shardX,LinearMap.toMatrix'_apply]; intro he; exact hx (Sum.inl.inj he)
    simp [show (splitCo S.ratio (Loc G 1))=(unitSplit G S 1) from rfl,h₁,h,shardX,LinearMap.toMatrix'_apply]
  erw [submatrix_apply, show clothe G S (Sum.inr j) = (j.1, Sum.inr j.2) from rfl, leftBound,slot0_acts]
  simp [shardX,LinearMap.toMatrix'_apply]
lemma sees_right (S : StepData c f) : Seen c (Equiv.refl _) (clothe G S) (rightBound G S.patch.L) (brim G c f) := by
  unfold Seen; rw [helmet_brim]; ext ⟨i,b⟩ (j|⟨j,d⟩)
  · rw [submatrix_apply, inflowL, rightBound, slot0_acts]
    simp [shardY,LinearMap.toMatrix'_apply]
  rw [submatrix_apply, show clothe G S (Sum.inr (j,d))=(j,Sum.inr d) from rfl,rightBound,slot0_acts];
  by_cases h : j=i <;> simp [h,shardY,LinearMap.toMatrix'_apply, Pi.single_apply]; grind
end summands
end YM.WilsonBulk

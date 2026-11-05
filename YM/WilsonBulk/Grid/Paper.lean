import YM.WilsonBulk.Trees.Map
import YM.Push.FREE_RESOLVENT.FullRow
import YM.Work.F08

/-! Little arithmetic for post-block qualitative widths and exact period fit.
No pre-block height claims (Ready below on any specified rate, then heights may
use L and all stencil data). Reuses F08, FreeResolvent inflight calculus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Finset Precision Exterior Matrix FreeResolvent Work.F08
open scoped Topology BigOperators Matrix

variable {n c L f : Side} {α β γ α' β' : Type} {G : Gauge} {θ σ M : ℝ}
open Stationary
section qualitative
def Stamped (F : Row α β) := ∀ σ, 0≤ σ → ∃ M, 0 ≤ M ∧ F.strip σ M
abbrev rough {α β : Type} (F : Row α β) (n : Side) := F.acts n
variable {P U : Row α β} {V : Row β γ}
namespace Stamped
lemma bound (h : Stamped P) (s : ℝ) : ∃ M, 0 ≤ M ∧ P.strip s M := by
  obtain ⟨M,hM,h⟩:= h (max s 0) (le_max_right ..); exact ⟨M,hM,strip_mono h (le_max_left ..) le_rfl⟩
lemma opposite (h : Stamped P) : Stamped (transRows P) := by
  intro σ hσ; obtain ⟨M,h,hP⟩:=h σ hσ; exact ⟨M,h,strip_trans hP⟩
lemma zero : Stamped (0 : Row α β) := by
  intro σ _; refine ⟨0,le_rfl,fun i j=>?_⟩; simp [Width,SumBudget]
lemma unit [DecidableEq α] : Stamped (unitRow α) := fun _ _=> ⟨1,zero_le_one,strip_unit⟩
lemma sub (h : Stamped P) (he : Stamped U) : Stamped (minusRows P U) := by
  intro σ hσ; obtain ⟨M,h,hP⟩:=h σ hσ; obtain ⟨K,he,hK⟩:=he σ hσ; exact ⟨_,add_nonneg h he,strip_minus hP hK⟩
lemma plus (h : Stamped P) (he : Stamped U) : Stamped (FreeResolvent.plusRows P U) := by
  intro σ hσ; obtain ⟨M,h,hP⟩:=h σ hσ; obtain ⟨K,he,hK⟩:=he σ hσ; exact ⟨_,add_nonneg h he, FreeResolvent.strip_plus hP hK⟩
lemma product [Fintype β] (h : Stamped P) (he : Stamped V) : Stamped (composeRows P V) := by
  intro σ hσ; obtain ⟨M,h,hP⟩:=h σ hσ; obtain ⟨K,he,hK⟩:=he σ hσ; exact ⟨_,by positivity,strip_compose hσ hP hK⟩
lemma weight (h : Stamped P) (v : ℝ) : Stamped (scaleRows v P) := by
  intro σ hσ; obtain ⟨M,hM,hP⟩:=h σ hσ; exact ⟨_,by positivity,strip_scale hP v⟩
lemma cobound (r : ℕ) : Stamped (Exterior.cobound r) := fun s _ => FreeResolvent.cobound_ready r s
lemma acts_sub (h : Stamped P) (he : Stamped U) : (minusRows P U).acts n=P.acts n-U.acts n :=
  acts_minus (le_refl 0) (h.bound 0).choose_spec.2 (he.bound 0).choose_spec.2 n
lemma acts_plus (h : Stamped P) (he : Stamped U) : (plusRows P U).acts n=P.acts n+U.acts n :=
  FreeResolvent.acts_plus (h.bound 0).choose_spec.2 (he.bound 0).choose_spec.2 le_rfl n
lemma comp [Fintype β] (h : Stamped P) (he : Stamped V) :
    (composeRows P V).acts n=P.acts n*V.acts n :=
  acts_compose (le_refl 0) (h.bound 0).choose_spec.2 (he.bound 0).choose_spec.2 n
end Stamped
end qualitative

section colors

-- paint several row-of-row types. Rectangular coarse parents.
def painted (F : Row α β) (fa : α'→α) (f : α'→G.ColorIndex) (ga : β'→β) (g : β'→G.ColorIndex) : Row α' β' :=
  fun i j x => if f i=g j then F (fa i) (ga j) x else 0
lemma painted_strip {F : Row α β} (fa : α'→α) (f : α'→G.ColorIndex) (ga : β'→β) (g : β'→G.ColorIndex)
    (hF : F.strip σ M) (h : 0≤ M) : (painted F fa f ga g).strip σ M := by
  intro i j; unfold painted; split -- split_if maybe
  · exact hF _ _
  simp [Width,SumBudget,h]
lemma Stamped.painted {F : Row α β} (fa : α'→α) (f : α'→G.ColorIndex) (ga : β'→β) (g : β'→G.ColorIndex)
    (hF : Stamped F) : Stamped (painted F fa f ga g) := by
  intro σ h; obtain ⟨M,h,hK⟩:= hF _ h; exact ⟨M,h,painted_strip _ _ _ _ hK h⟩
lemma colored (F : Row α β) (fa : α'→α) (f : α'→G.ColorIndex) (ga : β'→β) (g : β'→G.ColorIndex)
    (v z : Site c) (i : α') (j : β') :
    (painted F fa f ga g).acts c (v,i) (z,j) =
      if f i=g j then F.acts c (v,fa i) (z,ga j) else 0 := by split <;> simp [*,painted,Row.acts]

def fineColor (G : Gauge) {r t : ℕ} (F : Row (Co L (TypeFace r)) (Co L (TypeFace t))) :=
  painted F (fun x : Co L (Loc G r)=>(x.1,x.2.1)) (fun x=> x.2.2)
    (fun x : Co L (Loc G t)=>(x.1,x.2.1)) (fun x=> x.2.2)
def bondColor (G : Gauge) {r t : ℕ} (F : Row (Co L (TypeFace r)) (TypeFace t)) :=
  painted F (fun x : Co L (Loc G r)=>(x.1,x.2.1)) (fun x=> x.2.2)
    (fun x : Loc G t=>x.1) (fun x=> x.2)
def marketColor (G : Gauge) {r t : ℕ} (F : Row (TypeFace r) (Co L (TypeFace t))) :=
  painted F (fun x : Loc G r=>x.1) (fun x=> x.2)
    (fun x : Co L (Loc G t) =>(x.1,x.2.1)) (fun x=> x.2.2)
def stillColor (G : Gauge) {r t : ℕ} (F : Row (TypeFace r) (TypeFace t)) :=
  painted F (fun x : Loc G r=>x.1) (fun x=> x.2)
    (fun x : Loc G t=>x.1) (fun x=> x.2)
lemma see_fineColor (r t) (g : Ratio c f) (F : Row (Co g.count (TypeFace r)) (Co g.count (TypeFace t))) :
    ((fineColor G F).acts c).submatrix (splitCo g (Loc G r)) (splitCo g (Loc G t))=
      patron G ((F.acts c).submatrix (splitCo g (TypeFace r)) (splitCo g (TypeFace t))) := by
  rw [match_tensor]; ext ⟨x,i,u⟩ ⟨y,j,v⟩
  simp only [Matrix.submatrix_apply,tensor,Matrix.of_apply,split_co,fineColor]; rw [colored]
lemma see_bondColor (r t) (g : Ratio c f) (F : Row (Co g.count (TypeFace r)) (TypeFace t)) :
    ((bondColor G F).acts c).submatrix (splitCo g (Loc G r)) id=
      patron G ((F.acts c).submatrix (splitCo g (TypeFace r)) id) := by
  rw [match_tensor]; ext ⟨x,i,u⟩ ⟨y,j,v⟩; simp only [Matrix.submatrix_apply,tensor,Matrix.of_apply,id_eq,split_co,bondColor]; rw [colored]
lemma see_marketColor (r t) (g : Ratio c f) (F : Row (TypeFace r) (Co g.count (TypeFace t))) :
    ((marketColor G F).acts c).submatrix id (splitCo g (Loc G t))=
      patron G ((F.acts c).submatrix id (splitCo g (TypeFace t))) := by
  rw [match_tensor]; ext ⟨x,i,u⟩ ⟨y,j,v⟩; simp only [Matrix.submatrix_apply,tensor,Matrix.of_apply,id_eq,split_co,marketColor]; rw [colored]
lemma see_stillColor (c r t) (F : Row (TypeFace r) (TypeFace t)) :
    (stillColor G F).acts c= patron G (F.acts c) := by
  rw [match_tensor]; ext ⟨x,i,u⟩ ⟨y,j,v⟩; simp only [tensor,Matrix.of_apply,stillColor]; rw [colored]
end colors
section block

-- reblocking arbitrary rectangles; product with identity keeps counted rows and uses unperiodized support
variable [Fintype β] [DecidableEq β]
def rectangle (L : Side) (F : Row α β) : Row (Co L α) (Co L β) := fineCompose F (unitRow _)
lemma rect_paid (L : Side) {F : Row α β} (h : Stamped F) : Stamped (rectangle L F) := by
  intro s hs; obtain ⟨M,h,hK⟩:= h _ hs; exact ⟨_,by positivity,strip_fine (L:=L) hs hK (strip_unit (α:=Co L β))⟩
lemma rect_embedded (g : Ratio c f) {F : Row α β} (h : Stamped F) :
    F.acts f = ((rectangle g.count F).acts c).submatrix (splitCo g α) (splitCo g β) := by
  let E := splitCo g β
  have he : installed g (unitRow (Co g.count β)) = (1 : Matrix _ _ ℝ).submatrix E id := by
    unfold installed; rw [acts_unit]
  ext i j
  change _ = installed g (rectangle g.count F) i (E j)
  obtain ⟨M,-,h⟩:=h (0:ℝ) le_rfl
  rw [rectangle, installed_fine _ (le_refl 0) h strip_unit, he]; simp [Matrix.mul_apply, Matrix.one_apply,E.injective.eq_iff]
end block
section alignment
-- a `Seen` exact equality also frees both ambient dimension f and the torus chosen
-- from any size payments. Under real FPT costs. Later introduce properties for only
-- approximate tensor agreement as loops wind. For elementary row ops exact.
variable {A B D : Type}
def Seen (c : Side) (x : A ≃ Co c α) (y : B ≃ Co c β) (F : Row α β) (M : Matrix A B ℝ) :=
  M = (F.acts c).submatrix x y
variable {x : A ≃ Co c α} {y : B ≃ Co c β} {z : D ≃ Co c γ}
  {U U' : Matrix A B ℝ} {V : Matrix B D ℝ} {P P' : Row α β} {Q : Row β γ}
lemma Seen.plus (h : Seen c x y P U) (he : Seen c x y P' U') (hP : Stamped P) (hP' : Stamped P') : Seen c x y (plusRows P P') (U+U') := by
  change U=_ at h; change U'= _ at he; unfold Seen; rw [h,he,hP.acts_plus hP', submatrix_add]; rfl
lemma Seen.minus (h : Seen c x y P U) (he : Seen c x y P' U') (hP : Stamped P) (hP' : Stamped P') : Seen c x y (minusRows P P') (U-U') := by
  change U=_ at h; change U'= _ at he; unfold Seen; rw [h,he,hP.acts_sub hP', submatrix_sub]; rfl
lemma Seen.weight (h : Seen c x y P U) (r : ℝ) : Seen c x y (scaleRows r P) (r • U) := by unfold Seen at *; rw [h, acts_scale, submatrix_smul]; rfl
lemma Seen.trans (h : Seen c x y P U) : Seen c y x (transRows P) Uᵀ := by
  change U=_ at h; unfold Seen; rw [acts_trans, ← transpose_submatrix,← h]
lemma Seen.equal (h : Seen c x y P U) : (P.acts c) = repackM x y U := by
  unfold Seen at h; rw [h]; ext; simp [repackM]
lemma see_unit [DecidableEq A] [DecidableEq α] (x : A ≃ Co c α) : Seen c x x (unitRow α) 1 := by
  unfold Seen; rw [acts_unit]; ext; simp [Matrix.one_apply,x.injective.eq_iff]
section freq
variable [Fintype β] [Fintype B]
lemma Seen.chain (h : Seen c x y P U) (he : Seen c y z Q V) {p q : ℝ} (hP : P.strip σ p) (hP' : Q.strip σ q)
    (hs : 0≤ σ) : Seen c x z (composeRows P Q) (U*V) := by
  unfold Seen at *; rw [h,he, acts_compose hs hP hP']; ext i j; simp only [Matrix.mul_apply, Matrix.submatrix_apply]; exact Equiv.sum_comp y (fun k=> P.acts c (x i) k * Q.acts c k (z j))
lemma Seen.chain' (h : Seen c x y P U) (he : Seen c y z Q V) (hP : Stamped P) (hP' : Stamped Q) :
    Seen c x z (composeRows P Q) (U*V) := h.chain he (hP.bound 0).choose_spec.2 (hP'.bound 0).choose_spec.2 le_rfl
end freq
end alignment
end YM.WilsonBulk

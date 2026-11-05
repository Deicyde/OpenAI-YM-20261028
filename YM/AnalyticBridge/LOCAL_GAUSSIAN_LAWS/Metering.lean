import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.TellerFold
import YM.Push.FREE_RESOLVENT.FullRow

/-!
# Spatial reads of curled precision covariances

Compatible address and price on `plane G S F` (=actual fine d about
chosen slice, not a gauge/projected derivative), and other native
stencils. For E:. Include color and harmonic even in weight.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Current
open Function Lattice Wilson RG Precision Exterior Tree Matrix
open Bid FreeResolvent Bloch Laurent Work.F08
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side}
section Rect
variable {α β : Type} [Fintype β] [DecidableEq β]

def grouped (P : Patch) (Q : Row α β) : Row (Co P.L α) (Co P.L β) := fineCompose Q (unitRow _)
lemma grouped_price (P : Patch) {Q : Row α β} {s M : ℝ} (hs : 0≤s) (h : Q.strip s M) :
    (grouped P Q).strip s ((Fintype.card β:ℝ)*M) := by
  simpa [grouped] using (strip_fine (Q:=unitRow (Co P.L β)) hs h strip_unit)
lemma grouping (S : StepData c f) {Q : Row α β} {s M : ℝ} (hs : 0 ≤ s) (h : Q.strip s M) :
    Q.acts f = ((grouped S.patch Q).acts c).submatrix (splitCo S.ratio α) (splitCo S.ratio β) := by
  let E := splitCo S.ratio β
  have he : installed S.ratio (unitRow (Co S.ratio.count β)) = (1 : Matrix _ _ ℝ).submatrix E id := by unfold installed; rw [acts_unit]
  ext i j; change _ = installed S.ratio (grouped S.patch Q) i (E j)
  erw [grouped, installed_fine _ hs h strip_unit, he]; simp [Matrix.mul_apply, Matrix.one_apply, E.injective.eq_iff]
end Rect

section Book
variable {r t : ℕ}

def deck (G : Gauge) (P : Patch) (Q : Row (TypeFace r) (TypeFace t)) : Row (Co P.L (PAC G r)) (Co P.L (PAC G t)) := fun i j =>
  if i.2.2=j.2.2 then grouped P Q (i.1,i.2.1) (j.1,j.2.1) else 0

lemma deck_strip (P : Patch) {Q : Row (TypeFace r) (TypeFace t)} {s M : ℝ} (hs : 0≤s) (hM : 0≤M) (h : Q.strip s M) :
    (deck G P Q).strip s ((Fintype.card (TypeFace t):ℝ)*M) := by
  intro i j
  unfold deck
  split
  · exact grouped_price P hs h _ _
  simp [Width,RG.SumBudget, hM,Nat.cast_nonneg,mul_nonneg]
lemma deck_values (G : Gauge) (S : StepData c f) {Q : Row (TypeFace r) (TypeFace t)} {s M : ℝ} (hs : 0≤s) (h : Q.strip s M) :
    tensor G (Q.acts f)=((deck G S.patch Q).acts c).submatrix (splitCo S.ratio _) (splitCo S.ratio _) := by
  ext ⟨x,i,j⟩ ⟨y,b,k⟩
  by_cases he : j=k
  · rw [grouping S hs h,tensor,Matrix.of_apply,if_pos he,Matrix.submatrix_apply,Matrix.submatrix_apply,
      split_co,split_co,split_co,split_co]
    simp only [Row.acts,deck,Matrix.of_apply,if_pos he]; rfl
  rw [tensor,Matrix.of_apply,if_neg he,Matrix.submatrix_apply,split_co,split_co]
  simp [Row.acts,deck,he]

def headless (P : Patch) (G : Gauge) (r t : ℕ) (M : ℝ) :=
  ((Fintype.card (Co P.L (PAC G t)):ℝ)+Fintype.card (Co P.L (PAC G r)))*((Fintype.card (TypeFace t):ℝ)*M)
lemma headless_nn (P : Patch) (G : Gauge) (r t : ℕ) {M : ℝ} (hM : 0 ≤ M) : 0≤headless P G r t M := by unfold headless; positivity

lemma restrict_price (G : Gauge) (S : StepData c f) {Q : Row (TypeFace r) (TypeFace t)} {s M : ℝ} (hs : 0≤s) (hM : 0≤M) (h : Q.strip s M) :
    let p (r : ℕ) := fun i : FreeResolvent.Slot G f r => S.ratio.parent i.1
    (native c).Schur (p r) (p t) s (headless S.patch G r t M) (tensor G (Q.acts f)) := by
  let z t := splitCo S.ratio (PAC G t)
  intro p
  let X := deck G S.patch Q
  let C := ((Fintype.card (TypeFace t):ℝ)*M)
  have hx : X.strip s C := deck_strip _ hs hM h
  have hh : (native c).Schur Prod.fst Prod.fst s (headless S.patch G r t M) (X.acts c) := by
    unfold headless
    refine ⟨(downgrade (physical_rows hx hs c) hs).mono le_rfl ?_, (downgrade (physical_cols hx hs c) hs).mono le_rfl ?_⟩ <;> unfold C <;> gcongr <;> simp <;> positivity
  have he t : p t = Prod.fst ∘ (z t) := by funext i; simp [p,z,split_co]
  rw [he r,he t,deck_values G S hs h]
  exact hh.submatrix (z r).injective (z t).injective

end Book
lemma plane_sub (S : StepData c f) (F : Forest S.ratio) : plane (G:=G) S F=(tensor G (d 1 f)).submatrix id (plant F) := by
  ext i j; simp [plane,Matrix.mul_apply,insertion,mul_ite]
def curlTariff (G : Gauge) (P : Patch) (s : ℝ) := headless P G 2 1 (cobound_ready 1 s).choose
lemma curlTariff_nn (G : Gauge) (P : Patch) (s : ℝ) : 0≤curlTariff G P s := headless_nn _ _ _ _ ((cobound_ready 1 s).choose_spec.1)
def seat (S : StepData c f) (r : ℕ) := fun i : FreeResolvent.Slot G f r => S.ratio.parent i.1
lemma plane_price (S : StepData c f) (F : Forest S.ratio) (s : ℝ) (hs : 0≤s) :
    (native c).Schur (seat (G:=G) S 2) (theta S.ratio F) s (curlTariff G S.patch s) (plane S F) := by
  obtain ⟨hh,he⟩ := (cobound_ready 1 s).choose_spec
  have h := restrict_price G S hs hh he
  rw [plane_sub]
  change (native c).Schur ((seat _ 2) ∘ id) ((seat _ 1) ∘ plant F) s (curlTariff G S.patch s) ((tensor G (d 1 f)).submatrix id (plant F))
  exact h.submatrix Function.injective_id (plant_inj F)

lemma plane_bill (S : StepData c f) (F : Forest S.ratio) (s : ℝ) (hs : 0≤s) {Q : Matrix (Active G F) (Active G F) ℝ} {M : ℝ} (hM : 0≤M)
    (h : (native c).Schur (theta S.ratio F) (theta S.ratio F) s M Q) :
    let d := plane S F (G:=G)
    (native c).Schur (seat (G:=G) S 2) (seat (G:=G) S 2) s ((curlTariff G S.patch s*M)*curlTariff G S.patch s) (d*Q*d.transpose) := by
  have hp := plane_price S F s hs (G:=G); let he := curlTariff_nn G S.patch s
  exact (hp.mul h hs he hM).mul hp.transpose hs (mul_nonneg he hM) he
end YM.AnalyticBridge.LocalGaussianLaws.Current

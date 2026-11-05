import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Resolve
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Wage
import YM.Push.GRID_APPROXIMATION.AttachDefs

/-!
# Do the finite P preparation on the same free horizon

Use finite-torus KP0 read (on genuine through N vector), *not* a
conditioned covariance or a continuum approximation. No later covariance or
Gaussian probability estimates claimed. Carry full color lift.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.FacePrice
open Filter Function Set Lattice Wilson RG Cells Source Source.Drops
open Work Matrix Laurent Bloch Metric Exterior Precision Next.Free Resolve
open scoped Topology Matrix.Norms.Frobenius BigOperators ComplexConjugate
variable {G : Gauge} {m n : Side} {A : Bed} {V : Clip} {η D : ℝ} {j : ℕ}

private lemma hue (s : Signed) (p : PlaqAxes) : Compass.wind s p=turned s p := by
  unfold Compass.wind turned
  let a := p.val.1; let b := p.val.2
  change (if s.perm a < s.perm b then _ else _)*(if (Bool.xor false (s.flip a)) then _ else _)*(if (Bool.xor false (s.flip b)) then _ else _) = _
  simp only [Bool.false_xor]; ring
private lemma facing (s : Signed) : Surjective (reorient (n:=n) s) := by
  intro a
  let A : Edge (Site n) ≃ Body 1 n := Equiv.prodCongr (Equiv.refl _) axisEquiv
  let X := StepData.sendBonds s (0:Site n)
  let F (b : Edge (Site n)) := ((posDir b.2).rotate s).neg
  let f (b : Edge (Site n)) := if F b then -a (A b) else a (A b)
  let y : form 1 n := f ∘ X.symm ∘ A.symm
  refine ⟨y,?_⟩; ext b
  obtain ⟨c,rfl⟩ := A.surjective b
  unfold reorient; simp only [show (A c).2=axisEquiv c.2 from rfl,Equiv.symm_apply_apply]
  change (if F c then -y (A (X c)) else y (A (X c)))= _
  unfold y f; simp only [Function.comp_apply,Equiv.symm_apply_apply]; split <;> simp

variable (h : Floor A V n η D) (he : 0<η)
private lemma score (s : Signed) {r : ℝ} (hr : 0<r) (hj : 4≤j) (v : Train j) (l : ℝ) (e : Defined r l v A) (i q : Face (Per n)) :
    let c := fun i j => screenP h he (address n i) (address n j)
    turned s i.2 * turned s q.2 * c (Face.send s 0 i) (Face.send s 0 q)=c i q := by
  intro c; let K := charge A n; let L := Exterior.d 1 n; let P := field h he
  let S p := Face.send s (0:Site n) p
  let F (j) := P *ᵥ (Pi.single (address n j) (1:ℝ))
  have hu (a b) : dotProduct (reorient s a) (K*ᵥ(reorient s b))=dotProduct a (K*ᵥb) := by
    unfold K; rw [bespoke h v e]; exact Next.Free.apply_bill s r hr hj v n a b
  have hh (x : form 1 n) j : dotProduct x (K*ᵥ F j)=(L*ᵥ x) (address n j) := by
    have hx : K*P=L.transpose := hinge h he
    unfold F; rw [Matrix.mulVec_mulVec,hx,dotProduct_mulVec,vecMul_transpose]; simp
  have hd (a) (i : Face (Per n)) : (L*ᵥ reorient s a) (address n i)=turned s i.2 * (L*ᵥa) (address n (S i)) := rotations_d a s i.1 i.2
  have hx x : dotProduct x (K *ᵥ F q)=dotProduct x (K *ᵥ (turned s q.2 • reorient s (F (S q)))) := by
    obtain ⟨x,rfl⟩ := facing s x; rw [Matrix.mulVec_smul, dotProduct_smul, hu,hh,hh,hd]; rfl
  have hK : K*ᵥ F q=K*ᵥ (turned s q.2 • reorient s (F (S q))) := by
    ext b; specialize hx (Pi.single b (1:ℝ)); simpa using hx
  have hE : L*ᵥ F q = L*ᵥ (turned s q.2 • reorient s (F (S q))) := sub_eq_zero.mp
    ((Matrix.mulVec_sub L (F q) (turned s q.2 • reorient s (F (S q)))) ▸ ((nothing h he).mp (by rw [Matrix.mulVec_sub,hK,sub_self])))
  have hy u v : c u v=(L*ᵥF v) (address n u) := by
    change (L*P) _ _=_; unfold F; rw [Matrix.mulVec_mulVec]; simp
  rw [hy,hy i q,hE, Matrix.mulVec_smul, Pi.smul_apply,hd]; change _ = _*_ ; ring

variable (G) in
def funds : Copper G n where
  P i q := if i.2=q.2 then screenP h he (address n i.1) (address n q.1) else 0
  symm i q := by
    split <;> rename_i hq
    · rw [if_pos hq.symm]; exact congr_fun (congr_fun (balanced h he) _) _
    rw [if_neg (Ne.symm hq)]

lemma shadows (G : Gauge) (s : Signed) {r : ℝ} (hr : 0<r) (hj : 4≤j) (v : Train j) (l : ℝ) (e : Defined r l v A) :
    Compass.CopperMotion (funds G h he) s := by
  intro i q; rw [hue,hue]; dsimp only [funds,Compass.shine]; split_ifs
  · exact score h he s hr hj v l e i.1 q.1
  ring

section through
open Push.Corrected Dollars Compass Extraction
variable {C : Family G} {Y : Horizon C.path.levels} {d : ℕ} {Z : MapPrices}
open scoped Classical in
def bank (B : Series C) (h : Y.Suffices Z) : Ranks B where
  cov k N _p := if H : B.depth k ≤ N then
      funds G (h.all N _ H _) (Z.eta_pos _)
    else ⟨fun _ _=>0,fun _ _=>rfl⟩


structure Enables (B : Series C) (f : Extraction.Order) (d : ℕ) (Z : MapPrices) : Prop where
  society : ∀ᶠ k in atTop, f.late fun N p => Tribe C d (B.depth k) N p ∧ TrueStar C d (B.depth k) N p
  stage (y : ℝ) (hy : 0<y) : ∀ᶠ k in atTop, (C.path.levels.params (B.depth k)).columns ≤ (badge C (B.depth k))^y
  coin (y : ℝ) (hy : 0<y) : ∀ᶠ k in atTop, (Z.η (C.path.levels.clock.J (B.depth k)))⁻¹ ≤ (badge C (B.depth k))^y

-- suffices with the upper control specified before the `k` choices.
-- Present on every N with the ACTUAL trajectory (same through n).

end through
end YM.Further.CorrectedLift.FacePrice

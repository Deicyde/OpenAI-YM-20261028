import YM.Push.FREE_RESOLVENT.BlockRate
import YM.Push.FREE_RESOLVENT.SingleTag

/-!
# Budget interpolated full precision (discrete tags)
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Lever
open Lattice RG Precision Tree Matrix Mark TestD Bundle Filter Function Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {ι κ μ X E τ : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {v : τ → E} {A B : E → Matrix ι ι ℝ} {a : ι → X} {p : τ → X}
variable {D : Cost X} {o : X} {t r σ d M N γ : ℝ} {x : E} {k : ℕ}

-- include optional location mark about the endpoint o
abbrev park (D : Cost X) (p : τ → X) (d : ℝ) (o : X) := positions D (fun i : Option τ => i.elim o p) d

def mixture (A B : E → Matrix ι ι ℝ) := fun y => castLift A y + stir (B-A) y

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma gap_mixture (h : Gap (A x) r) (h' : Gap (B x) r) (he : 0 ≤ t) (ht : t ≤ 1) :
    Gap (mixture A B (x,t)) r := by
  constructor; intro v
  simp only [mixture, castLift, stir, Matrix.add_mulVec, Pi.sub_apply, Matrix.smul_mulVec,
    Matrix.sub_mulVec, dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]
  linarith only [mul_le_mul_of_nonneg_left (h.lower v) (sub_nonneg.mpr ht), mul_le_mul_of_nonneg_left (h'.lower v) he]

lemma parks (l : List τ) (D : Cost X) (p : τ → X) (d : ℝ) (o x) :
    (park D p d o).pay (l.map some) x=(positions D p d).pay l x := by
  induction l with
  | nil => rfl
  | cons t l h => rw [List.map_cons, pay,pay,h]; rfl

lemma collects {l : List (Option τ)} {m : Matrix ι ι ℝ} (h : none ∉ l)
    (H : (positions D p d).Bill D a a (l.filterMap id) σ M m) : (park D p d o).Bill D a a l σ M m := by
  constructor <;> constructor <;> intro i <;>
    rw [show (park D p d o).pay l (a i)=(positions D p d).pay (l.filterMap id) (a i) from
      (congr_arg (fun l => (park D p d o).pay l (a i)) (noTag h)).symm.trans (parks ..)]
  · exact H.row.rows i
  exact H.col.rows i

/-- ν(perm) tag affects only indicated sites. -/
def Alert (a : ι → X) (o : X) (A : E → Matrix ι ι ℝ) (x : E) : Prop := ∀ i j, a i ≠ o → a j ≠ o →
    (fun y => A y i j)=ᶠ[𝓝 x] fun _ => 0

-- Can reserve l.length * d although polynomial interpolation uses only
-- one actual none derivative.
lemma charge (D : Cost X) (p : τ → X) (l : List (Option τ)) (x o y : X) (hd : 0 ≤ d) (hx : x=o ∨ y=o) :
    (park D p d o).pay l x ≤ D.weight (l.length*d) x y*(positions D p d).pay (l.filterMap id) x := by
  induction l with
  | nil => simp [pay]
  | cons b l h =>
    rw [pay]
    have hp : 1 ≤ D.weight d x y := by rw [← D.weight_zero x y]; exact D.weight_mono hd x y
    apply (mul_le_mul_of_nonneg_left h (Mark.pos ..).le).trans
    rw [List.length_cons,Nat.cast_add_one,add_mul,one_mul,Cost.weight_add]
    cases b with
    | none =>
      change D.weight d x o*_ ≤ D.weight _ _ _ * D.weight d x y * (positions D p d).pay (l.filterMap id) x
      rw [mul_right_comm (D.weight _ _ _) (D.weight d x y), mul_comm _ (D.weight d x y)]
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (D.weight_nn ..) (Mark.pay_pos ..).le)
      rcases hx with rfl|rfl
      · simpa using hp
      rfl
    | some b =>
      have ht : ((some b)::l).filterMap id=b::l.filterMap id := rfl
      rw [ht,pay]
      change D.weight d x (p b)*(D.weight _ _ _*_) ≤ _*_* (D.weight d x (p b)*_)
      apply le_trans _ (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (D.weight_nn _ _ _) hp) (mul_nonneg
        (D.weight_nn ..) (Mark.pay_pos ..).le))
      exact le_of_eq (by ring)

lemma Rates.up {l : List (Option τ)} {m : Matrix ι ι ℝ} (hb : (positions D p d).Rates D a a (l.filterMap id) σ M m)
    (hx : ∀ i j, m i j≠0 → a i=o ∨ a j=o) (hd : 0 ≤ d) (he : γ+l.length*d ≤ σ) :
    (park D p d o).Rates D a a l γ M m := by
  constructor; intro i
  apply le_trans _ (hb.rows i); rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum; intro j _; by_cases h : m i j=0
  · rw [h,abs_zero,mul_zero,mul_zero,mul_zero,mul_zero]
  apply le_trans (mul_le_mul_of_nonneg_right (charge D p l (a i) o (a j) hd (hx i j h))
    (mul_nonneg (D.weight_nn ..) (abs_nonneg (m i j))))
  let P := (positions D p d).pay (l.filterMap id) (a i)
  change D.weight _ _ _ * P * _ ≤ P*_
  rw [mul_comm (D.weight _ _ _) P, mul_assoc P, ← mul_assoc (D.weight _ _ _), ← D.weight_add]
  apply mul_le_mul_of_nonneg_left _ (Mark.pay_pos ..).le
  rw [add_comm _ γ]
  exact mul_le_mul_of_nonneg_right (D.weight_mono he ..) (abs_nonneg _)

lemma safety (hA : Bundle v (positions D p d) D a a A x k σ M) (hh : Alert a o A x) (hd : 0 ≤ d) (hm : γ+k*d ≤ σ)
    (ht : t ∈ Icc (0:ℝ) 1) (he : 0 ≤ M) : Bundle (guides v) (park D p d o) D a a (stir A) (x,t) k γ M := by
  classical
  constructor
  · exact contDiffAt_snd.smul (hA.smooth.comp (f:=Prod.fst) (x,t) contDiffAt_fst)
  intro l hl
  let w := l.filterMap id; have hw := hA.bound w ((filter_lengths l).trans hl)
  rw [blend v _ (smooth_of_le hA.smooth hl)]
  split <;> rename_i h
  · have hp := collects (o:=o) h hw
    refine (show Bill _ _ _ _ _ _ (|t| * M) _ from ⟨rated _ hp.row,rated _ hp.col⟩).mono ?_ ?_
    · exact le_trans (le_add_of_nonneg_right (by positivity)) hm
    rw [abs_of_nonneg ht.1]; exact mul_le_of_le_one_left he ht.2
  split; · exact Bill.zero he
  have hL (i j) : jet v A w x i j ≠ 0 → a i=o ∨ a j=o := by
    intro H; by_contra! he
    have hp := hh i j he.1 he.2
    apply H; rw [← TestD.entry v w (smooth_of_le hA.smooth ((filter_lengths l).trans hl)), identical _ hp w]
    exact Affine.zero_null ..
  have hK : γ+l.length*d ≤ σ := le_trans (add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hd) _) hm
  exact ⟨Rates.up hw.row hL hd hK,Rates.up hw.col (fun i j h => (hL j i h).symm) hd hK⟩

lemma shield (H : Bundle v (positions D p d) D a a A x k σ M) (he : 0 ≤ M) :
    Bundle (guides v) (park D p d o) D a a (castLift A) (x,t) k σ M := by
  classical
  refine ⟨H.smooth.comp (f:=Prod.fst) (x,t) contDiffAt_fst,fun l hl => ?_⟩
  rw [casts _ _ _ (smooth_of_le H.smooth hl)]
  split; next h => exact collects h (H.bound _ ((filter_lengths l).trans hl))
  exact Bill.zero he

lemma Bundle.subtract (h : Bundle v (positions D p d) D a a A x k σ M) (h' : Bundle v (positions D p d) D a a B x k σ M) :
    Bundle v (positions D p d) D a a (A-B) x k σ (M+M) := by
  constructor
  · exact h.smooth.sub h'.smooth
  intro l hl
  rw [show jet v (A-B) l x=jet v A l x-jet v B l x from jet_sub _ _ (smooth_of_le h.smooth hl) (smooth_of_le h'.smooth hl)]
  exact (h.bound l hl).sub (h'.bound l hl)

lemma buoy (h : Bundle v (positions D p d) D a a A x k σ M) (h' : Bundle v (positions D p d) D a a B x k σ M) (hm : 0 ≤ M)
    (hy : Alert a o (B-A) x) (hd : 0 ≤ d) (hg : γ+k*d ≤ σ) (ht : t ∈ Icc (0:ℝ) 1) :
    Bundle (guides v) (park D p d o) D a a (mixture A B) (x,t) k γ (M+(M+M)) :=
  ((shield h hm).mono (le_trans (le_add_of_nonneg_right (by positivity)) hg) le_rfl).one_add
    (safety (Bundle.subtract h' h) hy hd hg ht (add_nonneg hm hm))
end YM.FreeResolvent.Lever

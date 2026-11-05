import YM.Progress.STATIONARY_SCENES.Green
import YM.Push.ABSOLUTE_SUMS.Basic


/-!
# Windows and volume uniform bills (real finite torus)

For the operated affine rows after cutting according to `Stores.till`.
Cost constants (Schur) allowed after-L. Utilities for weighted accounting
on all the physical indices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Win
open Matrix Progress.StationaryScenes Finset Lattice Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {c : Side}

open Green

section arrows
variable {n m p : Type*} [Fintype n] [Fintype m] [Fintype p] {η ν C D P Q : ℝ}
variable {a : n → Site c} {b : m → Site c} {e : p → Site c} {A B : Matrix n m ℝ}

lemma both_transpose (hx : Both a b A η C D) : Both b a A.transpose η D C := ⟨hx.2,hx.1⟩

lemma timesBoth {F : Matrix m p ℝ} (hη : 0 ≤ η) (h : Both a b A η C D) (hk : Both b e F η P Q)
    (hP : 0≤P) (hD : 0 ≤ D) : Both a e (A*F) η (C*P) (D*Q) := by
  unfold Both; rw [Matrix.transpose_mul, mul_comm D Q]
  exact ⟨h.1.multiply hη hk.1 hP,hk.2.multiply hη h.2 hD⟩

omit [Fintype n] in
lemma row_entry (hx : Rows a b A η C) (i : n) (j : m) : wt η (a i) (b j) * |A i j| ≤ C :=
  (single_le_sum (fun j (_ : j∈univ) => mul_nonneg (wt_pos η (a i) (b j)).le (abs_nonneg (A i j)))
    (mem_univ j)).trans (hx i)

omit [Fintype n] in
lemma mono (hx : Rows a b A η C) (hy : ν ≤ η) (ho : C ≤ D) : Rows a b A ν D := by
  intro i
  refine (le_trans ?_ (hx i)).trans ho
  exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (Real.exp_monotone
    (mul_le_mul_of_nonneg_right hy (by positivity))) (abs_nonneg _)

lemma monoBoth (hx : Both a b A η C P) (hy : ν ≤ η) (ho : C ≤ D) (hl : P ≤ Q) : Both a b A ν D Q :=
  ⟨mono hx.1 hy ho,mono hx.2 hy hl⟩

lemma plusBoth (hx : Both a b A η C P) (hy : Both a b B η D Q) : Both a b (A+B) η (C+D) (P+Q) :=
  ⟨hx.1.plus hy.1, by rw [Matrix.transpose_add]; exact hx.2.plus hy.2⟩

lemma negBoth (hx : Both a b A η C P) : Both a b (-A) η C P := by
  have hf := hx.1; have hg := hx.2
  unfold Both Rows; simp only [Matrix.transpose_neg, Matrix.neg_apply,abs_neg]; exact ⟨hf,hg⟩

lemma smulBoth (hx : Both a b A η C D) (r : ℝ) : Both a b (r • A) η (|r| *C) (|r| *D) :=
  ⟨hx.1.pay r, by rw [Matrix.transpose_smul]; exact hx.2.pay r⟩

lemma identities [DecidableEq n] (a : n → Site c) (η : ℝ) : Both a a (1 : Matrix n n ℝ) η 1 1 := by
  have hf : Rows a a (1 : Matrix n n ℝ) η 1 := by
    intro i; simp [Matrix.one_apply,wt, apply_ite (abs : ℝ → ℝ)]
  exact ⟨hf,by rw [Matrix.transpose_one]; exact hf⟩

/-! Pointwise → Rows. `P` INCLUDES color count. -/

def governs (b : m → Site c) (P : ℝ) := ∀ (Y : Site c) (D : ℕ),
  ((Finset.univ.filter fun j : m => separation Y (b j) ≤ D).card:ℝ) ≤ P*(1+(D:ℝ))^4

/-- Neighbor bill (include $\Pi$ and $\Pi^\star$ and chains; not inverting
on `\ell^∞`). -/
def planePrice (P η : ℝ) :=
    P*((η/2)⁻¹^4*(4:ℕ).factorial*Real.exp (η/2))*(1-Real.exp (-(η/2)))⁻¹

lemma planePrice_nn (hp : 0≤P) (hη : 0<η) : 0 ≤ planePrice P η := by
  have h : 0 < 1-Real.exp (-(η/2)) := by
    rw [sub_pos]; exact Real.exp_lt_one_iff.mpr (by linarith)
  unfold planePrice; positivity

omit [Fintype n] in
lemma governs_pay (hg : governs b P) (hp : 0≤P) (hη : 0<η) (v : Site c) :
    ∑ i, wt (-η) v (b i) ≤ planePrice P η := by
  let t := η/2
  have hh : 0<t := by unfold t; positivity
  let H := t⁻¹^4*(4:ℕ).factorial*Real.exp t
  have hm : 0 ≤ P*H := by unfold H; positivity
  let d i := separation v (b i)
  refine budget_sum (budget_degrees d (fun i => (wt_pos ..).le) hm
    (Real.exp_pos (-t)).le (Real.exp_lt_one_iff.mpr (by linarith)) ?_) Finset.univ
  intro k s hs
  let w := Real.exp (-η*k)
  have hw : (s.card:ℝ) ≤ P*(1+(k:ℝ))^4 := by
    apply le_trans _ (hg v k)
    norm_cast
    exact Finset.card_le_card (fun x hx => Finset.mem_filter.mpr ⟨mem_univ x,(hs x hx).le⟩)
  calc
    _ = (s.card:ℝ)*w := by
      rw [sum_congr rfl (show ∀ i∈s, wt (-η) v (b i) = w from
        fun i hi => congr_arg _ (show -η*d i=-η*(k:ℝ) by rw [hs i hi]))]; simp
    _ ≤ (P*(1+(k:ℝ))^4)*w := mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
    _ ≤ (P * (H*Real.exp (t*k))) * w := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (polynomial_cost hh (by positivity) _) hp) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_nat_mul]; unfold w; rw [← mul_assoc P, mul_assoc (P*H), ← Real.exp_add]; unfold t; ring_nf

omit [Fintype n] in
lemma point_rows (hg : governs b P) (hp : 0≤P) (he : ν < η) (hC : 0≤C)
    (hx : ∀ i j, wt η (a i) (b j) * |A i j| ≤ C) : Rows a b A ν (planePrice P (η-ν)*C) := by
  have hp' := governs_pay hg hp (sub_pos.mpr he)
  intro i
  apply le_trans _ (mul_le_mul_of_nonneg_right (hp' (a i)) hC); rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  apply le_trans _ (mul_le_mul_of_nonneg_left (hx i j) (wt_pos ..).le)
  rw [← mul_assoc]
  exact le_of_eq (by unfold wt; rw [← Real.exp_add]; ring_nf)

lemma point_both (hg : governs b Q) (hh : governs a P) (hp : 0≤P) (hq : 0≤Q) (he : ν < η) (hC : 0≤C)
    (hx : ∀ i j, wt η (a i) (b j) * |A i j| ≤ C) :
    Both a b A ν (planePrice Q (η-ν)*C) (planePrice P (η-ν)*C) := by
  refine ⟨point_rows hg hq he hC hx, point_rows hh hp he hC fun i j => ?_⟩
  rw [wt_symm]; exact hx j i

/-- Spend a sliver of width to cover paths traveling AT LEAST `R`
(this is where the window size buys something). -/
lemma reduce_far (h : Both a b A η C D) (he : ν ≤ η) (R : ℕ)
    (hr : ∀ i j, A i j≠0 → R ≤ separation (a i) (b j)) :
    Both a b A ν (Real.exp (-(η-ν)*R)*C) (Real.exp (-(η-ν)*R)*D) := by
  let w := Real.exp (-(η-ν)*R)
  have hh i j : wt ν (a i) (b j)*|A i j| ≤ w * (wt η (a i) (b j)*|A i j|) := by
    by_cases H : A i j=0
    · simp [H]
    rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    unfold w wt; rw [← Real.exp_add]
    have hf := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hr i j H)) (sub_nonneg.mpr he)
    apply Real.exp_monotone; linarith
  constructor
  · intro i
    apply le_trans _ (mul_le_mul_of_nonneg_left (h.1 i) (show 0 ≤ w from (Real.exp_pos _).le))
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun j _ => hh i j
  intro j
  apply le_trans _ (mul_le_mul_of_nonneg_left (h.2 j) (show 0 ≤ w from (Real.exp_pos _).le))
  rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _ => ?_
  simpa only [wt_symm ν (a i),wt_symm η (a i),Matrix.transpose_apply] using hh i j
end arrows

section upper
variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    {a : n → Site c} {η r u : ℝ}

omit [DecidableEq n] in
lemma to_schur (hx : Both a a A η u u) (hη : 0 ≤ η) (z : n → ℝ) :
    |dotProduct z (A *ᵥ z)| ≤ u*dotProduct z z := by
  have he := monoBoth hx hη le_rfl le_rfl
  apply Green.schur
  · simpa only [Rows,wt,zero_mul,Real.exp_zero,one_mul] using he.1
  simpa only [Rows,wt,zero_mul,Real.exp_zero,one_mul,Matrix.transpose_apply] using he.2

-- inverse of Hermitian with upper bound. Elementary variational proof so
-- no metric conversion costs.
lemma inverse_floor (hx : Both a a A η u u) (hu : 0<u) (hη : 0 ≤ η) (hh : A.PosDef) :
    Bottom A⁻¹ u⁻¹ := by
  have hf : A.transpose=A := hh.isHermitian
  intro z
  let G := A⁻¹
  let v := G *ᵥ z
  let b : ℝ := u⁻¹
  have he : A *ᵥ v = z := by
    unfold v G; rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hh.det_pos.ne'),
      Matrix.one_mulVec]
  have ht : dotProduct v (A *ᵥ z) = dotProduct z z := by
    have h := Matrix.dotProduct_transpose_mulVec A v z; rw [hf,he] at h; exact h
  have hm := hh.posSemidef.dotProduct_mulVec_nonneg (v-b • z)
  rw [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul, he, dotProduct_sub,sub_dotProduct,sub_dotProduct,
    dotProduct_smul,dotProduct_smul,smul_dotProduct,smul_dotProduct,smul_eq_mul,smul_eq_mul,smul_eq_mul,
    smul_eq_mul,ht] at hm
  have hk := mul_le_mul_of_nonneg_left ((abs_le.mp (to_schur hx hη z)).2) (sq_nonneg b)
  have hl : b^2*u=b := by unfold b; field_simp
  change b*dotProduct z z ≤ dotProduct z v
  rw [dotProduct_comm z v]
  rw [← mul_assoc, hl] at hk; linarith
end upper
end YM.AnalyticNext.ConnectedActivity.Win

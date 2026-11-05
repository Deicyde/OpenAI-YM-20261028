import YM.CellFourier.Circulant

/-!
# The finite row correction

Entries on the true cover. Use DFT cancellation only at the end, to
transport the exact annihilation to wrapped cells of any side.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F06
open Lattice Laurent Bloch  Finset Matrix
open scoped BigOperators Topology

variable {α β γ : Type*}

lemma row_strip_add {R S : Row α β} {η A B : ℝ} (hr : R.strip η A) (hs : S.strip η B) :
    Row.strip (R + S) η (A+B) := by
  intro i j
  let w := fun (T : Row α β) (x : Cover) => Real.exp (η * size x) * ‖T i j x‖
  have hw (x) : w (R+S) x ≤ w R x + w S x := by
    unfold w; simp only [Pi.add_apply]; rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le ..) (Real.exp_pos _).le
  have hu : Summable (w R) := (hr i j).2.1
  have hv : Summable (w S) := (hs i j).2.1
  have hn x : 0 ≤ w (R+S) x := by unfold w; positivity
  have h := (hu.add hv).of_nonneg_of_le hn hw
  refine ⟨hn, h, (h.tsum_le_tsum hw (hu.add hv)).trans ?_⟩
  rw [hu.tsum_add hv]; exact add_le_add (hr i j).2.2 (hs i j).2.2

lemma row_read_add {R S : Row α β} {η A B : ℝ} (hr : R.strip η A) (hs : S.strip η B)
    (p : Momentum) (hp : Within η p) : Row.read (R+S) p = R.read p + S.read p := by
  ext i j
  simp only [Row.read, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, Laurent.read,
    Complex.ofReal_add, smul_add]
  exact ((Width.series (Row.constant_strip R hr i j) p hp).2.1.of_norm).tsum_add
    ((Width.series (Row.constant_strip S hs i j) p hp).2.1.of_norm)

lemma read_fin (s : Finset Cover) (R : Row α β) (h : ∀ i j x, x ∉ s → R i j x = 0)
    (p : Momentum) (i : α) (j : β) :
    R.read p i j = ∑ x∈s, mode p x * (R i j x:ℂ) := by
  change (∑' x, mode p x * (R i j x:ℂ)) = _
  apply tsum_eq_sum; intro x hx; simp [h i j x hx]

def diffBox (s : Finset Cover) := (s.product s).image fun x => x.2 - x.1

lemma diffBox_mem (s : Finset Cover) {a b : Cover} (ha : a ∈ s) (hb : b ∈ s) : b-a ∈ diffBox s :=
  Finset.mem_image.mpr ⟨(a,b), mem_product.mpr ⟨ha,hb⟩, rfl⟩

variable [Fintype α]

/-- Adjoint offsets come with a minus sign. -/
def gramRow (r : ℝ) (s : Finset Cover) (R : Row α β) : Row β β := fun i j x =>
  ∑ k, ∑ a∈s, ∑ b∈s, if x=b-a then r * R k i a * R k j b else 0

lemma gramRow_extinct (r : ℝ) (s : Finset Cover) (R : Row α β) (i j x) (h : x ∉ diffBox s) :
    gramRow r s R i j x = 0 := by
  apply Finset.sum_eq_zero
  intro k _; apply Finset.sum_eq_zero
  intro a ha; apply Finset.sum_eq_zero
  intro b hb
  have hne : x ≠ b - a := by
    intro he; apply h; rw [he]; exact diffBox_mem s ha hb
  exact if_neg hne

lemma gramRow_eval (r : ℝ) (s : Finset Cover) (R : Row α β) (p : Momentum) (i j : β) :
    (gramRow r s R).read p i j =
      ∑ k, ∑ a∈s, ∑ b∈s, mode p (b-a) * (r * R k i a * R k j b : ℝ) := by
  rw [read_fin _ _ (gramRow_extinct r s R)]
  simp only [gramRow, Complex.ofReal_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [apply_ite ((↑):ℝ → ℂ), Complex.ofReal_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
    if_pos (diffBox_mem s ha hb)]

lemma gramRow_read (r : ℝ) (s : Finset Cover) (R : Row α β) (h : ∀ i j x, x ∉ s → R i j x = 0)
    (p : Momentum) (hp : star p = p) :
    (gramRow r s R).read p = (r:ℂ) • ((R.read p).conjTranspose * R.read p) := by
  ext i j
  rw [gramRow_eval, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.conjTranspose_apply, read_fin s R h p, star_sum, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [star_mul, show star (mode p a) = mode p (-a) by rw [← mode_adjoint, hp],
    sub_eq_add_neg, mode_shift]
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]; ring

variable [Fintype β]

lemma strip_of_fin (s : Finset Cover) (R : Row α β) (h : ∀ i j x, x ∉ s → R i j x = 0)
    (η : ℝ) : ∃ A : ℝ, 0 ≤ A ∧ R.strip η A := by
  let w := fun (i : α) (j : β) (x : Cover) => Real.exp (η * size x) * ‖R i j x‖
  have hn i j x : 0 ≤ w i j x := by unfold w; positivity
  let K := fun (i : α) (j : β) => ∑ x∈s, w i j x
  have hp i j : 0 ≤ K i j := Finset.sum_nonneg fun x _ => hn i j x
  have hp' i : 0 ≤ ∑ j, K i j := Finset.sum_nonneg fun j _ => hp i j
  refine ⟨∑ i, ∑ j, K i j, Finset.sum_nonneg (fun i _ => hp' i), ?_⟩
  intro i j
  have hs (x) (hx : x ∉ s) : w i j x = 0 := by simp [w, h i j x hx]
  refine ⟨hn i j, summable_of_ne_finset_zero (s:=s) (fun x hx => hs x hx), ?_⟩
  change (∑' x, w i j x) ≤ ∑ i', ∑ j', K i' j'
  rw [tsum_eq_sum hs]
  exact (Finset.single_le_sum (fun j' _ => hp i j') (mem_univ j)).trans
    (Finset.single_le_sum (fun i' _ => hp' i') (mem_univ i))

omit [Fintype α] in
lemma fiber_product (n : Side) (A : Site n → Matrix α β ℂ) (B : Site n → Matrix β γ ℂ) :
    fiber A * fiber B = fiber (fun p => A p * B p) := by
  ext ⟨x,i⟩ ⟨y,j⟩
  by_cases he : x=y
  · subst y; simp [Matrix.mul_apply,Fintype.sum_prod_type,fiber,ite_mul,mul_ite]
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [fiber, of_apply, if_neg he]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun k _ => ?_
  split_ifs <;> simp_all

/-- From a *right*-annihilation of symbols to equality at every finite period.
Uses absolute summability, so even if the side is one and many shifts wrap
together the period identity is unchanged. -/
lemma acts_coincide [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (R S : Row α β) (D : Row β γ) (hr : R.safe) (hs : S.safe) (hd : D.safe)
    (H : ∀ p : Momentum, star p = p → R.read p * D.read p = S.read p * D.read p) (n : Side) :
    R.acts n * D.acts n = S.acts n * D.acts n := by
  apply Bloch.prom_inj
  apply cancel_rotation n
  have h (P : Row α β) (hp : P.safe) :
      approached (P.acts n * D.acts n) * rotations n γ =
        rotations n α * fiber (fun p : Site n => P.read (mon p) * D.read (mon p)) := by
    rw [prom_mul, Matrix.mul_assoc, circulant n D hd, ← Matrix.mul_assoc,
      circulant n P hp, Matrix.mul_assoc, fiber_product]
  rw [h R hr, h S hs]; simp_rw [H _ (real_frequency _)]

end YM.Work.F06

import YM.Next.BOUNDARY.Coordinates
import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2
import YM.Next.FREE_KERNELS.Signal
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Post

/-!
# Spending on the flat active Hessian: uniform finite inverse bound

Elementary weighted argument, keep counting despite FiniteDimensional involved in
existence lemmas. Bounds even principal restrictions and the resolvent for ANY
nonnegative shift. Consumer on our actual scenes in `SliceGap.lean`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.StationaryScenes.Green

open Filter Lattice RG Wilson Precision Bid Function Matrix
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {f : Side} {ι σ χ : Type*} [Fintype ι] [Fintype σ] [Fintype χ]

def wt (η : ℝ) (x y : Site f) := Real.exp (η*separation x y)

def Rows (a : ι → Site f) (b : σ → Site f) (A : Matrix ι σ ℝ) (η C : ℝ) :=
  ∀ i, ∑ j : σ, wt η (a i) (b j) * |A i j| ≤ C

def Both (a : ι → Site f) (b : σ → Site f) (A : Matrix ι σ ℝ) (η C D : ℝ) :=
  Rows a b A η C ∧ Rows b a A.transpose η D

def Bottom (A : Matrix ι ι ℝ) (c : ℝ) :=
  ∀ v, c*dotProduct v v ≤ dotProduct v (A *ᵥ v)

lemma wt_pos (η : ℝ) (x y : Site f) : 0 < wt η x y := Real.exp_pos _
lemma wt_symm (η : ℝ) (x y : Site f) : wt η x y = wt η y x := by unfold wt; rw [separation_comm]
lemma wt_triangle {η : ℝ} (h : 0 ≤ η) (x y z : Site f) :
    wt η x z ≤ wt η x y*wt η y z := by
  unfold wt; rw [← Real.exp_add,← mul_add]; apply Real.exp_monotone
  apply mul_le_mul_of_nonneg_left _ h; exact_mod_cast separation_triangle x y z

variable {a : ι → Site f} {b : σ → Site f} {d : χ → Site f} {A A' : Matrix ι σ ℝ} {B : Matrix σ χ ℝ}
  {η C D : ℝ}

omit [Fintype ι] in
lemma Rows.multiply (hη : 0 ≤ η) (h : Rows a b A η C) (hk : Rows b d B η D) (hD : 0 ≤ D) :
    Rows a d (A*B) η (C*D) := by
  intro x
  let v (i : σ) := wt η (a x) (b i) * |A x i|
  calc
    _ ≤ ∑ j : χ, ∑ i : σ, v i*(wt η (b i) (d j)* |B i j|) := by
      refine Finset.sum_le_sum fun j _ => ?_; rw [Matrix.mul_apply]
      apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) (wt_pos ..).le).trans
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      apply (mul_le_mul_of_nonneg_right (wt_triangle hη (a x) (b i) (d j)) (by positivity)).trans
      unfold v; exact le_of_eq (by ring)
    _ = ∑ i, v i*∑ j, wt η (b i) (d j)*|B i j| := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ ≤ ∑ i, v i*D := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact mul_le_mul_of_nonneg_left (hk _) (mul_nonneg (wt_pos ..).le (abs_nonneg _))
    _ ≤ C*D := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (h _) hD

omit [Fintype ι] in
lemma Rows.plus (h : Rows a b A η C) (g : Rows a b A' η D) : Rows a b (A+A') η (C+D) := by
  intro i
  apply le_trans _ (add_le_add (h i) (g i))
  rw [← Finset.sum_add_distrib]; refine Finset.sum_le_sum fun j _ => ?_
  rw [← mul_add]; exact mul_le_mul_of_nonneg_left (abs_add_le ..) (wt_pos ..).le

omit [Fintype ι] in
lemma Rows.pay (h : Rows a b A η C) (u : ℝ) : Rows a b (u • A) η (|u| *C) := by
  intro x; apply le_trans _ (mul_le_mul_of_nonneg_left (h x) (abs_nonneg u)); rw [Finset.mul_sum]
  exact (Finset.sum_congr rfl fun i _ => by
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul]; ring).le

omit [Fintype ι] in
lemma Rows.restrict {κ τ : Type*} [Fintype κ] [Fintype τ] (h : Rows a b A η C)
    (i : κ → ι) (j : τ ↪ σ) : Rows (a ∘ i) (b ∘ j) (A.submatrix i j) η C := by
  classical
  intro x
  apply le_trans _ (h (i x))
  let L m := wt η (a (i x)) (b m)* |A (i x) m|
  have hu : ∀ m, 0 ≤ L m := fun m => mul_nonneg (wt_pos ..).le (abs_nonneg _)
  calc
    _ = ∑ m ∈ (Finset.univ.map j), L m := (Finset.sum_map ..).symm
    _ ≤ ∑ m : σ, L m := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hu _

section ij
variable {M P : Matrix ι ι ℝ} {r : ℝ}

lemma Bottom.restrict (h : Bottom M r) (j : σ ↪ ι) : Bottom (M.submatrix j j) r := by
  classical
  intro v
  let w i := if hi : ∃ m, j m=i then v (Classical.choose hi) else 0
  have he (i : σ) : w (j i)= v i := by
    have hh : ∃ m, j m=j i := ⟨i,rfl⟩
    unfold w; rw [dif_pos hh, j.injective (Classical.choose_spec hh)]
  have hs (F : ι → ℝ) : dotProduct w F = dotProduct v (F ∘ j) := by
    unfold dotProduct
    calc
      _ = ∑ i ∈ Finset.univ.map j, w i * F i := by
        symm; refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
        have hb : ¬ ∃ m, j m=i := fun ⟨m,hm⟩ => hi (Finset.mem_map.mpr ⟨m,Finset.mem_univ m,hm⟩)
        dsimp [w]; rw [dif_neg hb,zero_mul]
      _ = _ := by rw [Finset.sum_map]; simp_rw [he]; rfl
  have hh := h w
  rw [hs,show w ∘ j=v from funext he, hs] at hh
  apply hh.trans_eq
  congr 1; funext i
  change dotProduct (M (j i)) w=_
  rw [dotProduct_comm,hs,dotProduct_comm]; rfl

private lemma squares (v : ι → ℝ) (i : ι) : |v i|^2 ≤ dotProduct v v := by
  rw [sq_abs, pow_two]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ _)

private lemma dip {D u θ : ℝ} (h : 0 ≤ θ) (he : θ ≤ 1) (hu : -θ*D ≤ u) (hv : u ≤ θ*D) :
    |Real.exp u - 1| ≤ θ*Real.exp D := by
  have hx := convexOn_exp.2 (x:=D) (y:=0) (Set.mem_univ _) (Set.mem_univ _) h (show 0 ≤ 1-θ by linarith)
    (show θ+(1-θ)=1 by ring)
  simp only [smul_eq_mul,mul_zero,add_zero,Real.exp_zero,mul_one] at hx
  have ha := Real.exp_monotone hv
  have hb := Real.exp_monotone (show -u ≤ θ*D by linarith)
  have hp := Real.exp_pos u
  have hz : 1 - Real.exp u ≤ Real.exp (-u) - 1 := by
    rw [Real.exp_neg]
    have he := mul_inv_cancel₀ hp.ne'
    by_contra! hn
    nlinarith only [he,mul_lt_mul_of_pos_right hn hp,sq_nonneg (Real.exp u-1)]
  apply abs_le.mpr; constructor <;> linarith

/-- A sufficient Combes-style fractional diminution. -/
theorem diminishing {θ : ℝ} (hη : 0 ≤ η) (hθ : 0 ≤ θ) (hw : θ ≤ 1) (i j z : Site f) :
    |wt (θ*η) i z / wt (θ*η) j z - 1| ≤ θ*wt η i j := by
  unfold wt; rw [← Real.exp_sub]
  have ha : (separation i z:ℝ) ≤ (separation i j:ℝ)+(separation j z:ℝ) := by exact_mod_cast separation_triangle i j z
  have hb : (separation j z:ℝ) ≤ (separation i j:ℝ)+(separation i z:ℝ) := by
    rw [separation_comm i j]; exact_mod_cast separation_triangle j i z
  have h := mul_nonneg hθ hη
  apply dip hθ hw
  · have hp := mul_le_mul_of_nonneg_left hb h
    calc
      _ = -(θ*η*(separation i j:ℝ)) := by ring
      _ ≤ _ := by rw [mul_add] at hp; linarith
  have hp := mul_le_mul_of_nonneg_left ha h; rw [mul_add] at hp; linarith

lemma schur (F : Matrix ι ι ℝ) (w : ι → ℝ) (d : ℝ) (hx : ∀ i, ∑ j, |F i j| ≤ d)
    (hy : ∀ j, ∑ i, |F i j| ≤ d) : |dotProduct w (F *ᵥ w)| ≤ d*dotProduct w w := by
  have hX : ∑ i, ∑ j, |F i j| *(w i*w i) ≤ d*dotProduct w w := by
    simp_rw [← Finset.sum_mul,dotProduct,Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx i) (mul_self_nonneg _)
  have hY : ∑ i, ∑ j, |F i j| *(w j*w j) ≤ d*dotProduct w w := by
    rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul,dotProduct,Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hy i) (mul_self_nonneg _)
  have hz : |dotProduct w (F *ᵥ w)| ≤ ∑ i, ∑ j, |w i*(F i j*w j)| := by
    unfold dotProduct mulVec; simp_rw [dotProduct,Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs ..).trans
    exact Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs ..
  apply hz.trans
  apply le_of_mul_le_mul_left _ (show (0:ℝ)<2 by norm_num)
  apply le_trans _ ((add_le_add hX hY).trans_eq (two_mul _).symm)
  rw [← Finset.sum_add_distrib, Finset.mul_sum]; refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]; refine Finset.sum_le_sum fun j _ => ?_
  have he : 2*(|w i| *|w j|) ≤ w i*w i+w j*w j := by nlinarith only [sq_abs (w i),sq_abs (w j),sq_nonneg (|w i|-|w j|)]
  simp only [abs_mul]
  nlinarith only [mul_le_mul_of_nonneg_left he (abs_nonneg (F i j))]

private lemma one_entry (v : ι → ℝ) (i j : ι) (c : ℝ) (hc : 0 < c) (h : c*dotProduct v v ≤ v j) :
    |v i| ≤ c⁻¹ := by
  apply le_of_mul_le_mul_left _ hc
  have ha := mul_le_mul_of_nonneg_left (squares v i) hc.le
  have hb := mul_le_mul_of_nonneg_left (squares v j) hc.le
  rw [mul_inv_cancel₀ hc.ne']
  by_contra! H
  have he : 1 < c*|v j| := by nlinarith [le_abs_self (v j)]
  nlinarith only [he, hb,h, le_abs_self (v j),abs_nonneg (v j),
    mul_pos hc (show 0 < |v j| by by_contra! HN; nlinarith),
    mul_lt_mul_of_pos_left he (show 0 < |v j| by by_contra! HN; nlinarith)]

variable [DecidableEq ι]

/-- The actual two-sided inverse and pointwise exponential bound. E.g. take θ and r
both post. Principal extension via
restrict before calling. Includes empty coordinates, one-site case, and the
spectral parameter uniform $(k(1+u))^{-1}$. -/
theorem inverse {θ : ℝ} (hη : 0 ≤ η) (hr : 0 < r) (hθ : 0 ≤ θ) (hw : θ ≤ 1)
    (hh : θ*C ≤ r/2) (hM : IsHermitian M) (hg : Bottom M r)
    (h : Both a a M η C C) (u : ℝ) (hu : 0 ≤ u) :
    let A := M + u • (1 : Matrix ι ι ℝ)
    let c := min 1 (r/2)
    A*A⁻¹=1 ∧ A⁻¹*A=1 ∧
      ∀ i j : ι, wt (θ*η) (a i) (a j)*|(A⁻¹) i j| ≤ (c*(1+u))⁻¹ := by
  intro A c
  have hp : Bottom A (r+u) := by
    intro v
    unfold A; rw [Matrix.add_mulVec, dotProduct_add,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,add_mul]; exact add_le_add_left (hg v) _
  have hs : A.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · exact hM.add (show IsHermitian (u • (1 : Matrix ι ι ℝ)) by rw [Matrix.IsHermitian, conjTranspose_smul]; simp)
    intro v hv; rw [star_trivial]; apply lt_of_lt_of_le _ (hp v)
    obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by simpa only [Ne,funext_iff,Pi.zero_apply,not_forall] using hv
    exact mul_pos (by positivity) ((pow_pos (abs_pos.mpr hi) 2).trans_le (squares v i))
  have hd := hs.det_pos
  have hA := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hd.ne')
  refine ⟨hA, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hd.ne'), fun i j => ?_⟩
  let y (l : ι) := (A⁻¹) l j
  let s (l : ι) := wt (θ*η) (a l) (a j)
  let w (l : ι) := s l*y l
  let F : Matrix ι ι ℝ := Matrix.of fun k l => A k l*(s k/s l-1)
  have hf (k l : ι) : |F k l| ≤ θ*(wt η (a k) (a l)*|M k l|) := by
    have hy := diminishing hη hθ hw (a k) (a l) (a j)
    have hs k : 0 < s k := wt_pos ..
    by_cases H : k=l
    · subst k
      unfold F; rw [of_apply, div_self (hs _).ne', sub_self, mul_zero,abs_zero]
      exact mul_nonneg hθ (mul_nonneg (wt_pos ..).le (abs_nonneg _))
    unfold F; rw [of_apply,abs_mul]
    rw [show A k l=M k l by simp [H,A]]
    apply (mul_le_mul_of_nonneg_left hy (abs_nonneg _)).trans_eq; ring
  have he : |dotProduct w (F *ᵥ w)| ≤ r/2 * dotProduct w w := by
    refine schur _ _ _ (fun k => ?_) fun k => ?_
    · apply ((Finset.sum_le_sum (fun l _ => hf k l)).trans _).trans hh
      rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (h.1 k) hθ
    apply ((Finset.sum_le_sum (fun l _ => hf l k)).trans _).trans hh
    simp_rw [wt_symm _ _ (a k)]; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (h.2 k) hθ
  have hi (l : ι) : ((A+F) *ᵥ w) l = if l=j then 1 else 0 := by
    calc
      _ = s l*((A*A⁻¹) l j) := by
        rw [mulVec,dotProduct, Matrix.mul_apply,Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.add_apply]; unfold F w y; rw [of_apply]
        have h : 0 < s k := wt_pos ..
        field_simp; ring
      _ = _ := by by_cases H : l=j <;> simp [hA,H,s,wt]
  have hv : dotProduct w ((A+F) *ᵥ w) = w j := by simp only [dotProduct,hi]; simp
  rw [Matrix.add_mulVec,dotProduct_add] at hv
  have hpp := hp w
  have hwt : 0 ≤ dotProduct w w := le_trans (sq_nonneg _) (squares w i)
  have hh' : c*(1+u)*dotProduct w w ≤ w j := by
    have hx : c*(1+u) ≤ r/2 + u := by
      rw [mul_add,mul_one]; exact add_le_add (min_le_right ..) (mul_le_of_le_one_left hu (min_le_left ..))
    have hv' := (abs_le.mp he).1
    nlinarith only [hv,hpp,hv',mul_le_mul_of_nonneg_right hx hwt]
  have hc : 0 < c*(1+u) := mul_pos (lt_min zero_lt_one (half_pos hr)) (by positivity)
  calc
    _ = |w i| := by
      change s i*|y i| = |s i*y i|
      rw [abs_mul,abs_of_pos (wt_pos _ _ _)]
    _ ≤ _ := one_entry w i j _ hc hh'
end ij
end YM.Progress.StationaryScenes.Green

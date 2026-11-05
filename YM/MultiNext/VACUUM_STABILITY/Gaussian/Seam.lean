import YM.MultiNext.VACUUM_STABILITY.Gaussian.Laplace

set_option warningAsError false

/-!
# Component independence when the representation really has the projected covariance

Use the *whole* joint conditional law. No condition that the particular matrix square root
shares that range cut. Gram checks after conditioning, every linear test. Product relative to
the actual vectors and labels on that conditional calculation. Includes possible dummy Z
slots and singular Gaussian (T pins gauge beforehand).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Gauss
open Filter Finset Function MeasureTheory ProbabilityTheory
open scoped Topology BigOperators Classical

variable {I J H K : Type} [Fintype I] [Fintype J] [Fintype H] [Fintype K]

private lemma mgf_char (w : Row I) : (∫ x, Complex.exp ((crossed w x:ℂ)*Complex.I) ∂standard I) =
    Complex.exp (-(squares w:ℂ)/2) := by
  unfold crossed; simp_rw [Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  unfold standard; rw [integral_fintype_prod_eq_prod (fun i x => Complex.exp (↑(w i * x) * Complex.I))]
  have h (t : ℝ) : (∫ x, Complex.exp (↑(t*x)*Complex.I) ∂gaussianReal 0 1)=Complex.exp (-(t:ℂ)^2/2) := by
    simp_rw [Complex.ofReal_mul, ← charFun_apply_real,charFun_gaussianReal]; simp [neg_div]
  simp_rw [h,←Complex.exp_sum,squares]; apply congrArg Complex.exp
  simp [Complex.ofReal_sum,neg_div,sum_div]

-- Each output cluster i sees a J-dimensional view (pad to common J already). Actual
-- global samples via H. Candidate individual via K independently (needn't have common K
-- with H, can pad K across clusters; can reindex to and from physical slot numbers).
variable (q : I → J → Row H) (p : I → J → Row K)

def blocksMatch := ∀ i j (a b : J), crossed (q i a) (q j b) = if i=j then crossed (p i a) (p i b) else 0

-- energy s(q^T x) vs sum s(p_i^T x). avoids CFC.
def lump (s : Finset I) (w : I → Row J) : Row H := fun j => ∑ i∈s, crossed (Function.swap (q i) j) (w i)

private lemma double_sum (w v : Row J) (q p : J → Row H) :
    crossed (mapRows (Function.swap q) w) (mapRows (Function.swap p) v) =
      ∑ i,w i * ∑ j,v j * crossed (q i) (p j) := by
  rw [← rewrite_row]; unfold mapRows crossed; refine sum_congr rfl ?_; intro i _
  congr 1; simp_rw [Finset.mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro j _
  apply sum_congr rfl; intro k _; unfold Function.swap; ring

omit [Fintype I] in
private lemma block_cross (h : blocksMatch q p) (i j : I) (w v : Row J) :
    crossed (mapRows (Function.swap (q i)) w) (mapRows (Function.swap (q j)) v) = if i=j then
      crossed (mapRows (Function.swap (p i)) w) (mapRows (Function.swap (p i)) v) else 0 := by
  unfold blocksMatch at h; rw [double_sum]; simp_rw [h]; split
  · rename_i h'; simp only [h',double_sum]
  simp [*]

private lemma same_squares (w : I → Row J) (he : blocksMatch q p) : squares (lump q Finset.univ w) =
    ∑ i : I,squares (mapRows (Function.swap (p i)) (w i)) := by
  have hk {A : Type} [Fintype A] (x : Row A) : squares x=crossed x x := by simp [crossed,squares,sq]
  simp_rw [hk]
  let f i := mapRows (Function.swap (q i)) (w i)
  have ha (s : Finset I) (v : Row H) : crossed (lump q s w) v=∑ i∈s,crossed (f i) v := by
    unfold lump; rw [crossed]; simp_rw [Finset.sum_mul]; rw [sum_comm]; rfl
  have hb (s : Finset I) (v : Row H) : crossed v (lump q s w)=∑ i∈s,crossed v (f i) := by
    unfold lump; rw [crossed]; simp_rw [Finset.mul_sum]; rw [sum_comm]; rfl
  rw [ha]; simp_rw [hb]; unfold f; simp_rw [block_cross q p he]; simp

private def lone (i : I) (j : J) : I → Row J := fun x y => if x=i ∧ y=j then 1 else 0

private lemma exhibits (F : StrongDual ℝ (I → Row J)) (x : I → Row J) :
    F x=∑ i,crossed (fun j => F (lone i j)) (x i) := by
  have he : x=∑ i, ∑ j, x i j • lone i j := by
    ext i j
    simp [lone,Finset.sum_apply,ite_and]
  conv_lhs => rw [he,map_sum]
  simp only [map_sum,map_smul]; simp_rw [smul_eq_mul]
  unfold crossed; exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_comm ..

/-- Exact block joint law (use even with local density stickers). Need cross entries of
covariance zero and same marginal diagonals across all coordinates in use. -/
theorem blocked (h : blocksMatch q p) : Measure.map (fun x : Row H => (fun i : I => mapRows (q i) x)) (standard H) =
    Measure.pi (fun i : I => Measure.map (fun x : Row K => mapRows (p i) x) (standard K)) := by
  apply Measure.ext_of_charFunDual; ext v : 1
  let t i := fun j => v (lone i j); let w:=lump q Finset.univ t
  have hf (x : Row H) : v (fun i => mapRows (q i) x)=crossed w x := by
    rw [exhibits]; simp_rw [rewrite_row]; unfold w lump; rw [crossed]; simp_rw [Finset.sum_mul]; rw [sum_comm]; rfl
  rw [charFunDual_apply,charFunDual_apply,integral_map]
  rotate_left
  · apply Measurable.aemeasurable; unfold mapRows crossed; fun_prop
  · apply Measurable.aestronglyMeasurable; fun_prop
  simp_rw [hf]; rw [mgf_char]
  have he (x : I → Row J) : Complex.exp ((v x:ℂ)*Complex.I) = ∏ i : I,Complex.exp ((crossed (t i) (x i):ℂ)*Complex.I) := by
    rw [exhibits v x]; unfold t; simp_rw [Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  have ht i : (∫ x, Complex.exp ((crossed (t i) x:ℂ)*Complex.I) ∂Measure.map (fun x => mapRows (p i) x) (standard K)) =
      Complex.exp (-(squares (mapRows (Function.swap (p i)) (t i)):ℂ)/2) := by
    rw [integral_map]
    · simp_rw [rewrite_row]; exact mgf_char _
    · apply Measurable.aemeasurable; unfold mapRows crossed; fun_prop
    apply Measurable.aestronglyMeasurable; unfold crossed; fun_prop
  simp_rw [he]; rw [integral_fintype_prod_eq_prod (fun i x => Complex.exp ((crossed (t i) x:ℂ)*Complex.I))]
  simp_rw [ht,← Complex.exp_sum]
  unfold w; rw [same_squares _ p t h]; congr 1; simp only [Complex.ofReal_sum,sum_div,neg_div, Finset.sum_neg_distrib]

/-- Factor complex component occurrences over their disjoint supports in Gaussian when
using the legal exact Gram. Integrability to be paid separately in that application; present
lemma includes unbounded measurable factors when they have that property or when both
integrals degenerate. -/
lemma bills (h : blocksMatch q p) (f : I → Row J → ℂ) (he : ∀ i, Measurable (f i)) :
    ∫ x, ∏ i : I,f i (mapRows (q i) x) ∂standard H = ∏ i : I, ∫ x, f i (mapRows (p i) x) ∂standard K := by
  let g (w : I → Row J) := ∏ i,f i (w i)
  have hg : Measurable g := Finset.measurable_fun_prod _ fun i _ => (he i).comp (measurable_pi_apply _)
  let w i := Measure.map (fun x : Row K => mapRows (p i) x) (standard K)
  let u (x : Row H) := fun i => mapRows (q i) x
  have hv : Measurable u := by unfold u mapRows crossed; fun_prop
  have hp (i : I) : Measurable fun x => mapRows (p i) x := by unfold mapRows crossed; fun_prop
  change (∫ x,g (u x) ∂standard H)=_
  rw [←integral_map (f:=g) hv.aemeasurable hg.aestronglyMeasurable, blocked q p h]; unfold g
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_congr rfl fun i _ => integral_map (hp i).aemeasurable (he _).aestronglyMeasurable
end YM.Multi.Vacuum.Gauss

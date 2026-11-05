import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# The intact exterior work. Uniform even in the empty inventory.

E eq:drows, weak-annulus costs outside \\Omega\\, before any affine subtraction.
One may retain from F and I a selectable fraction of the direct coercivity (pay
back the resulting v/M penalty before claiming affordability). Separate from the
grants: NOTHING on these rows charged to earn in `full_grant`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial  Next.Fluctuations 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical 

variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S}

private lemma square_lower {a : ℝ} (_h : 0 ≤ a) (x y : G.Color) (he : ‖x‖ ≤ a) (ε : ℝ) (hε : ε ∈ Set.Icc (0:ℝ) 1) :
    ε*(a^2/4-‖y‖^2/2) ≤ a^2/2 +(‖y‖^2/2-inner ℝ y x) := by
  have hh : inner ℝ y x ≤ ‖y‖*a := (le_abs_self _).trans
    ((abs_real_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left he (norm_nonneg _)))
  have h0 : 0 ≤ a^2/2 +(‖y‖^2/2-inner ℝ y x) := by nlinarith [sq_nonneg (a-‖y‖)]
  have h1 : a^2/4-‖y‖^2/2 ≤ a^2/2 +(‖y‖^2/2-inner ℝ y x) := by nlinarith [sq_nonneg (a/2-‖y‖)]
  rcases le_total (a^2/4-‖y‖^2/2) 0 with ht|ht
  · exact (mul_nonpos_of_nonneg_of_nonpos hε.1 ht).trans h0
  exact (mul_le_of_le_one_left ht hε.2).trans h1

lemma workF_lower (R : ℕ) {U : Config G f} (V : Config G c) {t s : ℝ} (i : Cell f)
    (h : toll U i ≤ t) (he : PathData.kept T.high t i.1 U) (ε : ℝ) (hε : ε ∈ Set.Icc (0:ℝ) 1) :
    ε*(T.high.direct*toll U i^2/4-‖T.Mv R s V (i,false)‖^2/2) ≤ T.workF R U V t s i := by
  let b := Real.sqrt T.high.direct
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha : 0 ≤ toll U i := G.chord_nonneg _
  have ht : ‖shoot T.high U i‖ ≤ b*toll U i := by
    rw [shoot,norm_smul,Real.norm_of_nonneg hb]; exact mul_le_mul_of_nonneg_left (G.curvature_norm _) hb
  have hl := square_lower (mul_nonneg hb ha) _ (T.Mv R s V (i,false)) ht ε hε
  have hy (u : G.Color) := square_lower (norm_nonneg u) u (T.Mv R s V (i,true)) le_rfl 0
    (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 from Set.left_mem_Icc.mpr zero_le_one)
  unfold workF; rw [crown,trunk,if_pos he,PathData.clipped, if_pos (show G.chord _ ≤ t from h), Fintype.sum_bool]
  dsimp only [Xf,plotted]; simp only [not_false_eq_true, Bool.false_eq_true, ↓reduceIte]
  change _ ≤ ‖shorten _ _ _ _ _‖^2/2 + T.high.direct * toll U i^2/2 + _
  rw [mul_pow, show b^2=T.high.direct from Real.sq_sqrt T.high.quadratic_pos.le] at hl
  linarith only [hl,hy (shorten T.up R 1 U i)]

lemma workI_lower (R : ℕ) (Q V : Config G c) (s : ℝ) (i : Bond c)
    (ε : ℝ) (hε : ε ∈ Set.Icc (0:ℝ) 1) :
    ε*(S.kernel.penalty*wire Q V i^2/4-‖T.Mw R s V i‖^2/2) ≤ T.workI R Q V s i := by
  let b := Real.sqrt S.kernel.penalty
  have hb : 0≤b := Real.sqrt_nonneg _
  have ht : ‖Z S Q V i‖ ≤ b*wire Q V i := by
    rw [Z,norm_smul,Real.norm_of_nonneg hb]; exact mul_le_mul_of_nonneg_left (G.curvature_norm _) hb
  have he := square_lower (mul_nonneg hb (G.chord_nonneg _)) _ (T.Mw R s V i) ht ε hε
  rwa [mul_pow,show b^2=S.kernel.penalty from Real.sq_sqrt S.kernel.penalty_pos.le] at he -- may need monetary factor to twice this

/-- C row with output cut factor held together. Doesn't even need the kept
selector test (`trunk` already cancels here). -/
lemma workC_default (R : ℕ) (V : Config G c) (s : ℝ) (i : Cell c) (h : toll V i ≤ s) :
    T.workC R V s i + crown T.down T.low R S.patch.L.val s V i =
      (∑ j : Bool, ‖T.vision R s V (i,j)‖^2)/2 := by
  rw [workC,sub_add_cancel,Fintype.sum_bool,Fintype.sum_bool]; unfold vision thinned Xn plotted
  simp only [Bool.false_eq_true,↓reduceIte]; split
  · have hi : (if toll V i=0 then (1:ℝ) else min 1 (s/toll V i))=1 := by
      split <;> rename_i he
      · rfl
      have hh : 0<toll V i := lt_of_le_of_ne (G.chord_nonneg (faceValue V i)) (Ne.symm he)
      rw [min_eq_left (by rw [le_div_iff₀ hh,one_mul]; exact h)]
    rw [hi]; simp only [one_smul, real_inner_self_eq_norm_sq]; ring
  have hi : (if toll V i=0 then (1:ℝ) else min 1 (s/toll V i))=1 := by
    split <;> rename_i he
    · rfl
    have hh : 0<toll V i := lt_of_le_of_ne (G.chord_nonneg (faceValue V i)) (Ne.symm he)
    rw [min_eq_left (by rw [le_div_iff₀ hh,one_mul]; exact h)]
  rw [hi]; simp only [one_smul,inner_zero_left,norm_zero,zero_pow (by norm_num : 2≠0),real_inner_self_eq_norm_sq]; ring

def reserve (c : Clip) := min (1/2:ℝ) (c.linear/c.direct)
lemma reserve_pos (c : Clip) : 0<reserve c := lt_min (by norm_num) (div_pos c.tail_pos c.quadratic_pos)
lemma reserve_le (c : Clip) : reserve c ≤ 1/2 := min_le_left ..

/-- Even on defects, some output reserve still remains if the sieve was kept.
Cannot spend this when seeking an estimate without the V factor. -/
lemma crown_pays (R A : ℕ) (Q : PathData G) (p : Clip) (s : ℝ) (hs : 0 ≤ s) (V : Config G n) (i : Cell n) :
    reserve p * (∑ j : Bool, ‖thinned Q p s A R V (i,j)‖^2) ≤ crown Q p R A s V i := by
  let r := toll V i
  let b := Real.sqrt p.direct
  let a := if r=0 then (1:ℝ) else min 1 (s/r)
  have hr : 0 ≤ r := G.chord_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hl : a≤1 := by unfold a; split; rfl; exact min_le_left ..
  have hpos : 0≤a := by
    unfold a; split
    · norm_num
    exact le_min zero_le_one (div_nonneg hs hr)
  have hx := p.quadratic_pos
  have he : reserve p * ‖a • shoot p V i‖^2 ≤ PathData.clipped p s r := by
    have hh : ‖a • shoot p V i‖ ≤ a*(b*r) := by
      rw [norm_smul, Real.norm_of_nonneg hpos, shoot, norm_smul, Real.norm_of_nonneg hb]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (G.curvature_norm _) hb) hpos
    unfold PathData.clipped; split
    · apply (mul_le_mul (reserve_le _) (pow_le_pow_left₀ (norm_nonneg _) hh _) (by positivity) (by norm_num)).trans
      rw [mul_pow,mul_pow, show b^2=p.direct from Real.sq_sqrt hx.le]
      have ht : a^2 ≤ 1 := by simpa using pow_le_pow_left₀ hpos hl 2
      have hu := mul_le_mul_of_nonneg_right ht (mul_nonneg hx.le (sq_nonneg r))
      linarith
    rename_i hg
    have hv : 0<r := hs.trans_lt (lt_of_not_ge hg)
    have hy : ‖a • shoot p V i‖ ≤ s*b := hh.trans ((mul_le_mul_of_nonneg_right
      (show a ≤ s/r by unfold a; rw [if_neg hv.ne']; exact min_le_right ..)
      (mul_nonneg hb hr)).trans_eq (by field_simp))
    apply (mul_le_mul (show reserve p ≤ p.linear/p.direct from min_le_right ..)
      (pow_le_pow_left₀ (norm_nonneg _) hy _) (by positivity) (div_nonneg p.tail_pos.le hx.le)).trans
    rw [mul_pow, show b^2=p.direct from Real.sq_sqrt hx.le, show p.linear/p.direct*(s^2*p.direct)=p.linear*s*s by field_simp]
    exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hg)) (mul_nonneg p.tail_pos.le hs)
  have ht : reserve p * ‖(if PathData.kept p s i.1 V then shorten Q R A V i else 0)‖^2 ≤
      trunk Q p R A s V i := by
    unfold trunk; split
    · exact (mul_le_mul_of_nonneg_right (reserve_le p) (sq_nonneg ‖shorten Q R A V i‖)).trans_eq (by ring)
    rw [norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero]
  rw [Fintype.sum_bool,mul_add]; unfold crown thinned
  simp only [Bool.false_eq_true, ↓reduceIte]; exact (add_le_add ht he)

/-- Use with `Interior.interior_cost` (compare with the T-scale EBare).
These are the *actual* L,D rows at (U,Q(U,k),V), not a Gaussian substitute. -/
lemma workLD_lower (R : ℕ) (U : Config G f) (V Q : Config G c) (x : Cell c) (A C t s h e : ℝ) (hA : 0≤A*t)
    (hm : ∀ i, ‖T.vision R s V i‖ ≤ A*t)
    (he : ∀ i : Bool, ‖lGap T R U Q V (x,i)‖ ≤ C*h*e ∧
      ‖dGap T R V (T.vision R s V) (x,i)‖ ≤ C*(A*t)*e) :
    -(2*(A*t)*(C*h*e) + (A*t)*(C*(A*t)*e)) ≤ T.workL R U Q V s x + T.workD R V s x := by
  let v := T.vision R s V
  have hf (i : Bool) : -(A*t*(C*h*e)) ≤ inner ℝ (v (x,i)) (lGap T R U Q V (x,i)) := by
    apply neg_le_of_abs_le
    exact (abs_real_inner_le_norm ..).trans (mul_le_mul (hm _) ((he i).1) (norm_nonneg _) hA)
  have hg (i : Bool) : -(A*t*(C*(A*t)*e)) ≤ inner ℝ (v (x,i)) (dGap T R V v (x,i)) := by
    apply neg_le_of_abs_le
    exact (abs_real_inner_le_norm ..).trans (mul_le_mul (hm _) ((he i).2) (norm_nonneg _) hA)
  unfold v at *
  rw [workL_gap,workD_gap,Fintype.sum_bool,Fintype.sum_bool]
  linarith only [hf true,hf false,hg true,hg false]

end YM.SectorNext.Remainder

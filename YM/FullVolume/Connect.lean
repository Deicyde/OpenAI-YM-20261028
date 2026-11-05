import YM.FullVolume.Discrete
import YM.Extra.WEAK_SCALING_ACTLAW.Analysis

/-! Paths of unit steps inside coordinate boxes. Gives also Lipschitz
slope bounds INSIDE a ball around one grid endpoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Set Filter Metric MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {n:ℕ}

abbrev Dir (a:MotionIndex n): Points n:= Points.direction a.1 a.2
lemma tagged (t:ℝ)(a:MotionIndex n)(x:Positions n):
    tag t (x+drive a)=tag t x + t • Dir a := by
  ext i j
  change t*((↑((x+drive a) i j : ℤ)):ℝ)=tag t x i j+t * Dir a i j
  dsimp only [Dir,tag]; by_cases h:i=a.1 <;> by_cases he:j=a.2 <;>
    simp [drive,h,he,Points.direction,basis] <;> ring
lemma taggedN (t:ℝ)(a:MotionIndex n)(x:Positions n)(k:ℕ):
    tag t (x+k • drive a)= tag t x + (k*t) • Dir a:=by
  induction k with
  | zero=> simp
  | succ k ih=> rw [succ_nsmul,←add_assoc,tagged,ih]; push_cast; rw [add_mul,add_smul,one_mul]; abel
lemma paidDist (x:Positions n)(t:ℝ) (ht:0<t)(a:MotionIndex n)(k:ℕ):
    dist (tag t (x+k • drive a)) (tag t x) = k*t:=by
  have hv: x+k • drive a=advance x a.1 a.2 k:=by ext j:1; by_cases h:j=a.1 <;> simp [drive,h,advance]
  exact (congrArg (fun y=>dist (tag t y) (tag t x)) hv).trans ((extent _ _ _ _ _ ht).trans (mul_comm ..))
private def distance (x y : Positions n) := ∑ i:MotionIndex n, (y i.1 i.2-x i.1 i.2).natAbs
private theorem norm_tag {m : ℕ} (x y : Positions m) (t : ℝ) :
    dist (tag t x) (tag t y) ^ 2 = ∑ i : Fin m × Axis, (t * (x i.1 i.2 - y i.1 i.2 : ℤ))^2 := by
  rw [dist_eq_norm,← Points.flatten.norm_map,EuclideanSpace.real_norm_sq_eq]; simp only [map_sub,PiLp.sub_apply]
  refine Finset.sum_congr rfl fun i _ => ?_; change (_ * _ - _ * _) ^ 2 = _
  simp only [Int.cast_sub,mul_sub]

private lemma priced (t:ℝ)(ht:0<t)(x y:Positions n):t*distance x y ≤ (Fintype.card (MotionIndex n):ℝ)*dist (tag t y) (tag t x):=by
  unfold distance; push_cast; rw [Finset.mul_sum]; refine le_trans (Finset.sum_le_sum (g:=fun _=> dist (tag t y) (tag t x)) (fun i _=>?_)) (by simp)
  apply (sq_le_sq₀ (by positivity) dist_nonneg).mp
  rw [norm_tag]
  refine le_trans ?_ (Finset.single_le_sum (fun j (_:j∈Finset.univ)=> sq_nonneg (t*((↑(y j.1 j.2-x j.1 j.2 : ℤ)):ℝ))) (Finset.mem_univ i))
  apply le_of_eq; rw [mul_pow,mul_pow]
  let X:= y i.1 i.2-x i.1 i.2; congr 1
  change (X.natAbs:ℝ)^2=(X:ℝ)^2
  rw [← Int.cast_natCast (R:=ℝ),Int.natCast_natAbs,Int.cast_abs,sq_abs]

private lemma drive_at (a i:MotionIndex n) : drive a i.1 i.2= if i=a then 1 else 0:=by
  obtain ⟨i,j⟩:=i; obtain ⟨u,v⟩:=a
  by_cases h:i=u <;> by_cases hp:j=v <;> simp [drive,h,hp,Ne.symm]

private lemma closerTag (x y:Positions n) (a:MotionIndex n) (t:ℝ) (u:Positions n)
    (he : (u a.1 a.2-x a.1 a.2).natAbs+1=(y a.1 a.2-x a.1 a.2).natAbs)
    (h : ∀ i:MotionIndex n,i≠a → u i.1 i.2=y i.1 i.2) : distance x u+1=distance x y ∧ dist (tag t u) (tag t x) ≤ dist (tag t y) (tag t x):=by
  let P (z:Positions n)(a:MotionIndex n):= (z a.1 a.2-x a.1 a.2).natAbs
  constructor
  · unfold distance; change (∑ i,P u i)+1=∑ i,P y i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ (P y) (Finset.mem_univ a),add_right_comm, show P u a+1=P y a from he]
    apply congr_arg; exact Finset.sum_congr rfl fun i hi=>by unfold P; rw [h i (Finset.ne_of_mem_erase hi)]
  refine (sq_le_sq₀ dist_nonneg dist_nonneg).mp ?_; rw [norm_tag,norm_tag]; apply Finset.sum_le_sum
  intro i hi; by_cases hk:i=a
  · subst i; rw [sq_le_sq,abs_mul,abs_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact_mod_cast (show |(u a.1 a.2-x a.1 a.2 : ℤ)|≤ |(y a.1 a.2-x a.1 a.2 : ℤ)| by
      rw [← Int.natCast_natAbs,← Int.natCast_natAbs]; exact_mod_cast Nat.le_of_succ_le he.le)
  rw [h i hk]

lemma stroll {t:ℝ}(ht:0<t)(f:Positions n→ℂ)(x y:Positions n)(R L:ℝ)(hL:0≤L)(hx:dist (tag t y) (tag t x) ≤ R)
    (h:∀ (u:Positions n)(s:MotionIndex n),dist (tag t u) (tag t x) ≤ R → dist (f (u+drive s)) (f u) ≤ t*L):
    dist (f y) (f x) ≤ L*Fintype.card (MotionIndex n)*dist (tag t y) (tag t x) := by
  suffices hv : dist (f y) (f x) ≤ L*(t*distance x y) by
    exact hv.trans ((mul_le_mul_of_nonneg_left (priced _ ht x y) hL).trans_eq (by ring))
  generalize hh: distance x y=k; induction k using Nat.strong_induction_on generalizing y with
  | h k ih =>
    by_cases hp:y=x
    · rw [hp,dist_self]; positivity
    obtain ⟨i,hi⟩:= Function.ne_iff.mp hp; obtain ⟨j,hj⟩:= Function.ne_iff.mp hi
    let a:MotionIndex n:= (i,j)
    have hv (z:Positions n) (ht:distance x z+1=k) (hg:dist (tag t z) (tag t x) ≤ R) (h:dist (f y) (f z)≤ t*L): dist (f y) (f x) ≤ L*(t*k):= by
      have hE:= ih _ (Nat.lt_of_add_one_le ht.le) z hg rfl
      apply (dist_triangle _ (f z) _).trans ((add_le_add h hE).trans_eq ?_); rw [←ht]; push_cast; ring
    rcases lt_or_gt_of_ne hj with hz|hz
    · let z:= y+drive a
      have he: (z i j-y i j)=1:=by simp [z,drive,a]
      obtain ⟨hd,hB⟩:= closerTag x y a t z (show (z i j-x i j).natAbs+1=(y i j-x i j).natAbs by omega) (fun i hi=> by simp only [z,Pi.add_apply,drive_at a i,if_neg hi,add_zero])
      exact hv _ (hd.trans hh) (hB.trans hx) (dist_comm .. |>.trans_le (h y a hx))
    let z:= y-drive a
    have he:z i j=y i j-1:=by simp [z,drive,a]
    obtain ⟨hd,hB⟩:= closerTag x y a t z (show (z i j-x i j).natAbs+1=(y i j-x i j).natAbs by omega) (fun i hi=> by simp only [z,Pi.sub_apply,drive_at a i,if_neg hi,sub_zero])
    have hW:=hB.trans hx
    apply hv _ (hd.trans hh) hW; nth_rw 1 [← show z+drive a =y from sub_add_cancel ..]; exact h z a hW

lemma unique_units (f:Positions n→ℂ) {t:ℝ}(ht:0<t)(a:MotionIndex n)(x:Positions n):
    f (x+drive a)-f x=t • delta (drive a) t f x:=by
  rw [delta_at,Complex.real_smul,← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne'),one_mul]

end YM.FullVolume

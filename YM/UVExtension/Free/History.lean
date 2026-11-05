import YM.UVExtension.Limits
import YM.Next.FREE_KERNELS.Rack

/-! Convergence of the cumulative smoothing filters at fixed (unwrapped)
rescaled momentum. Key point is an infinite product along the actual history;
J can increase as along the construction and thickness in L is not lost from step to step. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Free
open Filter Set Function Lattice Laurent Bloch Metric Precision RG Next.Free
open scoped Topology BigOperators
variable {G : Gauge}
variable (A : Levels G)

/-- length and bookkeeping -/
lemma steps_tail (S : Schedule) (i k : ℕ) : S.steps i (k+1) = S.block i * S.steps (i+1) k := by
  induction k with
  | zero => simp [Schedule.steps]
  | succ k hk =>
    change S.steps i (k+1) * S.block (i+(k+1)) = _
    rw [hk]; rw [mul_assoc]
    refine congr_arg (S.block i * ·) ?_
    rw [Schedule.steps, show i+(k+1)=i+1+k by omega]

lemma flying_mass (d i : ℕ) : (flying A d i).mass=A.S.steps i d := by
  induction d generalizing i with
  | zero => rfl
  | succ d h =>
    rw [flying]; change A.S.block i * (flying A d (i+1)).mass= _; rw [steps_tail]; rw [h]

lemma steps_big (S : Schedule) (k i : ℕ) : 2^k ≤ (S.steps i k).val := by
  induction k with
  | zero => simp [Schedule.steps]
  | succ k h =>
    rw [pow_succ,Schedule.steps,PNat.mul_coe]; exact Nat.mul_le_mul h (le_trans (by decide : 2≤3) (S.block_large _))
lemma steps_infinite (i : ℕ) (S : Schedule) : Tendsto (fun d => (S.steps i d).val) atTop atTop := by
  refine tendsto_atTop_mono (fun k=>steps_big S k i) (tendsto_pow_atTop_atTop_of_one_lt ?_)
  exact (by norm_num : 1 < (2:ℕ))
lemma index_limit (i k : ℕ) : A.clock.J (i+k) ≤ A.clock.J i+k := by
  induction k with
  | zero => simp
  | succ k h =>
    exact (A.fits.stepSlow (i+k)).trans (Nat.add_le_add_right h _)

private def slot (m : ℕ) := (A.clock.op m 0).patch
@[simp] private lemma slot_size (m : ℕ) : (slot A m).L=A.S.block m := rfl

private lemma splitNarrow (L M : Side) (z : Momentum) : narrow (L*M) z=narrow M (narrow L z) := by
  ext j
  rw [narrow_apply,narrow_apply,narrow_apply,mul_side_complex,div_div]
private lemma scaleNarrow (M : Side) (z : Momentum) : M.val • narrow M z=z := by
  ext i
  change (↑M.val:ℕ) • (narrow M z i)=z i
  rw [narrow_apply,nsmul_eq_mul,mul_div_cancel₀ _ (side_ne _)]

private lemma small_twirl (M : Side) (z : ℂ) (j : ℤ) (hk : |j|≤M.val) (hv : (M.val:ℝ)*‖z‖≤domainRadius) :
    ‖twirl z j-1‖≤ meter.high*((M.val:ℝ)*‖z‖) := by
  have ht : ‖(j:ℂ)*z‖≤ (M.val:ℝ)*‖z‖ := by
    rw [norm_mul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [Complex.norm_intCast]; exact_mod_cast hk
  rw [show twirl z j-1=chip ((j:ℂ)*z) by unfold chip twirl; ring_nf]
  exact (meter.above _ (ht.trans hv)).trans (mul_le_mul_of_nonneg_left ht meter.high_pos.le)

private lemma mean_cost (M : Side) (z : ℂ) (hv : (M.val:ℝ)*‖z‖ ≤ domainRadius) :
    ‖rail M z-1‖ ≤ meter.high*((M.val:ℝ)*‖z‖) ∧ ‖plank M z-1‖ ≤ meter.high*((M.val:ℝ)*‖z‖) := by
  let f (i : ℕ) := twirl z (i-mid M)
  let g (i : ℕ) := twirl z i
  have he (f : ℕ → ℂ) : (M.val:ℂ)⁻¹*∑ i ∈ Finset.range M.val, (f i-1)=
      (M.val:ℂ)⁻¹*(∑ i ∈ Finset.range M.val, f i)-1 := by rw [Finset.sum_sub_distrib,mul_sub]; simp
  rw [plank_centers]; unfold rail; rw [← he g,← he f]
  refine ⟨average_bound M _ (fun i hi => small_twirl _ _ _ ?_ hv),
           average_bound M _ (fun i hi => small_twirl _ _ _ (all_centers M i (Finset.mem_range.mp hi)) hv)⟩
  rw [abs_of_nonneg (Int.natCast_nonneg _)]; exact_mod_cast (Finset.mem_range.mp hi).le

private lemma approx_mul (x y : ℂ) (hx : ‖x‖ ≤ 1) : ‖x*y-1‖ ≤ ‖x-1‖+‖y-1‖ := by
  calc
    _ = ‖(x-1)+x*(y-1)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le ..).trans (add_le_add_right ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) hx)) _)

private lemma approx_finset (Z : Finset Axis) {x : Axis→ℂ} (hx : ∀ i, ‖x i‖ ≤ 1) {c : ℝ} (h : ∀ i, ‖x i-1‖≤c) :
    ‖(∏ i∈Z,x i)-1‖≤ Z.card*c := by
  induction Z using Finset.induction_on with
  | empty => simp
  | insert i Z hi ih =>
    rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi]
    exact (approx_mul _ _ (hx i)).trans ((add_le_add (h i) ih).trans_eq (by push_cast; ring))

private lemma segment_cost (P : Patch) (p : Momentum) (a : Axis) (r : ℝ) (hp : physical p)
    (hx : ∀ i : Axis, (P.L.val:ℝ)*‖p i‖ ≤ r) (h : r≤domainRadius) :
    ‖pullLine P a p-1‖ ≤ ((P.J:ℝ)*4+1)*(meter.high*r) := by
  let B := meter.high*r
  let w := area P.L p
  have hP (i) : ‖plank P.L (p i)‖ ≤ 1 := by
    apply (plank_height P.L _).trans; rw [(physical_iff _).1 hp i]; simp
  have ht (i) : ‖plank P.L (p i)-1‖ ≤ B :=
    ((mean_cost _ _ ((hx i).trans h)).2).trans (mul_le_mul_of_nonneg_left (hx i) meter.high_pos.le)
  have hv : ‖w-1‖≤4*B := by
    simpa only [w, area, Axis, Finset.card_univ,Fintype.card_fin, Nat.cast_ofNat] using approx_finset Finset.univ hP ht
  have hy : ‖w‖≤1 := by
    unfold w area; rw [norm_prod]; exact Finset.prod_le_one (fun i _=> norm_nonneg _) (fun i _=> hP i)
  have hz (j : ℕ) : ‖w^j-1‖≤ j*(4*B) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ']; exact (approx_mul _ _ hy).trans ((add_le_add hv ih).trans_eq (by push_cast; ring))
  have hR : ‖rail P.L (p a)-1‖≤ B :=
    ((mean_cost _ _ ((hx a).trans h)).1).trans (mul_le_mul_of_nonneg_left (hx a) meter.high_pos.le)
  refine (approx_mul (w^P.J) _ (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy)).trans ?_
  exact (add_le_add (hz _) hR).trans_eq (by unfold B; ring)

private def point (i : ℕ) (p : Momentum) (k : ℕ) := narrow (A.S.steps i k) p
private def installment (i : ℕ) (a : Axis) (p : Momentum) (k : ℕ) : ℂ := pullLine (slot A (i+k)) a (point A i p (k+1))

private lemma drive_prod (d i : ℕ) (p : Momentum) (a : Axis) :
    (flying A d i).drive a (point A i p d)=∏ k ∈ Finset.range d, installment A i a p k := by
  induction d generalizing i p with
  | zero => simp [flying,Train.drive, Train.mass]
  | succ d h =>
    let P := slot A i
    let L := A.S.block i
    let x := narrow L p
    let Y := flying A d (i+1)
    have he (k) : point A i p (k+1)=point A (i+1) x k := by unfold point; rw [steps_tail, splitNarrow]
    have hx : point A i p 1=x := by unfold point; rw [Schedule.steps]; simp [x,L,Schedule.steps]
    have hP : Y.mass.val • point A i p (d+1)=x := by rw [he d,point, ← flying_mass A]; exact scaleNarrow ..
    rw [flying]; change (Train.hop P _ _ Y).drive _ _=_
    rw [Train.drive_links]
    change pullLine P a (Y.mass.val • point A i p (d+1))* (flying A d (i+1)).drive a _=_
    rw [hP,he d, Finset.prod_range_succ', show installment A i a p 0=pullLine P a x from by unfold installment; rw [hx]; rfl]
    rw [mul_comm, h (i+1) x]; congr 1
    refine Finset.prod_congr rfl fun j _=>?_
    dsimp only [installment]; rw [he (j+1), show i+1+j=i+(j+1) by omega]

private lemma installments (i : ℕ) (a : Axis) (p : Momentum) (hp : physical p) :
    Summable fun j : ℕ => ‖installment A i a p j-1‖ := by
  let f := fun j : ℕ => (1/2:ℝ)^j
  let h := fun j : ℕ => ((A.clock.J (i+1) + (j:ℝ))*4+1)*(meter.high*‖p‖*f j)
  have hf : Summable f := summable_geometric_two
  have hy : Summable h := by
    have hJ : Summable fun i:ℕ => (i:ℝ)*f i := by
      simpa only [f,pow_one] using (summable_pow_mul_geometric_of_norm_lt_one 1 (r:=(1/2:ℝ)) (by norm_num))
    refine ((hf.mul_left ((A.clock.J (i+1)*4+1)*(meter.high*‖p‖))).add (hJ.mul_left (4*(meter.high*‖p‖)))).congr ?_
    intro k; dsimp only [h,Pi.add_apply]; ring
  have hx : Tendsto (fun i=> ‖p‖*f i) atTop (𝓝 0) := by simpa using hf.tendsto_atTop_zero.const_mul ‖p‖
  apply hy.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hx.eventually_le_const domainRadius_pos] with k hk
  let y := point A i p (k+1)
  let D := (A.S.steps i k)
  let P := slot A (i+k)
  have ht (s : Axis) : (P.L.val:ℝ)*‖y s‖ ≤ ‖p‖*f k := by
    have hr : 2^k ≤ (D.val:ℝ) := by exact_mod_cast steps_big A.S k i
    have hL : A.S.steps i (k+1)=D*P.L := rfl
    have he : P.L.val≠0 := P.L.property.ne'; have hd : 0<(D.val:ℝ) := side_pos D
    rw [show y s=p s/(((D*P.L).val):ℂ) from by unfold y point; rw [narrow_apply,hL],norm_div,Complex.norm_natCast,mul_side_real]
    rw [show (P.L.val:ℝ)*(‖p s‖/(D.val*P.L.val:ℝ))= ‖p s‖/D.val by field_simp]
    calc
      _ ≤ ‖p‖/D.val := by gcongr; exact norm_le_pi_norm _ _
      _ ≤ ‖p‖/ (2:ℝ)^k := by gcongr
      _ = _ := by unfold f; rw [div_pow,one_pow,div_eq_mul_inv, one_div]
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  refine (segment_cost P _ a _ (narrow_real _ hp) ht hk).trans ?_
  unfold h
  rw [← mul_assoc meter.high]; gcongr
  · apply mul_nonneg (mul_nonneg meter.high_pos.le (norm_nonneg _)) (by unfold f; positivity)
  exact_mod_cast (show P.J ≤ A.clock.J (i+1)+k from (by have h:= index_limit A (i+1) k; rw [show i+1+k=i+k+1 by omega] at h; exact h))

lemma drive_history (a : Axis) (i : ℕ) (p : Momentum) (hp : physical p) :
    Arrives fun k => let Y:= flying A k i; Y.drive a (narrow Y.mass p) := by
  have hh := multipliable_one_add_of_summable (installments A i a p hp)
  have hg : Multipliable (installment A i a p) := hh.congr (fun i => by simp)
  apply (show Arrives fun j => ∏ l∈Finset.range j, installment A i a p l from
    ⟨_,hg.hasProd.tendsto_prod_nat⟩).copy
  filter_upwards with i'
  dsimp only; rw [flying_mass]; exact (drive_prod ..).symm
end YM.UVExtension.Free

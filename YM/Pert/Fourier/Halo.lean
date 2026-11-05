import YM.Pert.Fourier.Riemann
/-! Uniform cost for continuum annuli with the massless potential's positive heat mollifier.
Continental transform bound before removing damping.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open YM.Next.Rank.Radian MeasureTheory Filter Lattice Topology Set Function Metric
open scoped ContDiff BigOperators RealInnerProductSpace FourierTransform Classical

lemma major_global (a : ℝ) : ContDiff ℝ ∞ (major a) := major_cont.comp (show ContDiff ℝ ∞ (fun x:E4=>(a,x)) by fun_prop)
lemma white_hot (a : ℝ) (ha : 0≤a) : major a = fun x => major 1 ((Real.sqrt a) • x) := funext (fun x=> by simp only [major,norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg a)]; rw [mul_pow, Real.sq_sqrt ha]; congr 1; rw [neg_one_mul,neg_mul])
lemma major_toll (i : ℕ) : ∃ C>0,∀ {a : ℝ}, 0≤a → ∀ x : E4, 1/2 ≤‖x‖ → ‖iteratedFDeriv ℝ i (major a) x‖ ≤ C := by
  have H := ((major_global 1).of_le (show (i:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top))
  have hf : Fast (major 1) := by simpa only [Pi.mul_apply, one_mul] using! (rapidG (Spire.rope 1) zero_lt_one)
  obtain ⟨A,hA⟩ := (isCompact_closedBall (0:E4) 1).exists_bound_of_continuousOn (H.continuous_iteratedFDeriv le_rfl).continuousOn
  obtain ⟨B,hB,hB'⟩ := hf.2 i i
  let c:= max (max 1 B) A
  refine ⟨(2:ℝ)^i*c,mul_pos (pow_pos two_pos _) (lt_of_lt_of_le zero_lt_one (le_trans (le_max_left ..) (le_max_left ..))),fun {a} ha x hx => ?_⟩
  let s:= Real.sqrt a; have hp : 0≤s := Real.sqrt_nonneg _; let y:= s • x
  rw [white_hot a ha, iteratedFDeriv_comp_const_smul _ H]; dsimp only [id_eq]; rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (by positivity) _)]
  obtain hp'|hp':=le_total ‖y‖ 1
  · have he : s*‖x‖ ≤ 1 := by simpa only [y,norm_smul,Real.norm_of_nonneg hp] using hp'
    have hs : s^i ≤ (2:ℝ)^i := by gcongr; nlinarith only [he,hx,hp]
    exact mul_le_mul hs ((hA y (by simpa)).trans (le_max_right (max 1 B) A)) (norm_nonneg _) (by positivity)
  have he : s ≤ 2*‖y‖ := by rw [show ‖y‖=s*‖x‖ by simp [y,norm_smul,Real.norm_of_nonneg hp]]; nlinarith only [hx,hp]
  apply (mul_le_mul_of_nonneg_right (show s^i≤2^i*‖y‖^i by rw [←mul_pow]; gcongr) (norm_nonneg _)).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ((hB' y hp').trans (show B≤c from (le_max_right ..).trans (le_max_left ..))) (pow_nonneg zero_le_two _)

-- need avoid open Real conflict.
def halo (D : List Axis) (a : ℝ) (q : E4) := major a q * middle D 0 q
def annulus := {q:E4 | 1/2 ≤ ‖q‖} ∩ closedBall 0 3
lemma annular : IsCompact annulus := (isCompact_closedBall (0:E4) 3).inter_left (isClosed_le continuous_const continuous_norm)
lemma halo_support (D : List Axis) (a : ℝ) : tsupport (halo D a) ⊆ annulus := closure_minimal (fun q hq=> by
   have hfq : ‖q‖ ≠ 0 := fun h=> hq (by unfold halo middle; have hx : ‖q‖≤1/2 := h ▸ (by norm_num); rw [innermost hx, disk_one hx,sub_self,Complex.ofReal_zero,zero_mul,mul_zero]); clear hfq
   change 1/2≤‖q‖ ∧ _
   refine ⟨le_of_not_gt (fun h=>hq (by unfold halo middle; simp only [innermost h.le,disk_one h.le,sub_self,Complex.ofReal_zero,zero_mul,mul_zero])),mem_closedBall.mpr (dist_zero_right q ▸ le_of_not_gt (fun h=>hq (by unfold halo middle; have h': (2:ℝ) ≤‖q‖ := (show (2:ℝ)≤3 by norm_num).trans h.le; simp only [outermost h',disk_out (one_le_two.trans h'),sub_self,Complex.ofReal_zero,zero_mul,mul_zero])))⟩) annular.isClosed
lemma mid_zero (D : List Axis) : ContDiff ℝ ∞ (middle D 0) := contDiff_iff_contDiffAt.mpr fun x=> (middle_diff D 0 (by norm_num) x).comp x (f:=fun (i:E4) => ((0:ℝ),i)) (by fun_prop)
lemma halo_good (D : List Axis) (a : ℝ) : ContDiff ℝ ∞ (halo D a) := (major_global a).mul (mid_zero D)
lemma halo_bound (D : List Axis) (j : ℕ): ∃ C≥0, ∀ {i : ℕ}, i≤j → ∀ {a:ℝ}, 0≤a → ∀ x : E4, ‖iteratedFDeriv ℝ i (halo D a) x‖ ≤ annulus.indicator (fun _=>C) x := by
  choose A hp H using fun i => major_toll i
  choose B hB B' using fun i => middle_bound i D
  let cost (i k : ℕ) := (i.choose k : ℝ) * (A k) * B (i-k)
  let all := ∑ i ∈ Finset.range (j+1), ∑ k ∈ Finset.range (i+1), cost i k
  have cost0 (i k : ℕ) : 0 ≤ cost i k := mul_nonneg (mul_nonneg (by positivity) (hp k).le) (hB _).le
  let X (i : ℕ):ℝ := ∑ k ∈ Finset.range (i+1), cost i k
  refine ⟨all,Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun k hk => cost0 _ _, fun {i} hi {a} ha x => ?_⟩
  by_cases hx : x∈annulus
  · rw [indicator_of_mem hx]
    apply le_trans (c:=all) (b:=∑ k ∈ Finset.range (i+1),cost i k) _ (Finset.single_le_sum (f:=X) (fun _ _ => Finset.sum_nonneg fun a _ => cost0 _ _) (Finset.mem_range.mpr (show i<j+1 by omega)))
    apply (norm_iteratedFDeriv_mul_le (major_global a) (mid_zero D) x (WithTop.coe_le_coe.mpr le_top)).trans
    apply Finset.sum_le_sum; intro k _; have hb := B' (i-k) (0,x) ⟨show 0≤(0:ℝ) from le_rfl,zero_le_one⟩ (mem_closedBall.mpr ((mem_closedBall.mp hx.2).trans (show (3:ℝ) ≤ 6 by norm_num)))
    exact mul_le_mul (mul_le_mul_of_nonneg_left (H k ha x hx.1) (Nat.cast_nonneg _)) hb (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hp _).le)
  rw [show iteratedFDeriv ℝ i (halo D a) x=0 from by by_contra h; exact hx (halo_support D a ((support_iteratedFDeriv_subset i h))),indicator_of_notMem hx]; exact le_of_eq norm_zero

lemma cooling (D : List Axis) (j : ℕ) : ∃ C≥0,∀ {u : ℝ}, 0≤u → ∀ x : E4, ‖x‖^j * ‖harmon (halo D u) x‖ ≤ C := by
  obtain ⟨C,hC,H⟩ := halo_bound D j
  let f : E4→ℝ := annulus.indicator (fun _=>C)
  have fI : Integrable f := (integrable_indicator_iff annular.measurableSet).2 (integrableOn_const (annular.measure_lt_top).ne)
  let bins := Finset.range (0+1) ×ˢ Finset.range (j+1)
  refine ⟨(2:ℝ)^j * ∑ p ∈ bins, ∫ x, f x,by refine mul_nonneg (pow_nonneg zero_le_two _) (Finset.sum_nonneg fun _ _=>integral_nonneg (fun i=>indicator_nonneg (fun _ _=>hC) i)),fun {u} hu x=>?_⟩
  let g:=halo D u
  have gI (k i : ℕ) (_ : (k:ℕ∞)≤(0:ℕ)) (_ : (i:ℕ∞)≤(⊤:ℕ∞)) : Integrable (fun v : E4 => ‖v‖ ^ k * ‖iteratedFDeriv ℝ i g v‖) := by
     refine (continuous_norm.pow k |>.mul ((halo_good D u).continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top) |>.norm)).integrable_of_hasCompactSupport (((HasCompactSupport.iteratedFDeriv (annular.of_isClosed_subset isClosed_closure (halo_support D u)) i).norm).mul_left)
  have e := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K:=0) (N:=⊤) (halo_good D u) gI (show ((0:ℕ):ℕ∞) ≤ 0 from le_rfl) (show (j:ℕ∞) ≤ (⊤:ℕ∞) from le_top) (-x)
  simp only [harmon,norm_neg,norm_iteratedFDeriv_zero,pow_zero,one_mul,Nat.cast_zero,mul_zero,zero_add] at *
  refine e.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p hp=>integral_mono (gI _ _ (by have e : p.1=0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hp).1)); simp [e]) le_top) fI (fun y=>?_)) (pow_nonneg zero_le_two _))
  dsimp; rw [show p.1=0 from Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hp).1)),pow_zero, one_mul]; exact H (by have := Finset.mem_range.mp (Finset.mem_product.mp hp).2; omega) hu y
end YM.Pert.Band

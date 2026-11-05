import YM.OPE.Interpolate.Chart
/-!
# Leap cost
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Set MeasureTheory Lattice RG Metric
open scoped Topology BigOperators Classical ContDiff
variable {E F : Type*}{φ:Filter E}{T r:E→ ℝ}{x y g:E→ F}{a b:ℝ}

lemma most_often {W H:E→F→Prop}(hh:∀ (y:E→F),∀ (h:∀ i,W i (y i)), ∀ᶠ i in φ,H i (y i)) -- replace H
    (hx:∀ i,W i (x i)):∀ᶠ i in φ,∀ y,W i y → H i y:=by
    let f (i:E) := if h:∃ y,W i y∧¬ H i y then h.choose else x i
    have he i: W i (f i):=by
       unfold f; split; next h=> exact h.choose_spec.1
       exact hx _
    filter_upwards [hh f he] with i hi y hy; by_contra hv; have h:∃ y,W i y∧¬ H i y:= ⟨y,hy,hv⟩; unfold f at hi; rw [dif_pos h] at hi; exact h.choose_spec.2 hi

lemma leap_cost [NormedAddCommGroup F] [NormedSpace ℝ F] {V:E→ F→ℂ}
    (hT:Tendsto T φ atTop)(hz:RateLE φ T (fun i=>x i-y i) a)
    (hk:∀ (g:E→F),(∀ i, g i∈ closedBall (y i) ‖x i-y i‖) →
       (∀ᶠ i in φ,DifferentiableAt ℝ (V i) (g i)) ∧ RateLE φ T (fun i=> fderiv ℝ (V i) (g i)) b) : RateLE φ T (fun i=> V i (x i)-V i (y i)) (b+a):=by
    intro r hr; obtain ⟨s,hs,hs'⟩:= exists_between (lt_sub_iff_add_lt.mpr hr); let B i:= closedBall (y i) ‖x i-y i‖; have hx i:y i∈B i:=mem_closedBall_self (norm_nonneg _)
    have hh : ∀ᶠ i in φ, ∀ z,z∈B i → DifferentiableAt ℝ (V i) z ∧ ‖fderiv ℝ (V i) z‖ ≤ Real.exp (s*T i):=most_often (fun z hp=> (hk z hp|>.1).and (hk z hp|>.2 s hs)) hx
    filter_upwards [hh,hz (r-s) (by linarith)] with i hi hk
    refine ((convex_closedBall (y i) ‖x i-y i‖).norm_image_sub_le_of_norm_fderiv_le (fun z hx=>(hi z hx).1) (fun z hx=>(hi z hx).2) (hx i) (show x i∈B i by unfold B; rw [mem_closedBall,dist_eq_norm])).trans (?_); exact (mul_le_mul_of_nonneg_left hk (Real.exp_nonneg _)).trans_eq (by rw [← Real.exp_add,sub_mul]; ring_nf)
-- hT unused
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J]

lemma operator (F : (I→E4) →L[ℝ] ℂ) : ‖F‖ ≤ ∑ i : I × Axis, ‖F (kindle i.fst i.snd)‖:= by
    refine F.opNorm_le_bound (by positivity) fun u=>?_ ; have h : ∑ i : I×Axis, u i.1 i.2 • kindle (I:=I) i.1 i.2 = u:=by ext i a; rw [Fintype.sum_prod_type]; simp [kindle,Pi.single_apply,apply_ite]
    conv_lhs=>rw [← h]
    rw [map_sum]; simp_rw [map_smul]; refine (norm_sum_le _ _).trans (?_); rw [Finset.sum_mul]; refine Finset.sum_le_sum fun i _=>?_ ; rw [norm_smul,mul_comm]; exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le (u i.1) i.2).trans (norm_le_pi_norm u _)) (norm_nonneg _)

lemma rateOperator {F:E→ (I→ E4) →L[ℝ] ℂ}(hT:Tendsto T φ atTop)(hf:∀ b c,RateLE φ T (fun i=> F i (kindle b c)) a) : RateLE φ T F a :=
    (RateLE.sum (S:=Finset.univ) hT (fun p:I×Axis=>fun _=> (hf p.1 p.2).norm)).of_norm_le (Eventually.of_forall fun i=> operator _)

lemma cloud_jump (S:Schedule){k : E→ℕ}{x:E→ I→ E4}(hT:Tendsto T φ atTop)(hk:Height S φ T k a):∃ g:E→ I→ Cover, (∀ i, Screen (S.gridPoint (k i) ∘ g i)) ∧ RateLE φ T (fun i=> (S.gridPoint (k i) ∘ g i) - x i) (-a):=by
    let K : ℤ:= Cloud.count I ∅
    let g i:= Cloud.grid ∅ (S.a (k i)) (x i) (fun _ _=>0); let f (i):= S.gridPoint (k i) ∘ g i
    have h(i): Screen (f i):= Cloud.screened ∅ _ (S.a_pos _) _ _; refine ⟨g,h,RateLE.of_norm_le ((((RateLE.const (2:ℝ) hT).mul (hk.mesh.pays hT)).mul (RateLE.const (K:ℝ) hT)).mono (by simp)) ?_⟩
    refine Eventually.of_forall fun i=>?_ ; let z:= S.a (k i); have hx(b:I)(a:Axis): ‖((f i-x i) b) a‖ ≤ z*K:= Cloud.close_zero ∅ z (S.a_pos _) (x i) b a; have hp : 0 ≤ z*(K:ℝ):= mul_nonneg (S.a_pos (k i)|>.le) ((Int.cast_pos.mpr (Cloud.count_pos _))|>.le)
    rw [mul_assoc]; apply (pi_norm_le_iff_of_nonneg (mul_nonneg zero_le_two hp)).2; intro b
    let d:= (f i-x i) b; have he: ‖d‖^2 ≤ 4*(z*K)^2:=by
       rw [EuclideanSpace.real_norm_sq_eq]
       apply le_trans (Finset.sum_le_sum (g:=fun i:Axis=> (z*K)^2) (fun i hi=>?_ )); simp
       rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx b _ ) _
    change ‖d‖≤_; nlinarith only [he,hp]
end YM.OPE

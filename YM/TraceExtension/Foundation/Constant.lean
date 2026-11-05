import YM.TraceExtension.Foundation.Dilate

set_option autoImplicit false
noncomputable section
namespace YM.Trace
open StressFlux Labels Gauge Maxwell Tensor Analysis Function Set MeasureTheory Table Climb
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff
variable {G : Gauge} {L : Register G}

private def block (x : E4) (a i : Axis) : ℝ:= basis a i-2*x a*x i* (‖x‖^2)⁻¹
private def scaleP (x : E4):ℝ:=4*normal*(‖x‖^2)⁻¹^2
private lemma block_orth {x : E4} (hx : x ≠ 0) (a b : Axis) : ∑ i, block x a i * block x b i=basis a b := by
   let D(a:Axis):=2*x a *(‖x‖^2)⁻¹
   have ht (a i : Axis) : block x a i=basis a i-D a*x i:=by unfold block D; ring
   simp_rw [ht,show ∀ i : Axis,(basis a i-D a*x i)*(basis b i-D b*x i)=basis a i*(basis b i)-basis a i*(D b*x i)-basis b i*(D a*x i)+(D a*D b)*(x i)^2 from fun i=> by ring]
   have hi:=EuclideanSpace.real_norm_sq_eq x; have hz:‖x‖^2≠0:= pow_ne_zero 2 (norm_pos_iff.mpr hx).ne'
   rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,← Finset.mul_sum, ← hi]
   have hF (a : Axis) (f : Axis→ℝ):∑ i,basis a i * f i = f a:= by simp [basis_eq,ite_mul]
   rw [hF a (basis b).ofLp,hF,hF,show basis b a=basis a b by simp [eq_comm]]; unfold D; field_simp; ring

private lemma entry {x : E4} (hx : x ≠ 0) (a b i j : Axis): bareCurl a b i j x = scaleP x*(block x a i*block x b j-block x a j*block x b i) := by
   simp only [bareCurl,Pi.sub_apply,Bare.opp_grad hx,second_Green hx,block,scaleP]
   simp +decide only [basis_eq]; split_ifs <;> subst_vars <;> ring

lemma curl_squares {x : E4} (hx : x ≠ 0) : (∑ a, ∑ b, ∑ i, ∑ j, bareCurl a b i j x ^ 2) = (scaleP x)^2*24 := by
   let K:=block x; let D:=scaleP x
   have ht (a b i) : ∑ j,bareCurl a b i j x ^2 =
       D^2*(K a i^2+K b i^2- 2*K a i*K b i*basis a b) := by
      have he (j) : bareCurl a b i j x ^ 2 =D^2*(K a i^2 * (K b j*K b j) + K b i^2*(K a j*K a j)- (2*K a i*K b i)*(K a j*K b j)) := by rw [entry hx]; unfold D K; ring
      simp_rw [he,← Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_add_distrib]; simp_rw [← Finset.mul_sum]; rw [block_orth hx,block_orth hx,block_orth hx]; simp
   have hu(a b) : (∑ i, ∑ j,bareCurl a b i j x ^2) = D^2*(2-2*(basis a b)^2) := by
      simp_rw [ht,← Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_mul, mul_assoc]; simp_rw [← Finset.mul_sum]; simp_rw [pow_two]
      rw [block_orth hx,block_orth hx,block_orth hx]; norm_num [basis_eq]
   simp_rw [hu,D,← Finset.mul_sum]; norm_num +decide [Fin.sum_univ_four]

open Wick
/-- `n=2` with both signed Wick field legs. -/
lemma wick_norm {x : Points 2} (hx : x 0≠x 1) : quad (Bel L) x (fun _=> fromPol (Bel L) (square4 G)) =
       ↑(3*(G.lieDim:ℝ)/Real.pi^4* (‖x 0-x 1‖^8)⁻¹ : ℝ):= by
   have he : x∈conf _ := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
   let y:=x 0-x 1; have hy : y≠0:= sub_ne_zero.mpr hx
   let Z(a b : Axis):=reduceEq (pair G a b a b).val
   let S:=reduceEq (square4 G).val; let U:=∑ i, ∑ j, Z i j
   have hS : S=(1/4:ℝ) • U := by
      unfold S U square4; rw [show ∀ p : Label G 4, reduceEq (((1/4:ℝ) • p).val)=(1/4:ℝ) • reduceEq p.val from fun p=> (reduceEq.toLinearMap.restrictScalars ℝ).map_smul ..]; simp only [AddSubmonoidClass.coe_finsetSum,map_sum]; rfl
   have hv (a b i j:Axis): head x (Z i j) (Z a b)=G.lieDim * ↑(2*(bareCurl a b i j y)^2 : ℝ) := by unfold Z; rw [chains_read G hx]; unfold chains y; push_cast; ring
   rw [free_polynomials (p:=fun _=>square4 G) he]
   rw [show (fun _ : Fin 2=> reduceEq (square4 G).val)= ![S,S] from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩), ← head_at,hS,show head x _ ((1/4:ℝ) • U)=(1/4:ℝ) • head x ((1/4:ℝ) • U) U from ((head x _).restrictScalars ℝ).map_smul ..,head_at,← tail_at,show tail x U ((1/4:ℝ) • U) = (1/4:ℝ) • tail x U U from ((tail x _).restrictScalars ℝ).map_smul ..]
   rw [tail_at,← head_at]; unfold U; simp_rw [map_sum,head_at,← tail_at,map_sum,tail_at,←head_at]; simp_rw [hv,Complex.ofReal_mul,← Finset.mul_sum]
   -- sums cast
   simp_rw [← Complex.ofReal_sum,curl_squares hy,Complex.real_smul]; unfold scaleP; field_simp
   unfold normal y; push_cast; ring
end YM.Trace

import YM.AnalyticNext.GRID_STOP_ATTENUATION.Coarrival.Oper
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Path
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.Planned.PRIMARY_INTEGRAL_295.Gala
/-!
 # Comparison from sized slots at W₁ and 0 true torus patch.Perturb input f even if not Canon. one additional derivative up to PPE order. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Function Filter Finset Set Lattice Wilson RG Pressure
open JointLoad JointLoad.Heir Next.Foundations MultiNext.SignedSource Lyre
open WardBin.Lies
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{c f:Side}{j k n:ℕ}{x y : ℝ}{B: BudgetPoint}{w o:Site f}{b: Directions G f}
lemma higher {z : Directions G f} (hf:Sized x z B w)(h:x≤ y):Sized y z B w:= ⟨hf.1.trans h,fun i=>(hf.2 i).trans (mul_le_mul_of_nonneg_right h (Lyre.width_pos ..).le)⟩
section raised
variable (R:Rights G n){A:Config G f→ℝ}{X : Support f}{v u:Fin k→ Directions G f}{z:ℝ}
variable (hc:B.Regular X A)(hp:B.supBounds o X A z)(hθ:Sized x b B o)(hv:∀ i,Sized y (v i) B o)(hw:1 ≤ y)(hn:k+1 ≤ n)(hm:n≤ B.order)
    (hr:∀ e, Mom.needed X e→ ‖b e‖ ≤ 1 ∧ Lyre.width B o e ≤ 1)(h: ∀ u∈ Set.Icc (0:ℝ) 1, Healthy B.threshold X (increment 1 (u • b)))
include R hc hp hθ hv hw hn hm hr h
lemma fledgling : ‖iteratedFDeriv ℝ k (A ∘ increment 1) b v - iteratedFDeriv ℝ k (A ∘ increment 1) 0 v‖ ≤ x*y^n*R.fee*z:=by
  let q:=A ∘ increment 1; let p (t:ℝ):=iteratedFDeriv ℝ (k+1) q (t • b) (Fin.cons b v)
  have he(a:ℝ)(ha:a∈Set.Icc (0:ℝ) 1): ContDiffAt ℝ (↑(k+1:ℕ)) q (a • b):=(Heir.along hc (h a ha)).of_le (Nat.cast_le.mpr (hn.trans hm))
  have hz:=hp.1; have hQ:=R.large; have hx:=hθ.1
  let H:=x*y^n*R.fee*z
  have hh (a:ℝ)(ha:a∈Icc (0:ℝ) 1): ‖p a‖ ≤ H:= by
     have he : ∀ i:Fin (k+1), Sized ((Fin.cons x (fun _ : Fin k=> y) : Fin (k+1) → ℝ) i) ((Fin.cons b v : Fin (k+1) → Directions G f) i) B o:= Fin.cases (by simpa using hθ) (fun i=>by simpa using hv i)
     apply (R.moves 1 (a • b) (Fin.cons b v) _ hn (hn.trans hm) hc hp (h _ ha) _ he).trans
     · rw [Fin.prod_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; unfold H; gcongr; omega
     intro e ht; rw [Pi.smul_apply,norm_smul_of_nonneg ha.1]; exact ⟨mul_le_one₀ ha.2 (norm_nonneg _) (hr e ht).1,(hr e ht).2⟩
  have hf:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun t:ℝ=>iteratedFDeriv ℝ k q (t • b) v) (fun x hx=> (along_deriv b v x (he x hx)).hasDerivWithinAt) hh (convex_Icc ..) (show 0∈Icc (0:ℝ) 1 by simp) (show 1∈Icc (0:ℝ) 1 by simp); simpa only [zero_smul,one_smul,sub_zero,norm_one,mul_one] using hf
omit hr h hθ
include v
private lemma uprising (ha:∀ i,Sized x (u i - v i) B o) (hx:0≤x)(he:x≤y):
    ‖iteratedFDeriv ℝ k (A ∘ increment 1) 0 u - iteratedFDeriv ℝ k (A ∘ increment 1) 0 v‖ ≤ (2:ℝ)^n*(x*y^n*R.fee*z) := by
  let F:=A ∘ increment 1; let T:=iteratedFDeriv ℝ k F 0
  let y'(s:Finset (Fin k)):= T (s.piecewise (u-v) v)
  let C:=x*y^n*R.fee*z; have hk:= Nat.le_of_lt hn; have hQ:=R.large; have hz:=hp.1; have hC:0≤ C:=by unfold C; positivity
  have h (s:Finset (Fin k))(hs:s≠∅): ‖y' s‖ ≤ C:=by
    obtain ⟨i,hi⟩:= Finset.nonempty_iff_ne_empty.mpr hs
    let f':=Function.update (fun _:Fin k=> y) i x
    have hF:∏ t,f' t=x * ∏ t∈Finset.univ.erase i,f' t:= by rw [← prod_erase_mul _ _ (Finset.mem_univ i),show f' i=x from update_self ..,mul_comm _ x]
    refine (R.born 1 _ f' hk (hk.trans hm) hc hp (one_healthy _ _ B.threshold_pos.le) (fun j=> ?_)).trans ?_
    · by_cases he':j=i
      · subst j; simp [hi,Finset.piecewise,f']; exact ha i
      unfold f'; rw [update_of_ne he']; by_cases h':j∈ s<;> simp [h',Finset.piecewise]; exact higher (ha j) he; exact hv j
    have hp: ∏ j∈ Finset.univ.erase i,f' j= y^(k-1):= (Finset.prod_congr rfl (g:=fun _=> y) (fun j h=>update_of_ne (by simpa using! (Finset.mem_erase.mp h).1) ..)).trans (by simp)
    rw [hF,hp]; unfold C; gcongr; omega
  have hh:T u-T v = ∑ j∈Finset.univ.erase ∅, y' j :=by
    calc
     T u-T v = ∑ j,y' j-T v:=by rw [← T.map_add_univ (u-v) v]; simp -- def y'
     _ = _ := by rw [← sum_erase_add _ y' (Finset.mem_univ ∅)]; unfold y'; simp only [Finset.piecewise_empty,add_sub_cancel_right]
  change ‖T u- T v‖ ≤ _; rw [hh];
  refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=>C) (fun j hj=>h _ (Finset.mem_erase.mp hj).1)).trans ?_)
  simp only [Finset.sum_const,nsmul_eq_mul]; refine mul_le_mul_of_nonneg_right ?_ hC
  have he : (Finset.univ.erase (∅:Finset (Fin k))).card ≤ 2^k:= by simp
  exact_mod_cast he.trans (Nat.pow_le_pow_right (by norm_num) hk)
include hθ h hr
lemma migrant (ha:∀ i,Sized x (v i-u i) B o)(hh:∀ i,Sized y (u i) B o)(he:x≤y):
    ‖iteratedFDeriv ℝ k (A ∘ increment 1) b v - iteratedFDeriv ℝ k (A ∘ increment 1) 0 u‖ ≤ (1+(2:ℝ)^n)*(x*y^n*R.fee*z):=by
   refine (norm_sub_le_norm_sub_add_norm_sub _ (iteratedFDeriv ℝ k (A ∘ increment 1) 0 v) _).trans ?_
   rw [add_mul,one_mul]; exact add_le_add (Cub.fledgling R hc hp hθ hv hw hn hm hr h) (Cub.uprising R hc hp hh hw hn hm ha hθ.1 he)
end raised
end YM.PhysicalNext.Repeat.Cub

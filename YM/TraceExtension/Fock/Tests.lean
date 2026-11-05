import YM.TraceExtension.Fock.Regions

/-! Basic receipts on the comparison domain; don't abstract it by assumptions
 about charged fields or point values. We specify only matrix elements on
 vacuum vectors (using explicit W(h) read on those coherent amplitudes).
 No requirement comparing mixed connected insertion hierarchy for all W's. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {m n:ℕ}
lemma pol_squared (p:Space3)(i j:SpaceAxis) : ∑ k:SpaceAxis, polarization p i k * polarization p k j= polarization p i j:=by
    let d(a b:SpaceAxis):ℂ:= if a=b then 1 else 0; let a(i:SpaceAxis):ℂ:=p i; let g:= (((‖p‖^2:ℝ)⁻¹):ℂ); have he(i j): polarization p i j=d i j-a i*a j*g:=by unfold polarization d polarization.ifk a g;push_cast; ring
    have hh(i)(f:SpaceAxis→ℂ): ∑ k, d i k*f k=f i:=by simp [d,ite_mul]
    have hr(j)(f:SpaceAxis→ℂ):∑ k,f k*d k j=f j:=by simp[d,mul_ite]
    simp_rw [he];
    have hx(k:SpaceAxis): (d i k-a i*a k*g)*(d k j-a k*a j*g)= d i k*d k j-d i k*(a k*a j*g)-(a i*a k*g)*d k j+ (a i*a j*g^2)*a k^2:=by ring
    simp_rw [hx,Finset.sum_add_distrib, Finset.sum_sub_distrib, hh i (fun k=>d k j),hh i (fun k=>a k*a j*g), hr j (fun k=>a i*a k*g), ← Finset.mul_sum]
    rw [show ∑ k:SpaceAxis,a k^2=(↑(‖p‖^2:ℝ):ℂ) from ?_]
    · by_cases he:p=0
      · unfold g; simp [he]
      have hz:‖p‖ ≠ 0:=norm_ne_zero_iff.mpr he; unfold g; push_cast; field_simp; ring
    unfold a; simp [← Complex.ofReal_pow, ← Complex.ofReal_sum,← EuclideanSpace.real_norm_sq_eq]
lemma oneP (h:TestList m)(i:Label m)(p:Space3):
    ∑ k:SpaceAxis, polarization p i.2 k * testPhoton h (i.1,k) p= testPhoton h i p:=by
    unfold testPhoton; simp_rw[Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _=> ?_; simp_rw[← mul_assoc, ← Finset.sum_mul]; rw [pol_squared]
lemma geometryP (h:TestList m)(j:Tags m n) (z: Mom n)(t:Fin n) :
    ∑ k:SpaceAxis, polarization (z t) (j t).2 k* pureTest (fun _=> h) (update j t ((j t).1,k)) z = pureTest (fun _=>h) j z:=by
    let v(i):= testPhoton h (j i) (z i); let R:=∏ i∈Finset.univ.erase t,v i; have hh(y:Label m): pureTest (fun _=>h) (update j t y) z=testPhoton h y (z t)* R:=by
        unfold pureTest; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t), update_self]; congr 1; exact Finset.prod_congr rfl fun i hi=> by unfold v; rw [update_of_ne (Finset.mem_erase.mp hi).1]
    simp_rw [hh,← mul_assoc,← Finset.sum_mul]; rw[oneP]; exact Finset.mul_prod_erase _ v (Finset.mem_univ t)
lemma trailP (h:TestList m)(j:Tags m n): ∀ᵐ p∂photons n, coherent h (insertP ⟨n,j⟩ p)=(Real.exp (-qnorm h/2):ℂ) * unweighted h (insertP ⟨n,j⟩ p):=by
    let f:=unweighted_lp h; let y:ℂ:= Real.exp (-qnorm h/2)
    have hh: ∀ᵐ k∂sumMeasure m, coherent h k=y* unweighted h k:=by
        filter_upwards [Lp.coeFn_smul y (bareCoherent h), MemLp.coeFn_toLp f] with k hi hu; rw [← hu]; exact hi
    exact (sum_ae _).1 hh _
lemma coherent_iswave(h:TestList m): PhysicalWave (coherent h):=by
    constructor
    · intro n j i; filter_upwards [trailP h j,ae_all_iff.mpr (fun k:SpaceAxis=> trailP h (update j i ((j i).1,k)))] with p hp hz
      let R:ℂ:=I^n/(↑(Real.sqrt (n.factorial:ℝ)):ℂ); let s:ℂ:= Real.exp (-qnorm h/2)
      simp_rw [hp,hz]; change s*(R*pureTest _ _ _) = _; rw [← geometryP h j p i, Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _=>by unfold unweighted; dsimp only; unfold R; ring
    intro n s r; let e := MeasurableEquiv.piCongrLeft (fun _=>Space3) r.symm; have hv : MeasurePreserving e (photons n) (photons n) := measurePreserving_piCongrLeft (fun _=>photon) r.symm
    filter_upwards [trailP h s, hv.quasiMeasurePreserving.tendsto_ae.eventually (trailP h (s ∘ r))] with p hp he
    change _= coherent h _; have hz:e p=p ∘ r:= permutes r p; rw [hz] at he; rw [hp,he]; unfold unweighted; dsimp only; congr 2; exact Equiv.prod_comp r (fun i=>testPhoton h (s i) (p i))
lemma unweighted_norm (h:TestList m): ‖bareCoherent h‖^2=Real.exp (qnorm h):=by
    let S:= sumMeasure m; let U:= bareCoherent h; let F:=unweighted h; have hf:= unweighted_lp h
    have hp : (∫ p, ‖F p‖^2 ∂ S)=Real.exp (qnorm h):=by
       apply HasSum.unique (show HasSum (fun n=> (n.factorial:ℝ)⁻¹ * (qnorm h)^n) _ from ?_) ?_
       · apply HasSum.sigma (sum_hasSum (fun i=> ‖F i‖^2) hf.norm.integrable_sq)
         intro k; rw [show qnorm h^k=∑ (i:Tags m k), ∫ p,‖pureTest (fun _=>h) i p‖^2 ∂photons k from Eq.symm (by rw[pure_sum];simp)]
         simp_rw[F,unweighted,norm_mul, mul_pow,integral_const_mul]; rw [Finset.mul_sum]; norm_num [norm_div]; exact hasSum_fintype _
       simpa [Real.exp_eq_exp_ℝ,div_eq_mul_inv,mul_comm] using! NormedSpace.expSeries_div_hasSum_exp (qnorm h)
    have he: (∫ i, star (U i)*U i ∂S)=(↑(Real.exp (qnorm h)):ℂ):=by
       rw [← hp, ← integral_complex_ofReal]; apply integral_congr_ae; filter_upwards[MemLp.coeFn_toLp hf] with k hk; change U k=_ at hk; rw[hk,square_scalar]
    rw[← lp_inner,inner_self_eq_norm_sq_to_K] at he; change (↑‖U‖:ℂ)^2 = _ at he; rw[← Complex.ofReal_pow] at he; exact Complex.ofReal_inj.mp he
lemma coherent_norm (h:TestList m): ‖coherent h‖=1:=by
    apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : 2≠0)).mp
    rw [coherent,norm_smul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le, unweighted_norm,pow_two,← Real.exp_add, ← Real.exp_add, show -qnorm h/2+-qnorm h/2+qnorm h=0 from by ring]; simp
end YM.TraceExtension.Photons

import YM.FullVolume.Amp.Ledge
/- Contract board input already analytic.Weave bundles. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp.Beam
open Filter Function Finset Set RG Push.AbsoluteSums Ray
open scoped Topology BigOperators Classical ContDiff
variable {X Z:Type}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X][NormedAddCommGroup Z][NormedSpace ℝ Z][CompleteSpace Z]{Y:Type}[SeminormedAddCommGroup Y][NormedSpace ℝ Y]
variable {v:ℝ}
open UniformSpace
lemma listen (E:Y→L[ℝ] Z)(he:Isometry E)(hd:DenseRange E)(f:sun→Y→ X)(h:∀ s:sun,∀ i j:Y, f s (i-j)=f s i-f s j) (hc: 0≤v)(hF:∀ x:Y,∃ P:Beam X,‖P‖≤ v*‖x‖ ∧ ∀ s:sun,f s x=read _ s P) (B:Beam Z)(g:sun→ Y)(hg:∀ s:sun,E (g s)=read _ s B):∃ P:Beam X,‖P‖≤ v*‖B‖ ∧ ∀ s:sun,f s (g s)= read _ s P:=by
   choose T ht hX using hF
   have hh(i j:Y):T (i-j)=T i-T j:=by
       apply Beam.soul; intro s; change read _ s _ = read _ s _; rw [map_sub,←hX,←hX,←hX,h]
   let U:=AddMonoidHom.ofMapSub _ hh; let P:= AddMonoidHom.toRealLinearMap U (AddMonoidHomClass.continuous_of_bound U v ht)
   let A:=P.extend E; have hm(y):A (E y)=T y:= P.extend_eq hd he.isUniformInducing _
   have hr : ‖A‖≤ v:=ContinuousLinearMap.opNorm_le_bound _ hc (isClosed_property hd (isClosed_le A.continuous.norm (continuous_const.mul continuous_norm)) (fun x=>by rw [hm,he.norm_map_of_map_zero (map_zero _)]; exact ht x))
   exact ⟨song A B,(songN ..).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _)),fun i=>by rw [songL,←hg,hm,hX]⟩
-- up Coin as Pi. price bound ℓ sum per axes. E.world.P.So.
variable {ι:Type}[Fintype ι]
def lineup (f:ι→ Beam X) : Beam (ι → X):=by
   let y(i:ℕ) (k:ι):= f k i
   apply Subtype.mk y; apply memℓp_gen; simp only [ENNReal.toReal_one,Real.rpow_one]; apply Summable.of_nonneg_of_le (fun j=>norm_nonneg _) _ (summable_sum (f:=fun k (j:ℕ)=> ‖f k j‖) (s:=Finset.univ) (fun i _=> (paid (f i)).summable)); intro i; exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j hj=>norm_nonneg _)).mpr fun j => Finset.single_le_sum (fun j _=> norm_nonneg _) (Finset.mem_univ j)
lemma lineupN (f:ι→ Beam X): ‖lineup f‖≤∑ i,‖f i‖:=by
   let t:= lineup f; have ht (i:ι)(j:ℕ) : t j i=f i j:=rfl
   calc
    _=∑' i, ‖t i‖:=(paid t).tsum_eq.symm
    _≤∑' j, ∑ i, ‖f i j‖:=(paid t).summable.tsum_le_tsum (fun i => (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _=>norm_nonneg _)).mpr fun j=> Finset.single_le_sum (fun j _=>norm_nonneg _) (Finset.mem_univ j)) (summable_sum (s:=Finset.univ) (fun i _=> (paid (f i)).summable))
    _=_:=by rw [Summable.tsum_finsetSum _ ]; simp_rw [fun i=>(paid (f i)).tsum_eq]; intro i _; exact (paid (f i)).summable
lemma lineupL (f:ι→ Beam X)(s:sun)(i:ι): read _ s (lineup f) i=read _ s (f i):=by
   let A: (ι→ X)→L[ℝ] X:=ContinuousLinearMap.proj i; apply HasSum.unique (f:=(fun j:ℕ=> s.val^j • f i j)) _ (spar (f i) (abs_le.mpr s.property)); exact (A.hasSum (spar (lineup f) (abs_le.mpr s.property)))
-- product dense
lemma podium (E:Y→L[ℝ] X) (he:Isometry E)(hd:DenseRange E) :∃ P: (ι→Y)→L[ℝ] ι→ X, Isometry P ∧ DenseRange P ∧ ∀ x i, P x i= E (x i):=by
    let P: (ι→Y)→L[ℝ] ι→ X:= ContinuousLinearMap.pi fun i=> E.comp (ContinuousLinearMap.proj i)
    refine ⟨P,AddMonoidHomClass.isometry_of_norm _ ?_,?_ ,fun _ _=> rfl⟩
    · intro i; have hp(k): ‖P i k‖=‖i k‖:=he.norm_map_of_map_zero (map_zero _) _; refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j=> by rw [hp]; exact norm_le_pi_norm ..) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j=> by rw [←hp]; exact norm_le_pi_norm ..)
    intro y; refine Metric.mem_closure_iff.mpr fun ε h=> ?_
    have he(i): ∃ x:Y, dist (y i) (E x)<ε:= by obtain ⟨z,⟨x,rfl⟩,ht⟩:=Metric.mem_closure_iff.mp (hd (y i)) ε h; exact ⟨x,ht⟩
    choose x hx using he; exact ⟨P x,⟨x,rfl⟩, (dist_pi_lt_iff h).mpr hx⟩
end YM.FullVolume.Amp.Beam

import YM.OPE.Orbits.Profile
import YM.OPE.Orbits.Inclusions

/-!
# Real/covariant separated OPE at every fixed horizon

Uses the TRUE hierarchy with calibrated Final and its same views (including
the unselected one). Includes complete tested discrepancy/ground algebra,
phase mixtures, bounded-mass joint profiles. Coefficients `R.coef` independent
of truncation, viewer, exterior, in the real homogeneous-complement basis
`R.basis`; vector version in actual filtration spaces `R.fresh` with the
O(4) and reality intertwinings. Reader constructed once using the accepted
`YM.OPE` package. No unique projection or identification of all possible
prescriptions is needed. Exact projection compatibility under `cutTest`, but
no claim of convergence as horizon→infinity.

All these estimates are foundational power-with-arbitrary-slack estimates,
not using or asserting the matching-dependent sharpening. The strengthened
quantitative cost in arbitrary exterior subpower layers is `balance_rate` /
`all_rate` and `algebra_rate`. These include the signed discrepancy inherited
from `Exchange` / `adjustment_cost` not a perturbative truncation (via the
actual `Base'` and replicated arrays). There is no change of the order of limits
of `YM.OPE.Single` / `through_final`; polarizer manipulations are statements of
its continuum laws. We never send non-generic placements through the lattice
point-limit theorem. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Filter Function Set Table Extraction MeasureTheory
open scoped Topology ContDiff Classical Matrix.Norms.Frobenius BigOperators
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book} (U:Spec.Final C F S)
    (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (h:Services C F S){I J:Type}[Fintype I][Fintype J]{d:I→ℕ}{e:J→ℕ} (v:Labels S d)(w:Labels S e)
variable {M η δ ε:ℝ}(hM:0≤ M)(hη:0<η)(hδ:0<δ) (hε:0< ε)(D:ℕ)

/-- Kernel formula integrated against a character measure. A whole Table on
this mixture need not be reconstructed; these are exactly linear correlations
of the fixed physical choices. -/
def phaseMoment (μ:Measure U.α.space.X)(z:Loc I J): ℂ:= ∫ i, whole (U.α.ensemble i) z.1 v z.2.2 w ∂μ
def phaseSum (μ:Measure U.α.space.X)(D:ℕ)(z:Loc I J):ℂ := ∑ j:Fin (D+1), ∑ i:R.channels j.val, (R.coef j.val i z.1 v z.2.1) * ∫ χ,whole (U.α.ensemble χ) (sole z.2.1) ((sole (R.actor j.val i)):Labels S (fun _:Unit=>j.val)) z.2.2 w ∂μ
lemma same_in_mixture (μ:Measure U.α.space.X) [IsFiniteMeasure μ] (D:ℕ)(z:Loc I J) (hy:Injective (beside (sole z.2.1) z.2.2)): phaseSum U R v w μ D z = ∫ i, uponDiscount U R D v w z (some i) ∂μ:=by
    let f (m:ℕ)(i:R.channels m)(χ:U.α.space.X):=whole (U.α.ensemble χ) (sole z.2.1) ((sole (R.actor m i)):Labels S (fun _:Unit=>m)) z.2.2 w
    have hf(m i):Continuous (f m i):= ?_
    let g (m:ℕ) i:ℂ:=R.coef m i z.1 v z.2.1
    have hh(m i): Integrable (fun χ=>g m i*f m i χ) μ:=Continuous.integrable_of_hasCompactSupport (μ:=μ) (by fun_prop) (HasCompactSupport.of_compactSpace _)
    change _=∫ i,∑ j:Fin (D+1),∑ k:R.channels j.val, g j.val k*f j.val k i ∂μ
    have hv(j:ℕ): Integrable (fun i=>∑ k:R.channels j,g j k*f j k i) μ:= integrable_finsetSum _ (fun i hi=>hh ..)
    rw [integral_finsetSum _ (fun j (_:j∈Finset.univ)=> hv j.val)]; apply Finset.sum_congr rfl; intro i hi
    rw [integral_finsetSum _ (fun j hj=>hh _ _)]; exact Finset.sum_congr rfl (fun j hj=> integral_const_mul _ _ |>.symm)
    have hs:= U.phase.phase.decomposition.weak (viewing U (beside (sole z.2.1) z.2.2) (beside (names (d:=fun _:Unit=>m) (sole (R.actor m i))) (names w))); exact hs.congr (fun Q=> (character_sees U Q _ _ hy).trans ((whole_observed ..).symm))
include hM hη hδ hε h
lemma probability_mixtures : ∀ᶠ r:ℝ in 𝓝[>]0,∀ z∈ FitsOn I J M η δ r,∀ μ:Measure U.α.space.X, IsProbabilityMeasure μ → ‖phaseMoment U v w μ z-phaseSum U R v w μ D z‖ ≤ costRemainder D d ε r:=by
   filter_upwards [estimates_weighted (K:=U.α.space.X) U R h v w hM hη hδ hε D 1,profile_scope U R h v w hM hη hδ hε D] with r hr ht z hz μ hμ
   have h₁:∫ s, ‖(1:ℂ)‖ ∂μ ≤ (1:ℝ):=by simp
   have ho:=same_in_mixture U R v w μ D z (ht.2 z hz|>.1.2.2)
   obtain ⟨-,_,_,ht0,hbound⟩ :=(hr μ (fun _=>(1:ℂ)) (fun _=>z) aemeasurable_const (integrable_const _) h₁ (ae_of_all _ (fun i f=>hz))).1 id aemeasurable_id
   rw [← one_mul (costRemainder ..)]; refine Eq.trans_le (congr_arg norm (?_)) hbound
   simp only [Function.comp_apply, id_eq, one_mul] at ht0 ⊢; rw [← ht0,phaseMoment,ho]; rfl
omit hM hη hδ hε h

/-- Foundation stage proposition with one Reader quantified before demands. -/
structure Foundation (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin): Prop where
    coefficients (I:Type)[Fintype I] (d:I→ℕ)(v:Labels S d)(M η ε:ℝ) : M ≥ 0 → η > 0 → ε>0 → ∀ (j:ℕ)(i:R.channels j),∀ᶠ (r:ℝ) in 𝓝[>]0, ∀ (x:I→E4)(o:E4), WithinRoom r M η x o → ‖R.coef j i x v o‖≤r^((j:ℝ)-weight d-ε)
    discrepancy (I J:Type)[Fintype I][Fintype J](d:I→ℕ)(e:J→ℕ)(v:Labels S d)(w:Labels S e)(M η c ε:ℝ): M ≥ 0 → η > 0 → c > 0 → ε>0 → ∀ D:ℕ, ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (x:I→E4)(o:E4)(y:J→E4), WithinRoom r M η x o→ClearOf o y c→ Injective (beside x y) ∧ Injective (beside (sole o) y) ∧ ‖algebraError U R x o v y w D‖ ≤ r^((D:ℝ)+1 - weight d- ε) ∧ ∀ i:Viewers U, ‖formula U R x o v y w D i‖ ≤ r^((D:ℝ)+1- weight d-ε)

include h
lemma produce : Foundation U R :=
    ⟨fun _ _ _ v _ _ _ hM hη hε j i=> coefficient_separated U R h v hM hη hε j i, fun _ _ _ _ _ _ v w _ _ _ _ hM hη hc hε j=> quantitative_separated U R h v w hM hη hε j hc⟩

omit h in
/-- One actual Spec.Final with all the above estimates. The theorem also
provides `Services` for additional mixed exterior estimates or refinements. -/
theorem foundation (G:Gauge)(hh:G.Simple)(f:Extraction.Order) : ∃ (C:Family G)(g:Extraction.Order)(S:Table C.book), Services C (f.refine g) S ∧ ∃ (U:Spec.Final C (f.refine g) S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin), Foundation U R:=by
    obtain ⟨C,-,g,S,hs,⟨U⟩⟩:=through_final (b:=1) hh zero_lt_one f
    let T:=U.phase.transport; obtain ⟨p,hp⟩:= Prescription.chosen U.room.kernel.laws.toSymmetric T.injection
    let R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin := ⟨p,hp,U.room.kernel,T.injection,T.rights,T.spots⟩
    exact ⟨C,g,S,hs,U,R,produce U R hs⟩
end YM.OPE.Orbits

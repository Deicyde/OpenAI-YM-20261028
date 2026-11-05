import YM.TraceExtension.Fock.SpectrumGap
import YM.TraceExtension.Dyadic

/-! `prop:nfock` inference on the fixed vacuum. Also works by evaluation
inside the ambient full free Fock space on coming from gauge-invariant sector. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {G : Gauge} {C : Family G} {a : Extraction.Order} {S : Table C.book}
    {F : Spec.Final C a S} {μ : Measure E4} {m n : ℕ} {U : F.action.operators.H →ₗᵢ[ℂ] Ambient m} {A : ℝ}
variable (X : Comparison F U) (hL : LocalTest F U) (hp : TraceSpectrum F μ) (Y : Form F U) (ha : 0<A) (ht : EuclideanAsymptotic F A)
include X hp
lemma burn (i : Index m) (j : ℕ) : sectorsMass (Y.wave i) (barrel i.fst j) ≤ tally μ (((i.fst:ℝ)+1)*clock j) := by
    let B := ((i.fst:ℝ)+1) * clock j; unfold tally; rw [parts Y X hp B]
    refine le_trans (b:=sectorsMass (Y.wave i) (band B)) ?_ (ENNReal.le_tsum i); apply measure_mono
    intro p he; change time _ ≤ _; rw [total_energy];
    refine (Finset.sum_le_card_nsmul _ _ (clock j) (fun t _ => he t)).trans ?_
    dsimp only [B]; simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right (by linarith) ((show 0 ≤ (1:ℝ) from zero_le_one).trans (clock_ge j))
include ha ht
lemma consumes (i : Index m) : Evaporates (Y.wave i) where
    cover j := by
        obtain ⟨K,k,hK,h⟩ := hp.slab
        apply lt_of_le_of_lt (burn X hp Y i j); exact (h _ (one_le_mul_of_one_le_of_one_le (by simp) (clock_ge j))).trans_lt ENNReal.ofReal_lt_top
    top := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (log_high hp ha.le ht (i.fst+1) (by simp)) (fun _=> zero_le) (fun k=> mul_le_mul_right (burn X hp Y i k) _)
include hL
lemma finite_particles (i : Index m) : (4 ≤ i.1 → Y.wave i=0) ∧ width (Y.wave i) := by
    obtain ⟨d,hd⟩ := Y.surface X hp i
    rcases i with ⟨n,t⟩
    apply local_eigen _ (consumes X hp Y ha ht _) hd; exact local_position X hL hp Y t
lemma saturate : False := by
    obtain ⟨Y⟩ := form_exists X hp
    choose d hd using fun i:Index m=> (finite_particles X hL hp Y ha ht i).2
    let s : Finset (Index m) := Finset.sigma (Finset.range 4) fun i => Finset.univ
    let D : ℝ≥0:=∑ i∈s,d i
    apply does_not_fit hp ha ht D; refine Eventually.of_forall fun k=> ?_
    unfold tally; rw [parts Y X hp,tsum_eq_sum (s:=s)]
    · rw [show (↑D:ℝ≥0∞)=∑ i∈s,↑(d i) from ENNReal.ofNNReal_finsetSum ..,Finset.sum_mul];
      apply Finset.sum_le_sum; intro i hi; apply le_trans (b:=sectorsMass (Y.wave i) (barrel i.1 k))
      · apply measure_mono; intro p hm j; change time _ ≤ _ at hm; rw [total_energy] at hm; exact (Finset.single_le_sum (fun t _ => norm_nonneg (p t)) (Finset.mem_univ j)).trans hm
      exact (hd i k).trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (clock_ge k) (by decide : 6≤7))) _)
    intro i hi; rw [(finite_particles X hL hp Y ha ht i).1 (by simpa [s] using hi), sectors_zero]; rfl

omit hp X hL in
theorem excludes (X : Comparison F U) : ¬ Nfl F U := fun h => by
    obtain ⟨μ,hμ,-⟩ := traceSpectrum_exists F
    exact saturate X (from_nfl h) hμ ha ht

omit hp hL in
/-- Convenient invariant version. If comparing into an invariant subspace,
vacuum matrix elements may test just projected coherent vectors (the
vacuum-to-state components at these `W`, as obtained also by averaging).
Statement with *any* projection self-adjoint, acting identically on the image.
This proves there is not even such a preserving realization; no statement
about abstract nets. -/
theorem excludes_projected (P : Ambient m →L[ℂ] Ambient m) (he : P.adjoint=P) (hs : ∀ x, P (U x)=U x) :
    ¬ (∀ (f : Test4) (h : TestList m),
        HasCompactSupport ⇑f → (∀ i, HasCompactSupport ⇑(h i)) →
        (∀ i, Probe.bar (h i)=h i) → (∀ i, Fields.causal f (h i)) →
        inner ℂ (P (coherent (-h))) (signal F U f)=inner ℂ (signal F U (Probe.bar f)) (P (coherent h))) := by
    intro hw
    apply excludes ha ht X
    intro f g hx hg hH hP
    have hv := hw f g hx hg hH hP
    unfold signal at *
    conv at hv => lhs; rw [← ContinuousLinearMap.adjoint_inner_right,he,hs]
    conv at hv => rhs; rw [← ContinuousLinearMap.adjoint_inner_left,he,hs]
    exact hv
end YM.TraceExtension.Photons

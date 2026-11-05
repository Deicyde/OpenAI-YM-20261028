import YM.TraceExtension.Fock.Polar

/-! The vacuum-matrix locality condition at a fixed field smearing,
and extracting the photon amplitudes from coherent vectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical

variable {G : Gauge} {C : Family G} {a : Extraction.Order} {S : Table C.book}
    {F : Spec.Final C a S} {μ : Measure E4} {m n : ℕ} {U : F.action.operators.H →ₗᵢ[ℂ] Ambient m}

def OnVac (f : Test4) (x y : Ambient m) := ∀ h : TestList m,
    (∀ i, HasCompactSupport ⇑(h i)) → (∀ i, Probe.bar (h i)=h i) → (∀ i, Fields.causal f (h i)) →
    inner ℂ (coherent (-h)) x=inner ℂ y (coherent h)

/-- Tiny-region variant suffices: Weyls in any number of compact spacelike-separated-from-f
boxes; can require tests only with f confined to a ball of choice (eventually shrink it anyway). -/
def LocalTest (F : Spec.Final C a S) (U : F.action.operators.H →ₗᵢ[ℂ] Ambient m) :=
    ∃ r : ℝ, 0 < r ∧ ∀ (f : Test4), HasCompactSupport ⇑f → tsupport f ⊆ Metric.ball 0 r → OnVac f (signal F U f) (signal F U (Probe.bar f))
lemma from_nfl (h : Nfl F U) : LocalTest F U :=
    ⟨1,one_pos,fun f hf _ v => h f v hf⟩

abbrev sectionFn (x : Ambient m) (i : Index m) (p : Mom i.fst) := x (insertP i p)
lemma wave_lp (x : Ambient m) (i : Index m) : MemLp (sectionFn x i) 2 (photons i.1) := by
    have h : MemLp x 2 ((photons i.1).map (insertP i)) := (Lp.memLp x).mono_measure (Measure.le_sum _ i)
    have hs : AEStronglyMeasurable (sectionFn x i) (photons i.1) := ((Lp.stronglyMeasurable x).comp_measurable (embedP _).measurable).aestronglyMeasurable
    exact (memLp_norm_iff (μ:=photons i.1) hs).1 ((memLp_two_iff_integrable_sq hs.norm).2 ((embedP i).integrable_map_iff.1 h.norm.integrable_sq))
lemma product_int {X : Type*} [MeasurableSpace X] {μ : Measure X} {g h : X → ℂ} (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) :
    Integrable (fun i=>star (g i)*h i) μ := by
    have hv : MemLp (fun i => star (g i)) 2 μ := hg.mono hg.1.star (ae_of_all _ fun i => (norm_star _).le)
    exact hv.integrable_mul hh

/-- pairing linear in the electric test -/
def earlier (g : Fin n→ TestList m) (x : Ambient m) :=
    ∑ t : Tags m n, ∫ p, star (sectionFn x ⟨n,t⟩ p)*pureTest g t p ∂photons n
lemma inner_series (h : TestList m) (x : Ambient m) : HasSum (fun n : ℕ => (I^n/(↑(Real.sqrt (n.factorial:ℝ)):ℂ)) * earlier (fun _ : Fin n => h) x)
    (inner ℂ x (bareCoherent h)) := by
    rw [lp_inner]
    have he := MemLp.coeFn_toLp (unweighted_lp h)
    have hh : (fun i => star (x i)*bareCoherent h i) =ᵐ[sumMeasure m] (fun i => star (x i)*unweighted h i) :=
       he.mono fun i hi => by dsimp only; rw [show bareCoherent h i = _ from hi]
    rw [integral_congr_ae hh]
    apply HasSum.sigma (sum_hasSum _ (product_int (Lp.memLp x) (unweighted_lp h)))
    intro n
    have hx t : (∫ p, star (x (insertP ⟨n,t⟩ p))*unweighted h (insertP ⟨n,t⟩ p) ∂photons n) =
       (I^n/(↑(Real.sqrt (n.factorial:ℝ)):ℂ)) * (∫ p, star (sectionFn x ⟨n,t⟩ p)*pureTest (fun _=>h) t p ∂photons n) := by
        rw [← integral_const_mul]; congr! 1; ext p; dsimp only [unweighted,sectionFn,insertP]; ring
    unfold earlier; rw [Finset.mul_sum]
    simp_rw [hx]; exact hasSum_fintype _
lemma qnorm_neg (h : TestList m) : qnorm (-h)=qnorm h := by
    rw [← neg_one_smul ℂ h]; unfold qnorm; simp only [photon_smul,norm_mul,norm_neg,norm_one,one_mul]
lemma inner_series_out (h : TestList m) (x : Ambient m) : HasSum
    (fun n : ℕ => (I^n/(↑(Real.sqrt (n.factorial:ℝ)):ℂ)) * star (earlier (fun _ : Fin n => h) x))
    (inner ℂ (bareCoherent (-h)) x) := by
    have h1 (n : ℕ) (t : Tags m n) p : pureTest (fun _=>-h) t p = (-1:ℂ)^n * pureTest (fun _=>h) t p := by
        unfold pureTest; simp_rw [← neg_one_smul ℂ h,photon_smul,Finset.prod_mul_distrib]; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    have ht (n : ℕ) : earlier (fun _ : Fin n=>-h) x = (-1:ℂ)^n * earlier (fun _: Fin n =>h) x := by
        unfold earlier; simp_rw [h1, mul_left_comm (star _), integral_const_mul]; rw [Finset.mul_sum]
    have hy := (inner_series (-h) x).star
    rw [Complex.star_def,inner_conj_symm] at hy
    convert! hy using 1; ext n; simp only [ht,Complex.star_def,map_mul,map_div₀,map_pow,map_neg,map_one,Complex.conj_ofReal,conj_I]
    have he : (-I)^n * (-1:ℂ)^n=I^n := by rw [← mul_pow]; simp
    conv_lhs => rw [← he]
    ring
lemma constant_scale (h : TestList m) (b : ℝ) (x : Ambient m) (n : ℕ) :
    earlier (fun _ : Fin n=> (↑b:ℂ)•h) x = (↑b:ℂ)^n*earlier (fun _ : Fin n=>h) x := by
        have he (t : Tags m n) p : pureTest (fun _=> (↑b:ℂ) • h) t p = (↑b:ℂ)^n * pureTest (fun _=>h) t p := by
          unfold pureTest; simp_rw [photon_smul,Finset.prod_mul_distrib]; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
        unfold earlier; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
        rw [← integral_const_mul]; congr! 1; ext p; rw [he]; ring

/-- Sector equality at diagonal real test -/
lemma sectors (f : Test4) (x y : Ambient m) (hf : OnVac f x y) (h : TestList m)
    (hp : ∀ i, HasCompactSupport ⇑(h i)) (hR : ∀ i, Probe.bar (h i)=h i) (hw : ∀ i, Fields.causal f (h i)) (n : ℕ) :
    star (earlier (fun _ : Fin n => h) x)=earlier (fun _ : Fin n => h) y := by
    let D k := star (earlier (fun _ : Fin k => h) x) - earlier (fun _ : Fin k => h) y
    let s (k:ℕ) := (I^k/(↑(Real.sqrt (k.factorial:ℝ)):ℂ))*D k
    have hh a (ha : 0<a) : HasSum (fun k : ℕ => (↑(a:ℝ):ℂ)^k * s k) 0 := by
        let H := (↑a:ℂ) • h
        have hs (i) : tsupport ⇑(H i) ⊆ tsupport ⇑(h i) := tsupport_smul_subset_right (fun _ => (↑a:ℂ)) (h i)
        have he : inner ℂ (bareCoherent (-H)) x=inner ℂ y (bareCoherent H) := by
            have hz := hf H (fun i => (hp i).of_isClosed_subset (isClosed_tsupport _) (hs i))
              (fun i => by simp [H,hR]) (fun i q hQ u hu => hw i q hQ u (hs i hu))
            simp only [coherent,qnorm_neg,inner_smul_left,inner_smul_right,conj_ofReal] at hz
            exact mul_left_cancel₀ (by norm_cast; exact (Real.exp_pos _).ne') hz
        have ht := (inner_series_out H x).sub (inner_series H y); rw [he,sub_self] at ht
        refine HasSum.congr_fun ht ?_
        intro k; dsimp only [H,s,D]; rw [constant_scale,constant_scale]; simp only [star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]; ring
    have ht := powers_unique s hh n
    have he : D n=0 := (mul_eq_zero.mp ht).resolve_left (div_ne_zero (pow_ne_zero _ I_ne_zero)
       (by norm_cast; positivity))
    exact sub_eq_zero.mp he
end YM.TraceExtension.Photons

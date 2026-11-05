import YM.TraceExtension.Wick.Massive

/-!
Two point kernels of local polynomial fields with finitely many elementary
mass-shell covariances and finite differential orders. Specify a slightly
larger comparison class, closed under finite contractions (any coefficients,
need not themselves satisfy positivity, can include unit). Every monomial
in spacetime momentum from the differential numerator for an elementary
propagator belongs here: split as p₀^k times a continuous *homogeneous*
polynomial P in the spatial components. In `Mode` we even drop polynomiality of
those homogeneous functions. Evaluating a finite Wick polynomial two point
uses finite products of elementary mass-shell two point kernels (pairing signs,
color contractions etc absorbed in the arbitrary complex coefficients).
`Track.read` fixes this precisely as testing on total momentum; derivative
and transform normalization constants can all be absorbed in the coefficients.
We will test necessary identities even just on momentum cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Wick
open Set Filter Function Metric MeasureTheory Measure Mink Boundary
open scoped Topology BigOperators NNReal ENNReal Classical

structure Mode where
    mass : ℝ≥0
    j : ℕ
    k : ℕ
    P : Space3→ℝ
    cont : Continuous P
    power (v : Space3) (r:ℝ) (hr : 0<r) : P (r • v)=r^j*P v
namespace Mode
variable (L : Mode)
def onboard (p : Space3) := position p (freq L.mass ‖p‖)
def density (p : Space3) := 1/(2*freq L.mass ‖p‖)* (freq L.mass ‖p‖)^L.k * L.P p
def kernel (s : ℝ) (p : Space3) := density L p * Real.exp (-s*time (L.onboard p))
@[fun_prop] lemma on_cont : Continuous L.onboard := by
    apply Mink.divide.symm.continuous.comp (continuous_id.prodMk ?_); fun_prop

abbrev S2 := sphere (0:Space3) 1
def angular := ∫ p:S2, L.P p ∂(volume (α:=Space3)).toSphere

private def wheel := homeomorphUnitSphereProd Space3
private abbrev radius (p : Ioi (0:ℝ)) := p.val
private def radial (s x : ℝ) :=
    1 / (2*freq L.mass x) * freq L.mass x ^ L.k * x^L.j * Real.exp (-s*freq L.mass x)

private lemma turning : MeasurePreserving wheel
    ((volume (α:=Space3)).comap Subtype.val) ((volume (α:=Space3)).toSphere.prod (volumeIoiPow 2)) := by
    convert MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd (volume (α:=Space3)) using 1
    · rfl
    rw [show Module.finrank ℝ Space3=3 from finrank_euclideanSpace_fin]
private lemma revolve (s) (p : S2) (v : Ioi (0:ℝ)) : L.kernel s (wheel.symm (p,v)) = L.P p * radial L s v.val := by
    have he : ‖p.val‖=1 := by simp
    change L.kernel s (v.val • p.val) = _
    unfold kernel density onboard radial; rw [L.power _ _ v.property,norm_smul,Real.norm_of_nonneg (le_of_lt v.property), he, mul_one,YM.time_position]; ring
private lemma swing (s : ℝ) (p : ({0}ᶜ:Set Space3)) :
    L.kernel s p=L.P (wheel p).fst * L.radial s (wheel p).2 := by
    rw [← L.revolve s _ _,Prod.eta,Homeomorph.symm_apply_apply]
private lemma rays (s : ℝ) (x : Ioi (0:ℝ)) :
    Real.toNNReal ((x:ℝ)^2) • L.radial s x = (2:ℝ)⁻¹ * stream L.mass L.j L.k s x := by
    have hv : 0<x.val := x.property
    rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity),smul_eq_mul]; unfold radial stream
    have he := freq_pos L.mass hv; field_simp; ring
private lemma rad_int (s : ℝ) (hp : 0<s) : Integrable (L.radial s ∘ Subtype.val) (volumeIoiPow 2) := by
    unfold volumeIoiPow ENNReal.ofReal
    apply (integrable_withDensity_iff_integrable_smul (μ:=(volume (α:=ℝ)).comap Subtype.val) (f:=fun x:Ioi (0:ℝ)=>Real.toNNReal (x.val^2)) (by fun_prop)).mpr
    have hv := integrableOn_iff_comap_subtypeVal measurableSet_Ioi |>.1 (((stream_int _ _ _ _ hp) : IntegrableOn (stream L.mass L.j L.k s) _ _).const_mul (2:ℝ)⁻¹)
    exact hv.congr (ae_of_all _ fun x=> (rays L s x).symm)
lemma field_int (s : ℝ) (hp : 0<s) : Integrable (L.kernel s) := by
    have hc : MeasurableSet ({0}ᶜ:Set Space3):= (measurableSet_singleton _).compl
    let f : S2→ℝ:= fun p=>L.P p.val
    haveI : CompactSpace S2 := isCompact_iff_compactSpace.mp (isCompact_sphere ..)
    have hv : Integrable f (volume (α:=Space3)).toSphere := (show Continuous f from L.cont.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← restrict_compl_singleton (μ:=volume) (0:Space3),← IntegrableOn, integrableOn_iff_comap_subtypeVal hc]
    exact ((turning.integrable_comp_emb wheel.measurableEmbedding).2 (hv.mul_prod (rad_int L s hp))).congr (ae_of_all _ fun u=> (swing L s u).symm)
lemma field_value (s : ℝ) : (∫ p : Space3,L.kernel s p)=L.angular*(2:ℝ)⁻¹ * moment L.mass L.j L.k s := by
    let f : S2→ℝ:= L.P ∘ Subtype.val
    calc
       _ = ∫ p : ({0}ᶜ:Set Space3), L.kernel s p ∂volume.comap Subtype.val := by rw [integral_subtype_comap]; simp ; measurability
       _ = ∫ p : S2 × Ioi (0:ℝ), f p.1 * L.radial s p.2 ∂(volume (α:=Space3)).toSphere.prod (volumeIoiPow 2) := by
           apply Eq.trans _ (turning.integral_comp wheel.measurableEmbedding _); apply integral_congr_ae; exact ae_of_all _ (swing L s)
       _ = _ := by
           rw [integral_prod_mul f (fun x:Ioi (0:ℝ)=> L.radial s x)]
           change L.angular * _ = _; rw [mul_assoc]; congr 1
           unfold volumeIoiPow ENNReal.ofReal
           rw [integral_withDensity_eq_integral_smul]
           · simp_rw [rays]; rw [integral_const_mul, integral_subtype_comap measurableSet_Ioi]; rfl
           exact (measurable_subtype_coe.pow_const _).real_toNNReal
end Mode

structure Track where
    n : ℕ
    modes : Fin n→ Mode
namespace Track
variable (W : Track)
-- absolute Fourier functions, relative variables tested
abbrev Config := Fin W.n → Space3

def order (p : W.Config) : E4 := ∑ i,(W.modes i).onboard (p i)
def weight (p : W.Config) := ∏ i,(W.modes i).density (p i)
def tariff (ψ : E4→ℂ) (p : W.Config) := W.weight p • ψ (W.order p)
def read (ψ : E4→ℂ) := ∫ p,W.tariff ψ p
@[fun_prop] lemma order_cont : Continuous W.order := by unfold order; fun_prop

/-- Imaginary-axis kernel. -/
def euclidean (s : ℝ) := ∏ i, ∫ p, (W.modes i).kernel s p
lemma shaped (s : ℝ) : ∏ i, ∫ p,(W.modes i).kernel s p=W.euclidean s := rfl
lemma wave (p : W.Config) (s : ℝ) : weight W p * Real.exp (-s*time (W.order p)) = ∏ i,(W.modes i).kernel s (p i) := by
    unfold order weight Mode.kernel; rw [Finset.prod_mul_distrib,← clockL_at,_root_.map_sum,Finset.mul_sum,Real.exp_sum]; rfl
lemma damped_int (s : ℝ) (hs : 0<s) : Integrable (fun p : W.Config=>weight W p * Real.exp (-s*time (W.order p))) := by
    simp_rw [wave]; exact Integrable.fintype_prod (fun i => (W.modes i).field_int s hs)
lemma damp_reads (s : ℝ) : read W (fun p=> ↑(Real.exp (-s*time p))) = (↑(euclidean W s):ℂ) := by
    unfold read tariff euclidean
    rw [show (fun p => W.weight p • (↑(Real.exp (-s*time (W.order p))):ℂ)) = (fun p:W.Config => ((↑(∏ i,(W.modes i).kernel s (p i))):ℂ)) by
        ext1; rw [← wave,Complex.ofReal_mul]; rfl, integral_complex_ofReal]
    congr 1; exact integral_fintype_prod_eq_prod (μ:=fun i: Fin W.n=>volume) (fun i=> (W.modes i).kernel s)
lemma moments_expand : Expands W.euclidean := by
    let f i := fun s:ℝ=> ∫ p, (W.modes i).kernel s p
    have he (i : Fin W.n) : Expands (f i) := by
        let m := W.modes i
        rw [show f i=(m.angular*(2:ℝ)⁻¹) • (moment (m.mass:ℝ) m.j m.k) from funext (fun s=> m.field_value s)]; exact Expands.scale (moment_expands _ _ _) _
    have hv (x : Finset (Fin W.n)) : Expands (∏ i ∈ x,f i) := by
        induction x using Finset.induction_on with
        | empty=> rw [Finset.prod_empty]; exact own one_board
        | insert i s h ih=> rw [Finset.prod_insert h]; exact (he i).mult ih
    convert hv Finset.univ using 1; ext p; rw [Finset.prod_apply]; rfl
end Track
end YM.TraceExtension.Wick

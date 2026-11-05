import YM.Dash.Limits
import YM.OPE.Levy.Panel
/-!
# Two-field coercivity from the exact reflected label test

Use **second slot** with field adjoint (antilinear in the second, i.e. maybe
conjugate of some OS convention). Tilted uses *not* assumed Hermitian. Work
with the real part and do not assume positivity at finite cutoff. This allows
changing coordinates to/from mixed high-horizon columns at projection costs
without proximity of the physical tilt to the actual reflected position in any
*fixed* labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram
open Function Set Filter OPE.Levy
open scoped Topology BigOperators
section bilinear
variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
             [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ X]
variable {ι : Type*} {f : Filter ι}

-- finite-dimensional *estimate*, not a physical-price assumption
abbrev RealForm (V X : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] := V →L[ℝ] X →L[ℝ] ℝ
abbrev toForm (P : V →ₗ[ℝ] X →ₗ[ℝ] ℝ) : RealForm V X :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp P)

-- Work.A06 variant with arbitrary filter
lemma clm_criterion (v : ι → V →L[ℝ] X) (P : V →L[ℝ] X)
    (h : ∀ x, Tendsto (fun k => v k x) f (𝓝 (P x))) : Tendsto v f (𝓝 P) := by
  classical
  let b := Module.finBasis ℝ V
  let I := Fin (Module.finrank ℝ V)
  let L : (I → X) →ₗ[ℝ] V →L[ℝ] X := LinearMap.toContinuousLinearMap.toLinearMap.comp (b.constr ℝ).toLinearMap
  have he (g : V→L[ℝ] X) : L (fun i => g (b i)) = g := by
    apply ContinuousLinearMap.coe_injective
    exact b.ext fun i => b.constr_basis ..
  have hh := L.continuous_of_finiteDimensional.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr
    (show ∀ i,Tendsto (fun k => (fun j : I => v k (b j)) i) f (𝓝 ((fun j : I => P (b j)) i)) from fun i => h _))
  convert hh using 1
  · funext u; exact (he _).symm
  rw [he P]
lemma formsLimits (T : RealForm V X) (P : ι → RealForm V X)
    (h : ∀ x y, Tendsto (fun i => P i x y) f (𝓝 (T x y))) :
    Tendsto P f (𝓝 T) := clm_criterion P T fun x => clm_criterion (fun i => P i x) (T x) (h x)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ X] in
theorem stayNear {P : RealForm V X} {Q : ι → RealForm V X}
    (h : Tendsto Q f (𝓝 P)) {k : ℝ} (he : 0 < k) : ∀ᶠ i in f, ‖Q i-P‖ ≤ k := by
  have ht := (Metric.tendsto_nhds (a:=P) (u:=Q) (f:=f))
  apply (ht.mp ?_ k he).mono
  · intro i hi
    exact (dist_eq_norm (Q i) P) ▸ hi.le
  exact h

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ X] in
lemma resid (T : RealForm V X) (x : V) (y : X) :
    |T x y| ≤ ‖T‖ * ‖x‖ * ‖y‖ := ((T x).le_opNorm y).trans
      (mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg _))
def coercive (T : RealForm V V) (δ : ℝ) := ∀ x, δ*‖x‖^2 ≤ T x x
omit [FiniteDimensional ℝ V] in
lemma absorb (T P : RealForm V V) (δ δ' : ℝ) (hp : coercive T δ) (hr : ‖P-T‖ ≤ δ-δ') : coercive P δ' := by
  intro x
  have h : T x x-P x x ≤ (δ-δ')*‖x‖^2 := by
    have hy := (le_abs_self ((T-P) x x)).trans (resid _ _ _)
    have he := mul_le_mul_of_nonneg_right hr (sq_nonneg ‖x‖)
    rw [norm_sub_rev P T] at he
    change T x x-P x x ≤ _ at hy
    linarith only [hy, he]
  linarith only [h, hp x]

lemma margin (T : RealForm V V) (hp : ∀ x ≠ 0, 0 < T x x) : ∃ δ : ℝ, 0<δ ∧ coercive T δ := by
  classical
  let P := Metric.sphere (0:V) 1
  by_cases he : Nontrivial V
  swap
  · haveI := not_nontrivial_iff_subsingleton.mp he
    exact ⟨1,zero_lt_one,fun x=> by simp [Subsingleton.elim x (0:V)]⟩
  have hP x (hx : x∈P) : ‖x‖=1 := mem_sphere_zero_iff_norm.mp hx
  let f x:= T x x
  have h := FiniteDimensional.proper_real V
  obtain ⟨x,hx,hX⟩ := isCompact_sphere (0:V) 1|>.exists_isMinOn (NormedSpace.sphere_nonempty.mpr zero_le_one) (show ContinuousOn f P from (T.continuous.clm_apply continuous_id).continuousOn)
  have h' := hp x (fun hh => by have h:=hP x hx; rw [hh,norm_zero] at h; exact zero_ne_one h)
  refine ⟨f x,h',fun y=>?_⟩
  by_cases hy : y=0
  · simp [hy]
  let t:= ‖y‖
  have ht : 0 < t := norm_pos_iff.mpr hy
  let z := t⁻¹ • y
  have hz : ‖z‖=1 := by rw [show ‖z‖ = ‖t⁻¹‖ * ‖y‖ from norm_smul _ _, Real.norm_of_nonneg (inv_pos.mpr ht).le]; exact inv_mul_cancel₀ ht.ne'
  have hh := hX (mem_sphere_zero_iff_norm.mpr hz)
  change f x * t^2 ≤ f y
  have hY : t • z = y := by dsimp only [z]; rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  change f x ≤ f z at hh
  rw [← hY]; unfold f; rw [map_smul T,smul_apply,map_smul (T z),smul_eq_mul,smul_eq_mul]
  change f x * t^2 ≤ t * (t * f z)
  nlinarith only [mul_le_mul_of_nonneg_right hh (sq_nonneg t)]

end bilinear

variable {G : Gauge} {L : Register G} (Q : Table L)
-- uses Lean ℝ restriction of scalars. Should be same for Q.field defeq; fill.
section
variable {d : ℕ}

/-- use the same register reflection as Final, second slot. Real part even
if geometry doesn't enforce positivity. -/
def glass (h : Q.RealSpin)(d : ℕ)(x : Points 2) : RealForm (Q.Field d) (Q.Field d) := by
  let J := Q.adj h d timeAxis
  let T := linear₂ (Q.classMoment Q (fun _=>d) x)
  letI : FiniteDimensional ℝ (Q.Field d) := Module.Finite.trans ℂ _
  let M : Module.End ℝ (Q.Field d) :=
    { toFun := J
      map_add' a b := J.map_add _ _
      map_smul' a b := by
        change J (a • b)=a • J b
        rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),LinearMap.map_smulₛₗ]
        simp }
  let g (v : Q.Field d) := Complex.reCLM.toLinearMap.comp ((T v).restrictScalars ℝ|>.comp M)
  exact toForm ({ toFun := g
                  map_add' := fun v w => LinearMap.ext fun z => by simp [g]
                  map_smul' := fun a v => LinearMap.ext fun w => by simp [g] }
                  : Q.Field d →ₗ[ℝ] Q.Field d →ₗ[ℝ] ℝ)
lemma glass_reads (h : Q.RealSpin) (p : Points 2) (v w : Q.Field d):
    glass Q h d p v w = (Q.classMoment Q (fun _=>d) p ![v, Q.adj h d timeAxis w]).re := rfl
end
end YM.SharpGram

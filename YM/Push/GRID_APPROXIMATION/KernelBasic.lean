import YM.Next.EXTRACTION.Tails
import YM.Push.GRID_APPROXIMATION.Bounds

/-!
# One pullback by the actual block kernel

Measurable and sup controlled independent of the finite volume `IsKernel.bound`.
For the pointwise operation don't need positivity of β. Equivariance
hypotheses from `Calendar.blocks` when needed. No normalization of sources.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson Set Filter MeasureTheory Function
open scoped Topology BigOperators

variable {G : Gauge} {c f : Side} (S : StepData c f) (β : ℝ)

/-- Conditional back to the fine field, for bounded measurable observables. -/
def back (F : Config G c → ℂ) (U : Config G f) :=
    ∫ V, (S.density β U V:ℂ) * F V ∂prior G c

variable {F F' : Config G c → ℂ} {S β}

lemma den_env (h : S.IsKernel β G) : Envelope (fun x : Config G f × Config G c => S.density β x.1 x.2) := by
  obtain ⟨C,H⟩ := h.bound
  exact ⟨h.meas,C,fun x => (Real.norm_of_nonneg (h.positive x.1 x.2)).trans_le (H x.1 x.2)⟩

lemma back_integrand (h : S.IsKernel β G) (he : Envelope F) :
    Envelope (fun x : Config G f × Config G c => (S.density β x.1 x.2:ℂ) * F x.2) :=
  (den_env h).ofReal_env.mulC (he.comp_env measurable_snd)

lemma back_slice (h : S.IsKernel β G) (he : Envelope F) (U : Config G f) :
    Envelope (fun V => (S.density β U V:ℂ) * F V) :=
  by
    have hm : Measurable (fun V : Config G c => (U,V)) := measurable_const.prodMk measurable_id
    have hh := (back_integrand h he).comp_env hm
    exact hh

lemma back_bound (h : S.IsKernel β G) (hm : Measurable F) (C : ℝ) (hF : ∀ U, ‖F U‖ ≤ C)
    (U : Config G f) : ‖back S β F U‖ ≤ C := by
  have ht : Integrable (fun V => (S.density β U V:ℂ) * F V) (prior G c) :=
    (back_slice h (show Envelope F from ⟨hm,C,hF⟩) U).integrableC _
  unfold back
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    _ ≤ ∫ V, S.density β U V * C ∂prior G c := integral_mono ht.norm ((h.integrable U).mul_const _) fun V => by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (h.positive U V)]
      exact mul_le_mul_of_nonneg_left (hF V) (h.positive U V)
    _ = _ := by rw [integral_mul_const,h.total,one_mul]

lemma back_env (h : S.IsKernel β G) (he : Envelope F) : Envelope (back S β F) := by
  refine ⟨(back_integrand h he).meas.stronglyMeasurable.integral_prod_right'.measurable,?_⟩
  obtain ⟨C,H⟩ := he.cost; exact ⟨C,back_bound h he.meas _ H⟩

lemma back_const (h : S.IsKernel β G) (z : ℂ) : back (G:=G) S β (fun _ => z) = (fun _ => z) := by
  funext U
  rw [back,integral_mul_const,show (∫ V, ((S.density β U V : ℝ):ℂ) ∂prior G c) = (((∫ V, S.density β U V ∂prior G c) : ℝ):ℂ) from integral_ofReal (𝕜:=ℂ) (f := S.density β U),h.total,Complex.ofReal_one,one_mul]

lemma back_add (h : S.IsKernel β G) (he : Envelope F) (hf : Envelope F') :
    back S β (F+F') = back S β F + back S β F' := by
  funext U
  simp only [back,Pi.add_apply,mul_add]
  exact integral_add ((back_slice h he U).integrableC _) ((back_slice h hf U).integrableC _)



lemma back_star (_ : S.IsKernel β G) (_ : Envelope F) : back S β (fun V => star (F V)) =
    fun U => star (back S β F U) := by
  funext U; simp only [back,Complex.star_def,←integral_conj,map_mul,Complex.conj_ofReal]

/-- Equivariance under simultaneous transforms in the two variables with
probability Haar preserved in V. No translation/randomization of individual
shared tags. -/
lemma back_natural (h : S.IsKernel β G) (he : Envelope F) (t : Config G f → Config G f) (s : Config G c → Config G c)
    (hs : MeasurePreserving s (prior G c) (prior G c)) (hq : ∀ U V, S.density β (t U) (s V)=S.density β U V) :
    back S β (F ∘ s) = (back S β F) ∘ t := by
  funext U
  let g (V) := (S.density β (t U) V:ℂ)*F V
  have hm := integral_map (μ:=prior G c) (φ:=s) (f:=g) hs.aemeasurable (back_slice h he (t U)).meas.aestronglyMeasurable
  rw [hs.map_eq] at hm
  change (∫ V, _ ∂(prior G c)) = ∫ V, g V ∂prior G c
  rw [hm]; simp only [g,hq,comp_apply]

/-- Adjoint relation before normalization. Rightmost integrals over actual
fine probability Haar. -/
lemma back_dual (h : S.IsKernel β G) (he : Envelope F) (g : Config G f → ℂ) (hg : Integrable g (prior G f)) :
    (∫ V, S.push β g V * F V ∂prior G c) = ∫ U, g U * back S β F U ∂prior G f := by
  let Q (U : Config G f) (V : Config G c) := (S.density β U V • g U) * F V
  have ht : Integrable (Function.uncurry Q) ((prior G f).prod (prior G c)) := by
    obtain ⟨C,H⟩ := (he.comp_env (measurable_snd (α:=Config G f))).cost
    exact (StepData.push_integrand h _ hg).mul_bdd (he.meas.comp measurable_snd).aestronglyMeasurable
      (Eventually.of_forall H)
  have hh U V : g U * ((S.density β U V:ℂ) * F V) = Q U V := by simp [Q,Complex.real_smul]; ring
  simp_rw [StepData.push, back, ←integral_mul_const, ←integral_const_mul,hh]
  exact (integral_integral_swap ht).symm
end YM.Push.GridApprox

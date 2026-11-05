import Mathlib.Analysis.ODE.ExistUnique
import YM.Analysis.Homogeneous
import YM.PCalc.Band
import YM.Source.Local




/-!
# Produce H link flow in the image (even disconnected)

Construct in exponential coordinate neighborhood. Extend via uniqueness
on overlapping intervals; no compactness for continuation needed: left
invariance lets local interval work for ANY initial along path. Work for
C^1 coefficients (applies to any finite jet and h). Parameter analyticity
near fixed parameters is separate from existence.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Source.Hol
open Lattice RG Wilson Precision Set Function Filter MeasureTheory  Labels
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators NNReal

variable {G : Gauge}

def Leads (I : Set ℝ) (u : ℝ → G.El) (A : ℝ → G.Color) := ∀ b∈I,
    HasDerivAt (fun x => G.mat (u x)) (G.mat (u b)*G.colorMat (A b)) b

lemma agree {I : Set ℝ} (h : IsOpen I) (hc : Convex ℝ I) {b : ℝ} (hb : b∈I) {u v : ℝ → G.El} {A : ℝ → G.Color} (hu : Leads I u A)
    (hv : Leads I v A) (hx : u b = v b) : EqOn u v I := by
  let w (t : ℝ) := G.mat (u t * (v t)⁻¹)
  have he : ∀ i∈I, HasDerivAt w 0 i := by
    intro i hi; unfold w; simp only [G.mat_mul, G.mat_inv]
    simpa [Pi.mul_def,G.colorMat_skew,mul_assoc] using! (hu i hi).mul (hv i hi).star
  have hh : ∀ i∈I,w i=w b := by
    intro i hi
    exact h.is_const_of_deriv_eq_zero hc.isPreconnected (fun i hi => (he i hi).differentiableAt.differentiableWithinAt) (fun i hi => (he i hi).deriv) hi hb
  intro i hi
  apply mul_inv_eq_one.mp; apply G.mat_injective
  simpa [w,hx] using hh i hi

section
variable (G)

def dilate (a : G.Color × G.Color) := G.plog (G.mat (G.lieExp a.1) * G.mat (G.lieExp a.2))

def chartField (b : G.Color) := fderiv ℝ (fun v => dilate G (b,v)) 0

lemma dilate_form : ContDiffAt ℝ ω (dilate G) 0 := by
  have hf : ContDiffAt ℝ ω (fun x : G.Color × G.Color => G.mat (G.lieExp x.1)*G.mat (G.lieExp x.2)) 0 :=
    ((G.exp_jet.comp contDiff_fst).mul (G.exp_jet.comp contDiff_snd)).contDiffAt
  apply ContDiffAt.comp (f:=fun x => _) _ _ hf
  simp only [Prod.fst_zero, Prod.snd_zero,G.mat_lieExp_zero,G.mat_one,mul_one]
  exact G.plog_diff

lemma chartField_smooth : ContDiffAt ℝ ω (chartField G) 0 :=
    ContDiffAt.fderiv (f:=fun p x => dilate G (p,x)) (g:=fun _=>0) (dilate_form G) contDiffAt_const (by simp)

lemma stages : ∀ᶠ a in 𝓝 (0:G.Color),∀ b : G.Color,
    (fderiv ℝ (G.mat ∘ G.lieExp) a) (chartField G a b)=G.mat (G.lieExp a)*G.colorMat b := by
  let f (x y) := G.lieExp x*G.lieExp y
  have hg : ∀ᶠ a : G.Color × G.Color in nhds 0, G.lieExp (dilate G a)=f a.1 a.2 := by
    have he : Continuous fun a : G.Color × G.Color => f a.1 a.2:=by unfold f; fun_prop
    have hf := he.continuousAt.tendsto (x:=0); change Tendsto _ _ (nhds (f 0 0)) at hf
    rw [show f 0 0=1 by simp [f]] at hf
    exact hf.eventually G.plog_right
  have hx := mem_nhds_prod_iff.mp (hg.and ((dilate_form G).eventually (by simp)))
  obtain ⟨s,hs,t,ht,h⟩ := hx
  filter_upwards [hs,G.plog_left] with i hi hv b
  have hb : (0:G.Color) ∈ t := mem_of_mem_nhds ht
  have he (k) (hk : k∈t) := h (show (i,k)∈s ×ˢ t from ⟨hi,hk⟩)
  have hO : (fun v => G.mat (f i v)) =ᶠ[𝓝 0] (fun v => (G.mat ∘ G.lieExp) (dilate G (i,v))) := by
    filter_upwards [ht] with r hr; rw [comp_apply, (he r hr).1]
  have hD : DifferentiableAt ℝ (fun v => dilate G (i,v)) 0 := ((he 0 hb).2.differentiableAt (by simp)).comp _ ((differentiableAt_const i).prodMk differentiableAt_id)
  have ht : dilate G (i,0) = i := by unfold dilate; rw [G.mat_lieExp_zero,G.mat_one,mul_one]; exact hv
  have hF := (G.exp_jet.differentiable (by simp) (dilate G (i,0))).hasFDerivAt.comp (f:=fun v => dilate G (i,v)) 0 hD.hasFDerivAt
  have hb' : HasFDerivAt (fun v => G.mat (f i v)) _ (0:G.Color) := hF.congr_of_eventuallyEq hO
  unfold f at hb'; simp only [G.mat_mul] at hb'
  have hZ := hb'.unique ((hasFDerivAt_const (𝕜:=ℝ) (c:=G.mat (G.lieExp i)) _).mul' G.expDiff_zero)
  have hp := DFunLike.congr_fun hZ b
  rw [ht] at hp; exact hp.trans (by change G.mat (G.lieExp i) * G.colorMat b + (0:G.Mat)*G.mat (G.lieExp 0) = _; rw [zero_mul,add_zero])
end

section
variable {A : ℝ → G.Color} (h : ContDiff ℝ 1 A) (b : ℝ)
include h b
lemma interval : ∃ (s : Set ℝ), IsOpen s ∧ OrdConnected s ∧ b∈s ∧ ∃ u : ℝ→G.El, Leads s u A := by
  let f (z : ℝ × G.Color) := ((1:ℝ),chartField G z.2 (A z.1))
  have he : ContDiffAt ℝ 1 f (b,0) := by
    refine contDiffAt_const.prodMk ?_
    exact (((chartField_smooth G).of_le (m:=1) le_top).comp (f:=Prod.snd) (b,(0:G.Color)) contDiffAt_snd).clm_apply (h.contDiffAt.comp _ contDiffAt_fst)
  obtain ⟨α,hX,ε,hε,H⟩ := he.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ (t₀:=b)
  let I := Ioo (b-ε) (b+ε)
  have hb : b∈I := ⟨by linarith,by linarith⟩
  have eq : EqOn (fun i => (α i).1) id I := by
    let v i := (α i).1-i
    have hg : ∀ i∈ I, HasDerivAt v 0 i := by
      intro i hi
      have he : HasDerivAt (fun x => (α x).1) 1 i := (H i hi).fst
      simpa only [sub_self] using! (he.sub (hasDerivAt_id' i))
    intro i hi; have hr := isOpen_Ioo.is_const_of_deriv_eq_zero (f:=v) isPreconnected_Ioo (fun i hi => (hg i hi).differentiableAt.differentiableWithinAt) (fun i hi => (hg i hi).deriv) hi hb
    unfold v at hr; rw [hX] at hr; exact sub_eq_zero.mp (by simpa using hr)
  let u := fun x => (α x).2
  have hu : Tendsto u (𝓝 b) (𝓝 0) := by
    have ha := (continuous_snd.continuousAt.comp (H b hb).continuousAt).tendsto; simpa only [comp_apply,hX] using! ha
  obtain ⟨R,hR,Q⟩ := Metric.mem_nhds_iff.mp (inter_mem (isOpen_Ioo.mem_nhds hb) (hu.eventually (stages G)))
  refine ⟨Metric.ball b R, Metric.isOpen_ball, (convex_ball b R).ordConnected, Metric.mem_ball_self hR,G.lieExp ∘ u, fun i hi => ?_⟩
  have hv := Q hi
  have hq : HasDerivAt u (chartField G (u i) (A i)) i := by
    have hw := (H i hv.1).snd; simp only [f] at hw
    rw [show (α i).1=i from eq hv.1] at hw; exact hw
  have ht := (G.exp_jet.differentiable (by simp) (u i)).hasFDerivAt.comp_hasDerivAt i hq
  exact ht.congr_deriv (hv.2 (A i))
end

variable {A : ℝ → G.Color}
lemma Leads.translated {I u} (h : Leads I u A) (x : G.El) : Leads I (fun a => x*u a) A := by
  intro t ht
  simp only [G.mat_mul]
  simpa only [mul_assoc] using! (h t ht).const_mul (G.mat x)
lemma Leads.inherit {I u v} (he : IsOpen I) (h : Leads I u A) (hT : EqOn u v I) : Leads I v A := by
  intro t ht; rw [← hT ht]
  apply (h _ ht).congr_of_eventuallyEq; filter_upwards [he.mem_nhds ht] with i hi; rw [hT hi]

lemma pipes (h : ContDiff ℝ 1 A) : ∃ u, SolvesLink u A := by
  classical
  let H (x : ℝ) := ∃ U : Set ℝ, IsOpen U ∧ Convex ℝ U ∧ 0 ∈ U ∧ x∈U ∧ ∃ u, u 0=1 ∧ Leads U u A
  have h0 : H 0 := by
    obtain ⟨s,hs,h',hp,u,hx⟩ := interval h 0
    exact ⟨s,hs,h'.convex,hp,hp,_,inv_mul_cancel (u 0),hx.translated _⟩
  have hi : IsOpen {x | H x} := isOpen_iff_mem_nhds.mpr fun a ⟨U,hU,hc,he,x,b⟩ =>
    mem_of_superset (hU.mem_nhds x) (fun i hi => ⟨U,hU,hc,he,hi,b⟩)
  have hx : IsClosed {x | H x} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U,hu,hU,he,p,hp⟩ := interval h x
    filter_upwards [hu.mem_nhds he] with y hy
    rintro ⟨T,ho,hT,hn,hv,f,h1,h2⟩
    let u := fun a => (f y*(p y)⁻¹)*p a
    have he' : Leads U u A := hp.translated _
    have hh := agree (ho.inter hu) (hT.inter hU.convex) (show y∈ T∩U from ⟨hv,hy⟩) (fun i hi => h2 i hi.1) (fun i hi => he' i hi.2) (by simp [u])
    let g := T.piecewise f u
    have hQ : EqOn u g U := fun a ha => by
      unfold g; by_cases hx : a∈T; rw [piecewise_eq_of_mem _ _ _ hx]; exact (hh ⟨hx,ha⟩).symm
      rw [piecewise_eq_of_notMem _ _ _ hx]
    apply hx
    refine ⟨T∪U,ho.union hu,(hT.isPreconnected.union y hv hy hU.convex.isPreconnected).ordConnected.convex, subset_union_left hn,subset_union_right he,g,by simp [g,hn,h1],?_⟩
    rintro i (ha|ha)
    · exact (Leads.inherit ho h2 (EqOn.symm (piecewise_eqOn ..))) _ ha
    exact he'.inherit hu hQ _ ha
  have he : ∀ x, H x := by intro x; change x∈{x | H x}; rw [ show {x | H x}=univ from (IsClopen.eq_univ (show IsClopen _ from ⟨hx,hi⟩) ⟨_,h0⟩)]; trivial
  choose U hU hc ho hb f hy hS using he
  let v := fun a => f a a
  have H (a : ℝ) : Leads (U a) v A := Leads.inherit (hU a) (hS a) (by
    intro i hi
    apply agree (I:=U a∩U i) -- implicit names
      ((hU a).inter (hU i)) ((hc a).inter (hc i)) (show 0∈U a∩U i from ⟨ho a,ho i⟩) (fun j hj => hS a j hj.1)
      (fun j hj => hS i j hj.2) (by rw [hy,hy]) (show i∈_ from ⟨hi,hb i⟩))
  exact ⟨v, hy 0, fun i => H i i (hb i)⟩

lemma exists_ode (G : Gauge) : Nonempty (Hol G) := by
  have he (d : ℕ) (J : Jet G) (t : ℝ) (v : Edge Cover) : ContDiff ℝ 1 (partConnection d J t v) := by
    unfold partConnection; apply ContDiff.const_smul; unfold potential
    refine ContDiff.sum fun i _ => ?_
    exact ((Tensor.diag_smooth _ _)).comp (by fun_prop)
  choose f hf using fun d J t v => pipes (he d J t v)
  exact ⟨⟨f,hf⟩⟩
end YM.Source.Hol

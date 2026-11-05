import YM.RG08.Canon.Serif
/-! # Centered bundle through exact slice chart StepData
 Real path t; at each displayed period. No common β domain across N or tag.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {F : Forest S.ratio} {p : Clip} {R : PathData G} {σ K Λ : ℝ} {ρ : fieldDir G c 1 → AxisChart G F}
variable {η:ℝ} (v:Stationary.Link G c) (t:S.Choices) (D : ChartRatio G) (L : fieldDir G c 1 → (AxisChart G F)≃L[ℝ] AxisChart G F)
local notation "U" => AxisChart G F
local notation "X" => (U) × ℝ
local notation "Γ" => fieldDir G c 1

abbrev spanL (k:ℝ):Γ:= arm G c 1 (k • v)
lemma spanL_changes : ContDiff ℝ ω (spanL v):= (arm G c 1).contDiff.comp (contDiff_id.smul contDiff_const)
lemma spanL_e : Tendsto (spanL v) (𝓝 0) (𝓝 0) := by simpa [spanL] using! spanL_changes v |>.continuous.tendsto 0
variable {L}
-- Receipt after selecting real ∆ exactly.
structure Salvo (t : S.Choices) (F : Forest S.ratio) (R : PathData G) (p : Clip) (ρ : (Γ)→ AxisChart G F) (η : ℝ)
    (L : (Γ) → AxisChart G F≃L[ℝ]AxisChart G F) : Prop where
    critical : Critical F p R ρ
    ears : PriceGap F p R η
    price : 0 < η
    begun : L 0=ContinuousLinearEquiv.refl ℝ (AxisChart G F)
    smooth : ContDiffAt ℝ ω (fun i:Γ=> (L i).toContinuousLinearMap) 0
    reverseL : ContDiffAt ℝ ω (fun i:Γ=> (L i).symm.toContinuousLinearMap) 0
    honor : ∀ᶠ i in 𝓝 0, 0 < swing (L i) ∧ swing (L i)^2 * (Precision.hessian F t p R i (ρ i)).det=(Precision.hessian F t p R 0 (ρ 0)).det ∧
      ∀ y:AxisChart G F, jet (fun x:AxisChart G F=> tested F t p R i (ρ i + L i x)) 2 y = jet (tested F t p R 0) 2 y

variable {t} (h : Salvo t F R p ρ η L)
abbrev incount (ρ : (Γ)→(U))(L : (Γ)→ (U)≃L[ℝ](U)) (x : X):= ρ (spanL v x.2)+L (spanL v x.2) x.1
abbrev colorX (x:X):= spanL v x.2
abbrev incense (k:ℝ):= thermal F t p R ρ D (spanL v k)-thermal F t p R ρ D 0 -- unused implicits not inferred below
-- use h named binder not infer inc
local notation "Θ" => incount v ρ L
-- star value always in κ
include h
lemma insideLive : ContDiffAt ℝ ω Θ (0:X) ∧ Θ 0=0 := by
  have ha : ContDiffAt ℝ ω (colorX v (F:=F)) 0:= (spanL_changes v).contDiffAt.comp _ contDiffAt_snd
  have hf : colorX v (0:X)=0:= by simp [colorX,spanL];
  refine ⟨?_,?_⟩
  · have ht : ContDiffAt ℝ ω (fun z:X=> (L (colorX v z)).toContinuousLinearMap) 0:= (show ContDiffAt ℝ ω (fun i=>(L i).toContinuousLinearMap) (colorX v (0:X)) by rw [hf]; exact h.smooth).comp _ ha
    exact ((hf.symm ▸ h.critical.2.1: ContDiffAt ℝ ω _ (colorX v (0:X))).comp _ ha).add (ht.clm_apply contDiffAt_fst)
  change ρ (colorX v (0:X))+ L _ 0 = _; rw [map_zero,hf,h.critical.1,add_zero]

lemma crumb_control : ∀ u:U,u≠0 → 0 < jet (tested F t p R 0) 2 u := by
  intro u he; have ht := h.ears t u; have hz : 0 < η*(∑ i:F.Free, ‖u i‖^2) := by
    refine mul_pos h.price ?_
    obtain ⟨i,hi⟩:∃ i,u i≠0 := Classical.byContradiction (fun hw=> he (funext fun i=> Classical.byContradiction (fun h=> hw ⟨i,h⟩)))
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) _) (Finset.single_le_sum (f:=fun i=> ‖u i‖^2) (fun _ _=>sq_nonneg ..) (mem_univ i))
  unfold jet; rw [show (fun _ : Fin 2=> u)=![u,u] by funext j; fin_cases j <;> simp]; exact mul_pos (by positivity) (hz.trans_le ht)
lemma score_slow : ContDiffAt ℝ ω (fun x=>tested F t p R x (ρ x)) 0 := by
  exact ((show ContDiffAt ℝ ω (uncurry (tested F t p R)) (0,ρ 0) from by rw [h.critical.1]; exact (h.critical.2.2 t).1).comp (f:=fun x=> (x,ρ x)) _ (contDiffAt_id.prodMk h.critical.2.1))

omit h
abbrev starsP (_h:Salvo t F R p ρ η L) (x:X) := tested F t p R (spanL v x.2) (Θ x)- tested F t p R (spanL v x.2) (ρ (spanL v x.2)) + x.2^2
include h
set_option maxHeartbeats 450000 in
lemma schools : Passive (starsP v h) (jet (tested F t p R 0) 2) := by
  let U':=ρ; let W x:=tested F t p R x
  have ha : ContDiffAt ℝ ω (colorX v (F:=F)) 0:= (spanL_changes v).contDiffAt.comp _ contDiffAt_snd
  have hf : colorX v (0:X)=0:= by simp [colorX,spanL]
  have he:=insideLive v h
  have ht := h.critical.2.2 t
  refine ⟨?_,?_,crumb_control h⟩
  · have H := (show ContDiffAt ℝ ω (fun z:X=> W (spanL v z.2) (Θ z)) (0:X) from
       (show ContDiffAt ℝ ω (uncurry W) (colorX v (0:X),Θ 0) by rw [he.2,hf]; exact ht.1).comp (f:=fun z:X=> (colorX v z,Θ z)) _ (ha.prodMk he.1))
    exact (H.sub ((hf.symm ▸ score_slow h: ContDiffAt ℝ ω _ (colorX v (0:X))).comp (f:=fun x:X=>colorX v x) _ ha)).add (contDiffAt_snd.pow 2)
  filter_upwards [spanL_e v|>.eventually ht.2,spanL_e v|>.eventually h.honor,(continuousAt_id.prodMk h.critical.2.1.continuousAt|>.tendsto.comp (spanL_e v)).eventually (show ∀ᶠ x in 𝓝 (((0:Γ)),ρ 0),ContDiffAt ℝ ω (uncurry W) x from (show ContDiffAt ℝ ω (uncurry W) (0,ρ 0) by rw [h.critical.1]; exact ht.1).eventually (by simp))] with s hs hu hF
  let z:= spanL v s; let a x:=ρ z+L z x; let G':= W z ∘ a; let B:= -W z (ρ z)+s^2
  refine ⟨?_,fun x=>?_⟩
  · simp [starsP,incount]
  have hh : a 0=ρ z:= by simp [a]
  have hA : HasFDerivAt a (L z).toContinuousLinearMap 0:= (L z).toContinuousLinearMap.hasFDerivAt.const_add _
  have hP : ContDiffAt ℝ ω (W z) (a 0):= by
    rw [hh]; exact hF.comp (f:=fun u=> (z,u)) _ (contDiffAt_const.prodMk contDiffAt_id)
  have hz : (fun u=> starsP v h (u,s))= G'+fun _=> B:= by
    funext x; change W z (a x)- W z (ρ z) + s^2=W z (a x)+_; unfold B; ring
  rw [hz]
  have hG : ContDiffAt ℝ ω G' 0:= hP.comp _ (contDiffAt_const.add (L z).contDiff.contDiffAt)
  have hL (i : ℕ)(hi:i≠0): jet (G'+fun _=>B) i x=jet G' i x := by
    cases i with
    | zero=> contradiction
    | succ i=> unfold jet; rw [iteratedFDeriv_add_apply (hG.of_le le_top) contDiffAt_const, iteratedFDeriv_succ_const]; simp
  refine ⟨?_,(hL 2 (by decide)).trans (hu.2.2 x)⟩
  rw [hL 1 (by decide)]; unfold jet
  have ht : fderiv ℝ G' 0=0 := by rw [fderiv_comp (g:=W z) _ (hP.differentiableAt (by simp)) hA.differentiableAt,hh, show fderiv ℝ (W z) (ρ z)=_ from hs.fderiv,ContinuousLinearMap.zero_comp]
  simp [ht,iteratedFDeriv_one_apply]
end YM.RG08.Canon

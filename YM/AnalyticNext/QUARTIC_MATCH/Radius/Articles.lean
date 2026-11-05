import YM.AnalyticNext.QUARTIC_MATCH.Radius.Display
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Theme

/-!
# Costs on those true minimizing patches
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

namespace Articles
open Model
section overview
variable {G : Gauge} {c f : Side} (S : StepData c f)
def noise (u : S.Choices) (e : Edge (Site c)) (x : G.Color × Dir G f) :=
  S.kernel.penalty * G.price (G.lieExp x.1 * (S.prediction (represent x.2) u e)⁻¹)
lemma noise_smooth (u : S.Choices) (e : Edge (Site c)) (h : S.patch.Branches S.kernel G) :
    ContDiffAt ℝ ω (noise S u e (G:=G)) 0 := by
  unfold noise; refine ContDiffAt.mul contDiffAt_const ?_
  apply price_smooth (A := fun x : G.Color × Dir G f=> G.lieExp x.1 * (S.prediction (represent x.2) u e)⁻¹)
  have he : ContDiffAt ℝ ω (fun z : G.Color × Dir G f=> G.mat (S.prediction (represent z.2) u e)) 0 :=
    (Push.prediction_cont S h e u).comp (f:=Prod.snd) (0:G.Color × Dir G f) contDiffAt_snd
  simp_rw [G.mat_mul,G.mat_inv]; exact (G.exp_jet.contDiffAt.comp (f:=Prod.fst) _ contDiffAt_fst).mul
    ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ he)
end overview

variable {G : Gauge} {c f : Side}
structure Fine (G : Gauge) (S : StepData c f) where
  b : ℝ
  pos : 0<b
  cap : b<1
  tag : S.Choices
  offers (x : Dir G f) : ‖x‖≤ b → (∀ z,S.patch.usesMin S.kernel (Push.product S z x)) ∧
      ∀ i : Axis,S.patch.usesBest S.kernel (S.connector (represent x) tag.1 (0,i))
  jet (x : G.Color × Dir G f) : ‖x‖≤b → ∀ i : Axis, ContDiffAt ℝ ω (noise S tag (0,i) (G:=G)) x
  norms : ℕ→Axis→ ℝ
  cost (k : ℕ) (i : Axis) (x : G.Color × Dir G f) : ‖x‖≤b → ‖iteratedFDeriv ℝ k (noise S tag (0,i) (G:=G)) x‖ ≤ norms k i
  priced k i : 1≤ norms k i

abbrev Sheds (G : Gauge) (P : Patch) (K : KernelChoices) := Fine G (stepAt P K (marker P))
section
variable (S : StepData c f)
def sets (tag : S.Choices) (h : S.patch.Branches S.kernel G) : Fine G S := Classical.choice (by
  have hl : ∀ᶠ x : Dir G f in 𝓝 0,(∀ z,S.patch.usesMin S.kernel (Push.product S z x)) ∧
      ∀ i : Axis,S.patch.usesBest S.kernel (S.connector (represent x) tag.1 (0,i)) :=
    (eventually_all.mpr (fun p => Push.threshold S p)).and (eventually_all.mpr (fun (i : Axis) => eventually_best (S:=S) h tag.1 (0,i)))
  obtain ⟨b,hb,hh⟩ := room hl
  obtain ⟨d,hd,hg⟩ := room (show ∀ᶠ x in 𝓝 0,∀ i : Axis, ContDiffAt ℝ ω (noise S tag (0,i) (G:=G)) x from
    eventually_all.mpr fun i => (noise_smooth S tag (0,i) h).eventually (by simp))
  let c := min (1/2:ℝ) (min b d)
  have hc : c ≤ b := (min_le_right ..).trans (min_le_left ..); have hv : c ≤ d := (min_le_right ..).trans (min_le_right ..)
  choose F hF hx using fun k i=> ceilingD _ c (fun x h => hg x (h.trans hv) i) k
  exact ⟨c,lt_min (by norm_num) (lt_min hb hd),lt_of_le_of_lt (min_le_left ..) (by norm_num),tag,
    fun x h => hh x (h.trans hc),fun x h=> hg x (h.trans hv),F,hx,hF⟩)
end

section prediction
open Showroom
variable {c f : Side} {G : Gauge} (S : StepData c f) (hk : S.patch.Branches S.kernel G) (θ : S.Choices)
variable (P : Sheds G S.patch S.kernel)
include hk
theorem issued (e : Edge (Site c)) (x : G.Color × Dir G f) (h : ‖x.2‖ ≤ P.b) :
    S.patch.usesMin S.kernel (Push.product S e.1 x.2) ∧ S.patch.usesBest S.kernel (S.connector (represent x.2) θ.1 e) ∧
    noise S θ e x=noise (stepAt S.patch S.kernel (marker S.patch)) P.tag (stamp S.patch e.2) (x.1,pick S e.1 x.2) := by
  have hp := P.offers _ ((fits_token S e.1 x.2).trans h)
  have ht := hp.2 e.2
  obtain ⟨hx,hq⟩ := compiles S θ hk e x.2 P.tag hp.1
  have he := hq.symm ▸ ht
  refine ⟨hx,he,?_⟩
  unfold noise StepData.prediction Patch.predict
  rw [if_pos he,hq]; congr 3
  dsimp only; rw [if_pos ht]
variable (H : Forest S.ratio) (p : Clip) (W : PathData G)
omit hk in
def relates (e : Edge (Site c)) (x : ChartVars H G) := noise (stepAt S.patch S.kernel (marker S.patch)) P.tag (stamp _ e.2)
    (x.1 (e.1,coord e.2),pick S e.1 (axisLog H x))

variable {r : ℝ} (U : Shelf G r P.b) {x : ChartVars H G} (he : ‖x‖ < min P.b r)
include U he
lemma enforces (e : Edge (Site c)) : S.patch.usesMin S.kernel (expandAt (S.ratio.embed e.1) (live H x)) ∧
    S.patch.usesBest S.kernel (S.connector (live H x) θ.1 e) ∧
      relates S P H e x = S.kernel.penalty * G.price (represent x.1 e*(S.prediction (live H x) θ e)⁻¹) := by
  have hz := he.le.trans (min_le_right ..)
  rw [represent_link,← Showroom.makes S H U hz]
  obtain ⟨hx,hH,hv⟩ := issued S hk θ P e (x.1 (e.1,coord e.2),axisLog H x) (Showroom.inside S H U hz)
  exact ⟨hx,hH,hv.symm⟩

section insert
omit hk he U
lemma costOf {Q : Type*} [NormedAddCommGroup Q] (B : Dir G f→Q)
    {r b : ℝ} (U : Shelf G r b) (x : ChartVars H G) (e : Edge (Site c)) (he : ‖x‖ ≤ min b r) (h : ∀ y, ‖B y‖ ≤ ‖y‖) : ‖(x.1 (e.1,coord e.2), B (axisLog H x))‖ ≤ b := by
  exact max_le (((norm_le_pi_norm x.1 (e.1,coord e.2)).trans ((show ‖x.1‖ ≤ ‖x‖ from le_max_left ..).trans (he.trans (min_le_left ..))))) ((h (axisLog H x)).trans
    (Showroom.inside S H U (he.trans (min_le_right ..))))
end insert
omit hk he in
lemma copays (x : ChartVars H G) (e : Edge (Site c)) (he : ‖x‖ ≤ min P.b r) : ‖(x.1 (e.1,coord e.2),pick S e.1 (axisLog H x))‖ ≤ P.b :=
    costOf S H (pick S e.1) U x e he (fits_token S e.1)

omit hk he U in
def rises (_P : Sheds G S.patch S.kernel) (e : Edge (Site c)) (x : ChartVars H G) : G.Color × Dir G (native S.patch) :=
    (x.1 (e.1,coord e.2),pick S e.1 (axisLog H x))
omit hk in
lemma rose (e : Edge (Site c)) : ContDiffAt ℝ ω (rises S H P e) x :=
    ((contDiffAt_apply ℝ G.Color (e.1,coord e.2) x.1).comp (f:=Prod.fst) x contDiffAt_fst).prodMk ((pick S e.1).contDiff.contDiffAt.comp _
      (Showroom.priced S H U (he.le.trans (min_le_right ..))))
omit hk in
lemma bright (e : Edge (Site c)) : ContDiffAt ℝ ω (relates S P H e) x :=
    (P.jet _ (copays S P H U x e he.le) e.2).comp (f:=rises S H P e) _ (rose S P H U he _)

omit he hk U in
def tab {G : Gauge} {P : Patch} {K : KernelChoices} {r : ℝ} (B : Sheds G P K) (U : Shelf G r B.b) (t : ℝ) (n : ℕ) :=
    max 1 (Real.exp (n*t*capacity P)*fetch U P.L t n)

omit hk in
lemma grant (e : Edge (Site c)) (t : ℝ) (hp : 0 ≤ t) (k : ℕ) (h₀ : 0 < k) {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (B : Dir G f →L[ℝ] Q) (hB : ∀ x C, trials G (k*t) (S.ratio.embed e.1) x C → 0 ≤ C → ‖B x‖ ≤ Real.exp (k*t*capacity S.patch)*C) :
    Costs (On S H G t (S.ratio.embed e.1)) (budget _) (fun x : ChartVars H G=>(x.1 (e.1,coord e.2), B (axisLog H x))) x k (tab P U t k) := by
  let A : ChartVars H G →L[ℝ] G.Color := (ContinuousLinearMap.proj (R:=ℝ) (e.1,coord e.2)).comp (ContinuousLinearMap.fst ..)
  let i := S.ratio.embed e.1
  let f : ChartVars H G → Q := B ∘ axisLog H
  have hg : ContDiffAt ℝ ω (axisLog H (G:=G)) x := Showroom.priced S H U (he.le.trans (min_le_right ..))
  have hF : Costs (On S H G t i) (budget _) f x k (Real.exp (k*t*capacity S.patch)*fetch U S.patch.L t k) := by
    intro d b hx; have ht := Finset.prod_nonneg (s:=Finset.univ) (fun j _ => (hx j).1)
    have hh := rapid S H U (he.le.trans (min_le_right ..)) i k t hp d b hx
    unfold f; rw [B.iteratedFDeriv_comp_left hg le_top,mul_assoc (Real.exp _)]
    exact hB (iteratedFDeriv ℝ k (axisLog H) x d) _ hh
      (mul_nonneg (fetch_pos U _ _ _) ht)
  have he : Costs (On S H G t i) (budget _) (⇑A) x k 1 := by
    refine ordinary A (fun v a ha hh => ?_) zero_le_one k h₀
    have hv := hh.1 (e.1,coord e.2)
    change ‖v.1 (e.1,coord e.2)‖ ≤ 1*a; simpa only [i,Function.comp_apply, Green.wt,separation_self,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one,one_mul] using hv
  exact paired A.contDiff.contDiffAt (B.contDiff.contDiffAt.comp _ hg) (he.less (le_max_left ..)) (hF.less (le_max_right ..))

omit hk in
set_option maxHeartbeats 800000 in
lemma fast (e : Edge (Site c)) (t : ℝ) (hp : 0 ≤ t) (k : ℕ) (h₀ : 0 < k) : Costs (On S H G t (S.ratio.embed e.1)) (budget _) (rises S H P e) x k (tab P U t k) :=
    grant S P H U he e t hp k h₀ (pick S e.1) (fun x C hh hC => Model.token S e.1 x _ C hh (mul_nonneg (by positivity) hp) hC)
end prediction
end Articles
end YM.AnalyticNext.QuarticMatch.Radius

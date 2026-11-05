import YM.AnalyticNext.QUARTIC_MATCH.Radius.Articles
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Warrant
import YM.Progress.STATIONARY_SCENES.SliceGap


/-!
# The vertical gradient and its steered budgets

No dimension cost (sum paid by where the vertical key on slide reads). All
native links rather than normalized field norms. Keep a fraction of width.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
open Articles Showroom Model

lemma nearInside {X : Type*} [NormedAddCommGroup X] {x : X} {r : ℝ} (h : ‖x‖<r) : ∀ᶠ y in 𝓝 x, ‖y‖<r := continuous_norm.continuousAt.tendsto.eventually (gt_mem_nhds h)
namespace Purchase
variable {G : Gauge} {c f : Side} (S : StepData c f) (H : Forest S.ratio) (p : Clip) (R : PathData G)
open Green (address wt)

/-- Order in rotations not averaged away. -/
def slew (i : Key H G) : ChartVars H G := (0,frame H i)
def skew (θ : S.Choices) (i : Key H G) (x : ChartVars H G) := Analysis.D (slew S H i) (uncurry (tested H θ p R)) x
lemma allows (i : Key H G) (t : ℝ) (x : Site f) : On S H G t x (slew S H i) (wt t x (address H i))⁻¹ := by
  let w := wt t x (address H i); have he : 0<w := Green.wt_pos ..; have h : 0≤w⁻¹ := inv_nonneg.mpr he.le
  refine ⟨zeroed _ _ _ _ h,?_⟩; intro j
  by_cases hj : j=i.1
  · subst j
    change ‖(slew S H i).2 i.1‖ ≤ w⁻¹ * wt t (address H i) x
    rw [show wt t _ x=w from Green.wt_symm ..,inv_mul_cancel₀ he.ne']; simp only [slew, frame, Pi.single_eq_same, OrthonormalBasis.norm_eq_one,le_refl]
  change ‖frame H i j‖ ≤ w⁻¹ * _; rw [frame,Pi.single_eq_of_ne hj,norm_zero]; exact mul_nonneg h (Green.wt_pos ..).le

lemma menu_insert {X : Type*} {T : Ticket X} {k : ℕ} {d : Fin k→X} {c : Fin k→ℝ} (h : Menu T d c) {v : X} {r : ℝ} (he : T v r) (hr : 0 ≤ r) :
    Menu T (Fin.cons v d) (Fin.cons r c) := by intro i; refine Fin.cases ?_ (fun i=> ?_) i <;> simp only [Fin.cons_zero,Fin.cons_succ]; exact ⟨hr,he⟩; exact h _
variable {Q : Purchase} {F : Site f→ChartVars H G→ℝ} (hp : Q.Applies H p R F)
include hp
lemma works {x : ChartVars H G} (h : ‖x‖ < Q.width) (θ : S.Choices) : ContDiffAt ℝ ω (uncurry (tested H θ p R)) x := by
  refine (ContDiffAt.sum (s:=Finset.univ) (f:=F) (fun i _=> hp.smooth h i)).congr_of_eventuallyEq ?_
  exact (nearInside h).mono fun _ hx => hp.formula hx θ
lemma pitch (θ : S.Choices) {x : ChartVars H G} (h : ‖x‖<Q.width) (i : Key H G) : ContDiffAt ℝ ω (skew S H p R θ i) x :=
    Analysis.dSmooth (works S H p R hp h θ) _ (by simp)

variable (θ : S.Choices) {x : ChartVars H G} (h : ‖x‖<Q.width)
include h
omit hp h in
def vacancy (Q : Purchase) (m : ℕ) := Q.rates (m+1)/(m+1:ℝ)
omit hp h in
def earnings (Q : Purchase) (m : ℕ) := Q.fees (m+1)*Local.Premium.overall (Q.vacancy m)
omit hp h in
lemma vacant (Q : Purchase) (m : ℕ) : 0<Q.vacancy m := div_pos (Q.rate _) (by positivity)
omit hp h in
lemma feesEarn (Q : Purchase) (m : ℕ) : 1 ≤ Q.earnings m := by unfold earnings; exact one_le_mul_of_one_le_of_one_le (Q.cost _) (Premium.cover_ge _)
lemma accum (k : ℕ) (v : Key H G) (m) (hk : k ≤ m) : Costs (On S H G (Q.vacancy m) (address H v))
    (Polish.budget ℝ) (skew S H p R θ v) x k (Q.earnings m) := by
  let Z := address H v; let t := Q.vacancy m; let u := Q.rates (m+1); let r := Q.fees (m+1)
  have hu : 0<u := Q.rate _; have he : 0<t := Q.vacant _; have hb : 0≤r := zero_le_one.trans (Q.cost _)
  have hh : u=t*(m+1:ℝ) := (div_mul_cancel₀ _ (by positivity)).symm
  intro d c hC
  let a : Fin (k+1)→ChartVars H G := Fin.cons (slew S H v) d
  have hf := ((nearInside h).mono fun y h=> hp.formula h θ)
  let g := uncurry (tested H θ p R)
  have hz : iteratedFDeriv ℝ k (skew S H p R θ v) x d=∑ i : Site f,iteratedFDeriv ℝ (k+1) (F i) x a := by
    have hZ : g =ᶠ[𝓝 x] ∑ i,F i := hf.mono (fun i he => he.trans (Finset.sum_apply ..).symm)
    change iteratedFDeriv ℝ k (D (slew S H v) g) x d=_; rw [← cons_inner ((works S H p R hp h θ).of_le le_top),
      (hZ.iteratedFDeriv ℝ (k+1)).eq_of_nhds, iteratedFDeriv_sum_apply (fun i _ => (hp.smooth h i).of_le le_top), _root_.sum_apply]
  rw [hz]; unfold Polish.budget
  let b := ∏ j,c j; have hc : 0 ≤ b := Finset.prod_nonneg fun i _=> (hC i).1
  have hy (i : Site f) : ‖iteratedFDeriv ℝ (k+1) (F i) x a‖ ≤ (r*b)*(wt t i Z)⁻¹ := by
    let w := wt t i Z; let y := wt u i Z; have hp' : 1 ≤ w := Wages.wt_ge he.le ..
    have hv : Menu (On S H G u i) d (fun j=> c j*w) := fun j =>
      ⟨mul_nonneg (hC j).1 (zero_le_one.trans hp'),onward S H t (Showroom.move S H t (hC j).2 i he.le (hC j).1) u (by
        have hg : 0 ≤ (m:ℝ) := by positivity
        nlinarith) (mul_nonneg (hC j).1 (zero_le_one.trans hp'))⟩
    apply (hp.stamps h i (k+1) (m+1) (by omega) _ (Fin.cons y⁻¹ (fun j=> c j*w)) (menu_insert hv (allows S H v u i) (inv_nonneg.mpr (Green.wt_pos ..).le))).trans
    rw [Fin.prod_univ_succ]; simp only [Fin.cons_succ,Fin.cons_zero]; rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; change r*(y⁻¹*(b*w^k)) ≤ _
    have ht : y=w^(m+1) := by change wt u i Z=_; rw [hh]; unfold w Green.wt; rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [ht]; have hx : 0<w := by linarith
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp' hk) hc)
      (inv_nonneg.mpr (pow_pos hx _).le)) hb).trans_eq; change r*((w^(m+1))⁻¹*(b*w^m))=r*b*w⁻¹; field_simp; ring
  apply ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> hy i))).trans; rw [← Finset.mul_sum];
  have ht := Premium.lives (l:=1) he Z
  simp only [PNat.val_ofNat,Nat.cast_one,div_one,one_pow,mul_one] at ht
  exact (mul_le_mul_of_nonneg_left ht (mul_nonneg hb hc)).trans_eq (show r*b*_=Q.earnings m * b by unfold r t b earnings; ring)
end Purchase
end YM.AnalyticNext.QuarticMatch.Radius

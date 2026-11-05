import Mathlib.Data.Set.Finite.List
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Batch
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brush

/-!
# Read a chart while protecting all hard decisions

 Use **fixed** radius before delay. Pull chart coordinates for held-U
 test *everywhere* in Color (even if the sample is outside), glue smoothly.
 One-to-one and covers all w for V near evaluation. So budget can
 use the SAME packet marginals to pay derivatives; scores separate. Uses
 normalized colors, respects multiplication order.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical NNReal ENNReal
variable {G : Gauge} {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
open Brush
variable {d A : ℝ} {j : ℕ} {x : E}
namespace Eider

def plume (G : Gauge) (χ : Chi) (d : ℝ) (p : G.Mat) (a : G.Color) :=
    χ.innerShare d ‖a‖ • (G.plog (G.mat (G.lieExp a)*p)-a)

def fleece (G : Gauge) (χ : Chi) (d : ℝ) (p : G.Mat) (a : G.Color) := a+plume G χ d p a

-- Chart tuner: existence independent of χ and x and V. For U actual run in this Order post R.
structure Canary (G : Gauge) (d A : ℝ) : Prop where
  warm : 0 < d
  side : 0 < A
  closed : ∀ x:G.Color, ‖x‖ ≤ 2*d → G.plog (G.mat (G.lieExp x))=x
  right : ∀ x:G.Color, ‖x‖ ≤ d → ∀ g:G.El, ‖G.mat g - 1‖ ≤ A → G.lieExp (G.plog (G.mat (G.lieExp x * g))) = G.lieExp x * g
  around : ∀ x:G.Color, ‖x‖ ≤ 2*d → ∀ p:G.Mat, ‖p-1‖ ≤ A → ContDiffAt ℝ ω G.plog (G.mat (G.lieExp x)*p)

set_option maxHeartbeats 450000 in
lemma weave (G : Gauge) : ∃ d A, Canary G d A := by
  obtain ⟨s,hs,hF⟩:= Metric.nhds_basis_closedBall.eventually_iff.mp G.plog_left
  obtain ⟨a,r,hr,hY⟩:= reliable G
  have H:= hY r hr le_rfl
  let F (x:G.Color × G.Mat):= G.mat (G.lieExp x.1)*x.2
  have hh := H.patch 1 (by rw [G.chord_one]; linarith)
  have h0 : F (0,1)=1 := by simp [F]
  have ht : ∀ᶠ x in 𝓝 ((0,1):G.Color×G.Mat), ContDiffAt ℝ ω G.plog (F x) ∧ ‖F x-1‖ < G.colorScale * r := by
    have hC : ContinuousAt F (0,1) := (G.exp_jet.continuous.comp continuous_fst).continuousAt.mul continuous_snd.continuousAt
    refine Eventually.and ((show Tendsto F (𝓝 (0,1)) (𝓝 (F (0,1))) from hC).eventually (p:=fun x => ContDiffAt ℝ ω G.plog x) (((show F (0,1)=G.mat 1 from h0).symm ▸ hh).eventually (by simp))) ?_
    exact (hC.sub_const 1).norm.eventually (p:= (·<G.colorScale *r)) (gt_mem_nhds (by rw [h0, sub_self,norm_zero]; exact mul_pos G.colorScale_pos hr))
  obtain ⟨b,hb,hz⟩:= Metric.nhds_basis_closedBall.eventually_iff.mp ht
  let d := min s b / 2; have hd : 0 < d := half_pos (lt_min hs hb)
  have h (x : G.Color) (hc : ‖x‖ ≤ 2*d) (p : G.Mat) (he : ‖p-1‖ ≤ b) := hz (x:=(x,p)) (by
    rw [Metric.mem_closedBall,Prod.dist_eq, max_le_iff, dist_zero_right, dist_eq_norm]; exact ⟨hc.trans (by unfold d; linarith [min_le_right s b]),he⟩)
  refine ⟨d,b,hd,hb,fun x hx=> hF (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; apply hx.trans; unfold d; linarith [min_le_left s b])), ?_,fun x hx p hp=> (h x hx p hp).1⟩
  intro x hx g hg; apply H.right
  apply le_of_mul_le_mul_left _ G.colorScale_pos; rw [chord_dist]
  exact le_trans ((h x (by linarith) (G.mat g) hg).2.le) (mul_le_mul_of_nonneg_left (by linarith) G.colorScale_pos.le)

variable (p : Canary G d A) (χ : Chi)
include p
lemma cooler {a : G.Color} (h : 2*d ≤ ‖a‖) (M : G.Mat) : plume G χ d M a=0 := by
  unfold plume; have hp : χ.innerShare d ‖a‖=0 := by by_contra hn; exact (χ.chosen_lt _ _ p.warm hn).not_ge h
  rw [hp, zero_smul]
lemma nothing (a : G.Color) : plume G χ d 1 a=0 := by
  by_cases he : ‖a‖ ≤ 2*d
  · rw [plume,mul_one,p.closed a he, sub_self,smul_zero]
  exact cooler p χ (le_of_lt (lt_of_not_ge he)) _
lemma nothing_f : fleece G χ d 1=id := funext fun a=> by rw [fleece,nothing p,add_zero]; rfl
lemma sustaining {a : G.Color} (h : ‖a‖ ≤ d) (g : G.El) (he : ‖G.mat g-1‖ ≤ A) :
    G.lieExp (fleece G χ d (G.mat g) a)= G.lieExp a * g := by
  have hh : χ.innerShare d ‖a‖=1 := by
    have hv : ‖a‖/d ≤ 1 := (div_le_one p.warm).mpr h
    have hx : 0 ≤ ‖a‖/d := div_nonneg (norm_nonneg _) p.warm.le
    exact χ.to_one _ (by nlinarith)
  rw [fleece,plume,hh,one_smul,add_sub_cancel]
  exact p.right a h g he
lemma sheen (a : G.Color) (M : G.Mat) (he : ‖M-1‖ ≤ A) : ContDiffAt ℝ ∞ (uncurry (plume G χ d)) (M,a) := by
  by_cases hh : ‖a‖ ≤ 2*d
  · have hf : ContDiffAt ℝ ∞ (fun x:G.Mat × G.Color=> χ.innerShare d ‖x.2‖) (M,a) := by
      unfold Chi.innerShare; simp_rw [div_pow]; exact χ.smooth.contDiffAt.comp (M,a)
        (((contDiff_norm_sq ℝ).comp contDiff_snd).contDiffAt.div_const _)
    let L (x:G.Mat × G.Color):G.Mat := G.mat (G.lieExp x.2)*x.1
    have hh : ContDiffAt ℝ ∞ G.plog (L (M,a)) := (p.around a hh _ he).of_le le_top
    have hL : ContDiffAt ℝ ω L (M,a) := ((G.exp_jet.comp contDiff_snd).mul contDiff_fst).contDiffAt
    exact hf.smul ((hh.comp (M,a) (f:=L) (hL.of_le le_top)).sub (contDiff_snd (𝕜:=ℝ)).contDiffAt)
  refine (contDiffAt_const (c:=(0:G.Color))).congr_of_eventuallyEq ?_
  filter_upwards [(continuous_snd.tendsto (M,a)).norm.eventually (lt_mem_nhds (lt_of_not_ge hh))] with x hx using cooler p χ hx.le _

omit p [NormedSpace ℝ E] [NormedSpace ℝ Y] in
private lemma gather {A : Set (E × Y)} {s : Set Y} (h : IsCompact s) (he : ∀ y∈s,A∈𝓝 (x,y)) :
    ∀ᶠ v in 𝓝 x, ∀ y ∈ s,(v,y)∈ A := by
  obtain ⟨u,t,hx,-,hv,ht,hT⟩:= generalized_tube_lemma (isCompact_singleton (x:=x)) h (isOpen_interior (s:=A))
    (show {x} ×ˢ s⊆ interior A from by rintro ⟨y,z⟩ ⟨hx,hz⟩; rw [Set.mem_singleton_iff] at hx; change y=x at hx; subst y; exact mem_interior_iff_mem_nhds.mpr (he z hz))
  filter_upwards [hx.mem_nhds (hv (Set.mem_singleton x))] with z hz y hy using interior_subset (hT (show (z,y)∈ _×ˢ _ from ⟨hz,ht hy⟩))

lemma lamina (a:G.Color) (M:G.Mat) (he : ‖M-1‖ ≤ A) : ContDiffAt ℝ (↑j) (fun x:G.Mat × G.Color=> fderiv ℝ (fun v=> plume G χ d x.1 v) x.2) (M,a) := by
  let x := (M,a)
  have h := sheen p χ a M he
  have hh : ContDiffAt ℝ (↑(j+1:ℕ)) (uncurry (plume G χ d)) (M,a) := h.of_le (WithTop.coe_le_coe.mpr le_top)
  let L (x:(G.Mat×G.Color)×G.Color):=(x.1.1,x.2)
  have hx : ContDiffAt ℝ (↑(j+1:ℕ)) (uncurry fun x:G.Mat×G.Color=> plume G χ d x.1) ((M,a),a) := hh.comp ((M,a),a) (f:=L) (by unfold L; fun_prop)
  exact hx.fderiv
    (f:=fun x:G.Mat×G.Color=>plume G χ d x.1) (g:=Prod.snd) (m:=↑j) contDiffAt_snd (by push_cast; rfl)
lemma retreats (q : G.Mat) (a:G.Color) (he : 2*d < ‖a‖) : fderiv ℝ (fun v=> plume G χ d q v) a=0 := by
  refine (hasFDerivAt_const (𝕜:=ℝ) (c:=(0:G.Color)) _).congr_of_eventuallyEq (f₁:=fun v=> _) ?_ |>.fderiv
  filter_upwards [continuous_norm.continuousAt (lt_mem_nhds he)] with b hb using cooler p χ (show 2*d≤ ‖b‖ from hb.le) _

lemma limn : ∀ᶠ M : G.Mat in 𝓝 1, ∀ x : G.Color, ‖plume G χ d M x‖ < d/2 ∧ ‖fderiv ℝ (fun v=> plume G χ d M v) x‖<1/2 := by
  have hh a : ContinuousAt (fun v:G.Mat × G.Color=>plume G χ d v.1 v.2) (1,a) := (sheen p χ a 1 (by simp [p.side.le])).continuousAt
  have hm a : ContinuousAt (fun v:G.Mat × G.Color=>fderiv ℝ (fun t=>plume G χ d v.1 t) v.2) (1,a) :=
    (lamina p χ a 1 (j:=0) (by simp [p.side.le])).continuousAt
  let S := Metric.closedBall (0:G.Color) (2*d)
  let u := {v:G.Mat × G.Color | ‖plume G χ d v.1 v.2‖ < d/2 ∧ ‖fderiv ℝ (fun x=>plume G χ d v.1 x) v.2‖<1/2}
  have hg : ∀ a∈ S, u ∈ 𝓝 (1,a) := by
    intro a _
    have hv : (fun x=>plume G χ d (1:G.Mat) x)=fun _=> 0 := funext (nothing p χ)
    exact Filter.inter_mem ((hh a).norm.eventually (gt_mem_nhds
      (show ‖plume G χ d 1 a‖ < d/2 by rw [nothing p]; simp [p.warm])))
      ((hm a).norm.eventually (gt_mem_nhds (show ‖fderiv ℝ (fun x=> plume G χ d 1 x) a‖ < 1/2 by rw [hv]; norm_num)))
  filter_upwards [gather (A:=u) (s:=S) (isCompact_closedBall _ _) hg] with M hM x
  by_cases he : x∈ S; exact hM x he
  have hh : 2*d < ‖x‖ := by simpa [S,not_le] using he
  rw [cooler p χ hh.le,retreats p χ M x hh,norm_zero,norm_zero]
  exact ⟨half_pos p.warm,by norm_num⟩
end Eider
end YM.ConnectedActivityE6.Blaze

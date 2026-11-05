import YM.Extra.ITERATION_NO_LOSS.Determinant
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Liquid
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Withdrawal
import YM.Push.STATIONARY_UNIFORM.Continue



/-! # Pricing the actual fresh matrix Hessian determinant contribution

Across *any* continuation. All p without retuning. Uniform AFTER each
block length and input stage (incl path widths & costs σ,C etc);
also with disconnected case, active zero modes still have their actual
go. No ghost interpolation hypothesis.
Not a comparison to αS'+silent loop and so NOT FreshDet; width here
NOT usable in the exponential `.Charged` output without purchasing ahead of
all rolls (typically far too small: need the uniform pre-L coarse external
estimate of E.c2lp:Cdvert, which this real estimate doesn't do!). Pursue
post-L in trajectory separately, especially R thermal period error estimates
Phase: this size of strip does suit such a use but need acceptably priced
along whole history; expose further in Fluct. Coarser alternative to E
internal coarse-symbol traces at fixed L for after-L physical gates,
not claiming E §period limit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Dividends
open Jacobi Polytrace Withdrawal Function Lattice Gauge Finset RG Push.Uniform Filter Wilson Precision Bid Tree Matrix Exterior
    Extra.Iteration Extra.Iteration.Calibration Push Set Metric Pressure
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {t : S.Choices} {B : Forest S.ratio}
  {j n : ℕ} {μ C Λ : ℝ} {p : Clip} {R : PathData G} {Q : KernelChoices} {O : ChartRatio G}
  (A : Uniform.Before G μ C j Q n)

abbrev collected (B : Forest S.ratio) (t : S.Choices) (p : Clip) (R : PathData G) (O : ChartRatio G)
    (z : Positions (Joint B G)) := (1/2:ℝ)*determinantLog (priced B t p R) z-Liquid.bead O z

private lemma offeq : ∀ z : Positions (Joint B G), ContDiffAt ℝ ω (priced B t p R) z →
    block (priced B t p R) z = hessian B t p R ((paint B G z).1) ((paint B G z).2) := by
  intro z
  rw [show z = meetVar ((partSpace (Primary c G) (Key B G) z).1) ((partSpace _ _ z).2) from
    ((partSpace _ _).symm_apply_apply z).symm]
  intro hf; rw [paint_meet]; exact block_congr B t hf

private lemma actualPrint (B : Forest S.ratio) (t : S.Choices) (z : Positions (Joint B G)) (K : Matrix (Key B G) (Key B G) ℝ) (D : DecidableEq (Key B G)) (F : Fintype (Key B G)) (h : block (Uniform.priced B t p R) z=K) :
    Real.log (@Matrix.det (Key B G) D F ℝ _ K)= determinantLog (Uniform.priced B t p R) z := by
  -- specify actual det via underlying Decidable? generated wrong prod subtype classical, instead abstract
  unfold determinantLog; rw [h]
  rw [Subsingleton.elim D (fun a b => Classical.propDecidable (a=b)), Subsingleton.elim F (inferInstanceAs (Fintype (Key B G)))]
lemma viewed {g : In G c→AxisChart G B} (hw : Critical B p R g) (ho : LocalRatio O) :
    let L := curve (station g)
    let F := determinant B t R p g O
    F ∘ tint G _ =ᶠ[𝓝 0] collected B t p R O ∘ L := by
  intro L F
  have he : L 0=0 := by
    have hx : Uniform.station g 0=0 := by unfold Uniform.station; simp [hw.1]
    change meetVar 0 (Uniform.station g 0)=0; rw [hx]; exact (partSpace _ _).symm.map_zero
  have hz : ContDiffAt ℝ ω g ((tint G (Body 1 c)) 0) := by rw [map_zero]; exact hw.2.1
  have h : ContDiffAt ℝ ω (Uniform.station g) 0 := (tint G B.Free).symm.contDiff.contDiffAt.comp 0 (f:=g ∘ tint G _)
    (hz.comp 0 (f:=(tint G (Body 1 c))) (tint G (Body 1 c)).contDiff.contDiffAt)
  have hh := (show ContDiffAt ℝ ω L 0 from along h).continuousAt.tendsto; rw [he] at hh
  have ht : ContDiffAt ℝ ω (priced B t p R) (0:Positions (Joint B G)) := by
    have hd := (paint B G).map_zero
    unfold Uniform.priced; exact (show ContDiffAt ℝ ω _ (paint B G 0) from (by rw [hd]; exact ((hw.2.2 t).1))).comp _ (paint B G).contDiff.contDiffAt
  filter_upwards [hh.eventually (ht.eventually (by simp)), hh.eventually (Liquid.join (B:=B) ho)] with x hx hU
  have hx' : paint B G (L x)=(tint G _ x,g (tint G _ x)) := by
    change paint B G (meetVar x _) = _; rw [paint_meet]; unfold Uniform.station; simp
  change determinant B t R p g O ((tint G _) x)=collected B t p R O (L x)
  have hH := offeq (t:=t) (p:=p) (R:=R) (L x) hx
  change Real.log _ = Liquid.bead O (L x) at hU
  rw [hx'] at hU hH
  let u := tint G (Body 1 c) x
  let e : ℝ := (1/2:ℝ) * Real.log (hessian B t p R u (g u)).det
  change e - Real.log (∏ i:B.Free,O.J (g u i))=collected B t p R O (L x)
  have hr : e=(1/2:ℝ)*determinantLog (Uniform.priced B t p R) (L x) :=
    congrArg ((1/2:ℝ)*·) (actualPrint B t (L x) _ _ _ hH)
  exact congr_arg₂ (fun a b:ℝ=>a-b) hr hU

def shellRate (Y : ChartPrices) : ℝ := min (Y.width/2) (tiltWidth Y.coords (Y.gap/2) Y.width Y.value)
def money (Y : ChartPrices) (O : ChartRatio G) : ℝ :=
    feeVac Y.value (Y.gap/2/2)⁻¹ Y.coords (shellRate Y)+Liquid.aqueous O

variable (B t) {A}
variable (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q)
  (h : 4≤n)
local notation "Y" => A.tables p S.patch
variable (A) (he : LocalRatio O)
include A B t hp hK hj ht h he
lemma issued :
    let F := collected B t p R O
    let K := money Y O
    0 < shellRate Y ∧ 0≤K ∧ ContDiffAt ℝ ω F 0 ∧ ∀ (i j:Joint B G), ‖blade (bolt i) F 0‖ ≤ K ∧
      ‖mixed (bolt i) (bolt j) F 0‖ ≤ K*Decay (shellRate Y) (address B G i) (address B G j) := by
  let l := address B G
  let X := priced B t p R
  have hr := (A.receipt B t hp hK hj ht).1
  change Receipt l (Y).width n (Y).coords (Y).value (Y).initial (Y).gap X at hr
  have hh := hr.born 0 (Metric.mem_ball_self hr.pos_r)
  obtain ⟨hy,hc,-⟩ := @Receipt.priced_inverse _ _ _ _ _ _ _ _ _ _ _ _ _ hr (fun a b=>Classical.propDecidable (a=b)) 0 (Metric.mem_closedBall_self hr.reserveH_pos.le)
  have hm : 0 < shellRate Y := lt_min (half_pos hr.pos_a) (tiltWidth_pos _ (half_pos hr.pos_m) hr.pos_a hr.pos_C.le)
  have hf : 0 ≤ ((Y).gap/2/2)⁻¹ := (inv_pos.mpr (half_pos (half_pos hr.pos_m))).le
  have hv : 0 ≤ feeVac (Y).value ((Y).gap/2/2)⁻¹ (Y).coords (shellRate Y) := feeVac_nonneg _ hr.pos_C.le hf hm
  have hH := ((@face_det _ _ _ _ _ (fun a b : Key B G=>Classical.propDecidable (a=b)) _ _ (echogram hh.1)).log hy.ne')
  change ContDiffAt ℝ ω (determinantLog X) 0 at hH
  have hx := Liquid.hydrated (B:=B) he
  refine ⟨hm,add_nonneg hv (Liquid.aquatic _), (contDiffAt_const.mul hH).sub hx,fun i j=>?_⟩
  have H := bared hh.2 hh.1 h hr.pos_C.le hr.mult hy.ne' hm (show _ + _ ≤ _ by have hx : shellRate Y ≤ (Y).width/2 := min_le_left ..; linarith)
    (min_le_right ..) hf hc i j
  have hw := Liquid.thirst (r:=shellRate Y) he i j
  let b := feeVac (Y).value ((Y).gap/2/2)⁻¹ (Y).coords (shellRate Y)
  let D := Decay (shellRate Y) (l i) (l j)
  have hd : 0 ≤ b*D := mul_nonneg hv (decay_pos ..).le
  let U (i : Joint B G) (x : Positions (Joint B G)) := (1/2:ℝ)*blade (bolt i) (determinantLog X) x - blade (bolt i) (Liquid.bead O) x
  have hh (i : Joint B G) : blade (bolt i) (collected B t p R O)=ᶠ[𝓝 0] U i := by
    filter_upwards [hH.eventually (by simp),hx.eventually (by simp)] with y hf hg
    change fderiv ℝ ((fun x => (1/2:ℝ)*determinantLog X x) - Liquid.bead O) y (bolt i)= U i y
    have he := fderiv_sub (𝕜:=ℝ) (f:=fun x => (1/2:ℝ)*determinantLog X x)
      ((contDiffAt_const (c:= (1/2:ℝ))).mul hf |>.differentiableAt (by simp)) (hg.differentiableAt (by simp))
    rw [he]; change blade (bolt i) (fun x => (1/2:ℝ)*determinantLog X x) y - _ = _
    rw [product _ contDiffAt_const hf, blade_const,mul_zero,add_zero]; rfl
  refine ⟨?_,?_⟩
  · rw [(hh i).eq_of_nhds]; unfold U; apply (norm_sub_le ..).trans (add_le_add _ hw.1)
    rw [norm_mul]; exact le_trans (mul_le_mul_of_nonneg_left H.1 (norm_nonneg _)) (mul_le_of_le_one_left hv (by norm_num))
  unfold mixed
  have H2 := congr_arg (fun L : Positions (Joint B G) →L[ℝ] ℝ => L (bolt i)) (hh j).fderiv_eq
  change ‖blade (bolt i) (blade (bolt j) (collected B t p R O)) 0‖ ≤ _
  rw [show blade (bolt i) (blade (bolt j) (collected B t p R O)) 0 = blade (bolt i) (U j) 0 from H2]
  have hwc := fderiv_sub (𝕜:=ℝ) (f:=fun y => (1/2:ℝ)*blade (bolt j) (determinantLog X) y)
    ((contDiffAt_const (c:= (1/2:ℝ))).mul (smooth _ hH) |>.differentiableAt (by simp)) ((smooth (bolt j) hx).differentiableAt (by simp))
  change ‖fderiv ℝ ((fun y => (1/2:ℝ)*blade (bolt j) (determinantLog X) y) - blade (bolt j) (Liquid.bead O)) 0 (bolt i)‖ ≤ _
  rw [hwc]
  change ‖blade (bolt i) (fun y => (1/2:ℝ)*blade (bolt j) (determinantLog X) y) 0 - mixed (bolt i) (bolt j) (Liquid.bead O) 0‖ ≤ (b+Liquid.aqueous O)*D
  rw [product _ contDiffAt_const (smooth _ hH),blade_const,mul_zero,add_zero,add_mul]; apply (norm_sub_le ..).trans (add_le_add _ hw.2)
  rw [norm_mul]; exact le_trans (mul_le_mul_of_nonneg_left H.2 (norm_nonneg _)) (mul_le_of_le_one_left hd (by norm_num))

def volt (K : ChartPrices) (n : ℕ) := min (shellRate K) (responseRate K.coords n K.value K.width K.gap/2)
def bolted (K : ChartPrices) (n : ℕ) (O : ChartRatio G) := flowFee (money K O) (curveCost K.coords K.value K.width K.gap 2) K.coords (volt K n)

-- One common estimate on the entire graph. Also Vol(j) constants computed once.
lemma authentically (ρ : In G c→AxisChart G B) (hh : Critical B p R ρ) :
    let F := determinant B t R p ρ O ∘ tint G _
    let s := volt Y n
    let b := bolted Y n O
    0<s ∧ 0≤b ∧ ContDiffAt ℝ ω F 0 ∧ ∀ (i k:Primary c G),
      ‖(iteratedFDeriv ℝ 2 F 0) ![bolt i,bolt k]‖ ≤ b*Decay s (S.ratio.embed i.1.1) (S.ratio.embed k.1.1) := by
  intro F s b
  let l := address B G; let J := Primary c G; let u : J→Site f := l ∘ Sum.inl
  let D := responseRate (Y).coords n (Y).value (Y).width (Y).gap; let T := curveCost (Y).coords (Y).value (Y).width (Y).gap 2
  obtain ⟨hi,hp',hf,hb⟩:= issued t B A hp hK hj ht h he
  have hr := (A.receipt B t hp hK hj ht).1
  have hd : 0 < D := rate_pos hr; have hr' : 0 ≤ T := le_trans zero_le_one (curveCost_ge hr _)
  have hs : 0 < s := lt_min hi (half_pos hd)
  obtain ⟨g,hg⟩ := A.graph B hp hK hj ht
  let z := Uniform.station g
  let X := curve z
  let U := collected B t p R O
  have hhH := Metric.mem_ball_self (x:=(0:Positions (Primary c G))) hg.x_pos
  have hz := hg.series hhH
  have hT : ContDiffAt ℝ ω X 0 := along hz
  have hx : X 0=0 := by
    have hZ : Uniform.station g 0=0 := by unfold Uniform.station; simp [hg.critical.1]
    change meetVar 0 (Uniform.station g 0)=0; rw [hZ]; exact (partSpace _ _).symm.map_zero
  change ContDiffAt ℝ ω U 0 at hf
  have hU : ContDiffAt ℝ ω U (X 0) := hx ▸ hf
  have hE : F=ᶠ[𝓝 0] U ∘ X := by
    refine (EventuallyEq.trans ?_ (viewed hg.critical he))
    let W := tint G (Body 1 c)
    have hk : Tendsto W (𝓝 0) (𝓝 0) := map_zero W ▸ W.continuous.continuousAt.tendsto
    filter_upwards [hk.eventually (Uniform.Before.Service.is_extension hg hh)] with x e
    show determinant B t R p ρ O (W x)=determinant B t R p g O (W x)
    unfold determinant; rw [e]
  have hX : Envelope u l D 2 X 0 T := envelopes hr hz (hg.pricing hhH) (hg.entered hp hK hj ht hhH t) (by omega)
  have hB q (i : J) : ‖Withdrawal.move (bolt i) X 0 q‖ ≤ T*Decay D (l q) (u i) := by
    rw [← turn _ hT]; simpa only [entry,iteratedFDeriv_one_apply,Matrix.cons_val_zero,glaze,spanSites,Fin.sum_univ_one,Decay] using
      hX 1 (by decide) (by norm_num) ![i] q
  have hB' q (i k : J) : ‖rise (bolt i) (bolt k) X 0 q‖ ≤ T*(Decay D (l q) (u i)*Decay D (l q) (u k)) := by
    have hy := hX 2 (by decide) le_rfl ![i,k] q
    -- peel using come
    let L := ContinuousLinearMap.proj (φ:=fun _ : Joint B G=>ℝ) (R:=ℝ) q
    change ‖mixed _ _ (L ∘ X) 0‖ ≤ _
    rw [come _ _ _ hT,iter _ _ hT]; rw [show ![bolt i, bolt k]=(fun s : Fin 2=>bolt (![i,k] s)) from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)]; change ‖entry X 0 ![i,k] q‖ ≤ _
    simpa [glaze,Decay,spanSites,Fin.sum_univ_succ,mul_add,Real.exp_add] using hy
  refine ⟨hs,flow_nonneg hp' hr' _ hs,(hU.comp (f:=X) _ hT).congr_of_eventuallyEq hE,fun i k=>?_⟩
  rw [(hE.iteratedFDeriv ℝ _).eq_of_nhds,← iter (bolt i) (bolt k) (hU.comp (f:=X) _ hT)]
  exact merged (C:=money Y O) hT hU hr.mult hp' hr' hs (show s+s ≤ D by have ht : s≤D/2 := min_le_right ..; linarith)
    (show s≤shellRate Y from min_le_left ..) (fun i => hx.symm ▸ (hb i i).1) (fun i k => hx.symm ▸ (hb i k).2)
    hB hB' i k
end YM.Further.PhysicalPeriodLimitF933.Dividends

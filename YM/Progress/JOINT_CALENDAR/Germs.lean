import YM.Progress.JOINT_CALENDAR.Issue
import YM.Work.F05

/-!
# Classical and loop invoices that are unnecessary at this seam

On the actual scheduled stationary operation: compute agreement automatically
THROUGH quadratic via Hessian limits; positivity and analytic prerequisites of
`FiniteBound`, and reduction of both jet comparisons to just one tree/choice at
each period.

Uses the accepted F packages.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Progress.Joint
open Filter Lattice RG Wilson Precision Exterior Tree Bid Next.Scheduling Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n c f : Side}

lemma gaugeFiscal_smul (B : Bed) (a : Dir G n) (t : ℝ) :
    gaugeFiscal B (t • a) (t • a) = t^2*gaugeFiscal B a a := by
  have ht i : parts G 1 (t•a) i=t • parts G 1 a i := rfl
  unfold gaugeFiscal; simp only [ht,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,Finset.mul_sum];
  apply Finset.sum_congr rfl; intros; ring

lemma top_fiscal (B : Bed) (a : Dir G n) {p : Clip} {η C : ℝ} (hf : Floor B p n η C) (ht : B.diagonal.acts n=1) :
    gaugeFiscal B a a = ∑ x : Face (Per n), ‖Work.F03.faceCurl x a‖^2 := by
  unfold gaugeFiscal Precision.K
  simp only [← real_inner_self_eq_norm_sq, Work.F03.inner_color]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_assoc,hf.same,ht,Matrix.one_mul,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,
    dotProduct,← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site n)) plaqEquiv)]
  rfl

lemma energy_limit (B : Bed) (a : Dir G n) {p : Clip} {η C : ℝ} (hf : Floor B p n η C) (ht : B.diagonal.acts n=1) :
    Tendsto (fun t : ℝ => Wilson.energy (represent (t • a)) / t^2) (𝓝[≠] 0) (𝓝 (gaugeFiscal B a a/2)) := by
  rw [top_fiscal B a hf ht]; unfold energy; simp_rw [Finset.sum_div]
  refine tendsto_finsetSum _ (fun x _ => Work.F03.price_limit (V:=fun t => faceValue (represent (t • a)) x) ?_ (Work.F03.face_deriv x a))
  rw [zero_smul]; exact Push.stroll_zero ..

lemma energy_born : ContDiffAt ℝ ω (fun a : Dir G n => energy (represent a)) 0 := by
  unfold energy; apply ContDiffAt.sum; intro x _
  apply Work.F03.price_smooth (A:=fun a => faceValue (represent a) x)
  simp_rw [faceValue,← Work.F02.stringMat_physical]
  exact ((Work.F02.stringMat_contDiff (G:=G) _ _).restrict_scalars ℝ).contDiffAt.comp 0
    (Work.F02.physical_contDiffAt fun i => (Work.F03.represent_smooth i).contDiffAt)

lemma jets_of_shared_limit {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {f g : X → ℝ}
    (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) {Q : X → ℝ}
    (h : ∀ a : X,Tendsto (fun t : ℝ => f (t•a)/t^2) (𝓝[≠] 0) (𝓝 (Q a)))
    (h' : ∀ a : X,Tendsto (fun t : ℝ => g (t•a)/t^2) (𝓝[≠] 0) (𝓝 (Q a))) :
    ∀ j : ℕ,j ≤ 2 → SameJet j f g := by
  have hh := Work.F03.hessian_of_limit (f:=f-g) (Q:=fun _ _ => 0) ((hf.sub hg).of_le le_top)
    (fun a => by simpa only [Pi.sub_apply,sub_div,zero_div,sub_self] using (h a).sub (h' a))
    (fun _ _ _ => (add_zero _).symm) (fun _ _ => rfl)
  obtain ⟨h₁,h₂,h₃⟩ := hh
  rw [Pi.sub_apply, sub_eq_zero] at h₁
  rw [fderiv_sub (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp)),sub_eq_zero] at h₂
  rw [iteratedFDeriv_sub_apply (hf.of_le le_top) (hg.of_le le_top)] at h₃
  intro j hj
  refine ⟨hf,hg,?_⟩; ext m; interval_cases j
  · simpa only [iteratedFDeriv_zero_apply]
  · simp only [iteratedFDeriv_one_apply,h₂]
  · have he : m= ![m 0,m 1] := funext fun i => by fin_cases i <;> rfl
    rw [he]; exact sub_eq_zero.mp (h₃ _ _)

lemma top_second (B : Bed) {p : Clip} (W : PathData G) {σ Λ D η C : ℝ} (hf : Floor B p n η C) (ht : B.diagonal.acts n=1)
    (hs : W.Bounds p σ D Λ) (hw : Sworn B n G) (ha : Attached B W) :
    ∀ j,j≤2 → SameJet j (fun a : Dir G n => mainTerm p W (represent a)) (fun a => energy (represent a)) :=
  jets_of_shared_limit (Work.F02.mainTerm_contDiffAt hs fun i => (Work.F03.represent_smooth i).contDiffAt)
    energy_born (Work.F03.main_limit hs ha hf hw) (fun a => energy_limit B a hf ht)

variable {S : StepData c f} {W W' : PathData G} {p q : Clip} {U : Forest S.ratio} {σ Λ D η C σ' Λ' D' : ℝ}
    {ρ : Dir G c → AxisChart G U}

lemma fiscal_limit (B : Bed) (a : Dir G c) :
    Tendsto (fun t : ℝ => (1/2:ℝ)*gaugeFiscal B (t•a) (t•a)/t^2) (𝓝[≠] 0) (𝓝 (gaugeFiscal B a a/2)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[≠] 0,t ≠ 0 from self_mem_nhdsWithin] with t ht
  rw [gaugeFiscal_smul]; field_simp

lemma tested_second (B : Bed) (h : Critical U p W ρ) (hc : Comptroller U B p W) (A : Bed)
    (hh : HeatG U p W ρ A) (hf : Floor A q c η C) (ht : W'.Bounds q σ D Λ) (ha : Attached A W') (hs : Sworn A c G) :
    ∀ (t : S.Choices) (j : ℕ), j ≤ 2 → SameJet j (fun x => tested U t p W x (ρ x)) (fun x => mainTerm q W' (represent x)) := by
  intro t
  let F := Function.uncurry (tested U t p W)
  let u (a : Dir G c) := (a,ρ a)
  have hu : u 0=0 := by simp [u,h.1]
  have hd : fderiv ℝ F (u 0) = 0 := hu ▸ (hc t).2.1
  have hs' : ContDiffAt ℝ ω F (u 0) := by rw [hu]; exact (h.2.2 t).1
  have hg : ContDiffAt ℝ ω u 0 := contDiffAt_id.prodMk h.2.1
  have he : fderiv ℝ (F ∘ u) 0 = 0 := by
    rw [fderiv_comp _ (hs'.differentiableAt (by simp)) (hg.differentiableAt (by simp)),hd]; rfl
  let g (x : Dir G c) := (1/2:ℝ)*gaugeFiscal A x x
  let f (x : Dir G c) := mainTerm q W' (represent x)
  have hJ : ∀ j,j ≤ 2 → SameJet j g f := jets_of_shared_limit (hh t).2.1
    (Work.F02.mainTerm_contDiffAt ht fun i => (Work.F03.represent_smooth i).contDiffAt) (fiscal_limit A) (Work.F03.main_limit ht ha hf hs)
  obtain ⟨hv,h',-⟩ := Work.F03.hessian_of_limit (Q:=fun x y => gaugeFiscal A x y) ((hh t).2.1.of_le le_top) (fiscal_limit A)
    Work.F03.gaugeFiscal_add (fun x y => by
      simp_rw [Work.F03.metric_pair A ht ha _ _ hf,real_inner_comm (Work.F03.faceCurl _ x), real_inner_comm (Work.F03.ellLine W' _ x)])
  change ∀ (j : ℕ), j ≤ 2 → SameJet j (F ∘ u) f
  intro j hj; refine ⟨hs'.comp 0 hg, (hJ j hj).2.1,?_⟩
  rw [← (hJ j hj).2.2]
  interval_cases j
  · ext m; simp only [iteratedFDeriv_zero_apply, Function.comp_apply,hu]
    exact (hc t).1.trans hv.symm
  · ext m; simp only [iteratedFDeriv_one_apply, he]; rw [show fderiv ℝ g 0 = 0 from h']
  exact (hh t).2.2
end YM.Progress.Joint

namespace YM.Progress.Joint
open Filter Function Lattice RG Wilson Precision Exterior Tree Bid Next.Scheduling Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f} {W W' : PathData G} {p q : Clip} {U U' : Forest S.ratio} {σ Λ D η σ' Λ' D' : ℝ}
    {ρ : Dir G c → AxisChart G U} {ρ' : Dir G c → AxisChart G U'} {O : ChartRatio G}

lemma pulled_smooth {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : X → Config G n)
    (ha : ∀ i, ContDiffAt ℝ ω (fun x => G.mat (A x i)) 0) (s : Signed) (i) :
    ContDiffAt ℝ ω (fun x => G.mat (pull s 0 (A x) i)) 0 := by
  unfold pull Step.read
  split
  · exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (ha _)
  exact ha _

lemma loop_born {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (h : W.Bounds p σ D Λ)
    (A : X → Config G n) (ha : ∀ i, ContDiffAt ℝ ω (fun x => G.mat (A x i)) 0) :
    ContDiffAt ℝ ω (fun x => Precision.loop W (A x)) 0 := by
  unfold Precision.loop Patch.average; apply contDiffAt_const.mul (ContDiffAt.sum _); intro s _
  exact Work.F02.uncut_contDiffAt (A:=fun x => pull s 0 (A x)) h.width h.two (pulled_smooth A ha s)

lemma draft_born (h : W.Bounds p σ D Λ) (α : ℝ) : ContDiffAt ℝ ω (draft (c:=c) α W p) 0 := by
  have he (e) := (Work.F03.represent_smooth (G:=G) (n:=c) e).contDiffAt (x:=0)
  refine (contDiffAt_const.mul ?_).add (loop_born h represent he)
  unfold secondTerm Patch.average; apply contDiffAt_const.mul (ContDiffAt.sum _); intro s _
  exact Work.F02.quadratic_contDiffAt (A:=fun x => pull s 0 (represent x)) h (pulled_smooth _ he s)

lemma thermal_born (t : S.Choices) (h : W.Bounds p σ D Λ) (hc : Critical U p W ρ)
    (ha : 0<η) (hQ : PriceGap U p W η) (hO : LocalRatio O) : ContDiffAt ℝ ω (thermal U t p W ρ O) 0 := by
  let g := fun x : Dir G c => (x,ρ x)
  have hz : g 0 = 0 := by simp [g,hc.1]
  have hg : ContDiffAt ℝ ω g 0 := contDiffAt_id.prodMk hc.2.1
  have he : ContDiffAt ℝ ω (fun z : Dir G c × AxisChart G U => fderiv ℝ (fderiv ℝ (tested U t p W z.1)) z.2) (g 0) := by
    rw [hz]; exact Work.F05.curve_partial (F:=fun x => fderiv ℝ (tested U t p W x)) (Work.F05.curve_partial (hc.2.2 t).1)
  have hj (i j) : ContDiffAt ℝ ω (fun x => hessian U t p W x (ρ x) i j) 0 := by
    simp only [hessian, Matrix.of_apply, iteratedFDeriv_two_apply, cons_val_zero,cons_val_one]
    exact (((he.comp 0 hg).clm_apply contDiffAt_const).clm_apply contDiffAt_const)
  have hd : ContDiffAt ℝ ω (fun x => (hessian U t p W x (ρ x)).det) 0 := by
    simp_rw [det_apply']; refine ContDiffAt.sum (fun i _ => contDiffAt_const.mul (contDiffAt_prod ?_))
    intro j _; exact hj ..
  have hJ := hO.germ 0 (Metric.mem_ball_self hO.patch)
  have hP i : ContDiffAt ℝ ω (fun x => O.J (ρ x i)) 0 := by
    rw [← show ρ 0 i = 0 by rw [hc.1]; rfl] at hJ
    exact hJ.comp (f:=fun x => ρ x i) 0 ((contDiffAt_pi.mp hc.2.1) i)
  have hA (i) : ContDiffAt ℝ ω (fun x => G.mat (lifting U (represent x) (ρ x) i)) 0 :=
    ((show ContDiffAt ℝ ω (fun z => G.mat (Work.F03.live U (G:=G) z i)) (g 0) by rw [hz]; exact Work.F03.live_smooth U i).comp 0 hg)
  refine ((loop_born h _ hA).add (contDiffAt_const.mul (hd.log ((Work.F05.hessian_pos ha hQ hc t).self_of_nhds).ne'))).sub ?_
  refine (contDiffAt_prod fun i _ => hP i).log ?_
  simp [hc.1,hO.anchored]

lemma option_germs (hs : S.patch.Branches S.kernel G) (h : Critical U p W ρ) (t r : S.Choices) (O : ChartRatio G) :
    (fun x => tested U t p W x (ρ x)) =ᶠ[𝓝 0] (fun x => tested U r p W x (ρ x)) ∧
      thermal U t p W ρ O=ᶠ[𝓝 0] thermal U r p W ρ O := by
  have he := Work.F04.tested_germ hs U p W t r
  have hx := Work.F05.crit_home h
  have hi := he.comp_tendsto hx
  refine ⟨hi,?_⟩
  filter_upwards [hx.eventually (eventually_eventually_nhds.mpr he)] with x hg
  have ha : tested U t p W x =ᶠ[𝓝 (ρ x)] tested U r p W x :=
    Work.F05.hold_near (V:=fun z => tested U t p W z.1 z.2=tested U r p W z.1 z.2) hg
  unfold thermal hessian; rw [(ha.iteratedFDeriv ℝ 2).self_of_nhds]

/-- Invoices may match just ONE branch/tree per torus (still use actual
paths, orientations and the two waves including zero/polarization).
F05 about actual predictors/weights, no swapping approximate jets for
identity after differentiation. Doesn't remove any *period*. -/
lemma trial_agrees (hL : Larger (G:=G) S) (h : W.Bounds p σ D Λ) (hO : LocalRatio O)
    (h₁ : Critical U p W ρ) (h₂ : Critical U' p W ρ') (ha : 0<η) (hq : PriceGap U p W η) (hq' : PriceGap U' p W η)
    (t t' : S.Choices) :
    (∀ j, iteratedFDeriv ℝ j (fun x => tested U t p W x (ρ x)) 0 = iteratedFDeriv ℝ j (fun x => tested U' t' p W x (ρ' x)) 0) ∧
      iteratedFDeriv ℝ 2 (thermal U t p W ρ O) 0 = iteratedFDeriv ℝ 2 (thermal U' t' p W ρ' O) 0 := by
  obtain ⟨he,b,hb⟩ := Work.F05.answer G c f S hL U U' p W σ D Λ η η ρ ρ' h h₁ h₂ ha ha hq hq' O hO t'
  obtain ⟨hf,hg⟩ := option_germs hL.1 h₁ t t' O
  refine ⟨fun j => ((hf.trans he).iteratedFDeriv ℝ j).self_of_nhds,?_⟩
  rw [((hg.trans hb).iteratedFDeriv ℝ 2).self_of_nhds]
  have hD : ContDiffAt ℝ 2 (thermal U' t' p W ρ' O) 0 := (thermal_born t' h h₂ ha hq' hO).of_le le_top
  rw [show (fun x => thermal U' t' p W ρ' O x+b)=thermal U' t' p W ρ' O + (fun _ => b) from rfl,
    iteratedFDeriv_add_apply hD contDiffAt_const, iteratedFDeriv_const_of_ne (by decide : 2 ≠ 0)]
  simp
end YM.Progress.Joint

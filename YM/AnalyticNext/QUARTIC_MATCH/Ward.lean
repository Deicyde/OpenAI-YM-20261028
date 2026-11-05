import YM.AnalyticNext.QUARTIC_MATCH.Rephase

/-!
# Coarse gauge and color invariance. Ward closure only at first unmatched jet

Literal transformations near identity. Closure on real coefficient tensors including
ALL directions; not obtaining an analytic strip claim from one mesh. Cf. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch
open Filter Function Matrix Precision RG Lattice Exterior Tree Bid Wilson
open Work.F03 Work.F04 Work.F05 Topology
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge}
namespace Joint
variable {n c f : Side} {S : StepData c f}

lemma rec_zero : records (1 : Config G c)=0 := by funext i; simp [records]

def adjust (z : Dir G c × LieSpin G c) := records (Lattice.gauge (power z.2) (represent z.1))

lemma adjust_zero : adjust (0:Dir G c × LieSpin G c)=0 := by rw [adjust,Prod.snd_zero,Prod.fst_zero,power_zero,trivial,link_one,rec_zero]

lemma traced (i : Edge (Site c)) : Smooth (0 : Dir G c × LieSpin G c) fun z => Lattice.gauge (power z.2) (represent z.1) i := by
  have he (i : Site c) : Smooth (0 : Dir G c × LieSpin G c) fun z => power z.2 i :=
    Smooth.power ((contDiffAt_apply ℝ G.Color i _).comp _ contDiffAt_snd)
  exact ((he _).mul (show Smooth (0 : Dir G c × LieSpin G c) (fun z => represent z.1 i) from
    (represent_smooth (G:=G) i).contDiffAt.comp _ contDiffAt_fst)).mul (he _).inv

lemma adjust_analytic : ContDiffAt ℝ ω (adjust (G:=G) (c:=c)) 0 := by
  apply contDiffAt_pi.mpr
  intro i
  exact (traced (G:=G) (i.1,axisEquiv.symm i.2)).plog (by rw [Prod.snd_zero, Prod.fst_zero, power_zero,trivial,link_one]; rfl)

lemma adjusted : ∀ᶠ z : Dir G c × LieSpin G c in 𝓝 0,
    represent (adjust z)=Lattice.gauge (power z.2) (represent z.1) := by
  have he (i : Edge (Site c)) : ∀ᶠ z : Dir G c × LieSpin G c in 𝓝 0,
      G.lieExp (adjust z (i.1,coord i.2))=Lattice.gauge (power z.2) (represent z.1) i := by
    have ht := (traced (G:=G) i).tendsto
    dsimp only [Prod.snd_zero, Prod.fst_zero] at ht
    rw [power_zero,trivial,link_one] at ht
    simp only [adjust,records,show axisEquiv.symm (coord i.2)=i.2 from axisEquiv.symm_apply_apply _, Prod.eta]
    exact ht.eventually G.plog_right
  filter_upwards [eventually_all.mpr he] with z hz
  funext i; rw [represent_link,hz]

/-- Positive-link color differential. -/
def gradient (u : LieSpin G c) : Dir G c := fun i => u (i.1+step (axisEquiv.symm i.2)) - u i.1

lemma adjust_rate (a : Dir G c × LieSpin G c) : fderiv ℝ adjust 0 a = a.1 - gradient a.2 := by
  funext i; rcases i with ⟨i,j⟩; obtain ⟨j,rfl⟩ := axisEquiv.surjective j
  apply G.colorMat_injective
  let e : Edge (Site c) := (i,j)
  let T := fun t : ℝ => adjust (t • a)
  let Q (t : ℝ) := power (t • a.2)
  let b := fderiv ℝ adjust 0 a
  have hd : HasDerivAt T b 0 := Push.side _ (adjust_analytic.differentiableAt (by simp)) _
  have he : ∀ᶠ t : ℝ in 𝓝 0, represent (T t) = Lattice.gauge (Q t) (represent (t • a.1)) := by
    have ht : Tendsto (fun t : ℝ => t • a) (𝓝 0) (𝓝 0) := by simpa using! (show Continuous (fun t : ℝ => t • a) by fun_prop).tendsto 0
    exact ht.eventually adjusted
  have hv : T 0=0 := by unfold T; rw [zero_smul,adjust_zero]
  have hE : HasDerivAt (fun t : ℝ => G.mat (represent (T t) e)) (G.colorMat (b (i,coord j))) 0 := by
    simp_rw [represent_link]
    have hA : T 0 (i,coord j) = 0 := by rw [hv]; rfl
    exact (hA.symm ▸ G.expDiff_zero : HasFDerivAt _ _ (T 0 (i,coord j))).comp_hasDerivAt (f:=fun t => T t (i,coord j)) (0:ℝ) (hasDerivAt_pi.mp hd (i,coord j))
  have hy (i) : HasDerivAt (fun t : ℝ => G.mat (Q t i)) (G.colorMat (a.2 i)) 0 := by
    have hB : (0:ℝ) • a.2 i = 0 := zero_smul ..
    have h : HasDerivAt (fun t : ℝ => t • a.2 i) (a.2 i) 0 := by
      simpa using! (hasDerivAt_id' (0:ℝ)).smul_const (a.2 i)
    exact (hB.symm ▸ G.expDiff_zero : HasFDerivAt _ _ ((0:ℝ) • a.2 i)).comp_hasDerivAt 0 h
  have hz : HasDerivAt (fun t : ℝ => G.mat (Lattice.gauge (Q t) (represent (t • a.1)) e))
      (G.colorMat ((a.1-gradient a.2) (i,axisEquiv j))) 0 := by
    simp_rw [Lattice.gauge,G.mat_mul, G.mat_inv]
    convert! ((hy i).mul (represent_rate a.1 e)).mul (hy (i+step j)).star using 1
    simp only [Pi.mul_apply]
    simp only [show Q 0=1 by unfold Q; rw [zero_smul, power_zero]]
    simp only [e,Pi.sub_apply,gradient,zero_smul,link_one,show axisEquiv.symm (coord j)=j from axisEquiv.symm_apply_apply _,Pi.one_apply,G.mat_one,
      G.colorMat_skew,one_mul,mul_one,star_one,map_sub, show axisEquiv j=coord j from rfl]
    abel
  exact (hE.congr_of_eventuallyEq (he.mono fun t ht => congr_arg (fun V => G.mat (V e)) ht.symm)).unique hz

lemma lieExp_color (t : G.El) (v : G.Color) : G.lieExp (G.adjoint t v)=t*G.lieExp v*t⁻¹ := by
  apply G.mat_injective
  simp only [G.mat_mul,G.mat_lieExp,G.mat_inv,G.mat_adjoint]
  exact G.exp_conjugate ..

/-- All-orientation/fiber color equivariance useful for the path labels. -/
def colors (t : G.El) {ι : Type*} [Fintype ι] : (ι → G.Color) →L[ℝ] ι → G.Color :=
    ContinuousLinearMap.pi fun i => (G.adjoint t).toContinuousLinearMap ∘L ContinuousLinearMap.proj i
lemma colors_onto (t : G.El) {ι : Type*} [Fintype ι] : Surjective (colors t (ι:=ι)) := by
  intro x
  refine ⟨colors t⁻¹ x, funext fun i => ?_⟩
  change G.adjoint t (G.adjoint t⁻¹ (x i))=_
  rw [← G.adjoint_mul,mul_inv_cancel,G.adjoint_one]
lemma rep_colors (t : G.El) (a : Dir G n) : represent (colors t a)=Lattice.gauge (fun _ => t) (represent a) := by
  funext i; rw [Lattice.gauge, represent_link, represent_link]; exact lieExp_color ..

def turn (z : LieSpin G c × LieSpin G c) : LieSpin G c := fun i => G.plog (G.mat ((power z.1 * power z.2) i))

lemma turn_zero : turn (0:LieSpin G c × LieSpin G c)=0 := by funext i; simp [turn,power_zero]
lemma turned (i : Site c) : Smooth (0:LieSpin G c × LieSpin G c) fun z => (power z.1 * power z.2) i :=
  (Smooth.power ((contDiffAt_apply ℝ G.Color i _).comp _ contDiffAt_fst :
      ContDiffAt ℝ ω (fun z : LieSpin G c × LieSpin G c => z.1 i) 0)).mul
    (Smooth.power ((contDiffAt_apply ℝ G.Color i _).comp _ contDiffAt_snd))
lemma turn_analytic : ContDiffAt ℝ ω (turn (G:=G) (c:=c)) 0 :=
    contDiffAt_pi.mpr fun i => (turned (G:=G) i).plog (by simp [power_zero])
lemma turn_law : ∀ᶠ z : LieSpin G c × LieSpin G c in 𝓝 0, power (turn z) = power z.1 * power z.2 := by
  have he (i : Site c) : ∀ᶠ z : LieSpin G c × LieSpin G c in 𝓝 0,
      power (turn z) i=(power z.1 * power z.2) i := by
    have hm := (turned (G:=G) i).tendsto
    change Tendsto (fun z : LieSpin G c × LieSpin G c => (power z.1*power z.2) i) _ (𝓝 ((power (0:LieSpin G c)*power (0:LieSpin G c)) i)) at hm
    rw [power_zero, mul_one] at hm; exact hm.eventually G.plog_right
  filter_upwards [eventually_all.mpr he] with z hz; exact funext hz
lemma turn_left : ∀ᶠ z : LieSpin G c in 𝓝 0, turn (0,z)=z := by
  have hh (i : Site c) : ∀ᶠ z : LieSpin G c in 𝓝 0, G.plog (G.mat (G.lieExp (z i)))=z i :=
    ((continuous_apply i).tendsto (0:LieSpin G c)).eventually G.plog_left
  filter_upwards [eventually_all.mpr hh] with z hz
  funext i; rw [turn,power_zero,one_mul]; exact hz i

section
variable {T : Forest S.ratio} {B : Bed} {p : Clip} {W : PathData G} {b : Dir G c → AxisChart G T}
    {σ C Λ η : ℝ}
variable (h : S.patch.Branches S.kernel G) (hW : W.Bounds p σ C Λ) (hb : Critical T p W b)
    (hc : Comptroller T B p W) (hp : 0 < η) (hh : PriceGap T p W η)
include h hW hb hc hp hh

theorem color_value (k : S.Choices) (t : G.El) : value T k p W b ∘ colors t =ᶠ[𝓝 0] value T k p W b := by
  let F : Vertical G c f →L[ℝ] Vertical G c f := (colors t).prodMap (colors t)
  let L : Dir G c →L[ℝ] Dir G c := colors t
  let U := F ∘L ContinuousLinearMap.snd ℝ (Dir G c) (Vertical G c f)
  symm
  apply transfigures h hW hb hc hp hh k k id L U contDiffAt_id L.contDiff.contDiffAt
    U.contDiff.contDiffAt rfl (map_zero _) (map_zero _)
  · filter_upwards with z
    let φ : Spin G c := fun _ => t
    let w : Spin G f := fun _ => t
    have hw (x : LieSpin G c) : power (colors t x)=(φ * power x)*(w ∘ S.ratio.embed)⁻¹ :=
      funext fun i => lieExp_color ..
    change _ = fieldAction _ _ _ _ (represent (colors t z.1)) (represent (colors t z.2.1)) (power (colors t z.2.2))
    rw [hw,rep_colors,rep_colors,fine_gauge h hW,coarse_gauge]; rfl
  filter_upwards with z y
  have hu : vMap (⇑U) z=F := by rw [vMap,U.fderiv]; rfl
  rw [hu]
  obtain ⟨a,ha⟩ := colors_onto t y.1
  obtain ⟨b,hb⟩ := colors_onto t y.2
  exact ⟨(a,b), Prod.ext ha hb⟩

theorem gauge_value (k : S.Choices) : value T k p W b ∘ adjust =ᶠ[𝓝 0] value T k p W b ∘ Prod.fst := by
  let M := (Dir G c × LieSpin G c) × Vertical G c f
  let F (z : M) : LieSpin G c × LieSpin G c := (z.1.2,z.2.2)
  let U (z : M) : Vertical G c f := (z.2.1,turn (F z))
  have hF : ContDiffAt ℝ ω F 0 :=
    (contDiffAt_snd.comp _ contDiffAt_fst).prodMk (contDiffAt_snd.comp _ contDiffAt_snd)
  have hU : ContDiffAt ℝ ω U 0 := (contDiffAt_fst.comp _ contDiffAt_snd).prodMk (turn_analytic.comp (f:=F) (0:M) hF)
  symm; apply transfigures h hW hb hc hp hh k k Prod.fst adjust U contDiffAt_fst adjust_analytic hU rfl adjust_zero (Prod.ext rfl turn_zero)
  · have he : Tendsto F (𝓝 0) (𝓝 0) := hF.continuousAt.tendsto
    filter_upwards [he.eventually turn_law,(continuous_fst.tendsto (0:M)).eventually adjusted] with z hz hx
    change _ = fieldAction S k p W (represent (adjust z.1)) (represent z.2.1) (power (turn (F z)))
    rw [hx,hz]; exact (coarse_gauge ..).symm
  apply vMap_surjective hU (T:=id) differentiableAt_id rfl
  filter_upwards [(continuous_snd.tendsto (0 : Vertical G c f)).eventually turn_left] with z hz
  exact Prod.ext rfl hz
end
end Joint
end YM.AnalyticNext.QuarticMatch

import YM.AnalyticNext.QUARTIC_MATCH.Pre.Center
import YM.AnalyticNext.QUARTIC_MATCH.Rephase

/-!
# Centered joint calculus

Energy and the literal fine gauge variation. Real flat. Keeps access back
to the rooted slice and recognition with the same path data. Usable on any
admissible finite torus without mesh or rank exclusions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Pre
open Filter Function Lattice RG Wilson Precision Push Bid Exterior Bloch Matrix Tree Work.F03 Work.F04
open Joint Knot
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

attribute [local instance] Gauge.frobInner

namespace Centered

variable {G : Gauge} {n c f : Side}

section tools
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def record (t : Spin G c) : LieSpin G c := fun i => G.plog (G.mat (t i))
@[simp] lemma record_power : record (1:Spin G c)=0 := by funext i; simp [record]
lemma write_right {θ : X → Spin G c} (h : ∀ i, Smooth 0 (fun v => θ v i)) (he : θ 0=1) : power ∘ record ∘ θ =ᶠ[𝓝 0] θ := by
  have hg (i : Site c) : ∀ᶠ v : X in 𝓝 0,power (record (θ v)) i=θ v i := by
    have hh : Tendsto (fun v => θ v i) (𝓝 0) (𝓝 (θ 0 i)) := (h i).tendsto
    rw [he] at hh; exact hh.eventually G.plog_right
  filter_upwards [eventually_all.mpr hg] with v hv; exact funext hv
lemma write_left : record ∘ power =ᶠ[𝓝 (0:LieSpin G c)] id := by
  have he (i : Site c) : ∀ᶠ v : LieSpin G c in 𝓝 0, G.plog (G.mat (G.lieExp (v i)))=v i :=
    ((continuous_apply i).tendsto (0:LieSpin G c)).eventually G.plog_left
  filter_upwards [eventually_all.mpr he] with v hv; exact funext hv
lemma write_smooth {θ : X → Spin G c} (h : ∀ i,Smooth (0:X) (fun v => θ v i)) (he : θ 0=1) :
    ContDiffAt ℝ ω (record ∘ θ) 0 :=
    contDiffAt_pi.mpr fun i => (h i).plog (congr_fun he i)
lemma power_jet (x : Site c) : Smooth (0:LieSpin G c) fun a => power a x :=
    Smooth.power (contDiffAt_apply _ _ _ _)
lemma power_ray {u : ℝ → LieSpin G c} {v : LieSpin G c} (he : u 0=0) (h : HasDerivAt u v 0) (i : Site c) :
    HasDerivAt (fun x : ℝ => G.mat (power (u x) i)) (G.colorMat (v i)) 0 := by
  have hh := (hasDerivAt_pi.mp h i)
  have hv : u 0 i=0 := congr_fun he i
  exact (hv.symm ▸ G.expDiff_zero : HasFDerivAt (fun a => G.mat (G.lieExp a)) _ (u 0 i)).comp_hasDerivAt (f:=fun x => u x i) _ hh
lemma power_rate (u : LieSpin G c) (i : Site c) : HasDerivAt (fun s : ℝ => G.mat (power (s • u) i)) (G.colorMat (u i)) 0 :=
    power_ray (u:=fun s => s • u) (by simp) (by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const u) i
end tools

variable (S : StepData c f) (t : S.Choices)
abbrev JointSpace (G : Gauge) (c f : Side) := Dir G c × Vertical G c f
local notation "Y" => Vertical G c f
local notation "Z" => JointSpace G c f

def cash (p : Clip) (W : PathData G) (z : JointSpace G c f) := mainTerm p W (represent z.2.1) +
    groupEnergy S.kernel (Lattice.gauge (power z.2.2) (send S t z.2.1)) (represent z.1)
def twist (z : Y) : Spin G c := power z.2 * (centroid S t.1 z.1)⁻¹
def rooted (z : Y) : Y := (z.1,record (twist S t z))
def crown (z : Y) : Spin G c := power z.2 * (centroid S t.1 z.1)
def crowned (z : Y) : Y := (z.1,record (crown S t z))

variable (h : S.patch.Branches S.kernel G)
include h

section
lemma twist_one : twist S t (0:Y)=1 := by simp [twist,at_identity S h,power_zero]
lemma root_start : rooted S t (0:Y) = 0 := Prod.ext rfl (by change record (twist S t 0)=0; rw [twist_one S t h,record_power])
lemma crown_one : crown S t (0:Y)=1 := by simp [crown,at_identity S h,power_zero]
lemma crowned_one : crowned S t (0:Y)=0 := Prod.ext rfl (by change record (crown S t 0)=0; rw [crown_one S t h,record_power])
lemma twist_smooth (i : Site c) : Smooth (0:Y) (fun z => twist S t z i) :=
    ((show Smooth (0:Y) (fun z => power z.2 i) from (power_jet (G:=G) i).comp (f:=Prod.snd) (0:Y) contDiffAt_snd)).mul
      ((center_smooth S h t.1 i).inv.comp (f:=Prod.fst) (0:Y) contDiffAt_fst)
lemma crowned_rate (i : Site c) : Smooth (0:Y) (fun z => crown S t z i) :=
    ((show Smooth (0:Y) (fun z => power z.2 i) from (power_jet (G:=G) i).comp (f:=Prod.snd) (0:Y) contDiffAt_snd)).mul
      ((center_smooth S h t.1 i).comp (f:=Prod.fst) (0:Y) contDiffAt_fst)
lemma analytic : ContDiffAt ℝ ω (rooted S t (G:=G)) 0 := contDiffAt_fst.prodMk (write_smooth (twist_smooth _ t h) (twist_one _ t h))
lemma analytic' : ContDiffAt ℝ ω (crowned S t (G:=G)) 0 := contDiffAt_fst.prodMk (write_smooth (crowned_rate _ t h) (crown_one _ t h))
lemma roots : rooted S t ∘ crowned S t =ᶠ[𝓝 (0:Y)] id := by
  filter_upwards [write_right (crowned_rate S t h) (crown_one S t h), (continuous_snd.tendsto (0:Y)).eventually write_left] with v hv hh
  refine Prod.ext rfl ?_
  change power (record (crown S t v))=crown S t v at hv
  change record (power (record (crown S t v)) * (centroid S t.1 v.1)⁻¹)=v.2
  rw [hv,crown,mul_inv_cancel_right]; exact hh

lemma wires (p : Clip) (W : PathData G) : cash S t p W =ᶠ[𝓝 0] Joint.action S t p W ∘ (fun z => (z.1,rooted S t z.2)) := by
  filter_upwards [(continuous_snd.tendsto (0:Z)).eventually (write_right (twist_smooth S t h) (twist_one S t h))] with z hz
  unfold cash Joint.action fieldAction
  change _=_+groupEnergy _ (Lattice.gauge (power (record (twist S t z.2))) (S.prediction (represent z.2.1) t)) (represent z.1)
  rw [show power (record (twist S t z.2))=twist S t z.2 from hz,twist,← gaugeTwice]; rfl
lemma root_draft : ∀ᶠ z : Z in 𝓝 0,Surjective (vMap (rooted S t ∘ Prod.snd) z) := vMap_surjective
    ((analytic S t h).comp (f:=Prod.snd) (0:Z) contDiffAt_snd) ((analytic' S t h).differentiableAt (by simp)) (crowned_one _ _ h) (roots _ _ h)
end

section
variable {T : Forest S.ratio} {p : Clip} {W : PathData G} {b : Dir G c→AxisChart G T} {σ C Λ : ℝ}
    (hP : W.Bounds p σ C Λ) (hb : Critical T p W b)
include hP hb
lemma starts : ContDiffAt ℝ ω (cash S t p W) 0 := by
  let v (z : Z) : Z := (z.1,rooted S t z.2)
  have hv : v 0=0 := Prod.ext rfl (root_start S t h)
  exact (((hv.symm ▸ Joint.root_born h hP hb t) : ContDiffAt ℝ ω (Joint.action S t p W) (v 0)).comp _
    (show ContDiffAt ℝ ω v 0 from contDiffAt_fst.prodMk ((analytic S t h).comp (f:=Prod.snd) (0:Z) contDiffAt_snd))).congr_of_eventuallyEq (wires S t h p W)
lemma buys (B : Bed) (hv : Comptroller T B p W) {η : ℝ} (he : 0 < η) (hq : PriceGap T p W η)
    (d : Dir G c→Y) (hd : OnShell (cash S t p W) d 0) (e0 : d 0=0) :
    cash S t p W ∘ arc d =ᶠ[𝓝 0] Joint.value T t p W b := by
  let v (z : Z) : Z := (z.1,rooted S t z.2)
  have hh : v 0=0 := Prod.ext rfl (root_start S t h)
  have heU := vert_pull (L:=id) (p:=rooted S t ∘ Prod.snd) ((analytic S t h).comp (f:=Prod.snd) (0:Z) contDiffAt_snd) contDiffAt_id (wires S t h p W)
    (show ContDiffAt ℝ ω (Joint.action S t p W) (v 0) from hh.symm ▸ Joint.root_born h hP hb t)
  have ht : Tendsto v (𝓝 0) (𝓝 0) := by
    have he' := (show ContDiffAt ℝ ω v 0 from contDiffAt_fst.prodMk ((analytic S t h).comp (f:=Prod.snd) (0:Z) contDiffAt_snd)).continuousAt.tendsto; rwa [hh] at he'
  have hx := ht.eventually (Joint.recognizes h hP hb t B hv he hq)
  have ha : arc d 0 = 0 := Prod.ext rfl e0
  have hk := hd.arc_smooth.continuousAt.tendsto; rw [ha] at hk
  filter_upwards [hk.eventually heU,hk.eventually (root_draft S t h),hk.eventually hx,
    hk.eventually (wires S t h p W),hd.station] with z hz hs hw hh hy
  apply hh.trans (hw ?_)
  apply ContinuousLinearMap.ext; intro y
  obtain ⟨u,rfl⟩ := hs y
  exact DFunLike.congr_fun (hz.symm.trans hy) u
end
end Centered
end YM.AnalyticNext.QuarticMatch.Pre

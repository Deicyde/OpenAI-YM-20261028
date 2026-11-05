import YM.TraceExtension.Perfect.Tyke
import YM.Next.STATIONARY.FrameEst.Stencils

/-! # Compact stencil chart independent of period for directional critical prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:Patch}{Y:KernelChoices}
variable {c f:Side} (S:StepData c f)(t:S.Choices)

def pillow (v:Bool)(x:BassInput G P)(i:Option Axis):G.El:= entryCap P (parkIt i (pianoU v x) P)
def rawPose (v:Bool)(x:BassInput G P)(i:Axis):G.El:=
    (pianoC v x none * pillow v x none) * victoryBox P (pianoU v x) i * (pianoC v x (some i) * pillow v x (some i))⁻¹
lemma pillow_germ (h:P.Branches Y G)(v i):ContDiffAt ℝ ω (fun x:BassInput G P=> G.mat (pillow v x i)) 0:=by exact tower_carries h v i
lemma pose_germ (h:P.Branches Y G)(v i): ContDiffAt ℝ ω (fun x:BassInput G P=> G.mat (rawPose v x i)) 0:=by
 let F := pianoC (G:=G) (P:=P) v
 have hF : Army F 0:= actors h false v
 let E := pillow (G:=G) (P:=P) v
 have hE : Army E 0:= pillow_germ h v
 let H x := F x none * E x none * (F x none)⁻¹ * poseBox false v x i * F x (some i) * (E x (some i))⁻¹ * (F x (some i))⁻¹
 have hh : ContDiffAt ℝ ω (fun x=> G.mat (H x)) 0:= ((((((hF none).mul (hE none)).mul (hF.inv none)).mul (poseCast h false v i)).mul (hF (some i))).mul (hE.inv (some i))).mul (hF.inv (some i))
 suffices he: ∀ x, rawPose v x i=H x by simp_rw [he];exact hh
 intro x; unfold H poseBox; rw [show musicStand false v x=F x from rfl]; unfold rawPose; unfold F E; group
lemma raw0 (h:P.Branches Y G)(v i): rawPose v (0:BassInput G P) i=1:=by
    simp only [rawPose,pianoC_origin, piano_origin, victory_box0 h, pillow]; simp only [piano_origin,entry_zero h,parkIt,hall_one]; simp

def tuneP (p:Axis)(j:G.ColorIndex)(x:BassInput G P) := plogC G (rawPose true x p * (rawPose false x p)⁻¹) j
lemma tune_jet (h:P.Branches Y G)(p j): ContDiffAt ℝ ω (tuneP (P:=P) (G:=G) p j) 0:=by
  let H x:= rawPose (P:=P) (G:=G) true x p * (rawPose false x p)⁻¹
  have he: ContDiffAt ℝ ω (fun x=> G.mat (H x)) 0:= (pose_germ h true p).mul (Push.Loops.mat_inv_diff (pose_germ h false p))
  exact (EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.contDiffAt.comp (f:=fun x=> G.plog (G.mat (H x))) 0 ((show ContDiffAt ℝ ω G.plog (G.mat (H 0)) from by simp [H,raw0 h]; exact G.plog_diff).comp (f:=fun x=> G.mat (H x)) _ he)

variable (h:S.patch.Branches S.kernel G)
include h
lemma pillow_at (v : Bool)(i : Site c) : ∀ᶠ x : Bang G c f in 𝓝 0,∀ j:Option Axis, bears S t (initialBang v x).1 ((j.map fun a => i+step a).getD i) = pillow v (pianist S i x) j:=by
 filter_upwards [piano_pact (G:=G) S h v i,eventually_all.mpr (fun k : Site c=> centered_wire S t h (initial_nice (G:=G) v).1 (by rw [initial_zero]; rfl) k 0)] with x hx hh
 intro j; cases j with
 | none=> dsimp only [Option.map,Option.getD]; rw [(hh i).1]; simp only [pillow,entryCap,entryHat,parkIt,hx.1]
 | some a=> simp only [Option.map,Option.getD]; rw [(hh (i+step a)).1,← house_moves S (initialBang v x).1]; simp [pillow,parkIt,entryCap,entryHat,(hx.2 a).2]
lemma raw_pose (v:Bool)(p:Site c)(i:Axis) : ∀ᶠ x : Bang G c f in 𝓝 0,
    ribbon S t (initialBang v x) (p,i)= rawPose v (pianist S p x) i:=by
 filter_upwards [pillow_at S t h v p,piano_pact (G:=G) S h v p,centered_wire S t h (initial_nice (G:=G) v).1 (by rw [initial_zero]; rfl) p i] with x hx he hy
 rw [rawPose,piano_tops,piano_tops,← hx, ← hx,← (he.2 _).1,← hy.2]; simp only [ribbon,Lattice.gauge, Option.getD,Option.map]; group
lemma pin_germ (p:Site c) (i:Axis)(j:G.ColorIndex): ∀ᶠ x : Bang G c f in 𝓝 0, worn S t 1 (Stationary.extend x.1.2) x.2.1 (p,coord i,j)=tuneP i j (pianist S p x):=by
 filter_upwards [raw_pose S t h true p i, raw_pose S t h false p i] with x hx hy
 rw [tuneP, ← hx,← hy]; unfold worn; simp only [atire,dress_one,initialBang,↓reduceIte]; exact congr_arg (fun x:G.Color=> x j) (content_at ..)

-- matrix entries
abbrev barTag (U:Stationary.Joint G c f) : Bang G c f := ((0,retract U),0)
abbrev outTest (z:Link G f): Bang G c f:= (0,((z,0),0))
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]{U:X→ Stationary.Joint G c f}{p : Clip}{R:PathData G}{α M C:ℝ}
lemma tunes_the (hz:R.Bounds p α M C)(hU:Thaw U 0)(e : U 0=1)(A:Link G f)(v : Site c) (i : Axis)(j:G.ColorIndex) :
    ∀ᶠ z in 𝓝 0, fineRelay S t (U z) A (v,coord i,j) = fderiv ℝ (tuneP i j) (pianist S v (barTag (U z))) (pianist S v (outTest (c:=c) A)):=by
 let k:=pianist (G:=G) S v
 let L:ℝ→Bang G c f:= fun z=> z • outTest A
 let B(x): Bang G c f:= barTag (U x); have hT:B 0=0:=by simp [B,barTag,e]
 have ht : Tendsto B (𝓝 0) (𝓝 0):=by
    have hv : ContDiffAt ℝ ω B 0:= (ContDiffAt.prodMk contDiffAt_const (hU.log e)).prodMk contDiffAt_const; rw [← hT]; exact hv.continuousAt.tendsto
 let g: BassInput G S.patch→ ℝ:= tuneP i j
 filter_upwards [(show Tendsto k _ (𝓝 0) from by simpa using k.continuous.tendsto 0).comp ht|>.eventually ((tune_jet h i j).eventually (by simp)), ht.eventually (eventually_eventually_nhds.mpr (pin_germ S t h v i j)), (show Tendsto U _ (𝓝 1) from e ▸ hU.cont.tendsto).eventually extend_retract,Stationary.awake t hz hU (by rw [e];rfl) h root_customs] with x hx he hh hf
 let z:= B x; let W (a:ℝ):= z + a • outTest A; let H := worn S t 1 (U x)
 have hw:HasDerivAt W (outTest A) 0:= (ray_id (outTest A)).const_add _
 have hZ:W 0=z:=by unfold W; rw [zero_smul,add_zero]
 have hW:Tendsto W (𝓝 0) (𝓝 z):=hZ ▸ hw.continuousAt.tendsto
 suffices ht : (fun a:ℝ=> H (a • ((A,0):Vault G c f)) (v,coord i,j)) =ᶠ[𝓝 0] fun a:ℝ=> g (k (W a)) by
    have hd:HasDerivAt (fun a:ℝ=> g (k (W a))) (fderiv ℝ g (k z) (k (outTest A))) 0:= ((show HasFDerivAt g (fderiv ℝ g (k z)) ((k ∘ W) 0) from by rw [Function.comp_apply,hZ]; exact (hx.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 (k.hasFDerivAt.comp_hasDerivAt 0 hw))
    exact (hasDerivAt_pi.mp (Push.side H (hf.wist.differentiableAt (by simp)) (A,0)) (v,coord i,j)).unique (hd.congr_of_eventuallyEq ht)
 filter_upwards [hW.eventually he] with a ha
 change _= g (k _); change _ = g (k (W a)) at ha; rw [← ha]; simp [W,z,B,outTest,barTag,hh,H]
end YM.Trace.Perfect

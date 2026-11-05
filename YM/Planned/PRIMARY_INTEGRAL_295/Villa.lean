import YM.Planned.PRIMARY_INTEGRAL_295.Clouds
import YM.Planned.PRIMARY_INTEGRAL_295.Steeple
/-!
# Precision/HILTS paths on real coarse torus for Loom Ancestor

Now assumptions at Gram paths and b rows (normalized affine vector already
verified external sphere requirement). No smooth b rewriting under patches
unless literal X & Vc hypothesis. Preserve all data/indices in full H 
including global ray estimator `ν` on SAME installed W tree. Windows literal
physical Keys incl held center. Cost synthesis polynomial. Not proving external
contact formulas identify Gram entries, etc. Off-hub zeros for active
centered requests, so compression does not require a fake alternate sampler.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Villa
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Nimbuses Tropics Cedar Kelps Precision Exterior Tree Streets Porous Carrier Bloch Place
open Bazaars Launch Shapes Floor Glints Fizz Gush Progress.StationaryScenes.Green Push.Uniform
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {E F ι κ : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n k d : ℕ} {C M σ α t u s : ℝ} {T : Finset Cover} {c f : Side} {S:StepData c f} {G : Gauge} {Ψ : Labels.Frame G d}

-- all keys incl unavailable. Rays read strictly same Motion map in
-- permit. Support & cuts all retained post.
abbrev Acres (f:Side) (G:Gauge):=Edge (Site f)× G.ColorIndex
variable (V:Gush G S E)
def outlier (i:V.Keys): Acres f G := (i.1.val.val,i.2)
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma outlier_inj : Injective (outlier V) := by
   rintro ⟨i,j⟩ ⟨k,l⟩ h
   cases i; cases k; unfold outlier at h; simp_all; exact Subtype.ext h.1

def rays (W:Lines S.ratio.count) (y:E) (a:Acres f G):ℝ:=
    (Streets.streamFill S _ (crick S V.tree W (V.b y)) a.1) a.2

/-- Physical hub labels chosen to include WORLD D rows adequate at W.
C columns conditional on this same gauge/frame at V each y-path receipt. 
A appears COMPLETED. No Gram improvement unless cut proves exactness with
actual measured tickets. foam is actual affine-source b divided by t, *not*
cbc b-Coarse. Echo includes marker ∀ intersections with patch predicates etc
through Raw/M receipts separate. No assumptions on b outside hub here.
-/
structure Post where
   hub : Finset (Acres f G)
   h₀ (i): outlier V i ∈ hub
   homes : Windows (⟨fun i:V.Keys=> (⟨outlier V i,h₀ i⟩:hub),fun _ _ h=> outlier_inj V (congr_arg Subtype.val h)⟩:V.Keys ↪ hub)
   A : E→Matrix (Acres f G) (Acres f G) ℝ
   foam : E→Acres f G→ℝ

namespace Post
variable {V} (P: Post V)
def period : P.hub→Site c:=fun j=> S.ratio.parent j.val.1.1
def beacon : V.Keys ↪ P.hub:=⟨fun i=>⟨outlier V i,P.h₀ i⟩, fun _ _ h=> outlier_inj V (congr_arg Subtype.val h)⟩
def foyer (x:E): Matrix P.hub P.hub ℝ:= (P.A x).submatrix Subtype.val Subtype.val
def sky (W:Lines S.ratio.count) (x:E): P.hub→ℝ:= (rays V W x) ∘ Subtype.val
def ash (x:E): P.hub→ℝ:= P.foam x ∘ Subtype.val

-- U even Probe coherence.
structure Service (T:Finset Cover) (W:Lines S.ratio.count) (h:Aim) (k:ℕ) (r:ℕ) (u s : ℝ) : Prop where
    tests : P.homes.Vestal h P.foyer P.ash (P.sky W) P.period k u s r
    mistCost : 2*u^11*Windows.mist h r≤1
    data : V.C=ᶠ[𝓝 0] fun x:E=> P.homes.coin (P.foyer x)
    dane (i:V.Keys) : (fun x=> (V.mean x i.1.val) i.2) =ᶠ[𝓝 0] fun x=> P.homes.morn (P.foyer x) (P.ash x) i
    snow : ∀ i:V.Keys, ∀ j:P.homes.W i, ∀ k:Acres f G, k∉ P.hub → (fun x=> P.A x j.val.val k)=ᶠ[𝓝 0] 0
    cups : (Fintype.card V.held:ℝ) ≤ u
    ridge : V.ε ∈ Ioc 0 1 ∧ 8 ≤ u*V.ε
    profiles : ∀ x, Envelope x k V.pulse.χ u
    footprint : V.encompasses T

-- Merchant payout after volcano V.T. Actual factors billed peppers.
open Glints.Windows

def bark (k:ℕ) (u:ℝ):= max (Glaze.clearFuel u) (u^2*willow u k)
lemma bask_power (k:ℕ): ∃ (A:ℝ)(N:ℕ),1≤A∧∀ u≥1,u≤ bark k u ∧ bark k u ≤ A*u^N:=by
   obtain ⟨M,b,hM,h⟩:=will_power k
   refine ⟨M+2,5+b+2,by linarith,fun u hu=>?_⟩
   refine ⟨?_,max_le ?_ ?_⟩
   · have hw:=pow_le_pow_right₀ hu (show 1≤5 by norm_num)
     rw [pow_one] at hw; refine le_trans (b:=Glaze.clearFuel u) (by unfold Glaze.clearFuel; linarith) (le_max_left ..)
   · unfold Glaze.clearFuel; exact mul_le_mul (by linarith) (pow_le_pow_right₀ hu (by omega)) (by positivity) (by linarith)
   calc
    _ ≤ u^2*(M*u^b):=mul_le_mul_of_nonneg_left (h u hu) (by positivity)
    _ = M*u^(b+2):=by ring
    _ ≤ _:=mul_le_mul (by linarith) (pow_le_pow_right₀ hu (by omega)) (by positivity) (by linarith)

section
variable {h:Aim} {W:Lines S.ratio.count} {r:ℕ}
theorem remitted (ht:P.Service T W h k r u s) (hh: bark k u≤M):V.Kind k M:=by
   let H:=ht.tests
   have hu:=H.price; have hp : (Fintype.card V.Keys:ℝ)≤u:=
     (Nat.cast_le.mpr (Fintype.card_le_of_embedding P.beacon)).trans H.tops
   let Y:= fun x:E=> P.homes.coin (P.foyer x)
   have hB : Glaze.clearFuel u ≤ M:= (le_max_left ..).trans hh
   obtain ⟨a,b,hw,hRt⟩:=bask_power k; have hR: u≤M:= (hRt u hu).1.trans hh
   have hm:=hu.trans hR; have he : 1≤Glaze.clearFuel u:=Glaze.clearFuel_pos u hu
   have hx:= Glaze.balance P.homes H.toGlaze ht.mistCost; change Clear (Y 0) (Glaze.clearFuel u) at hx
   have hf:=ht.data
   constructor
   · rw [hf.self_of_nhds]; refine ⟨hm,hx.2.1,fun z=>?_⟩
     apply (hx.2.2 z).trans; refine mul_le_mul_of_nonneg_right hB ?_
     exact nonneg_of_mul_nonneg_right ((sq_nonneg _).trans (hx.2.2 z)) (lt_of_lt_of_le zero_lt_one he)
   · have hg:=stream_em (fun i j=>Glaze.licked P.homes H.toGlaze i j)
     have ht : (Fintype.card V.Keys:ℝ)^2*willow u k ≤ M:= (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp 2)
       (zero_le_one.trans (hu.trans (will_le hu k)))).trans ((le_max_right ..).trans hh)
     exact Ember.renamed (Ember.weakening hg ht) (hf.mono (fun x hh=> congr_arg (MapB V.Keys) hh))
   · filter_upwards [hf] with x hx; rw [hx]; exact Windows.coin_symmetric ..
   · exact hp.trans hR
   · exact ht.cups.trans hR
   · exact ⟨ht.ridge.1,ht.ridge.2.trans (mul_le_mul_of_nonneg_right hR ht.ridge.1.1.le)⟩
   · exact fun x=> Seas.less (ht.profiles x) hR





-- use at Service and Worth interpretation

def herald (G:Gauge) (u:ℝ) (k : ℕ) := (Fintype.card G.ColorIndex:ℝ)*Vestal.till k u

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private lemma streams (T:Finset Cover) (g:E→AxisChart G V.tree) (i:Spot T) (x:E):
    let a:Edge (Site f):=(wrap f (Place.first i).val,Place.beam i); let H := meets T S V.tree
    (H∘g) x i=if ha:a∈V.tree.trunks then 0 else g x ⟨a,ha⟩:=by
  intro a H; change Streets.streamFill S V.tree (g x) a=_
  unfold Streets.streamFill; rw [ContinuousLinearMap.pi_apply]; split <;> rfl


end
end Post
end YM.Planned.PrimaryIntegral295.Villa

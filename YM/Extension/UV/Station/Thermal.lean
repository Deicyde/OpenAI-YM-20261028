import YM.Extension.UV.Station.Survey
import YM.Extension.UV.Station.Tracking
/-! Passing the finite-period two-jet covers to actual profile clusterpoints.
Field-independent scalar offsets still not compared. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Extension.UV.LoopRate
open Function Filter Lattice Precision RG Wilson Exterior Tree WilsonStartup.Change Stationary StationaryData
open scoped Matrix ContDiff BigOperators Topology Matrix.Norms.Frobenius
section finite
variable {G:Gauge} {c f:Side}{S:StepData c f}(F:Forest S.ratio) (t:S.Choices) {W T:PathData G} {p q:Clip}
  {C:ChartRatio G} (hC:LocalRatio C)
local notation "Z"=>VChart G F
local notation "M"=>fieldDir G c 1
local notation "H"=>AxisChart G F

def logJ (D:ChartRatio G) (a:AxisChart G F) := Real.log (∏ i,J_proj D a i) where J_proj (D:ChartRatio G) (a:AxisChart G F) k:=D.J (a k)
lemma j_smooth (hC:LocalRatio C) : ContDiffAt ℝ ω (logJ F C) 0 :=by
 apply ContDiffAt.log (f:=fun a=>(∏ i, (logJ.J_proj F C a i))) (x:=0)
 · apply contDiffAt_prod
   intro i hi
   apply ContDiffAt.comp (g:=C.J) (x:=(0:H)) (f:=fun a=>a i)
   · change ContDiffAt ℝ ω C.J _; apply hC.germ; simpa using hC.patch
   exact (contDiff_apply ℝ G.Color i).contDiffAt -- maybe
 simp [logJ.J_proj,hC.anchored]

def detAction (W:PathData G) (p:Clip) (a:M) (b:H) := (hessian F t p W a b).det
def mass (W:PathData G) (p:Clip) (C:ChartRatio G) (u:Z) := (1/2 :ℝ)* Real.log (detAction F t W p u.1 u.2) - logJ F C u.2
def pulses (W:PathData G) (u:Z):= loop W (readFine F u)
lemma thermal_split g W : thermal F t p W g C=(pulses F W + mass F t W p C) ∘ WilsonStartup.Change.graph g := by funext i; exact (by unfold thermal pulses mass detAction logJ readFine Function.comp WilsonStartup.Change.graph; dsimp [logJ.J_proj]; ring)

lemma det_here : uncurry (detAction F t W p) = slice_det (E:=fieldDir G _ 1) (F:=AxisChart G F) (ι:=Key F G) (frame F) (onSlice F t p W):=rfl

section
variable {p' : Clip} {η:ℝ} {A : Crossover p p' W T η F} {u:ℕ→fieldDir G c 1→AxisChart G F}
   {R R':ℕ→PathData G} {α₀:ℝ}{α:ℕ→ℝ}{D:ℝ}
   (hM:Tracks ∞ (fun n=>onSlice F t p (R n)) (onSlice F t p W) (0:VChart G F)) (hA:Crossover.Accepts F A u) (he:∀ᶠ n in atTop,Critical F p (R n) (u n))
   (hp:Tracks ∞ (fun n=>pulses F (R n)) (pulses F W) (0:VChart G F))
   (hp':Tracks ∞ (fun n v=>loop (R' n) (represent v)) (loop T ∘ (represent (n:=c))) 0)
   (hk:Tracks ∞ (fun n v=>secondTerm p' (R' n) (represent v)) (secondTerm p' T ∘ (represent (n:=c))) 0)
   (hα:Tendsto α atTop (nhds α₀))
include hM hA hC hp in
lemma price_track : Tracks ∞ (fun n=>pulses F (R n) + mass F t (R n) p C) (pulses F W + mass F t W p C) 0:=by
   have ht : Tracks ∞ (fun n (z:Z)=>detAction F t (R n) p z.1 z.2) (Function.uncurry (detAction F t W p)) 0:=by rw [det_here]; convert determinant_tracks (frame F) hM using 1; funext n; exact det_here ..
   let L:=fun (a:ℝ)=> (1/2 : ℝ)*Real.log a
   have hl:ContDiffAt ℝ ω L (detAction F t W p 0 0):= contDiffAt_const.mul (contDiffAt_id.log (show detAction F t W p 0 0 ≠ (0:ℝ) from by unfold detAction; rw [←hA.crit.1]; exact (Work.F05.hessian_pos hA.positive hA.gap hA.crit t).self_of_nhds.ne'))
   let J (z:Z):=logJ F C z.2
   have hj:=Tracks.unswerving J ((j_smooth F hC).of_le (m:=∞) le_top |>.comp (f:=Prod.snd) (0:Z) contDiffAt_snd) -- at snd 0 =0
   exact hp.add ((ht.outside L hl).sub hj)
include hM hA hC hp he -- for thermal_track
lemma thermal_track (k:ℕ)(v:M): Tendsto (fun n=>dirT (thermal F t p (R n) (u n) C) k 0 v) atTop (nhds (dirT (thermal F t p W A.choice C) k 0 v)):=by
 let w n:=WilsonStartup.Change.graph (u n); let s:= WilsonStartup.Change.graph A.choice
 have hw j x : Tendsto (fun n=>dirT (w n) j 0 x) atTop (nhds (dirT s j 0 x)):= by
   unfold s; change Tendsto _ _ (nhds (dirT (fun z=>(id z,A.choice z)) j 0 x)); rw [tensor_joint (onSlice F t p W) id A.choice _ contDiffAt_id (hA.crit.2.1.of_le le_top)]
   apply (tendsto_const_nhds.prodMk_nhds (hA.travel j x)).congr'
   exact he.mono fun n hn=> (tensor_joint (onSlice F t p W) id (u n) (v:=x) 0 contDiffAt_id (hn.2.1.of_le le_top)).symm
 simp_rw [thermal_split]
 apply solved_comp _ _ (price_track F t hC hM hA hp) w s _ _ _ hw
 · filter_upwards [he] with n hn; exact ⟨(station_of hn t).at0,(station_of hn t).chart.of_le le_top⟩
 · exact (station_of hA.crit t).at0
 · exact (station_of hA.crit t).chart.of_le le_top
omit hM hA hC hp he in
include hk hp' hα in
lemma draft_track (k:ℕ)(v:M): Tendsto (fun n=>dirT (draft (α n) (R' n) p') k 0 v) atTop (nhds (dirT (draft α₀ T p') k 0 v)):=by
   have hf:=hk.at_each.and hp'.at_each
   have hel (w₁ w₂ : M→ℝ) (a:ℝ) (h₁:ContDiffAt ℝ ∞ w₁ 0) (h₂:ContDiffAt ℝ ∞ w₂ 0): dirT (fun x=> a*w₁ x+w₂ x) k 0 v = a*dirT w₁ k 0 v+dirT w₂ k 0 v:=by
       let L : ℝ→L[ℝ]ℝ:= a • ContinuousLinearMap.id ℝ ℝ
       change dirT (L∘w₁+w₂) k 0 v = L (dirT w₁ k 0 v)+dirT w₂ k 0 v
       rw [dirT,iteratedFDeriv_add_apply ((L.contDiff.contDiffAt.comp _ h₁).of_le (mod_cast le_top)) (h₂.of_le (mod_cast le_top))] -- clean
       exact congrArg (·+ _) (linear_dirT L w₁ _ _ rfl h₁ k v)
   rw [show draft (c:=c) (G:=G) α₀ T p'=fun v=>α₀*(secondTerm p' T ∘ represent) v+(loop T ∘ represent) v from rfl,hel _ _ _ hk.at_limit hp'.at_limit]
   apply ((hα.mul (tracks_t _ _ _ hk k v)).add (tracks_t _ _ _ hp' k v)).congr'
   exact hf.mono fun n hn=>Eq.symm (hel _ _ _ hn.1 hn.2)
include hk hp' hα in
lemma inherited {v:M}
 (hD:∀ᶠ n in atTop,|iteratedFDeriv ℝ 2 (thermal F t p (R n) (u n) C) 0 ![v,v] - iteratedFDeriv ℝ 2 (draft (α n) (R' n) p') 0 ![v,v]| ≤ D):
      |dirT (thermal F t p W A.choice C) 2 0 v - dirT (draft α₀ T p') 2 0 v| ≤ D:=by
   have h1:(fun (_:Fin 2)=>v)=![v,v]:=by ext1 i; fin_cases i <;> rfl
   apply le_of_tendsto (continuous_abs.continuousAt.tendsto.comp ((thermal_track F t hC hM hA he hp 2 v).sub (draft_track hp' hk hα 2 v)))
   exact hD.mono fun n hn=>by simpa only [dirT,Function.comp_apply,h1] using hn
end
end finite
end YM.Extension.UV.LoopRate

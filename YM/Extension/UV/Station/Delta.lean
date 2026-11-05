import YM.Extension.UV.Station.Thermal
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Extension.UV.LoopRate
open Function Filter Lattice Precision RG Wilson Exterior Tree WilsonStartup.Change Stationary StationaryData
open scoped Matrix ContDiff BigOperators Topology Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side}{S:StepData c f}(F:Forest S.ratio) (t:S.Choices) {W T:PathData G} {p q:Clip}
  {C:ChartRatio G} (hC:LocalRatio C)
local notation "Z"=>VChart G F
local notation "M"=>fieldDir G c 1
local notation "ChartA"=>AxisChart G F
local notation "Y"=>fieldDir G f 1

def L (f:Side)(Q:PathData G)(a:fieldDir G f 1):= loop Q (represent a)
def Q' (f:Side) (p:Clip)(Q:PathData G) (a:fieldDir G f 1):= secondTerm p Q (represent a)
private noncomputable abbrev take (f:Side) := (arm G f 1)

lemma rooted (W:PathData G)(p:Clip)(h:∃ σ C Λ,W.Bounds p σ C Λ) :
  Matches 2 (AT f p W) (Q' f p W) 0 ∧ Matches 1 (L f W) 0 0:= by
    obtain ⟨σ,C,Λ,h⟩:=h
    have h3:= (turns_analytic (m:=f) W.cubic h.width h.three).contDiffAt (n:=ω); have h4:= (turns_analytic (m:=f) W.quartic h.width h.four).contDiffAt (n:=ω); have h2:= (turns_analytic (m:=f) W.loop h.width h.two).contDiffAt (n:=ω)
    have hs:= (stain_knit (m:=f) W p h).analytic.contDiffAt (n:=ω)
    let T:= (arm G f 1).symm
    have hx₁:intended (m:=f) p W ∘ T = AT f p W:= funext fun a=> by unfold AT intended input Function.comp T; simpa
    have hx₂:inputSeries (m:=f) p W ∘ T = Q' f p W:= funext fun a=> by unfold inputSeries Q' input Function.comp T; simpa
    have hx₃:turnSeries (m:=f) W.loop ∘ T = L f W:= funext fun a=> by unfold turnSeries L loop input Function.comp T; simpa
    have hm : Matches 2 (intended (m:=f) p W) (inputSeries p W) 0:=by
       rw [intent]
       refine ⟨(hs.add h3).add h4,hs,fun i hi=>?_⟩
       rw [iteratedFDeriv_add_apply (f:=(inputSeries (m:=f) p W + turnSeries W.cubic)) ((hs.add h3).of_le le_top) (h4.of_le le_top),iteratedFDeriv_add_apply (hs.of_le le_top) (h3.of_le le_top), (rays_jet h4.analyticAt 4).mp (turns_low _ _ h.four) _ (by omega),(rays_jet h3.analyticAt 3).mp (turns_low _ h.width h.three) _ (by omega),add_zero,add_zero]; exact h.width
    have hm':Matches 1 (turnSeries W.loop (m:=f)) (fun _=>0) 0:=by
       refine ⟨h2, contDiffAt_const,fun j hj=>?_⟩; rw [(rays_jet h2.analyticAt 2).mp (turns_low _ h.width h.two) _ (by omega)]; exact congr_fun iteratedFDeriv_zero.symm 0 -- check
    rw [show (0:Link G f)=_ from T.map_zero.symm] at hm hm'
    rw [←hx₁, ←hx₂, ←hx₃]
    exact ⟨hm.comp_refl T.contDiff.contDiffAt,hm'.comp_refl T.contDiff.contDiffAt⟩
private lemma pulse_smooth {P:PathData G} (h:∃σ C Λ,P.Bounds p σ C Λ) : ContDiffAt ℝ ω (pulses F P) 0:=by
    have he:= (rooted P (f:=f) p h).2.left
    have hv: (L f P) ∘ (Work.F03.axisLog F) =ᶠ[𝓝 (0:Z)] pulses F P := (log_works (G:=G) F).mono fun z hz=> by change represent _ = _ at hz; change loop P _ = loop P _; rw [hz]
    exact ((log_zero F (G:=G)).symm ▸ he).comp (0:Z) (log_smooth F) |>.congr_of_eventuallyEq hv.symm

section matchData
variable {P₁ P₂:PathData G} {η:ℝ} {A: Crossover p q W T η F}{B:Crossover p q P₁ P₂ η F} {u u':ℕ→ fieldDir G c 1→ AxisChart G F}
  (hA:Crossover.Accepts F A u) (hB:Crossover.Accepts F B u') (hW:Matches 4 (AT f p W) (AT f p P₁) 0)
include hC hA hB hW
lemma mass_delta : Matches 2 (mass F t W p C ∘ WilsonStartup.Change.graph A.choice) (mass F t P₁ p C ∘ WilsonStartup.Change.graph B.choice) 0:=by
  let x:=A.choice; let y:=B.choice; let g:=WilsonStartup.Change.graph x; let g':=WilsonStartup.Change.graph y; let hF:= hA.crit; let h:=tested_match hW hF t
  have hQ := definite_of hA.gap hA.positive t h.left
  have he : Matches 2 g g' 0 := ((compare h (station_of hF t) (station_of hB.crit t) hQ).1.lower (by decide))
  have hx := (station_of hF t).at0
  let f (P : PathData G) := fun z : Z => (hessian F t p P z.1 z.2).det
  have hdet : Matches 2 (f W) (f P₁) (g 0) := Eq.mpr (congr_arg (Matches 2 (f W) (f P₁)) hx) (compare_det h)
  have hd : Matches 2 (f W ∘ g) (f P₁ ∘ g') 0 := hdet.comp he
  have hj := he.refl_comp (u:=fun z:Z=> logJ F C z.2) ((show g 0=(0:Z) from hx).symm ▸ (j_smooth F hC).comp (f:=Prod.snd) (0:Z) contDiffAt_snd)
  have h₁ := (Work.F05.hessian_pos hA.positive hA.gap hF t).self_of_nhds
  exact hd.together hj (H:=fun a b => (1/2)*Real.log a - b) (((contDiffAt_fst.log h₁.ne').const_smul (1/2 : ℝ)).sub contDiffAt_snd)
include t
omit hC in
lemma graph_equal : Matches 2 (WilsonStartup.Change.graph A.choice) (WilsonStartup.Change.graph B.choice) 0:=
  ((compare (tested_match hW hA.crit t) (station_of hA.crit t) (station_of hB.crit t) (definite_of hA.gap hA.positive t (hA.crit.2.2 t).1)).1.lower (by decide)) -- edit
def current (v:fieldDir G c 1) (x:fieldDir G c 1→AxisChart G F) := fderiv ℝ (WilsonStartup.Change.graph x) 0 v
def tune (v:fieldDir G c 1) (x:fieldDir G c 1→AxisChart G F) := Bid.stretch (S:=S) F (current F v x)
omit hC hB hW in
lemma pulse_core (v:M)(he:∃σ C Λ,W.Bounds p σ C Λ): dirT (pulses F W ∘ WilsonStartup.Change.graph A.choice) 2 0 v=dirT (L f W) 2 0 (Bid.stretch (S:=S) F (current F v A.choice)):=by
    have hv: (L f W) ∘ (Work.F03.axisLog F ∘ WilsonStartup.Change.graph A.choice) =ᶠ[𝓝 (0:M)] pulses F W ∘ WilsonStartup.Change.graph A.choice := by
        filter_upwards [(station_of hA.crit t).home.eventually (log_works (G:=G) F)] with x hx
        exact congrArg (loop W) hx
    let hx := WilsonStartup.Change.graph A.choice
    have hq : ContDiffAt ℝ ω (Work.F03.axisLog F ∘ hx) 0:= (show ContDiffAt ℝ ω _ (hx 0) from (show hx 0=0 from (station_of hA.crit t).at0).symm ▸ log_smooth F).comp _ (station_of hA.crit t).chart
    have hg:=swing_main hx (Work.F03.axisLog F) (0:M) v ((show hx 0=0 from (station_of hA.crit t).at0).symm ▸ log_smooth F) (station_of hA.crit t).chart
    rw [show hx 0=0 from (station_of hA.crit t).at0,log_dir (G:=G) (S:=S)] at hg
    have hW:=(rooted W (f:=f) p he).2
    exact (DFunLike.congr_fun ((hv.iteratedFDeriv ℝ 2).self_of_nhds).symm _).trans ((pure_pull (k:=2) (g:=L f W) (w:=Work.F03.axisLog F ∘ hx) (by decide) hW.left hq (show Work.F03.axisLog F (hx 0)=0 from (show hx 0=0 from (station_of hA.crit t).at0).symm ▸ log_zero F) (by intro i hi; have he:=hW.jets i (by omega); simpa using he) v).trans (by rw [hg];rfl))

omit hC in
lemma current_eq (v:M): current F v A.choice=current F v B.choice:=by
  have hh : dirT (WilsonStartup.Change.graph A.choice) 1 0 v = dirT (WilsonStartup.Change.graph B.choice) 1 0 v:=
    DFunLike.congr_fun ((graph_equal F t hA hB hW).jets 1 (by norm_num)) _
  simpa only [current,dirT_one] using hh
lemma equation (v:M) (he:∃σ C Λ,W.Bounds p σ C Λ)(he':∃σ C Λ,P₁.Bounds p σ C Λ):
    dirT (thermal F t p W A.choice C) 2 0 v - dirT (thermal F t p P₁ B.choice C) 2 0 v=dirT (L f W) 2 0 (tune F v A.choice) - dirT (L f P₁) 2 0 (tune F v A.choice):=by
  let g:= WilsonStartup.Change.graph A.choice; let g':= WilsonStartup.Change.graph B.choice
  have hQ := mass_delta F t hC hA hB hW
  have hel {q z:M→ℝ}(hq:ContDiffAt ℝ ω q 0)(hz:ContDiffAt ℝ ω z 0): dirT (q+z) 2 0 v = dirT q 2 0 v + dirT z 2 0 v:= DFunLike.congr_fun (iteratedFDeriv_add_apply (hq.of_le le_top) (hz.of_le le_top)) _
  have hx₁ : ContDiffAt ℝ ω (pulses F W ∘ g) 0:= ((show g 0=0 from (station_of hA.crit t).at0).symm ▸ pulse_smooth F he).comp _ (station_of hA.crit t).chart
  have hx₂ : ContDiffAt ℝ ω (pulses F P₁ ∘ g') 0:= ((show g' 0=0 from (station_of hB.crit t).at0).symm ▸ pulse_smooth F he').comp _ (station_of hB.crit t).chart
  rw [thermal_split,thermal_split]
  change dirT (pulses F W ∘ g + mass F t W p C ∘ g) .. - dirT (pulses F P₁ ∘ g' + mass F t P₁ p C ∘ g') ..= _
  rw [hel hx₁ hQ.left,hel hx₂ hQ.right]
  have hd := DFunLike.congr_fun (hQ.jets 2 le_rfl) (fun _=>v)
  rw [show dirT (mass F t W p C ∘ g) 2 0 v=dirT (mass F t P₁ p C ∘ g') 2 0 v from hd,add_sub_add_right_eq_sub,show dirT (pulses F W ∘ g) 2 0 v = _ from (pulse_core F t hA v he), show dirT (pulses F P₁ ∘ g') 2 0 v = _ from (pulse_core F t hB v he'),current_eq F t hA hB hW]
  simp only [tune,current_eq F t hA hB hW]
end matchData
end YM.Extension.UV.LoopRate

import YM.WilsonBulk.Build.Invoice
import YM.Next.STATIONARY.Joint.Gauge

/-!
# Algebra-real border gate (joint near across private charts)

Absolute log coordinates on tree T. Material determinant compatibility with
WHEN branch toll in log density, still no volume amplitude claims. Use
`slit.process` which employs full fine measure-preserving transformation.
Can use at ANY aux. spectator length (period). Keeps analyticity order
ω here. The physical change outside this collar isn't asserted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Atelier.Coursing
open Lattice RG Wilson Precision Exterior Sheet
open Function Filter Sum
open Work.F05 (toll parcel)
open Stationary (Army)
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {α X ι κ : Type} [Fintype ι] [Fintype κ] {c f : Side} {G : Gauge} {S : StepData c f}
variable (R : Tabletop κ → Carries G S) (F L : Coursing ι S) (P : Bed)
abbrev Secrets (G : Gauge) (ι κ : Type) := Tabletop (Chamber (LegsT G ι) κ)
variable (u v : Tabletop κ → Interface G c) (J : ChartRatio G)
-- log change on slice transported x; subtract opposite mean at fixed spectator.

def seatingA (G : Gauge) (F : Coursing ι S) (P : Bed) (u : Tabletop κ→Interface G c) (z : Secrets G ι κ) := dress G F (whitener G F P u z)
def removal (G : Gauge) (y : F.tree.Slice G) : AxisChart G F.tree := fun i=> G.plog (G.mat (y i))
def taxi (z : Secrets G ι κ) := (R (lower _ _ z)).slit F.tree L.tree (Work.F05.exposure F.tree 0 (seatingA G F P u z))
def lands (z : Secrets G ι κ) : Tabletop (LegsT G ι) := (dress G L).symm (removal L G (taxi R F L P u z)) - quill (priceK G L P) (v (lower _ _ z))
lemma seating_tag (z : Secrets G ι κ) : seatingA G L P v (ride (lands R F L P u v) z)= removal L G (taxi R F L P u z) := by
  rw [seatingA,whitener,lower_ride,upper_ride,lands,sub_add_cancel,ContinuousLinearEquiv.apply_symm_apply]
lemma taxi_as (z : Secrets G ι κ) : taxi R F L P u z= Profiles.wick L.tree ((R (lower _ _ z)).routeG (signal G f (palace G F P u z))) := by
  rw [palace,signal_trunk]; rfl
-- operation coherence for a visitor supplied by the actual gauge & pull
structure Legible : Prop where
  plays : Army (fun z : Secrets G ι κ=> (R (lower _ _ z)).routeG (signal G f (palace G F P u z))) 0
  arrived : (R 0).routeG 1=1
omit [Fintype ι] in
lemma tea_one (F : Coursing ι S) : Profiles.wick F.tree (1:Config G f)=1 := by
  rw [show (1:Config G f)=F.tree.drape 1 by symm; funext i; by_cases he:i∈ F.tree.trunks; exact F.tree.on_tree _ ⟨i,he⟩; exact F.tree.off_tree _ ⟨i,he⟩, Profiles.wick_root]
lemma taxi_origin (h : u 0=0) (hx : (R 0).routeG 1=1) : taxi R F L P u 0=1 := by rw [taxi_as,palace_zero _ h,signal_zero,map_zero,hx,tea_one]
omit [Fintype ι] in
lemma removal_closed : removal F G 1=0 := by ext i; simp [removal]
lemma lands_origin (hu : u 0=0) (hv : v 0=0) (hx : (R 0).routeG 1=1) : lands R F L P u v 0=0 := by rw [lands, taxi_origin _ _ _ _ _ hu hx, removal_closed, map_zero,map_zero,hv,quill_zero,sub_zero]
lemma taxi_jet (hh : Legible R F P u) : Army (taxi R F L P u) 0 := by -- type params check
  intro i; simp_rw [taxi_as,Profiles.wick,Profiles.wiped]; exact ((Stationary.drape_lit S L.tree hh.plays).slant hh.plays) i
lemma lands_jet (h : u 0=0) (hv : ContDiffAt ℝ ω v 0) (hh : Legible R F P u) : ContDiffAt ℝ ω (lands R F L P u v) 0 := by
  let Z := taxi R F L P u
  have he : ContDiffAt ℝ ω (removal L G ∘ Z) 0 := by
    apply contDiffAt_pi.mpr; intro i; refine ContDiffAt.comp (g:=G.plog) (f:=fun z=> G.mat (Z z i)) 0 ?_ ?_; rw [show Z 0=1 from taxi_origin _ _ _ _ _ h hh.arrived, Pi.one_apply,G.mat_one]; exact G.plog_diff
    exact taxi_jet _ _ _ _ _ hh i
  let D:=lower (LegsT G ι) κ; exact ((dress G L).symm.contDiff.contDiffAt.comp 0 he).sub ((quill_smooth _).contDiffAt.comp 0 ((show ContDiffAt ℝ ω v (D 0) by rw [map_zero]; exact hv).comp _ D.contDiff.contDiffAt))
lemma equal_slices (h : u 0=0) (hh : Legible R F P u) :
    ∀ᶠ z in 𝓝 (0:Secrets G ι κ),Work.F05.exposure L.tree 0 (seatingA G L P v (ride (lands R F L P u v) z))=taxi R F L P u z := by
  let t:= taxi R F L P u
  have he i : ∀ᶠ z in 𝓝 (0:Secrets G ι κ), G.lieExp (G.plog (G.mat (t z i)))=t z i := by
    refine (tendsto_pi_nhds.mp ((show Tendsto t (𝓝 0) (𝓝 1) from ?_)) i).eventually G.plog_right
    rw [← (show t 0=1 from taxi_origin _ _ _ _ _ h hh.arrived)]; exact (taxi_jet _ _ _ _ _ hh).cont.tendsto
  filter_upwards [eventually_all.mpr he] with z hv; rw [seating_tag]; ext1 i; simp only [Work.F05.exposure,link_one,replica_one,Pi.one_apply,mul_one]; exact hv i
lemma into_loom (h : u 0=0) (hh : Legible R F P u) :
    ∀ᶠ z in 𝓝 (0:Secrets G ι κ), signal G f (palace G L P v (ride (lands R F L P u v) z))= Profiles.wiped L.tree ((R (lower _ _ z)).routeG (signal G f (palace G F P u z))) := by
  filter_upwards [equal_slices R F L P u v h hh] with z hz
  rw [taxi_as] at hz; rw [← Profiles.wears]; conv_lhs => rw [palace,signal_trunk]
  exact congr_arg L.tree.drape hz
-- germ: cruise fixed y over ext ν then vert theta private
lemma charting {θ : Secrets G ι κ→Tabletop (LegsT G ι)} {z : Secrets G ι κ} (h : ContDiffAt ℝ ω θ z) : ContDiffAt ℝ ω (verticalChange θ z) (upper _ _ z) := by
  let A := LegsT G ι; let p (i:Tabletop (LegsT G ι)) := Sum.elim i (lower _ _ z)
  have hp : ContDiffAt ℝ ω p (upper _ _ z) := (assemble (LegsT G ι) κ).contDiff.contDiffAt.comp _ (contDiffAt_id.prodMk contDiffAt_const)
  exact ((show p (upper _ _ z)=z from mirror_pose z).symm ▸ h).comp _ hp -- possible rewrite all
lemma seating_shifted (z : Secrets G ι κ) : seatingA G F P u z= shiftPrice G F (quill (priceK G F P) (u (lower _ _ z))) (upper _ _ z) := rfl
lemma invoice [DecidableEq ι] (hu : ContDiffAt ℝ ω u 0) (h : u 0=0) (hv : ContDiffAt ℝ ω v 0) (ht : v 0=0) (he : Legible R F P u) (hJ : LocalRatio J) :
    let T:= lands R F L P u v; ∀ᶠ z in 𝓝 (0:Secrets G ι κ), toll F.tree J (seatingA G F P u z)=|(tilted T z).det| * toll L.tree J (seatingA G L P v (ride T z)) := by
  intro T
  have hT:= lands_jet R F L P u v h hv he
  let U:=upper (LegsT G ι) κ; let D:=lower (LegsT G ι) κ; let b z := quill (priceK G F P) (u (D z)); let d z:= quill (priceK G L P) (v (D z)); let X:=seatingA G F P u; let Y:=seatingA G L P v∘ ride T
  have hx : Tendsto X (𝓝 0) (𝓝 0) := by
    have hp : X 0=0 := by unfold X seatingA; rw [whiten_zero _ h,map_zero];
    exact hp ▸ ((F.dress G).continuous.continuousAt.comp (whiten_jet (F:=F) (P:=P) G hu).continuousAt).tendsto
  have hr : ContDiffAt ℝ ω (ride T) 0:= ride_jet T hT
  have hy : Tendsto Y (𝓝 0) (𝓝 0) := by
    have H : Y 0=0:= by unfold Y Function.comp T seatingA; rw [ride_zero _ (lands_origin _ _ _ _ _ _ h ht he.arrived),whiten_zero _ ht,map_zero]
    have hp : ContDiffAt ℝ ω (ride T) 0:= hr
    suffices h : ContDiffAt ℝ ω Y 0 from H ▸ h.continuousAt.tendsto
    unfold Y; refine ((L.dress G).contDiff.contDiffAt.comp _ (show ContDiffAt ℝ ω (whitener G L P v) (ride T 0) from ?_)).comp _ hr
    rw [ride_zero T (lands_origin _ _ _ _ _ _ h ht he.arrived)]; exact whiten_jet _ hv
  have hg : ∀ᶠ z in 𝓝 (0:Secrets G ι κ), privateGate G F L (R (D z)) J (b z) (d z) (verticalChange T z) (U z) := by
    filter_upwards [equal_slices R F L P u v h he,hT.eventually (by simp),hx.eventually (Work.F05.parcel_zero F.tree hJ),hy.eventually (Work.F05.parcel_zero L.tree hJ)] with z h₁ hz h₂ h₃
    have hx : shiftPrice G F (b z) (U z)= X z:= rfl
    have hy : shiftPrice G L (d z) (verticalChange T z (U z))=Y z := by unfold Y d U D verticalChange Function.comp; rw [seating_shifted,lower_ride,upper_ride,mirror_pose]
    refine ⟨charting hz,hx ▸ h₂,hy ▸ h₃,?_⟩; rw [hx,hy]; exact h₁
  filter_upwards [eventually_eventually_nhds.mpr hg,hT.eventually (by simp)] with z hz hT'
  have hp : ∀ᶠ y in 𝓝 (U z), privateGate G F L (R (D z)) J (b z) (d z) (verticalChange T z) y := by
    have he := ((field_left (LegsT G ι) κ (D z) (U z)).continuousAt.tendsto)
    have hx : Sum.elim (U z) (D z)=z := mirror_pose _
    rw [hx] at he; refine (he.eventually hz).mono fun y hm=> ?_; unfold b d U D verticalChange at *; simpa using hm
  rw [fee_ordinary (θ:=T) (z:=z) (hT'.differentiableAt (by simp))]; have he := privateFee G F L (R _) J hJ _ _ _ _ hp
  unfold verticalChange U at he; rw [mirror_pose] at he -- dependent occurrence under det! adjust
  exact he
end YM.WilsonBulk.Atelier.Coursing

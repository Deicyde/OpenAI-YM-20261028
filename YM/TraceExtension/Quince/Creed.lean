import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Central
import YM.TraceExtension.Quince.Pay
/-! # End of E.Barn.Chromatic invoice at U=1. Actual footage used by Mercury survives per-test barriers. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Gas Ursell Trees Daisy Daisy.Charity Push.SectorMeasure.Oriented Brim Lotus Peak Greenbelt WardBin.Lies Next.Foundations
open Mercury Blaze.March Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation Malachite Matter Shell Flux Poll Pond Polar Silica Eider Set Gaussian Tablet Quill Baffle Prism
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
    {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {W μ x C' : ℝ} {R : Rep G f}
    {p j n m k : ℕ} {L : Side} {Q: ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {d A t C w M N z β r η v b Y' q e: ℝ}{C₀ : Libretto G n}
open Cub
section head
variable {u:Site c} {g:Config G c→ℝ}
lemma staysW {m:ℕ}(h:∀ V U, (∀ i: Bond c,separation u i.1 ≤ m→V i= U i)→ g V=g U) (l:List (Directions G c))(W:Directions G c→Directions G c)(he:∀ i∈l,∀ j: Bond c,separation u j.1 ≤ m→W i j=i j):
    ∀ V U, (∀ i:Bond c,separation u i.1 ≤ m→V i=U i)→leftDerivs g l V=leftDerivs g (l.map W) U:=by
   induction l with
   | nil=>exact h
   | cons i l ih=>
     intro V U hv
     refine congr_arg (fun f=>deriv f 0) (funext fun (t:ℝ)=>show leftDerivs g l (increment V (t • i))=_ from ih (fun i hi=>he _ (List.mem_cons_of_mem _ hi)) _ (increment U (t • W i)) (fun j hj=>?_))
     unfold increment; simp only [hv j hj,Pi.smul_apply,he i (by simp) j hj]
end head
variable (H:Cash W x μ L Q o C T R) (f' : Leaf R) (i : ℕ) (hx:f'.turn=.logKey i)
variable (D:Record)(κ q':Chi)(ε:ℝ)(hN: Captain H p C' d v t A b r M q m Chi.canonical) (hR:Herd H hN.conduit A M m)
variable (L':Config G f→ℝ)(h':R.p.Regular (R.activities.reg i).support L')(hm:f'.ingredient=masked R.p.threshold (R.activities.reg i).support L')
    (h:C₀.Z=C₀.Z)(hp:Plays C₀ D B R.p P T x)(hv:PermitY Q C₀ D B.power W o κ μ x z L) (hB:B.B=radiusB x)(hn:B.order≤p) (hq:Q.halo+5≤k)
    (hh:coverNumber B.B (plate H i).support≤ B.B)
set_option quotPrecheck false
local notation "Y₀"=> plate H i
local notation "X"=> R.activities.reg i
local notation "T0"=> (1:Config G c)
-- helper should know shape.J.Cl.K. orientation op sign.
variable {τ:ℝ} (he:R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support L' τ)
    (hs: Until C₀ D B R.p S (R.activities.reg i).site (R.activities.reg i).support (plate H i).support (Malachite.radiusD x) x)
    {P': Teller G}{X':Tube G S}(hZ:Plays C₀ D B R.p P' X' x) (hV: ∀ F k, Mercury.hore H i D κ q' ε L' F k=(mapcase H i F).hymn X' (gStep R.beta) q' ε k L' (Baffle.magic D R.p R.beta κ) 1)
    (hP: opalW C₀ D B R.p (radiusD x) L (R.activities.reg i).support k x (gStep R.beta) ≤ 1)
local notation "u0"=> gStep R.beta
local notation "s"=> opalW C₀ D B R.p (radiusD x) L (R.activities.reg i).support k x u0
local notation "s0"=> clocks C₀ τ * s * Moments.meter (Lute.heads G R.p L (R.activities.reg i).support k x) 0 D.K (2*((n+1)+(n+1)))
include hp hv hB hP hZ hh hn hq hV hs he hR hm hx h'
lemma anthemW (hj:j+1≤ n)(l:List (Directions G c))(hl:l.length ≤ j)(hb:∀ v∈l,B.dirBound (plate H i).site v): let F:= matin f' H (icon H i) Chi.canonical; let Z:=dimW (R.activities.reg i).site (radiusD x) X' L'
    ‖leftDerivs F l 1-leftDerivs Z l 1‖ ≤ f'.weight*z+s0:=by
  intro F Z
  letI : Nonempty (Forest S.ratio):= Tree.select _ S.patch.odd_side; let A:= Classical.arbitrary (Forest S.ratio)
  let t:= (Y₀).support; have hU:= one_healthy (G:=G) t _ B.threshold_pos.le
  have hT:= cornice H f' i hx D Chi.canonical hN hp hR hn; let O:=(plate H i).site; have hM: ∀ V U,(∀ i:Bond c,separation O i.1 ≤ radiusD x→V i=U i)→ Z V=Z U:=by
    intro V U hv; unfold Z dimW; simp only[Function.comp_apply]; congr 3; ext1 i; unfold Heir.crop; split; · next hh=> rw [Lattice.gauge, Lattice.gauge,hv i hh]
    rfl
  let σ (v:Directions G c) (i:Bond c):= if separation O i.1 ≤ radiusD x then v i else 0; let L0:= l.map σ
  have hf:= H.laws.data; have hL:= hf.funds.length_eq
  have hk: ∀ v∈L0,B.dirBound (Y₀).site v:=by
     intro v hv; obtain ⟨u,h,rfl⟩:=List.mem_map.mp hv; intro i; unfold σ; split; · exact hb u h i
     rw [norm_zero]; positivity [B.threshold_pos]
  have hK(v)(hv:v∈L0): ‖v‖ ≤ canopyW G L B.power x:=by
     have hS:B.threshold ≤ 2*fiery G x L:=by rw [hp.rehearsed.temp_eq,← hL]; exact hf.room.temperatures
     have hvv:=hk v hv; have ha:= B.threshold_pos.trans_le hS; have ha':0≤2*fiery G x L:=ha.le
     apply (pi_norm_le_iff_of_nonneg (show 0≤ canopyW G L B.power x from mul_nonneg ha' (pow_nonneg (by positivity) _))).2; intro j
     by_cases he':separation O j.1 ≤ radiusD x
     · have hy:= hvv j; apply hy.trans; rw [separation_comm _ (Y₀).site]; unfold canopyW; gcongr
     obtain ⟨u,hh,hu⟩:=List.mem_map.mp hv; rw [← hu,show σ u j=0 from if_neg he',norm_zero]; unfold canopyW; positivity
  have hl:L0.length ≤ j:=by unfold L0; rw [List.length_map]; exact hl
  have hyd: j ≤ n:=Nat.le_of_lt hj
  have hp': n=B.order:=hp.rehearsed.test.symm
  let G' :=(fun V:Config G c=>groves H i D κ q' ε V L')
  let a:=leftDerivs G' L0 1
  rw [March.stays (g:=F) hT.sites l σ (fun i hi j hj=> if_pos (hs.feasible _ hj)) T0 T0 (fun _ _ _=>rfl), staysW hM l σ (fun i hi j hj=> if_pos hj) T0 T0 (fun _ _=>rfl)]
  have heq:a=likely (fun F: Greenbelt.Reserve S=> likely (fun g:S.Choices=> leftDerivs (hore H i D κ q' ε L' (allot F) g) L0 1)) := (masts H i D κ q' ε T0 hp L' h' hU).2 _ (hl.trans hyd)
  have hk':0< u0:=inv_pos.mpr (Real.sqrt_pos.mpr H.laws.intake.positive)
  apply (norm_sub_le_norm_sub_add_norm_sub _ a _).trans (add_le_add (signs H f' i hx D κ q' ε hN hR _ h' hm hp hv hB hn hh 1 hU L0 ((hl.trans hyd).trans_eq hp') hk hK) ?_)
  rw [heq]; refine like_sub_tame _ (fun x'=> like_sub_tame _ (fun g=>?_))
  rw [hV]; let v':= Greenbelt.allot x'; have h:= gasketW (a:=mapcase H i v') (U:=1) (k:=g) (d:=ε) (q:=q') hZ h' he (R.activities.reg i).anchor hs hj (billboard H hq i) κ hk' (hL.symm ▸ hP) L0 hl hk
  rw [hL] at h
  exact h
end YM.PhysicalNext.Repeat.Quince

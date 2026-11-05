import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Dolphin
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Riddle
import YM.ProofPorts.GRID_RENEWED_RESERVES.LedgerSheet
/-! # End of E.Barn.Chromatic invoice at U=1. Actual footage used by Mercury survives per-test barriers. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
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
lemma cabin {ι:Type} (U0 : Museum F x (bareStores S) K Y ι) (X:Tube G S)(f':Config G f→ℝ) (o:Site f)(ho:o ∈ K) : LocalOn Y (deem o x X f'):=by -- edit
   intro A B h; let y:=S.ratio.parent o; suffices Heir.crop y (reach x) (1:Site c→G.El) A= Heir.crop y (reach x) 1 B from congr_arg (f' ∘ increment (1:Config G f) ∘ Heir.route X) this
   ext1 i; unfold Heir.crop; split; swap; rfl
   next h' =>
   have hs:= U0.asks o (Finset.mem_union_left _ ho); let z:=separation y (i.1+step i.2)
   have hz : z ≤ Heir.reach x+4 := calc
       _ ≤ Heir.reach x + 1:= (separation_triangle y i.1 _).trans (Nat.add_le_add h' ?_)
       _ ≤ _:=by omega
   swap; · rw [separation_comm,separation,add_comm,add_sub_cancel_right]; exact pdist_step _
   unfold Lattice.gauge; rw [h i (hs (halo_spec.mpr ⟨y,Finset.mem_singleton_self _,h'.trans (by omega)⟩)) (hs (halo_spec.mpr ⟨y,Finset.mem_singleton_self _,hz⟩))]

lemma like_sub_tame {A : Type}[Fintype A][Nonempty A](F : A→ℝ)(hp:∀ i, ‖F i-b‖ ≤ t): ‖likely F-b‖ ≤ t:=by
    have h: likely F - b=likely (fun i=>F i-b):=by nth_rw 1 [← likely_constant (A:=A) b]; unfold likely; rw [Finset.sum_sub_distrib,mul_sub]
    have hV:0<(Fintype.card A:ℝ):=by positivity
    rw [h, likely,norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hV.le)]
    refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum (g:=fun _=> t) (fun i _=> hp i))) (inv_nonneg.mpr hV.le)).trans ?_
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul, inv_mul_cancel_left₀ hV.ne']

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
    (hs: Short S R.p (R.activities.reg i).support)
    {P': Teller G}{X':Tube G S}(hZ:Plays C₀ D B R.p P' X' x) (hV: ∀ F k, Mercury.hore H i D κ q' ε L' F k=(mapcase H i F).hymn X' (gStep R.beta) q' ε k L' (Baffle.magic D R.p R.beta κ) 1)
    (hP: opal C₀ D B R.p L (R.activities.reg i).support k x (gStep R.beta) ≤ 1)
local notation "u0"=> gStep R.beta
local notation "s"=> opal C₀ D B R.p L (X).support k x u0
local notation "s0"=> clocks C₀ τ * s * Moments.meter (Lute.heads G R.p L (X).support k x) 0 D.K (2*((n+1)+(n+1)))
include hp hv hB hP hZ hh hn hq hV hs he hR hm hx h'
lemma anthem (hj:j+1≤ n)(l:List (Directions G c))(hl:l.length ≤ j)(hb:∀ v∈l,B.dirBound (plate H i).site v): let F:= matin f' H (icon H i) Chi.canonical; let Z:=deem (R.activities.reg i).site x X' L'
    ‖leftDerivs F l 1-leftDerivs Z l 1‖ ≤ f'.weight*z+s0:=by
  intro F Z
  letI : Nonempty (Forest S.ratio):= Tree.select _ S.patch.odd_side; let A:= Classical.arbitrary (Forest S.ratio)
  let t:= (Y₀).support; have hU:= one_healthy (G:=G) t _ B.threshold_pos.le
  have hT:= cornice H f' i hx D Chi.canonical hN hp hR hn; have hM:LocalOn t Z:= cabin (mapcase H i A) X' L' _ (X).anchor
  let σ (v:Directions G c) (i:Bond c):= if i.1∈ t then v i else 0; let L0:= l.map σ
  have hf:= H.laws.data; have hL:= hf.funds.length_eq
  have hk: ∀ v∈L0,B.dirBound (Y₀).site v:=by
     intro v hv; obtain ⟨u,h,rfl⟩:=List.mem_map.mp hv; intro i; unfold σ; split; · exact hb u h i
     rw [norm_zero]; positivity [B.threshold_pos]
  have hK(v)(hv:v∈L0): ‖v‖ ≤ canopyW G L B.power x:=by
     have hS:B.threshold ≤ 2*fiery G x L:=by rw [hp.rehearsed.temp_eq,← hL]; exact hf.room.temperatures
     refine pacing _ t ?_ _ (Y₀).anchor rfl (hk v hv) x _ (hB ▸ hh) hS; obtain ⟨u,hh,hu⟩:=List.mem_map.mp hv; intro i h; rw [← hu]; exact if_neg h
  have hl:L0.length ≤ j:=by unfold L0; rw [List.length_map]; exact hl
  have hyd: j ≤ n:=Nat.le_of_lt hj
  have hp': n=B.order:=hp.rehearsed.test.symm
  let G' :=(fun V:Config G c=>groves H i D κ q' ε V L')
  let a:=leftDerivs G' L0 1
  rw [March.stays (g:=F) hT.sites l σ (fun i hi j hj=> if_pos hj) T0 T0 (fun _ _ _=>rfl), March.stays hM l σ (fun i hi j hj=> if_pos hj) T0 T0 (fun _ _ _=>rfl)]
  have heq:a=likely (fun F: Greenbelt.Reserve S=> likely (fun g:S.Choices=> leftDerivs (hore H i D κ q' ε L' (allot F) g) L0 1)) := (masts H i D κ q' ε T0 hp L' h' hU).2 _ (hl.trans hyd)
  have hk':0< u0:=inv_pos.mpr (Real.sqrt_pos.mpr H.laws.intake.positive)
  apply (norm_sub_le_norm_sub_add_norm_sub _ a _).trans (add_le_add (signs H f' i hx D κ q' ε hN hR _ h' hm hp hv hB hn hh 1 hU L0 ((hl.trans hyd).trans_eq hp') hk hK) ?_)
  rw [heq]; refine like_sub_tame _ (fun x'=> like_sub_tame _ (fun g=>?_))
  rw [hV]; let v':= Greenbelt.allot x'; have h:= gasket (a:=mapcase H i v') (U:=1) (k:=g) (d:=ε) (q:=q') hZ h' he (X).anchor hs hj (billboard H hq i) κ hk' (hL.symm ▸ hP) L0 hl hk
  rw [hL] at h -- likely dependent h
  exact h
end YM.PhysicalNext.Repeat.Cub

import YM.TraceExtension.Terrace.PriceLimit
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Finset Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux Next.UVStress
open Further.PhysicalPeriodLimitF933 Next.Rank.Spindle Cells PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Next.Rank.Station
open UVNext.FreeStress (camera)
open MeasureTheory
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
set_option quotPrecheck false
local notation "A"=>C.path.levels
local notation "V!"=> C.labels.level 5
variable (P:C.Makes) (h:G.Simple)(θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels) {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} {S:Table C.book} {Z:Arch C} {X:Scaling S}
variable (hb:(𝓛:Filter (ℕ×ℕ)) ≤ F.fuse) (hS:S.Hierarchy) (HF:F.PointLimits C S)
variable {V:∀ i,Vane C i}{Y:∀ d i:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}{H:(Cells.standard C).Hierarchy}
variable (hq:Gondola F H X 𝓛 V Y) (hp:StarPath F H X hS 𝓛) {s:ℕ → Bowl (C.labels.level 5) →L[ℝ] (TableOne H.spin)}
variable (hP:Spun Z X V H s) (hZ:steep 𝓛 Z) {J:DiffPlan (Cells.standard C)}{W':DiffPlan S} (hw:W'.Derivatives S) (hJ:J.Derivatives (Cells.standard C))(ho:J.Orientation H.spin)
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "m!"=>Stern V
variable (t:ℕ → ℕ×ℕ→ C.label 5)(x:ℕ→ Bowl (C.labels.level 5))(hy:Mission V 𝓛 t (fun i=>((x i).val 0)))
include ht hM P hb h θ K hS HF hq hy hp hZ hP hw hJ ho
lemma small_means (p:ℕ) (v:ℕ→ Bowl (C.labels.level 5)) (hv:∀ᶠ i in atTop,∀ a:Axis,(v i).val a=(Z.β (Stern V i))⁻¹ • swale Z 5 (Stern V i) ((x i).val a)) :
     Tendsto (fun i=> (A).clock.hatBeta (Stern V i)^p • s i (v i)) atTop (𝓝 0):=by
    let Q i:= (V i).k; let u i:=beaconV i V
    let m (i):=Stern V i; let T (i):=(A).clock.hatBeta (m i)^p; let Z' i:=T i • s i (v i)
    refine listened_G hS hp hJ hw u (nearing (grow_big hq h) (fun i=>shine i)) Z' ho h ?_
    intro w; let K':= Further.CorrectedLift.ladder C 4 w
    let f(j):=(A).clock.hatBeta (summit (A) j)^p * (tilt_cap (A) j)^5 * Tau (A) j (-100);
    have ht₀ : Tendsto (f ∘ Q) atTop (𝓝 0):=by
       refine (whither (h:=h) ( ((stickK _ h θ).pows h p|>.push ((titles _ h).pows h 5)).prod (ticket_exp _ _) ) (show 0+(-100:ℝ)*Dust<0 by norm_num)).comp hq.growth
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) ?_ ht₀)
    filter_upwards [hP.starts,hv,ear_price P h θ K ht hM hb hS HF hq t (fun i=>(x i).val 0) hy w,hq.growth.eventually ((Sstar (A)).eventually_ge_atTop (C.ref 5))] with i ha hb' he hk
    let b:= b_zoom V i; have hz:0<b:= shine i; let a:= C.S.a (Q i); let y:= X.r i • u i; have hX:X.r i=a*b:= (hq.season i).2.symm; let f':= x i; let v':= S.project 5 (f'.val 0); let z:= Z.β (Stern V i)
    let V':= X.U i 5; have hZ':0 < z:= measured hb P hZ (m i)
    have hh: V' (Z' i|>.val 0) = (T i*b^ (5:ℕ)) • (a^ (5:ℕ) • v'):=by
        let b':= crown Z X (Stern V) 5 i; let Y':= Vault S Z 5 (m i) b'; change V' (T i • (s i (v i)).val 0)= _
        -- goal
        rw [show V' (T i • _)=_ from (V'.toLinearMap.restrictScalars ℝ).map_smul .., ha, hb']; change T i • (V' (V'.symm (Y' (z⁻¹ • swale _ _ _ _))))=_
        rw[LinearEquiv.apply_symm_apply,show Y' (z⁻¹ • _)=_ from (Y'.restrictScalars ℝ).map_smul ..,show (Y'.restrictScalars ℝ) (swale Z 5 (Stern V i) ((x i).val 0))= _ from fisc hZ P hb ht hk _ (frames_night V! f' 0) b']; change T i • (z⁻¹ • (crown Z X _ 5 i • v'))= _; rw [smul_smul z⁻¹,crown,hX, smul_smul,smul_smul];
        congr 1; change T i*(z⁻¹*(z*(a*b)^5))= _; field_simp
    let M:=Work.A01.frontRead (S:=S) (n:=1) ![⟨4,X.U i 4 w⟩] y 5
    change ‖S.useAt S y ![⟨5,V' ((Z' i).val 0)⟩,⟨4,X.U i 4 w⟩]‖ ≤ _
    rw [hh]; have heq(t): M t=S.useAt S y ![⟨5,t⟩,⟨4,X.U i 4 w⟩]:= Work.A01.front_eval ![⟨4,X.U i 4 w⟩] y 5 t
    rw [← heq]; rw[show M ((T i*b^ (5:ℕ)) • (a^ (5:ℕ) • v'))=(T i*b^ (5:ℕ)) • M (a^ (5:ℕ) • v') from (M.restrictScalars ℝ).map_smul ..]
    have hT':0 ≤ T i:=pow_nonneg (bell ..|>.le) _
    rw[norm_smul,Real.norm_of_nonneg (by positivity :0≤ T i*b^ (5:ℕ)),heq];
    apply le_trans (mul_le_mul_of_nonneg_left he (show 0 ≤ T i*b^ (5:ℕ) from by positivity)); change (T i*b^ (5:ℕ))* _≤ T i*(tilt_cap _ _ )^ (5:ℕ)*_ ; apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz.le (tiltP _ (hq.season i|>.1.high.2)) _) hT') (Tau_pos ..|>.le)
end YM.Trace.Terrace

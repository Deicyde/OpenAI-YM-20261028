import YM.TraceExtension.Verse.Round
import YM.TraceExtension.LogScaling
import YM.TraceExtension.Foundation.Constant
import YM.TraceExtension.Chart.Line
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Verse
open Function Filter Set Extraction OS OS.Ground Spec MeasureTheory Wilson
open RG Terrace MergeProof.East Next.Rank Next.Rank.East Next.UVStress Further.CorrectedLift Climb
open Analysis TraceExtension Boundary Over
open scoped Topology BigOperators InnerProductSpace Classical ContDiff
variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book} (F:Final C f S)
variable {H:(Cells.standard C).Hierarchy}{J:Scaling S}{V:∀ i,Vane C i}{Y:∀ d _:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}(hq:Gondola f H J 𝓛 V Y)
local notation "S'"=> Cells.standard C
local notation "A'"=> C.path.levels

abbrev width (x:Points 2):=‖x 0-x 1‖
lemma axis_shape (x : Points 2)(h:x∈conf 2): S.classMoment (selected F) _ x (fun _=>center F) = euclidean F (width x):=by
    let X:= F.sector.turns; let Y:= fun _ : Fin 2=> (⟨4,center F⟩: S.Tag); let u:= x 0-x 1; let t:= width x; let v:=(-t) • basis timeAxis
    obtain ⟨K,hK⟩:= OS.Ground.columns (Submodule.reflection (Submodule.span ℝ ({u-v}:Set E4)).orthogonal)
    have he : ‖u‖=‖v‖:= by simp [v,t,u,norm_smul]
    have hw : Ortho.move K (x 0) - Ortho.move K (x 1)= v:= by
        change Ortho.motion K _ - Ortho.motion K _ = v; rw [← map_sub]; change Ortho.move K u= v; rw[hK]; exact Submodule.reflection_sub he
    have hu : S.useAt (selected F) (Points.move K x) Y=S.useAt (selected F) x Y:=by
        have hx:X.label K ∘ Y=Y:= funext fun i=> congr_arg (Sigma.mk 4) (trace_turn F.phase.transport.spin F.phase.transport.spots K)
        have hh : S.useAt (selected F) (Points.move K x) (X.label K ∘ Y)=_:= F.phase.phase.sym F.α.atPoint 2 Y x h K; rw[hx] at hh; exact hh
    have ht : opposed t 0-opposed t 1=v:=by
        ext1 i; fin_cases i<;> simp [opposed,v,Bid.bothH,Boundary.place,pairH, YM.position]
        · change (0:ℝ)-0= -(0:ℝ); ring
        · change (0:ℝ)-0= -(0:ℝ); ring
        change -(t/2)-t/2=-t;ring
    let y:=opposed t 1-Ortho.move K (x 1)
    have hv : Points.across y (Points.move K x)=opposed t:=by
       ext1 i; fin_cases i
       · change Ortho.move K (x 0)+y=_; unfold y; change Ortho.move _ _+_ = opposed t 0; rw[← sub_eq_zero]; rw [show Ortho.move K (x 0)+(opposed t 1-Ortho.move K (x 1))-opposed t 0=(Ortho.move K (x 0)-Ortho.move K (x 1))-(opposed t 0-opposed t 1) from by abel,hw,ht,sub_self]
       change Ortho.move K (x 1)+y=_; unfold y;abel
    change S.useAt (selected F) x Y= _; rw [← hu]; unfold euclidean; rw [← hv]; exact ((selected_hierarchy F).translations _ _ (Points.move_in K h) y (fun _=> ⟨4,S.representative 4 (center F)⟩)).symm

abbrev clue (s:ℝ):= s^8*(Real.log s⁻¹)^ (2:ℕ)
/-- normalization on curvature convention. -/
def award (G:Gauge):=12*(d2 G^ (2:ℕ)/b0 G^ (2:ℕ))*G.lieDim/Real.pi^4
variable {Z: Terrace.Arch C} (hb:(𝓛:Filter (ℕ×ℕ)) ≤ f.fuse)

section homogeneous
private lemma priced {L:Register G} (S T : Table L)(u:S.Field 4)(p:ℝ)(x:Points 2): S.classMoment T (fun _=>4) x (fun _=> p • u)= p^2 • (S.classMoment T (fun _=>4) x (fun _=> u)):=by
   let t:ℂ:= ↑p
   let M:=S.classMoment T (fun _ : Fin 2=>4) x
   rw [show (fun _ : Fin 2=> p • u)=(fun _=> t • u) from funext (fun _=> Complex.coe_smul ..),M.map_smul_univ (fun _ : Fin 2=> t)]; unfold t;simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin, ← Complex.ofReal_pow,Complex.real_smul]; rfl
include hb
lemma tagline (h:G.Simple)(h₁:Scribe f J V Z F.sector 𝓛 F.room.kernel H) {x:Points 2}(hh:x∈generic 2)(ht:Scaling.window 100 2∈𝓝 x) : Tendsto (fun i=> clue (J.r i) • euclidean F (J.r i*width (fad (V i) x))) atTop (𝓝 (↑(award G/(width x)^8):ℂ)):=by
    let U:= selected F; let H':= F.phase.phase; let R:= H'.decomposition; let a(i):= ZoomValue J (BQ Z V) (center F) i; let P:(Bel C.book).Field 4:= (4*d2 G) • OScale C.book; let p:=tendsto_id (x:=atTop (α:=ℕ)); clear p
    obtain ⟨Y,hq⟩:=h₁.meters
    have he:= rainbow hq F.room hb R H'.still H'.states H'.chosen F.α.atPoint (selected_respects F) h hh ht (fun i _=> a i) (fun _=> P) (fun _=> h₁.goal U)
    let x0:= width x; let H4:=3*(G.lieDim:ℝ)/Real.pi^4*x0⁻¹^8
    have hp: x 0≠x 1:= (show Injective x.ofLp from generic_conf _ hh).ne (by decide)
    have hv: ((S').classMoment (S') (fun _=> 4) x (fun _=> P))= (4*d2 G)^2 • (↑H4:ℂ):=by
       unfold P; rw[priced]; have hx:= wick_norm (L:=C.book) hp; unfold H4; rw [inv_pow]; exact congr_arg _ hx
    have hz:= (h₁.clock.pow 2).smul he
    rw [hv, smul_smul] at hz
    have hk(ψ : ℝ) : (G.slopeConstant⁻¹ ^2 * ((4*d2 G)^2)) • (ψ:ℂ)= (↑(4*(d2 G^2/b0 G^2)*ψ:ℝ):ℂ):=by rw [beta_eq,Complex.real_smul]; push_cast;ring
    rw [hk,show 4*(d2 G^2/b0 G^2)*H4= award G/(width x)^8 from by unfold award H4 x0;ring] at hz
    refine hz.congr' ?_
    filter_upwards [h₁.grows.eventually_gt_atTop 0, (rounds hq h x).eventually ((genericOpen 2).mem_nhds hh), (rounds hq h x).eventually ht] with i hi hy ht
    let r:= J.r i; let Q:=fad (V i) x; let s:= rum (V i) x; let w:= BQ Z V i; have hr: s=r • Q:=by unfold s; rw [raw, (hq.season i).2]
    have hr' : width s=r*width Q:= by rw [hr,width,PiLp.smul_apply,PiLp.smul_apply,← smul_sub,norm_smul,Real.norm_of_nonneg (J.positive i).le]
    have hc:s∈conf 2:=generic_conf _ (mixed hq _ i hy ht.2).usable
    let t:=center F
    change (LogZoom J i/w)^2 • (S.classMoment (selected F) _ s fun _ :Fin 2=> J.U i 4 (a i))=_; rw [show J.U i 4 (a i)=(w*r^(4:ℕ)) • t from LinearEquiv.apply_symm_apply ..,priced,axis_shape F s hc,hr',smul_smul, show (LogZoom J i/w)^2*(w*r^(4:ℕ))^2=clue r from ?_]
    change (Real.log r⁻¹/w)^2*_=_; unfold clue; have hw:w≠0:= hi.ne'; field_simp
end homogeneous
end YM.Trace.Verse

import YM.TraceExtension.Atlas.Web
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East Next.Rank
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S){H:(Bel C.book).Hierarchy}
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{J:Scaling S}{V:∀ i,Vane C i}{Z:Arch C}
variable (h₁:Scribe X J V Z F.sector 𝓛 F.room.kernel H)

open LinearMap
section
variable {L:Register G}{S:Table L}{T : Table.Rotation S}{H:S.Hierarchy}
lemma expect_turn (H:S.Hierarchy)(K:S.Rotation)(ht:K.Oriented S)(v:S.Field 4)(s: Ortho): expectation S 4 (K.act 4 s v)=expectation S 4 v:=by
   have hv:=ht 1 (fun _=>⟨4,v⟩) 0 (Next.UVStress.conf1) s; rw [show Points.move s (0:Points 1)=0 from PiLp.ext fun i => map_zero (Ortho.motion s)] at hv; rw[onepoint,onepoint]; exact hv
variable {d:ℕ}
-- inverse CLm
variable {E: Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E][CompleteSpace E]
def opEquiv (u:E≃ₗ[ℂ] E): Mat E:= LinearMap.toContinuousLinearMap u.toLinearMap
lemma step_round (u:ℕ→ E≃ₗ[ℂ] E)(h:Tendsto (opEquiv ∘ u) atTop (𝓝 1)): Tendsto (fun i=>opEquiv (u i).symm) atTop (𝓝 1):=by
   have hr:=NormedRing.inverse_continuousAt (1: (Mat E)ˣ); have hh:= hr.tendsto.comp h; rw[Units.val_one,Ring.inverse_one] at hh; apply hh.congr; intro i
   let x:=u i; let p:= opEquiv x; let q:=opEquiv x.symm; have hk:p*q=1:= ContinuousLinearMap.ext (fun i=> x.apply_symm_apply _); have ht:q*p=1:=ContinuousLinearMap.ext (fun i=> x.symm_apply_apply _)
   have hu:IsUnit p:=⟨⟨p,q,hk,ht⟩,rfl⟩;apply hu.mul_right_inj.mp; change _=p*q; rw [hk]; exact Ring.mul_inverse_cancel p hu

variable (F':S.Rotation)(A:S.RealSpin) (h: Spin.Port F' A)
lemma patch_op(s:Ortho) (v:ℕ→ E≃ₗ[ℂ] E)(f:ℕ→ (E ≃ₗ[ℂ] S.Field d))(T: Mat E)(hV:Tendsto (opEquiv ∘ v) atTop (𝓝 1)) (ht:Tendsto (fun i=> circle h (f i) s) atTop (𝓝 T)): Tendsto (fun i=> circle h ((v i).trans (f i)) s) atTop (𝓝 T):=by
    let x:=step_round v hV
    have hh:= (x.mul ht).mul hV; rw[one_mul,mul_one] at hh
    exact hh.congr (fun i=> ContinuousLinearMap.ext (fun j=> rfl))

open MeasureTheory
attribute [local instance] Work.A15.compact_ortho
local instance : MeasurableSpace Ortho := borel Ortho
local instance : BorelSpace Ortho := ⟨rfl⟩
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E][CompleteSpace E][NormedSpace ℝ E][IsScalarTower ℝ ℂ E]
lemma Peg (f g:Ortho→* (Mat E))(hf:Continuous f)(hg:Continuous g)(P:E→L[ℂ] ℂ)(hP:∀ v x,P (f v x)= P x)(hp:∀ v x,P (g v x)=P x)(x): P (meanO f g x)=P x:=by
    rw[meanO_value f g hf hg,← P.integral_comp_comm]
    · simp_rw [ContinuousLinearMap.mul_apply,hP,hp]; simp
    exact ((hf.mul (hg.comp continuous_inv)).clm_apply continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end
structure AlignV (K:S.Hierarchy)(U: Spec.Algebra S)(H:(Bel C.book).Hierarchy)(v:change S 4): Prop where
    align : AlignO U K.spin H 4 v
    cent : ∀ x, expectation S 4 (v x)= expectation (F₀) 4 x

include h h₁
lemma nearby (P:ℕ→change S 4)(hp:Tendsto (fun k=>moveV (S:=S) 4 (J.U k 4) (P k)) atTop (𝓝 1))(r:Ortho): Tendsto (fun i=>circle (compassF F) (P i) r) atTop (𝓝 (circle (compass (C:=C) (H:=H) h) (LinearEquiv.refl ℂ ((F₀).Field 4)) r)):=by
    apply (patch_op F.sector.turns F.room.kernel.spin (compassF F) r (fun i=>actMove (S:=S) 4 (J.U i 4) (P i)) _ _ hp (acts_tends h h₁ 4 r)).congr
    intro i; change circle _ _ r=circle _ (P i) r; congr 1; congr 1; ext1 x; exact LinearEquiv.apply_symm_apply ..
-- exact averaging
-- choose canonical convention.Gr.Unit.
def gaze (h:G.Simple)(L:change S 4): Mat ((Bel C.book).Field 4) := meanO (circle (compassF F) L) (circle (compass (C:=C) (H:=H) h) (LinearEquiv.refl ℂ ((Bel C.book).Field 4)))
structure XScope (r:ℝ)(v:change S 4): Prop where
    frame: AlignV F.room.kernel F.sector H v
    precess: ∃ u:change S 4, AngularH F.room.kernel H r u∧∀ x,v x=u (gaze (H:=H) F h u x)
lemma fulfill : ∃ P:ℕ→ change S 4,Tendsto (fun k=> moveV (S:=S) 4 (J.U k 4) (P k)) atTop (𝓝 1)∧ ∀ᶠ i:ℕ in atTop,XScope (H:=H) F h (J.r i) (P i):=by
    let K:= F.room.kernel
    obtain ⟨U,hU,hΩ⟩:= boss F h h₁
    let Q (i):=circle (compassF F) (U i); let L:=LinearEquiv.refl ℂ ((Bel C.book).Field 4); let Q':=circle (compass (C:=C) (H:=H) h) L
    let M i:= gaze (H:=H) F h (U i); have hM : Tendsto M atTop (𝓝 1):= eventualMeanO Q (fun i=>circle_cont ..) Q' (circle_cont ..) (nearby F h h₁ U hU)
    let Z(i):= if ht:IsUnit (M i) then (unit_shape (M i) ht).choose else L; let P(i):= (Z i).trans (U i); have hp:= hM.eventually (Units.isOpen.mem_nhds isUnit_one);
    have he : ∀ i,IsUnit (M i)→∀ x,Z i x=M i x:= by intro i hi x; unfold Z; rw[dif_pos hi]; exact LinearMap.congr_fun (unit_shape _ hi).choose_spec _
    have ht:= hU.mul hM; rw [mul_one] at ht
    refine ⟨P,ht.congr' (hp.mono (fun i hi=> ContinuousLinearMap.ext (fun x=> ?_))),?_⟩
    · change (J.U i 4).symm (U i _)= (J.U i 4).symm (U i (Z i x)); rw[he i hi]; rfl
    filter_upwards[hp,hΩ] with i hi H'
    let Y:= U i; let A:= Q i
    have hE(x): P i x=Y (M i x):= congr_arg _ (he i hi x)
    refine ⟨⟨⟨?_,?_,?_⟩,?_⟩,Y,H',hE⟩ <;> obtain ⟨T,hT,hF,ht⟩:= H'.pose <;> try change Y=_ at hT
    · intro x; let g(s: (Bel C.book).Field 4):= (F₀).conj H.spin 4 s; let B:= LinearMap.toContinuousLinearMap (StressFlux.conjQ (d:=4) H.spin)
      have hu(v):Y (B v)= S.conj F.room.kernel.spin 4 (Y v):= by rw[hT];exact (coverV_H _ _ _ hF.twist hF.bar v).1
      have hx(s v): B (Q' s v)=Q' s (B v):=(compass (H:=H) h).real ..
      have hY(s v): Q i s (B v)=B (Q i s v):=by
           let p:= F.sector.turns.act 4 s; apply Y.injective;change Y (Y.symm (p (Y _)))=_; rw [hu (Q i s v),Y.apply_symm_apply, hu];change _=S.conj _ _ (Y (Y.symm _));rw[Y.apply_symm_apply]; exact ((compassF F).real ..).symm
      rw [hE,hE]; exact (congr_arg _ (mean_maps (f:=Q i) (g:=Q') (circle_cont ..) (circle_cont ..) B hY (fun s v=> (hx s v).symm) x)).trans (hu (M i x))
    · let u:=(F₀).unit 4; have hv:Y u= S.unit 4:=by rw[hT]; exact coverV_unit ..
      have ha(s):Q i s u=u:=by apply Y.injective; change Y (Y.symm _)= _; rw [Y.apply_symm_apply];change F.sector.turns.act _ _ (Y u)= _; rw[hv,F.phase.transport.spots.identity]
      rw [hE,show M i u=u from mean_fixed (Q i) Q' (circle_cont ..) (circle_cont ..) _ ha (fun v=> (baseRights (C:=C) (H:=H) h).identity ..)]; exact hv
    · intro s x; rw[hE,hE];
      have hx:= congr_arg (fun f : Mat ((Bel C.book).Field 4)=> f x) (underO (Q i) Q' (circle_cont ..) (circle_cont ..) s); change Y.symm (F.sector.turns.act _ _ (Y _))= M i (Q' s x) at hx; exact (congr_arg Y hx.symm).trans (Y.apply_symm_apply _)
    intro x;rw[hE]
    have hz(x):expectation S 4 (Y x)=expectation (F₀) 4 x:= by rw[hT];exact coverV_scale ..
    rw[hz]; let B:=LinearMap.toContinuousLinearMap (expectation (F₀) 4)
    have hh(s v): B (Q i s v)=B v:=by change expectation (F₀) 4 (Q i s v)=_;rw[← hz];change expectation S 4 (Y (Y.symm _))=_; rw [Y.apply_symm_apply]; exact (expect_turn K F.sector.turns F.phase.transport.motion (Y v) s).trans (hz v)
    have hP : (turns C).Oriented (F₀):=Maxwell.Free.gear_motion _
    exact Peg (f:=Q i) (g:=Q') (circle_cont ..) (circle_cont ..) B hh (fun s x=> expect_turn H (turns C) hP x s) x
end YM.Trace.Pilot

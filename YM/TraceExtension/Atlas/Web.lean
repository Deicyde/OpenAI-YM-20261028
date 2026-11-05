import YM.TraceExtension.Atlas.Broad
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

section
variable {L L':Register G}{S:Table L}{T:Table L'}
lemma glitter (H:S.Hierarchy)(K:T.Hierarchy)(B:ℕ→Carpet T)(f:ℕ→ Active S ≃ₗ[ℂ] Active T) (P:Carpet S)(h:∀ v w, Tendsto (fun i=> B i (f i v) (f i w)) atTop (𝓝 (P v w)))(he:∀ i x,f i (starA H x)= starA K (f i x))(hp:∀ i v x,f i (swingA H v x)=swingA K v (f i x))(v w): Tendsto (fun i=> Hmean K (B i) (f i v) (f i w)) atTop (𝓝 (Hmean H P v w)):=by
    unfold Hmean; simp_rw [hbasis_apply, ← hp,_root_.add_apply,ContinuousLinearMap.flip_apply, flipC_apply, ← he]; exact tendsto_finsetSum _ fun s _=> ((h ..).add (h ..)).add (((h ..).add (h ..)).star)
lemma nest_cover(H:S.Hierarchy)(K:T.Hierarchy)(U:Active S ≃ₗ[ℂ] Active T)(V:Active S ≃ₗ[ℂ] Active S)(x): coverV H K (V.trans U) x= coverV H K U (coverV H H V x):=by
    simp only [coverV_at, map_add,map_smul,show man H (S.unit 4)=0 from Subtype.ext (const_out H.laws), man_fix, (fun x:Active S=> (belongs _).1 x.property), mean_unit H.laws];simp
lemma glitter' (H:S.Hierarchy)(K:T.Hierarchy)(r:ℕ→ℝ)(f:ℕ→ Active S ≃ₗ[ℂ] Active T)(he:∀ i x,f i (starA H x)= starA K (f i x))(hp:∀ i v x,f i (swingA H v x)=swingA K v (f i x))(g:ℝ) (h:∀ v w,Tendsto (fun i=>cine K (r i) (f i v) (f i w)) atTop (𝓝 (cine H g v w)))(v w): Tendsto (fun i=> LiftB (f i).toLinearMap (scannerX K (r i)).val v w) atTop (𝓝 ((scannerX H g).val v w)):=by
    have hu(i): LiftB (f i).toLinearMap (scannerX K (r i)).val v w=Hmean K (cine K (r i)) (f i v) (f i w):=by simp only [liftB_at,LinearEquiv.coe_coe,scannerX]
    simp_rw [hu]; let B':=scannerX H g; rw [show (scannerX H g).val v w= Hmean H (cine H g) v w from rfl]; exact glitter H K (fun i=>cine K (r i)) f (cine H g) h he hp v w
lemma reL (f:Active S≃ₗ[ℂ] Active T)(g:Active S≃ₗ[ℂ] Active S)(P:Carpet S)(Q:Carpet T)(h:LiftB g.toLinearMap (LiftB f.toLinearMap Q)=P) : LiftB (g.trans f).toLinearMap Q=P:=by rw[← h];rfl
lemma approach {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E](f:ℕ→E≃ₗ[ℂ] E)(h : Tendsto (fun i=> LinearMap.toContinuousLinearMap (f i).toLinearMap) atTop (𝓝 (1:Mat E)))(x:E): Tendsto (fun i=> f i x) atTop (𝓝 x):= ((ContinuousLinearMap.apply ℂ E x).continuous.continuousAt.tendsto).comp h

end
include h h₁
-- actual X unselected.Grimm.S.
structure AngularH (K:S.Hierarchy)(H:(Bel C.book).Hierarchy)(r:ℝ)(f:change S 4) : Prop where
    pose : ∃ U:Active (F₀)≃ₗ[ℂ] Active S, f=coverV H K U ∧ Favor K H U∧ LiftB U.toLinearMap (scannerX K r).val= (scannerX H 1).val
set_option maxHeartbeats 600000 in
lemma boss : ∃ P:ℕ→change S 4,Tendsto (fun k=> moveV (S:=S) 4 (J.U k 4) (P k)) atTop (𝓝 1) ∧ ∀ᶠ i in atTop, AngularH F.room.kernel H (J.r i) (P i):=by
    let K:= F.room.kernel; obtain ⟨p,hp,hκ⟩:= firstL F h h₁;let W(i):=coverV H K (p i)
    let A(i):laceC H:=⟨LiftB (S:=S) (p i).toLinearMap (scannerX K (J.r i)).val,lift_laceC _ _ _ (hp i).bar (hp i).twist _⟩
    have he (v w): Tendsto (fun i=>cine K (J.r i) (p i v) (p i w)) atTop (𝓝 (cine H 1 v w)):=by
        let P:=(swingA H (Signed.mirror 0) v);let x:=P.val;let y:=w.val; rw [cine_pay,one_smul]
        refine (uv_p F h h₁ W hκ ![x,y] (camera 0) (shutter 0)).congr ?_; intro i;rw[cine_pay, ← (hp i).twist]
        unfold W; congr 1; funext j; fin_cases j <;> exact coverV_act ..
    have hh (v w): Tendsto (fun i=> A i|>.val v w) atTop (𝓝 ((scannerX H 1).val v w)):=by
       change Tendsto (fun i=>LiftB (p i).toLinearMap (scannerX K (J.r i)).val v w) atTop (𝓝 ((scannerX H 1).val v w)); exact glitter' H K (J.r) p (fun i=> (hp i).bar) (fun i=> (hp i).twist) 1 he v w
    obtain ⟨U,hU,hT⟩:=roadway h A hh; let Z(i):= (U i).trans (p i); let B(i):=coverV H K (Z i); let t(i):=coverV H H (U i)
    refine ⟨B,Work.A05.clm_convergence _ _ (fun v=> ?_), hT.mono (fun i hi=> ?_)⟩
    · have ht:Tendsto (fun i=> t i v) atTop (𝓝 v):=by
         let P:= man H v;have hy:Tendsto (fun i=> U i P) atTop (𝓝 P):= approach U hU P
         have hv:= (continuous_subtype_val.continuousAt.tendsto.comp hy).add_const (expectation (F₀) 4 v • (F₀).unit 4); change Tendsto _ _ (𝓝 (P.val+_)) at hv; rw [show P.val+expectation (F₀) 4 v • (F₀).unit 4=v from (stepV H).left_inv v] at hv; exact hv
      exact (Dash.arcing hκ ht).congr (fun i=> by change (J.U i 4).symm (W i (t i v))=(J.U i 4).symm (B i v); exact congr_arg _ (nest_cover ..|>.symm))
    refine ⟨Z i,rfl,?_,?_⟩
    · constructor
      · intro x; change p i (U i _)= _; have hx: U i (starA H x)=starA H (U i x):= (th_star (f:=⟨_,hi.1⟩) x); rw[hx,(hp i).bar];rfl
      intro v x; change p i (U i _)=_; have hx: U i (swingA H v x)= swingA H v (U i x):= th_swing (f:=⟨_,hi.1⟩) v x; rw [hx,(hp i).twist];rfl
    change LiftB ((U i).trans (p i)).toLinearMap _=_; apply reL; change LiftB (U i).toLinearMap (A i).val=_; exact hi.2
end YM.Trace.Pilot

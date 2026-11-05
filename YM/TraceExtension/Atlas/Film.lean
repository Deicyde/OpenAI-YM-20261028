import YM.TraceExtension.Atlas.Center
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {C:Family G}{L L':Register G}{S : Table L} {T:Table L'}

def stepV (H:S.Hierarchy): S.Field 4 ≃ₗ[ℂ] ℂ × Active S where
   toFun x:= (expectation S 4 x,man H x)
   invFun x:= x.2.val + x.1 • S.unit 4
   left_inv := fun x=> sub_add_cancel ..
   right_inv := fun ⟨x,y⟩=>Prod.ext (by change expectation S 4 _= x; rw [map_add,map_smul,(belongs _).1 y.property,mean_unit H.laws,zero_add]; simp) (by apply Subtype.ext; change centering S 4 _=y.val; rw[map_add,map_smul,const_out H.laws,zero_center];simp)
   map_add':=fun x y=> Prod.ext (map_add ..) (map_add ..)
   map_smul':=fun x y=> Prod.ext (map_smul ..) (map_smul ..)

def coverV(H:S.Hierarchy)(K:T.Hierarchy)(U:Active S≃ₗ[ℂ] Active T): S.Field 4≃ₗ[ℂ] T.Field 4:= (stepV H).trans (((LinearEquiv.refl ℂ ℂ).prodCongr U).trans (stepV K).symm)
lemma coverV_at(H:S.Hierarchy)(K:T.Hierarchy)(U:Active S≃ₗ[ℂ] Active T)(x): coverV H K U x=(U (man H x)).val+expectation S 4 x • T.unit 4:=rfl
lemma coverV_act(H:S.Hierarchy)(K:T.Hierarchy)(U:Active S≃ₗ[ℂ] Active T)(x:Active S): coverV H K U x.val=(U x).val:=by rw[coverV_at,man_fix,(belongs _).1 x.property]; simp
lemma coverV_scale(H:S.Hierarchy)(K:T.Hierarchy)(U:Active S≃ₗ[ℂ] Active T)(x:S.Field 4): expectation T 4 (coverV H K U x)=expectation S 4 x:= by rw[coverV_at,map_add,map_smul, (belongs _).1 (U _).property,mean_unit K.laws]; simp
lemma coverV_unit(H:S.Hierarchy)(K:T.Hierarchy)(U:Active S≃ₗ[ℂ] Active T): coverV H K U (S.unit 4)=T.unit 4:=by rw[coverV_at,mean_unit H.laws,show man H (S.unit 4)=0 from Subtype.ext (const_out H.laws)];simp
lemma foray(H:S.Hierarchy) (s:Signed)(x):expectation S 4 (S.mirror H.spin 4 s x)=expectation S 4 x∧ expectation S 4 (S.conj H.spin 4 x)=star (expectation S 4 x):=by
    constructor
    · have he:=mirror_center H x s; rw [value_center,value_center,map_sub,map_smul,S.mirror_unit] at he; exact ((smul_left_injective _ (S.alive 4 H.laws)) (sub_right_inj.mp he.symm))
    have he:=conj_center H x; rw[value_center,value_center,map_sub,map_smulₛₗ,S.conj_unit] at he; exact (smul_left_injective ℂ (S.alive 4 H.laws) (sub_right_inj.mp he.symm))
lemma coverV_H(H:S.Hierarchy)(K:T.Hierarchy)(U:Active S≃ₗ[ℂ] Active T) (hh:∀ s x,U (swingA H s x)=swingA K s (U x))(hz:∀ x,U (starA H x)=starA K (U x))(x:S.Field 4) : coverV H K U (S.conj H.spin 4 x)= T.conj K.spin 4 (coverV H K U x) ∧ ∀ i,coverV H K U (S.mirror H.spin 4 i x)=T.mirror K.spin 4 i (coverV H K U x):=by
    constructor
    · rw [coverV_at,coverV_at,map_add, map_smulₛₗ,T.conj_unit, (foray H 1 x).2, show man H (S.conj H.spin 4 x)=starA H (man H x) from ?_,hz,star_act]; rfl
      apply Subtype.ext; rw[star_act]; exact (conj_center H x).symm
    intro s; rw[coverV_at,coverV_at,map_add,map_smul,T.mirror_unit,(foray H s x).1,show man H (S.mirror H.spin 4 s x)=swingA H s (man H x) from ?_,hh,swing_act];apply Subtype.ext; rw[swing_act]; exact (mirror_center H x s).symm

lemma centerV(H:S.Hierarchy)(K:T.Hierarchy)(U:S.Field 4≃ₗ[ℂ] T.Field 4)(hu:U (S.unit 4)=T.unit 4): ∃ f:Active S ≃ₗ[ℂ] Active T,∀ v:Active S,f v= man K (U v.val):=by
    let Y:=(man K).comp ((U.toLinearMap).comp (Active S).subtype); let P:=(man H).comp ((U.symm.toLinearMap).comp (Active T).subtype)
    have he{G:Gauge}{L L':Register G}{S:Table L}{T:Table L'}(U:S.Field 4≃ₗ[ℂ] T.Field 4)(H:S.Hierarchy)(K:T.Hierarchy)(hu:U (S.unit 4)= T.unit 4)(v:Active S): man H (U.symm (centering T 4 (U v.val)))=v:=by
        rw[value_center,map_sub, U.symm_apply_apply,map_smul,← hu,U.symm_apply_apply]; apply Subtype.ext; change centering S 4 _= _; rw [map_sub,map_smul,const_out H.laws,zero_center];simp
    let f: Active S≃ₗ[ℂ] Active T:= LinearEquiv.ofLinear Y P (LinearMap.ext fun x=> by
         have hx:=he U.symm K H ((U.symm_apply_eq).mpr hu.symm) x; exact hx) (LinearMap.ext fun x=>he U H K hu x)
    exact ⟨f,fun x=>rfl⟩
end YM.Trace.Pilot

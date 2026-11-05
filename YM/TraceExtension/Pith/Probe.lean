import YM.TraceExtension.Atlas.Crash
import YM.TraceExtension.Atlas.Last
import YM.TraceExtension.Foundation.Constant

/-! Explicit determining square through the needed orders for the trace
 coefficient, validated on actual aligned homogeneous parity-compatible position
 frame. No hypothesis on diagonal insertions. This is a separate readout
 of the necessary orders of the Ward-test system in these measuring fields;
 the coefficient computation itself is in physical derivation through matched
 stationary/Jacobian calculations.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pith
open Function Filter Set Extraction Ward Climb Spec Over Pilot Table Analysis Maxwell StressFlux Work Work.A05
open scoped Topology BigOperators InnerProductSpace Classical ContDiff
variable {G:Gauge}{C:Family G}{p:Extraction.Order}{n:ℕ}
section
variable {L:Register G}{S:Table L}(U:DiffPlan S) (H:S.Hierarchy)(hu:U.Derivatives S)(x:Points (n+1))(hx:x∈conf (n+1)){s:ℝ}
local instance relay (n:ℕ) : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
include hu hx H
def pron(a:Axis)(Y:S.Field 4)(v:Fin n→ S.Field 4)(x:Points (n+1))(s:ℝ): ℂ := Points.gradient 0 a (fun z=> S.classMoment S (fun _=>4) (s • z) (Fin.cons (α:=fun _:Fin (n+1)=> S.Field 4) Y v)) x

lemma strains(a:Axis)(Y:S.Field 4)(v:Fin n→ S.Field 4)(hr:0<s): pron a Y v x s= (s:ℂ)* frontRead (s • x) (fun i=>⟨4,v i⟩) (4+1) (U.deriv 4 a Y):=by
    have he := smul_conf hr hx; let z : Fin n → S.Tag := fun i=>⟨4,v i⟩
    let t:= Fin.cons (α:=fun _:Fin (n+1)=> S.Tag) (⟨4,Y⟩:S.Tag) z
    let f(q):= disc t q
    have hF : DifferentiableAt ℝ f (s • x):= (((S.class_smooth S H.smooth t).contDiffAt ((conf_open _).mem_nhds he)).differentiableAt (by simp))
    let D:Points (n+1)→L[ℝ] Points (n+1):= s • ContinuousLinearMap.id ℝ _
    let g(i):S.Tag:= ⟨4, Fin.cons (α:=fun _:Fin (n+1)=> S.Field 4) Y v i⟩
    have hp:g=t:= funext (Fin.forall_fin_succ.mpr ⟨rfl,fun _=>rfl⟩)
    change Points.gradient 0 a (fun y=> disc g (s • y)) x=_
    rw [hp,frontRead_at,disc,hu.kernels 4 a Y he z]
    change fderiv ℝ (f ∘ D) x _ = _
    have hθ:= hF.hasFDerivAt
    let A:=fderiv ℝ f (s • x)
    have ht : HasFDerivAt (f ∘ D) (A.comp D) x:=HasFDerivAt.comp x (g:=f) (f:=⇑D) hθ D.hasFDerivAt
    rw [ht.fderiv]; let v:=Points.direction (0:Fin (n+1)) a
    change fderiv ℝ f (s • x) (s • v)= _
    rw [map_smul]; exact Complex.real_smul ..
end

-- Nonzero B
local instance (n:ℕ) : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
abbrev sail : Points 2:=Points.direction 0 timeAxis
lemma sail_on {t:ℝ}(h:0<t): t • sail∈conf (1+1):=by
    refine smul_conf h ?_
    have hz : basis timeAxis ≠ 0:= norm_pos_iff.mp (by simp)
    intro i j; fin_cases i<;> fin_cases j<;> try simp only [sail,Points.direction, PiLp.single_apply]
    · intro _; trivial
    · simpa using hz
    · simpa using Ne.symm hz
    intro _; trivial
private def Ftax (C:Family G):ℝ:= 3*(G.lieDim:ℝ)/Real.pi^4
lemma sails_val (C:Family G)(t:ℝ)(h:0<t):
    let F:= Bel C.book; let v:= stepField C
    F.classMoment F (fun _=>4) (t • sail) (fun (_ : Fin 2)=>v)= (Ftax C * (t^8)⁻¹ : ℝ):=by
    intro F v; set x:= t • sail; have hz: x 0≠ x 1:= fun he=> zero_ne_one (sail_on h he)
    have he:= wick_norm (L:=C.book) hz
    have hb :‖x 0-x 1‖=t:=by unfold x; simp [sail,Points.direction,norm_smul,abs_of_pos h]
    rw [hb] at he; exact he
set_option maxHeartbeats 700000 in
lemma sails_peak (H:(Bel C.book).Hierarchy): pron (S:=Bel C.book) timeAxis (stepField C) (fun _:Fin 1=>stepField C) sail 1=(Ftax C*(-8):ℝ):=by
    let F:= Bel C.book; let u:=stepField C; let g:= fun z: Points 2=> F.classMoment F (fun _=>4) z (fun _=> u); let A'(p:ℝ):= p • sail
    have ht:sail∈conf _:= by simpa only [one_smul] using (sail_on one_pos)
    have hF:DifferentiableAt ℝ g sail:=((F.class_smooth F H.smooth (fun _:Fin 2=>⟨4,u⟩)).contDiffAt ((conf_open _).mem_nhds ht)).differentiableAt (by simp)
    let L:ℝ→L[ℝ] Points 2:= LinearMap.toContinuousLinearMap (LinearMap.toSpanSingleton ℝ _ sail)
    have he:HasDerivAt A' sail 1:=by
        have hx: L 1=sail:=one_smul ℝ sail
        rw [← hx]; exact L.hasFDerivAt.hasDerivAt
    have hp:= (show DifferentiableAt ℝ g (A' 1) from (by rw [show A' 1=sail from one_smul ..]; exact hF)).hasFDerivAt.comp_hasDerivAt (1:ℝ) he
    change HasDerivAt (g ∘ A') ((_root_.fderiv ℝ g _) _) _ at hp
    simp only [show A' 1=sail from one_smul ..] at hp
    have hz: HasDerivAt (g ∘ A') (↑(Ftax C*(-8)):ℂ) 1:=by
       let p(x:ℝ):= x^8
       have hh:=((hasDerivAt_id' (1:ℝ)).pow 8).inv (by simp); norm_num at hh
       have hv:= Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 1 (hh.const_mul (Ftax C)); exact hv.congr_of_eventuallyEq ((lt_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).mono (fun x hx=> sails_val C _ hx))
    unfold pron; simp_rw [one_smul,show Fin.cons (α:=fun _:Fin (1+1)=>_) (stepField C) (fun _=>stepField C)=(fun _ : Fin 2=>u) from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)]
    exact hp.unique hz
lemma sail_b (H:(Bel C.book).Hierarchy)(h:G.Simple): pron timeAxis (stepField C) (fun _:Fin 1=>stepField C) sail 1 ≠ 0:=by
    rw [sails_peak H]; have hx:0<Ftax C:=by unfold Ftax; have ht:0 < (G.lieDim:ℝ):= Nat.cast_pos.mpr (by rw [Gauge.lieDim, ← G.colorIso.finrank_eq]; haveI := h.nontrivial_color; exact Module.finrank_pos); positivity
    exact_mod_cast mul_ne_zero hx.ne' (by norm_num : (-8:ℝ)≠0)
end YM.Trace.Pith

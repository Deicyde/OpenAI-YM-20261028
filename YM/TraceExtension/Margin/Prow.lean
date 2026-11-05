import YM.TraceExtension.Terrace.Turf
import YM.TraceExtension.Pi.Born
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Lattice Matrix Precision Laurent Labels Source RG Wilson StressFlux
open Finset Kits Pressure Terrace Terrace.Glade Work Further.PhysicalPeriodLimitF933
open Shunt Perfect Turret Weir Extra.Histories Next.Foundations Planned.PrimaryIntegral295 Place
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s:Side}{Φ:Peat G s}{H:Hol G}
-- rotate assessed reading.Divergence compatible through stage 5 in polarized quotient and bare.
def accord (J:Jet G)(i:Axis):Label G 4→ₗ[ℝ] ℂ:= prong (J 0) (bentV (J 1) i)
lemma curb (s:Signed)(j:ℕ)(x:Taylor G j): Taylor.turn s.ortho⁻¹ (Taylor.turn s.ortho x)=x:=by rw [← Taylor.turn_mul,inv_mul_cancel,Taylor.oneTurn]
lemma wrapA (s:Signed)(A:Taylor G 1)(i:Axis): bentV (Taylor.turn s.ortho A) (s.perm i)= sign s i • Taylor.turn s.ortho (bentV A i):=by
    refine (smul_right_injective _ (r:=(2:ℝ)) (by positivity)) ?_; dsimp only; rw [← sum_legs0, ← sum_legs0]; refine Finset.sum_congr rfl fun a _=>sum_congr rfl fun b _=>?_ ; obtain ⟨a,rfl⟩:=s.perm.surjective a; obtain ⟨b,rfl⟩:=s.perm.surjective b
    rw [←bendV, curl1_turn,map_smul (curl0 ..),curl0_turn,smul_smul,bendV]
lemma shifted_leg (u:Signed)(J:Jet G)(i:Axis): Taylor.turn u.ortho⁻¹ (bentV (J 1) (u.perm i))= sign u i • bentV (shifted u J 1) i:=by
    have ht:= wrapA u (shifted u J 1) i; rw [show Taylor.turn u.ortho (shifted u J 1)=J 1 from ?_] at ht
    · rw [ht,map_smul,curb]
    change Taylor.turn u.ortho (Taylor.turn u.ortho⁻¹ _) = _; rw[← Taylor.turn_mul,mul_inv_cancel,Taylor.oneTurn]
lemma shift_s (u:Signed)(t:Taylor G 0): shifted u (Pi.single 0 t)=Pi.single 0 (Taylor.turn u.ortho⁻¹ t):=by
    funext k; by_cases h:k=0; · subst k;simp[StressFlux.shifted,changedJet]
    simp [StressFlux.shifted, changedJet, h,Pi.single_eq_of_ne]
lemma steamer(u:Signed)(x y:Taylor G 0)(v:Label G 4): prong x y (tensor u.ortho v)=prong (Taylor.turn u.ortho⁻¹ x) (Taylor.turn u.ortho⁻¹ y) v:= by
    have hx(w:Jet G) : prink w (tensor u.ortho v)=prink (StressFlux.shifted u w) v:=by
         change Labels.read w (rotated u.ortho v.val)=Labels.read (StressFlux.shifted u w) v.val; exact eval_changed ..
    unfold prong; simp only[LinearMap.sub_apply,LinearMap.add_apply,hx]; rw [shift_s,shift_s,shift_s,map_add,show shifted u (0:Jet G)=0 from funext fun i=>map_zero _]
lemma ivy_scale(x:Taylor G 0)(v:ℝ): ivy (0:Site s) (v • x)= v • ivy 0 x:=by
    unfold Kits.ivy; rw[←fume_leg, show (fun z i=>(v • x : Taylor G 0).value i z)=v • radialValue x from ?_, fume_scale, sC_weights, show fume (radialValue x)=_ from fume_leg x]
    funext z k; rfl
variable {F:Labels.Frame G 4}{Z:Labels.Frame G 5}
lemma patch_true {d:ℕ}(F:Frame G d)(s:Motion)(x:F.Coeff)(h:realBar (F.coords.symm x)=F.coords.symm x):Prism F s x = F.act s.1.ortho x:=by
   let y:=F.act s.1.ortho x; change Motion.patch F s x=_; unfold Motion.patch; split; swap; · rfl
   ext1 i; change star (y i)=y i; rw[← F.conj_basis]; apply congr_fun; change F.coords (realBar (F.coords.symm (F.coords _)))=_; rw[LinearEquiv.symm_apply_apply]; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,real_turn,h];rfl
lemma psyche (i:Axis)(u:Signed)(w:F.Coeff) (A:loom G s) (h:JetTest H 0 (F.coords.symm w) (Complex.ofRealCLM∘A.val))(hp:G.Simple)(J:Jet G): accord J (u.perm i) (F.coords.symm (F.act u.ortho w))=(sign u i) • accord (shifted u J) i (F.coords.symm w):=by
    let a:= shifted u J; unfold accord; rw [show F.coords.symm (F.act u.ortho w)=tensor u.ortho (F.coords.symm w) from F.coords.symm_apply_apply _,steamer,shifted_leg]
    rw[sprig5 _ _ A h hp,sprig5 _ _ A h hp,ivy_scale,sheen_scale_r]; push_cast; rfl
lemma cloakR {d:ℕ}(F:Frame G d)(t:F.Coeff)(u:Motion)(h: realBar (F.coords.symm t)=F.coords.symm t): F.coords.symm (Prism F u t)=tensor u.1.ortho (F.coords.symm t):=by rw[patch_true F _ _ h]; exact F.coords.symm_apply_apply _
end YM.Trace.Margin

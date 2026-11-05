import YM.TraceExtension.Terrace.Bang
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
set_option quotPrecheck false
local notation "A"=> C.path.levels
variable {d N p k i:ℕ}
local notation "F"=> C.labels.level d
section
lemma dollar (x a:ℝ): Next.Rank.Perch.bill a x = Wave a x:=by unfold Next.Rank.Perch.bill Wave; rw[mul_comm]; rfl
variable (H:C.Makes)
include H
lemma scores_core (T:Module.End ℂ (C.label d))(V:Tested C d k N p T)(hq:InvoiceSky C k N p d T)(hk:C.ref d ≤ k)(h:k≤N)(v:C.label d):
    (F).coeffSize ((F).core (awake C d k N p v)-(F).core (T v)) ≤ AgeK C.path.levels (-(1/2:ℝ)) k*(2*(F).coeffSize ((F).core (T v))):=by
    let w:= T v 0; let y:= v-w • C.refUnit d; let Z: Module.End ℂ (C.label d):= ((C.S.a k:ℂ)^d)⁻¹ • (nib_linear C H (p:=p) hk h).mk' _
    have hZ(t:C.label d): Z t=awake C d k N p t:=rfl
    have hζ: Z (C.refUnit d)= (F).e0:=by rw [hZ,awake,show columns C d k N p _= _ from nib_unit C H hk h, unitVec]; rw[smul_smul,inv_mul_cancel₀ (pow_ne_zero d (by exact_mod_cast (C.S.a_pos _).ne')),one_smul]
    have hs : T y= (F).core (T v):=by unfold y; rw [map_sub,map_smul,V.unit,drop]
    have ht: (F).core (Z y)=(F).core (Z v):=by unfold y; rw [map_sub,map_smul,hζ, map_sub,map_smul,show (F).core (F).e0=0 from ?_]; rw[smul_zero,sub_zero]; rw[drop];simp[Labels.Frame.e0]
    have hh: (F).core (T y)= (F).core (T v):=by rw [hs,drop (F) ((F).core _)]; simp [Frame.core]
    have he := (Work.G08.size_core (F) (Z y-T y)).trans (hq y); let x:=AgeK (A) (-(1/2:ℝ)) k
    rw [map_sub,hh,ht,hZ] at he
    apply he.trans; simp only[dollar,neg_div]; change x*_≤x*_; apply mul_le_mul_of_nonneg_left _ (wake ..|>.le); rw [← hs]; exact V.cost C _ _

lemma mintage (T:Module.End ℂ (C.label d))(V:Tested C d k N p T)(hk:C.ref d ≤ k)(h:k≤N)(v:C.label d)(u:ℝ)(ha:d ≤5)(hG:G.Simple)(ht:Cgrade (C.labels.level d) v) :
    let X:= C.path.β N p k; let t:=(A|>.budget k).threshold
    (F).core (T (ladd C u k N p d T v)) = (X*t^ (2:ℕ)*u^d) • (F).core v:=by
   intro X t; let L:= ladd C u k N p d T; let x:= T (L v); let a:= shrink C k N p; have hx:0<X:= Overlay.beta_positive H.wilson h; have hy:0<t:= ((A).budget k).threshold_pos
   have ht': (a⁻¹)^ (2:ℕ)=X*t^2:=by change (((Real.sqrt X)⁻¹ / t)⁻¹)^ (2:ℕ)=_; rw [inv_div,div_inv_eq_mul,mul_pow,Real.sq_sqrt hx.le,mul_comm]
   have hp: (F).scaled a x=weightTag C d u v:= poured H hk h u T V v
   have hξ:x=(F).scaled a⁻¹ (weightTag C d u v):=by have hA:= (F).scaled_inv (inv_ne_zero (shrink_pos C H h p|>.ne')) x; rw[inv_inv,hp] at hA; exact hA.symm
   change (F).core x=_; rw[hξ]; let Y:= C.labels.level d; ext1 i
   by_cases hi:i=0
   · subst i; simp[Frame.core]
   change update (Y.scaled _ _) 0 0 i =(X*t^2 * u^d) • update v 0 0 i; rw [update_of_ne hi,update_of_ne hi,Frame.scaled_apply]; by_cases hv:v i=0; · simp[weightTag,hv]
   rw[(nbase Y ha _ hi hG).2.2,show (a⁻¹)^2=X*t^2 from ht']; simp only [weightTag,LinearMap.coe_mk,AddHom.coe_mk,ht i hi hv,Complex.real_smul]; push_cast; ring

lemma via_step (T:Module.End ℂ (C.label d))(V:Tested C d k N p T)(hq:InvoiceSky C k N p d T)(hk:C.ref d ≤ k)(h:k≤N)(v:C.label d)(u:ℝ)(hu:0≤u)(ha:d ≤5)(hG:G.Simple)(ht:Cgrade (C.labels.level d) v) :
    let L:=ladd C u k N p d T;let r:= C.S.a k*u; let z:= C.path.β N p k * r^d;let w:= z • (F).core v
    (F).coeffSize (spine C d k N p (L v)-w) ≤ AgeK C.path.levels (-(1/2:ℝ)) k*(2*z*(F).coeffSize ((F).core v)):=by
   intro L r z w; let a:=C.S.a k; let x:= T (L v); let t:= ((A).budget k).threshold; let B:= C.path.β N p k; let g:=B*t^ (2:ℕ)*u^d
   have hm: (F).core x=g • (F).core v:= mintage H T V hk h v u ha hG ht
   have ht:= ((A).budget k).threshold_pos; have hx:0<a:= C.S.a_pos _; have hz:0 ≤ g:= by have ht:0 <t:=ht; have h:0<B:=Overlay.beta_positive H.wilson h;unfold g; positivity
   let Z:=(t^ (2:ℕ))⁻¹ * a^d; have hZ: 0≤Z:=by unfold Z t; positivity
   have he: Z*g=z:=by unfold Z z r g; change _=B*(a*u)^d; have hk :t≠0:=ht.ne'; field_simp; ring
   have hs : spine C d k N p (L v)-w = Z • ((F).core (awake C d k N p (L v)) - (F).core x) :=by
       rw [smul_sub,hm,smul_smul,he]; congr 1
       unfold Z awake; rw [←Complex.ofReal_pow, ←Complex.ofReal_inv,map_smul,show (↑((C.S.a k^d)⁻¹):ℂ) • (F).core (columns C d k N p (L v))=_ from (RCLike.real_smul_eq_coe_smul (K:=ℂ) _ _).symm]; rw[smul_smul]; unfold spine; change _=( (t^2)⁻¹*a^d*(a^d)⁻¹ ) • _; rw [mul_assoc,mul_inv_cancel₀ (pow_ne_zero d hx.ne'),mul_one]
   rw[hs,count_smul,Real.norm_of_nonneg hZ]; apply le_trans (mul_le_mul_of_nonneg_left (scores_core H T V hq hk h (L v)) hZ)
   let V0:=AgeK (A) (-(1/2:ℝ)) k; change Z*(V0*(2*(F).coeffSize ((F).core x))) ≤ _; rw [hm,count_smul,Real.norm_of_nonneg hz]; apply le_of_eq; rw [← he]; ring
end
end YM.Trace.Terrace

import YM.UVExtension.Lacing.Ram
/-!
 # Graph-step architecture. at every complex coordinate its inputs under Motion may be OTHER values of the parameter.
 Hence require *family* per motion. cone delivered, eq genuine. Strong stability even without complex orientation equations.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Motion Next.Foundations
open Bid Concert BoundedContinuousFunction Eyelet RoutesF Work.G08
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n n':Side}{d:ℕ} {F:Frame G d}{p P :BudgetPoint}{H:Hol G}
local notation "R"=> RoutesF F n n' p P H
local notation "E"=> Cow G n' p d H
local notation "B"=> Cow G n P d H
local notation "Lc"=> Bucket F P H n
set_option quotPrecheck false
variable (L:Motion→RoutesF F n n' p P H)(Y Y':Motion→(F.Coeff→ₗ[ℂ] Cow G n' p d H))(hn:2≤ n.val)
local notation "a'"=> major L Y hn
local notation "b'"=> minor L Y hn
local notation "F1"=> F.Coeff
variable {L Y hn}
-- two-way Φ & normal remainder Cone
structure Tollgate (F :Frame G d) (u v c w s:ℝ):Prop where
    calm : 1 ≤ c -- leading price
    t_now : 1 ≤ w  -- output cone
    t_next : 1 ≤ s  -- input cone
    /- quantitative margins -/
    turn : 2*c*((u+2*u*s)*orbitCost F) ≤1
    weight : (v+2*u*s)*orbitCost F*(2*c) ≤ w
    orbit : (1+w)*(2*u*s)*orbitCost F*(2*c) ≤ (1/8)*w
    lens : (2*u*s) * (1+w)*(2*c) ≤ (1/8)*w
    seance : (2*u*s) * (2*c) ≤1/8
variable {u v c w s:ℝ} {r:Side}{T:Heading F} (h:Tollgate F u v c w s)
variable (hR: ∀ i:Motion, (Tips (L i) r T u v)) (hp:∀ x:F.Coeff,F.coeffSize (T.map x) ≤ c*F.coeffSize x ∧ F.coeffSize (T.map.symm x) ≤ c* F.coeffSize x)(hh: ∀ i x, ‖Y i x‖ ≤ s*F.coeffSize (F.core x))
include h hR hp hh
lemma Gate (hn:2≤ n.val)(x:F.Coeff) : F.coeffSize x ≤ 2*c*F.coeffSize (major L Y hn x)∧ F.coeffSize (F.core x) ≤ 2*c*F.coeffSize (F.core (major L Y hn x)) ∧‖minor L Y hn x‖ ≤ w* F.coeffSize (F.core (major L Y hn x)):=by
   have hs:=h.t_next; obtain ⟨he,ht⟩:= sailC L Y hn hR (zero_le_one.trans hs) hh x
   let M:= major L Y hn; let X:= M x; let z:=vowel F r x; have hx: F.coeffSize (F.core x) ≤ F.coeffSize (F.core z):=by rw [show F.core z= _ from core_vowel F r x]; exact (size_vowel F r _).1
   let k:=F.coeffSize; have hc: 0≤2*c:=mul_nonneg zero_le_two (zero_le_one.trans h.calm)
   have hn':2*c*k (X-T.map z)≤ k (F.core z):= by
      apply (mul_le_mul_of_nonneg_left he hc).trans; change 2*c*((_)*k (F.core x)) ≤ _; rw [←mul_assoc]; exact (mul_le_of_le_one_left (size_nonneg ..) h.turn).trans hx
   have hD:=lead_bounds F c h.calm T.map hp X z (hn'.trans (size_core ..))
   have hm' : 2*c* F.coeffSize (F.core X-T.map (F.core z)) ≤ F.coeffSize (F.core z):=by
       rw [T.core_comm z, ← map_sub]; apply le_trans (mul_le_mul_of_nonneg_left (size_core ..) hc) hn'
   have hY:= (lead_bounds F c h.calm T.map hp (F.core X) (F.core z) hm').1
   have he':= (hR (1,false)).wing; have hv:=(hR (1,false)).counts.calm
   refine ⟨(size_vowel ..).1.trans hD.1,hx.trans hY,ht.trans ((mul_le_mul_of_nonneg_left hY (by have hhh:=orbitCost_one_le F; positivity :0≤ (v+2*u*s)*orbitCost F)).trans ?_)⟩
   rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h.weight (size_nonneg ..)

lemma carat (hn:2≤ n.val) : Bijective (major L Y hn):=by
   let T: F.Coeff→ₗ[ℂ] F.Coeff:= (major L Y hn).toLinearMap
   have he:Injective T:= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun x hx=> by
       have ht:major L Y hn x=0:=hx
       apply size_separates F; simpa [ht,Frame.coeffSize] using (Gate h hR hp hh hn x).1))
   exact ⟨he,(LinearMap.injective_iff_surjective.mp he)⟩

omit h hR hp hh
variable (L Y hn)
-- outside domain junk allowed

section inverse
variable {Ω : Type}[NormedAddCommGroup Ω][NormedSpace ℂ Ω]
def steers (f:Ω→L[ℂ] Ω): Ω ≃ₗ[ℂ] Ω:=if h:Bijective f then LinearEquiv.ofBijective f.toLinearMap h else LinearEquiv.refl _ _
lemma steers_eq (f:Ω→L[ℂ] Ω)(hf:Bijective f)(x:Ω): steers f x=f x:=by unfold steers; rw [dif_pos hf]; rfl
end inverse
def steer : F1 ≃ₗ[ℂ] F1:= steers (major L Y hn)

def crown : F.Coeff→ₗ[ℂ] B:= (minor L Y hn).toLinearMap.comp (steer L Y hn).symm.toLinearMap -- hn section via notation?
variable {L Y hn}
include h hR hp hh
lemma focal (hn:2≤ n.val)(x): steer L Y hn x= major L Y hn x:=steers_eq _ (carat h hR hp hh hn) x
lemma pilfer (hn: 2≤ n.val)(x): crown L Y hn (major L Y hn x)=minor L Y hn x:=by rw [← focal h hR hp hh]; unfold crown; simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply]; exact rfl
lemma brunt (hn:2 ≤ n.val) (x): ‖crown L Y hn x‖ ≤ w*F.coeffSize (F.core x):=by
    obtain ⟨x,rfl⟩:=(carat h hR hp hh hn).2 x
    rw [pilfer h hR hp hh]; exact (Gate h hR hp hh _ x).2.2
end YM.UVExtension.Lacing

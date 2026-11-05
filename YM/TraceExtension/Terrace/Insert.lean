import YM.TraceExtension.Terrace.Path
import YM.Push.STRESS_FLUX.Low
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Maxwell Push.CutoffProjectors Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East StressFlux
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G} {F: Extraction.Order} {𝓛: Ultrafilter (ℕ×ℕ)}
set_option quotPrecheck false
local notation "a!"=> (𝓛:Filter (ℕ×ℕ))
local notation "A"=> C.path.levels
variable {Z:Arch C} (hZ: steep 𝓛 Z) {d m j k:ℕ}
local notation "D!"=> C.labels.level d
-- undo swale including when unit price. generic half
lemma immune4 (h:G.Simple) {v:Label G 4}(hp:v∈ equationIdeal G 4) : v=0:=by
   obtain ⟨T,hT,hq,he⟩:= StressFlux.low (by decide) v; have he' := Low.linear_invariant h (Low.covariance hT he)
   apply label_ext; intro J
   obtain ⟨X,hX⟩:= shell_affine (J 0); let Y: TaylorTower G:= Pi.single 0 X
   have hs:= ideal_meaning.mp hp Y
   rw[he] at *; simpa only [Low.eval,he', hq le_rfl,LinearMap.zero_apply,add_zero, Y, Pi.single_eq_same,hX, Submodule.coe_zero,map_zero] using hs
lemma sane4 (h:G.Simple): Bijective ((Cells.standard C).project 4):=by
   let T:=Cells.standard C; refine ⟨LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_),T.onto 4⟩
   intro v hv; have hk : v∈ T.null 4:= (Submodule.Quotient.mk_eq_zero _).mp hv
   rw [show T.null 4= _ from Further.CorrectedLift.freeKernel C 4 ] at hk
   have he : (C.labels.level 4).coords.symm v ∈ Maxwell.equationIdeal G 4:= Maxwell.ideal_meaning.mpr ((equation_iff (C.labels.level 4)).mp hk)
   exact (C.labels.level 4).coords.symm.injective ((immune4 h he).trans (map_zero _).symm)
lemma royal4 (h:G.Simple) (v:C.label 4): Further.CorrectedLift.ladder C 4 ((Cells.standard C).project 4 v)=v:= (sane4 h).1 (Further.CorrectedLift.ladder_reads _)
lemma actual4 (h:G.Simple) {S:Table C.book} (X: Climb.Scaling S): Bijective (S.project 4):=⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ((LinearEquiv.ofBijective _ (sane4 (C:=C) h)).finrank_eq.trans (X.U 0 4).finrank_eq)).mpr (S.onto 4), S.onto 4⟩
/-- Includes θ conversion; on H spin vectors with no units it exactly inverts swale. -/
def booty(Z:Arch C)(d i:ℕ)(v:ℝ) : Module.End ℂ (C.label d):=(v*((A).budget i).threshold^ (2:ℕ)) • (Z.M d i).symm.toLinearMap
lemma treasure(Z:Arch C)(d i:ℕ)(v:ℝ)(x:C.label d): booty Z d i v x=(v*((C.path.levels.budget i).threshold^ (2:ℕ))) • (Z.M d i).symm x:=rfl
/-- The label that buys the observed local operator in units of a `v` dilation. -/
def Vault (S:Table C.book)(Z:Arch C)(d i:ℕ)(v:ℝ) : C.label d →ₗ[ℂ] S.Field d:= (S.project d).comp (booty Z d i v)
lemma cash_pin (S:Table C.book)(Z: Arch C)(x:C.label d)(b:ℝ): Vault S Z d j b (swale Z d j x)= b • S.project d ((Z.M d j).symm ((C.labels.level d).core (Z.M d j x))):=by
    let T:= Z.M d j; let e:ℝ:=((A).budget j).threshold; have he:0<e:= ((A).budget j).threshold_pos; unfold Vault; rw[LinearMap.comp_apply,treasure,land];
    have hv (x y): T.symm (x • (y:C.label d))=(x:ℝ) • T.symm y:= (T.symm.toLinearMap.restrictScalars ℝ).map_smul ..
    rw [show (Z.M d j).symm _= _ from hv (e^ (2:ℕ))⁻¹ ((D!).core (T x)),smul_smul,show b* ((A).budget j).threshold^2*(e^2)⁻¹=b from by change b*e^2*(e^2)⁻¹=b; field_simp, (show ∀ y:C.label d,S.project d (b • y)=b • S.project d y from fun _=> ((S.project d).restrictScalars ℝ).map_smul ..)]
lemma king_unit : C.book.scalar d=C.refUnit d:=by
    change _=((C.path.S.a (C.ref d): ℂ)^d) • (C.labels.level d).e0;rfl
variable (H:C.Makes) (hb: (𝓛:Filter (ℕ×ℕ)) ≤ F.fuse)
include hZ H hb
lemma receipt (hp:C.ref d ≤ j): booty Z d j 1 ((D!).e0)= ((((A|>.budget j).threshold^2:ℝ):ℂ)*((C.S.a j:ℂ)^d)⁻¹) • C.refUnit d:=by
   let V:= Z.M d j; let p:= ((C.S.a j:ℂ)^d); let t:= ((A).budget j).threshold; rw [treasure,one_mul]
   have he:p ≠ 0:=pow_ne_zero _ (by exact_mod_cast (C.S.a_pos _).ne');
   have ht: (Z.M d j).symm (p • (D!).e0)= C.refUnit d:=V.injective (by rw [LinearEquiv.apply_symm_apply,move_anchor_unit hZ H hb hp]; rfl)
   have hx: V.symm (D!).e0=p⁻¹ • C.refUnit d:=by rw [← ht,map_smul, inv_smul_smul₀ he]
   rw [show (Z.M d j).symm (D!).e0=_ from hx, RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]; rfl
lemma cash_pinc (S:Table C.book)(ht:S.Basic)(x:C.label 4)(b:ℝ)(hc:C.ref 4 ≤ j): centering S 4 (Vault S Z 4 j b (swale Z 4 j x))= b • centering S 4 (S.project 4 x):=by
   rw[cash_pin]; let P:= centering S 4; rw [show centering S 4 (b • _)=_ from (P.restrictScalars ℝ).map_smul ..]; congr 1
   rw[drop,map_sub,LinearEquiv.symm_apply_apply]; simp_rw [map_sub,map_smul];
   have hu : P (S.project 4 ((Z.M 4 j).symm (C.labels.level 4).e0))=0:=by
       let t:= ((A).budget j).threshold; have ht':0<t:= ((A).budget j).threshold_pos
       suffices he: t^ (2:ℕ) • P (S.project 4 ((Z.M 4 j).symm (C.labels.level 4).e0))=0 from (smul_eq_zero.mp he).resolve_left (pow_ne_zero _ ht'.ne')
       let e:=P.comp (S.project 4); change t^ (2:ℕ) • e _=_; rw [show ∀ v:C.label 4, t^ (2:ℕ) • e v=e (t^ (2:ℕ) • v) from fun v=> ((e.restrictScalars ℝ).map_smul (t^ (2:ℕ)) _).symm]
       let F' := C.labels.level 4; rw[show t^ (2:ℕ) • (Z.M 4 j).symm F'.e0= _ from (by rw [treasure,one_mul]: _=booty Z 4 j 1 F'.e0),receipt hZ H hb hc,map_smul, show e (C.refUnit 4)=0 from by rw [← king_unit]; exact const_out ht,smul_zero]
   change _- P (((Z.M 4 j x) 0) • (S.project 4 ((Z.M 4 j).symm (C.labels.level 4).e0)))=_; rw[map_smul,hu,smul_zero,sub_zero];rfl
end YM.Trace.Terrace

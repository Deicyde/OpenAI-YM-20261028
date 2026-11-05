import YM.TraceExtension.Terrace.Calendar
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.FreeRanks
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux
open Further.PhysicalPeriodLimitF933
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G} {F: Extraction.Order} {𝓛: Ultrafilter (ℕ×ℕ)}
set_option quotPrecheck false
local notation "U#"=> C.labels.level 5
local notation "A"=> C.path.levels
variable {Z:Arch C} {S:Table C.book}{X:Scaling S}
section maps
def reflA {d:ℕ}(F:Frame G d)(s:Signed): Module.End ℝ F.Coeff := (F.act s.ortho).restrictScalars ℝ
def reflB {d:ℕ}(F:Frame G d): Module.End ℝ F.Coeff where
    toFun := star
    map_add' x y:= star_add ..
    map_smul' c x:=by ext i; simp
abbrev Bowl (F:Frame G 5):= vectors (reflA F) (reflB F)
abbrev Cone (F:Frame G 4):= tensors (reflA F) (reflB F)
lemma real_forms (F:Frame G 5) (v:Bowl F)(i): star (v.val i)=v.val i:=v.property.1 i
lemma frames_night (F:Frame G 5)(v:Bowl F)(i):night F (v.val i):=by
   have ht:=v.property.2 archV i; unfold night; apply ht.trans; simp[archV,sign]
lemma candle (F:Frame G 5) (x:F.Coeff): realBar (F.coords.symm x)= F.coords.symm (star x):= F.coords.injective (by ext1 i; rw [F.conj_basis,LinearEquiv.apply_symm_apply];rfl)
def plate (F:Frame G 5) : Bowl F≃ₗ[ℝ] RawOne G:=
    { vectorMap (F.coords.symm.toLinearMap.restrictScalars ℝ) (K:=reflA F) (D:=spinR) (R:=reflB F) (T:=conjR)
            (fun s x=> (show F.coords.symm (F.act s.ortho x)=tensor s.ortho (F.coords.symm x) from by rw [show F.act s.ortho x=F.coords _ from rfl,LinearEquiv.symm_apply_apply];rfl)) (fun x=> (candle F x).symm) with
      invFun := vectorMap (F.coords.toLinearMap.restrictScalars ℝ) (K:=spinR) (D:=reflA F) (R:=conjR) (T:=reflB F)
          (fun s x => (Frame.act_coords F s.ortho x).symm) (fun x=> (by change F.coords (realBar x)=star (F.coords x); apply F.coords.symm.injective; rw [LinearEquiv.symm_apply_apply,← candle, LinearEquiv.symm_apply_apply]))
      left_inv:=fun x=>Subtype.ext (funext fun i=>F.coords.apply_symm_apply _)
      right_inv:=fun x=>Subtype.ext (funext fun i=>F.coords.symm_apply_apply _) }
lemma vspin {L:Register G}{T:Table L}(H:T.RealSpin)(v:TableOne H)(i:Axis) : T.mirror H 5 archV (v.val i)= -v.val i:= (v.property.2 archV i).trans (by simp[sign,archV])
end maps
section imaging
variable (F':Frame G 5)
lemma projection_kernel_L {a:(Cells.standard C).RealSpin}{v : RawOne G} (h:G.Simple): vectorProjection a v=0 ↔ ∃ c:ℝ,v=c • (⟨eom G,eom_rows G⟩:RawOne G):=by
    let T:=Cells.standard C; let Z:RawOne G:=⟨eom G,eom_rows G⟩; let H:= vectorProjection a
    constructor
    · intro hv; obtain ⟨w,rfl⟩:= (coordinates1 h).surjective v
      have hK(d:Axis): T.project 5 ((C.labels.level 5).coords ((basisV w).val d))=0:= congr_fun (congr_arg Subtype.val hv) d
      have hP(d:Axis): (C.labels.level 5).coords ((basisV (G:=G) w).val d) ∈ Push.CutoffProjectors.equationSpace (C.labels.level 5):=by
         rw [← Further.CorrectedLift.freeKernel C 5]; exact (Submodule.Quotient.mk_eq_zero _).mp (hK d)
      have hu(b): (basisV (G:=G) w).val b ∈ Maxwell.equationIdeal G 5:=by
         apply Maxwell.ideal_meaning.mpr; intro X; simpa only[LinearEquiv.symm_apply_apply] using (Push.CutoffProjectors.equation_iff _).mp (hP b) X
      obtain ⟨he,hS⟩:= (through_eq w h).mp hu
      refine ⟨w 2,Subtype.ext ?_⟩; funext i; rw[basisV_apply,he,hS]; simp
    rintro ⟨c,hc⟩; change H v=0; have he : H Z=0:=by apply Subtype.ext; funext i; change fromPol (Cells.standard C) (eom G i)=0; exact equation_killed (L:=C.book) i
    rw [hc,map_smul,he,smul_zero]

def Vbase (a : (Cells.standard C).RealSpin) : Bowl (C.labels.level 5) →ₗ[ℝ] TableOne a := vectorProjection a ∘ₗ (plate (C.labels.level 5)).toLinearMap
lemma valV (a:(Cells.standard C).RealSpin) (v: Bowl (C.labels.level 5))(i): (Vbase a v).val i=(Cells.standard C).project 5 (v.val i):=by
    change StressFlux.fromPol (Cells.standard C) _ = _; rw[fromPol_formula]; change (Cells.standard C).project 5 ((C.labels.level 5).coords ((C.labels.level 5).coords.symm _))=_; rw[LinearEquiv.apply_symm_apply]
def Stem5 (F:Frame G 5): Bowl F:= (plate F).symm (⟨eom G,eom_rows G⟩:RawOne G)
lemma Stem5_kernel {a:(Cells.standard C).RealSpin}(v:Bowl (C.labels.level 5)) (h:G.Simple) : Vbase a v=0 ↔ ∃ c:ℝ,v=c • Stem5 (C.labels.level 5):=by
    unfold Vbase; rw[LinearMap.comp_apply,projection_kernel_L h]; constructor
    · rintro ⟨c,hc⟩; exact ⟨c,(plate (C.labels.level 5)).injective (by rw [map_smul, Stem5,LinearEquiv.apply_symm_apply]; exact hc)⟩
    rintro ⟨c,hc⟩; rw [hc]; refine ⟨c,?_⟩; simp [Stem5]
lemma Stem5_alive (F:Frame G 5)(h:G.Simple): Stem5 F≠0:=by
    let v:=plate F; intro hv; have hx := v.map_zero; have he: v (Stem5 F)=0:=by rw [hv]; exact hx
    have he : (⟨eom G,eom_rows G⟩:RawOne G)=0:= (LinearEquiv.apply_symm_apply v _).symm.trans he; exact eom_nonzero h (congr_arg Subtype.val he)

lemma Vbase_sure (a:(Cells.standard C).RealSpin): Surjective (Vbase a):= (vectorProjection_onto a).comp (plate (C.labels.level 5)).surjective
-- expose explicit section value given ladder.No renaming
lemma section5 (a:(Cells.standard C).RealSpin): ∃ U: TableOne a →ₗ[ℝ] Bowl (C.labels.level 5),∀ v:TableOne a, Vbase a (U v)=v∧ ∀ i,(U v).val i=Further.CorrectedLift.ladder C 5 (v.val i):=by
    let F':= C.labels.level 5; let U:=Further.CorrectedLift.ladder C 5; let S:=Cells.standard C
    let f:=vectorMap (U.toLinearMap.restrictScalars ℝ) (K:=spinQ a) (D:=reflA F') (R:=conjQ a) (T:=reflB F') (fun s v=> ladder_spin a s v) (fun v=> ladder_conj a v)
    exact ⟨f,fun v=> ⟨Subtype.ext (funext fun i=> (valV a (f v) i).trans (ladder_reads _)),fun i=>rfl⟩⟩
end imaging
end YM.Trace.Terrace

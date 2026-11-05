import YM.TraceExtension.Atlas.Face
import YM.TraceExtension.Atlas.Aligned
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge}{C: Family G}{X:Extraction.Order}{L:Register G}
variable {S T: Table L}
abbrev Active (S:Table L) := LinearMap.ker (expectation S 4)
lemma belongs (x:S.Field 4): x∈ Active S ↔ expectation S 4 x=0:= Iff.rfl
lemma zero_center (x:Active S): centering S 4 x.val=x.val:=by rw [value_center,(belongs x.val).1 x.property,zero_smul,sub_zero]
lemma center_lands (H:S.Hierarchy) (x:S.Field 4):centering S 4 x∈ Active S:= centers_field H.laws x
def man (H:S.Hierarchy): S.Field 4→ₗ[ℂ] Active S:= (centering S 4).codRestrict _ (center_lands H)
def swingA (H:S.Hierarchy)(v:Signed):Module.End ℂ (Active S):= ((man H).comp (S.mirror H.spin 4 v)).comp (Active S).subtype
def starA (H:S.Hierarchy): (Active S) →ₛₗ[starRingEnd ℂ] (Active S):= ((man H).comp (S.conj H.spin 4)).comp (Active S).subtype
lemma man_fix (H:S.Hierarchy)(v:Active S): man H v.val=v:= Subtype.ext (zero_center ..)
lemma swing_act(H:S.Hierarchy)(v:Signed)(x:Active S): (swingA H v x).val=S.mirror H.spin 4 v x.val:=by change centering S 4 (S.mirror H.spin 4 v x.val) =_; rw[← mirror_center H x.val v, zero_center]
lemma star_act(H:S.Hierarchy)(x:Active S): (starA H x).val=S.conj H.spin 4 x.val:=by change centering S 4 (S.conj H.spin 4 x.val) =_; rw[← conj_center H x.val, zero_center]
lemma swing_mul(H:S.Hierarchy)(v z:Signed)(x): swingA H (v*z) x =swingA H v (swingA H z x):= Subtype.ext (by simp only [swing_act,Table.mirror_mul])
lemma swing_stars(H:S.Hierarchy)(s:Signed)(x): starA H (swingA H s x)=swingA H s (starA H x):= Subtype.ext (by simp only [star_act,swing_act,Table.mirror_star])
lemma star_invol(H:S.Hierarchy)(x):starA H (starA H x)=x:= Subtype.ext (by simp only [star_act, Table.reflect_star])
variable {H:(Bel C.book).Hierarchy}

def page (C:Family G)(p:Face): Active (Bel C.book):= ⟨petal C.book.grid p, mean_bond ..⟩
lemma map_petal (C:Family G)(h:G.Simple)(p:Option Face): stand C.book.grid h p=embed C.book.grid 4 (sectors p):=by rw[stand, Module.Basis.mk_apply]; rfl
lemma landpage (C:Family G)(h:G.Simple)(p:Face): stand C.book.grid h (some p)=(page C p).val:=map_petal ..
lemma page_basis (h:G.Simple)(v:Active (Bel C.book)): ∃ f: Face→ℂ, v=∑ i,f i • page C i:=by
    let P:= C.book.grid; let B:= stand P h;let g(i):= B.repr v.val i
    have hh:∑ i,g i • B i=v.val:= B.sum_repr v.val; rw [Fintype.sum_option] at hh
    have ht:B none=(Bel C.book).unit 4:= (map_petal ..).trans (pin_unit ..); rw [ht] at hh
    have hu(i:Face): B (some i)=(page C i).val:=landpage ..
    simp_rw [hu] at hh
    have hx:g none=0:=by have he:=congr_arg (expectation (Bel C.book) 4) hh; simp_rw [map_add,map_smul,map_sum,map_smul] at he
                         simpa only [show expectation (Bel C.book) 4 _=1 from mean_unit (Maxwell.table_regular _), (belongs _).1 v.property, (fun i=> (belongs _).1 (page C i).property : ∀ i, expectation (Bel C.book) 4 (page C i).val=0), smul_eq_mul, mul_one, mul_zero, Finset.sum_const_zero, add_zero] using he
    rw[hx,zero_smul,zero_add] at hh
    refine ⟨g ∘ Option.some,Subtype.ext ?_⟩
    rw [AddSubmonoidClass.coe_finsetSum]; exact hh.symm
lemma page_ind (h:G.Simple):LinearIndependent ℂ (page C):=by
    apply LinearIndependent.of_comp ((Active (Bel C.book)).subtype)
    rw [show (⇑(Active (Bel C.book)).subtype ∘ page C)=(fun p:Face=> stand C.book.grid h (some p)) from funext (fun p=> (landpage C h p).symm)]
    exact (stand C.book.grid h).linearIndependent.comp Option.some (Option.some_injective _)
lemma page_real (p:Face): starA H (page C p)=page C p:= Subtype.ext (by rw[star_act];exact link_real ..)
lemma paired(p q:Face): (∃ (s:Signed)(c:ℂ), c*c=1 ∧ swingA H s (page C p)= c • page C p∧swingA H s (page C q)=(-c) • page C q)∨
    ∃ (s:Signed)(c:ℂ), c*c=1 ∧ swingA H s (page C p)= c • page C q∧swingA H s (page C q)=c • page C p:=by
    rcases flip_sig C.book.grid H.spin p q with ⟨s,c,h,hp,hq⟩|⟨s,c,h,hp,hq⟩
    exacts [Or.inl ⟨s,c,h,Subtype.ext ((swing_act ..).trans hp),Subtype.ext ((swing_act ..).trans hq)⟩,Or.inr ⟨s,c,h,Subtype.ext ((swing_act ..).trans hp),Subtype.ext ((swing_act ..).trans hq)⟩]
end YM.Trace.Pilot

import YM.TraceExtension.Atlas.Moire
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ComplexOrder
variable {G : Gauge}{C: Family G}{X:Extraction.Order}{L L':Register G}
variable {S: Table L}{S' : Table L'}
open LinearMap
section
variable {E K T: Type*} [NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E][NormedAddCommGroup K][NormedSpace ℂ K][FiniteDimensional ℂ K][NormedAddCommGroup T][NormedSpace ℂ T][FiniteDimensional ℂ T]
-- from separate maps. steering, symmetric, etc
lemma brunch (f:E→ E→ ℂ)(h:∀ x,IsLinearMap ℂ (f x))(hp:∀ x, IsLinearMap ℂ (fun i=> f i x)) : ∃ P:Bi E,∀ i j,P i j=f i j:=by
    let b(i):= LinearMap.toContinuousLinearMap (IsLinearMap.mk' _ (h i)); apply packV f _ (fun i j=>show b i j=f i j from rfl)
    intro x; exact ⟨LinearMap.toContinuousLinearMap (IsLinearMap.mk' _ (hp x)),fun i=>rfl⟩
omit [FiniteDimensional ℂ E][FiniteDimensional ℂ K] in
def pullBi (P:Bi E)(f g : K→L[ℂ] E): Bi K:= ( (ContinuousLinearMap.compL ℂ K E ℂ).flip g).comp (P.comp f)
-- real conj subrestrict variant
lemma ccome (q:E →ₛₗ[starRingEnd ℂ] E)(B:Bi E) : ∃ P:Bi E,∀ v w,P v w= star (B (q v) (q w)):= by
    apply brunch
    · intro x; constructor
      · intro a b; simp only [map_add,star_add]
      intro a b; rw [map_smulₛₗ,(B _).map_smul,smul_eq_mul,star_mul']; rw [show ∀ c:ℂ,star (starRingEnd ℂ c)=c from fun a=> star_star a]; rfl
    intro x; constructor
    · intro a b; simp only[map_add,_root_.add_apply,star_add]
    intro a b; rw [map_smulₛₗ,B.map_smul,_root_.smul_apply,smul_eq_mul,star_mul']; rw [show ∀ c:ℂ,star (starRingEnd ℂ c)=c from fun a=> star_star a]; rfl

def flipC(q:E →ₛₗ[starRingEnd ℂ] E) (B:Bi E):Bi E:= (ccome q B).choose
lemma flipC_apply (q:E →ₛₗ[starRingEnd ℂ] E) (B:Bi E) (v w): flipC q B v w= star (B (q v) (q w)):= (ccome ..).choose_spec v w
end

-- `Carpet`

def LiftB (f : Active S'→ₗ[ℂ] Active S) (P:Carpet S): Carpet S':=pullBi P (LinearMap.toContinuousLinearMap f) (LinearMap.toContinuousLinearMap f)
lemma liftB_at (f : Active S'→ₗ[ℂ] Active S)(B: Carpet S)(v w): LiftB f B v w=B (f v) (f w):=rfl

section
variable {H:S.Hierarchy}
def laceC (H:S.Hierarchy): Submodule ℝ (Carpet S) where
    carrier:={f| (∀ i j,f i j=f j i)∧(∀ i j,f (starA H i) (starA H j)=star (f i j)) ∧ ∀ s v w,f (swingA H s v) (swingA H s w)=f v w}
    add_mem' := fun {f g} ⟨hx,hP,hT⟩ ⟨hy,hS,hK⟩=> by
        refine ⟨?_,?_,?_⟩
        · intro i j; simp only [_root_.add_apply]; rw[hx i j, hy i j]
        · intro i j; simp only[_root_.add_apply,hP,hS,star_add]
        intro s v w; simp only [_root_.add_apply,hT,hK]
    smul_mem' := fun a _ ⟨hx,hP,hT⟩=> by
        refine ⟨?_,?_,?_⟩
        · intro i j; simp only [_root_.smul_apply]; rw[hx i j]
        · intro i j; simp only [_root_.smul_apply,hP,star_smul,star_trivial]
        intro s v w; simp only [_root_.smul_apply,hT]
    zero_mem':=⟨fun _ _=>rfl,fun i j=>by simp,fun _ _ _ =>rfl⟩

def HBasis (H:S.Hierarchy)(B:Carpet S): Carpet S:= ∑ i: Signed, LiftB (swingA H i) B
lemma hbasis_apply(H:S.Hierarchy)(B:Carpet S)(v w): HBasis H B v w=∑ i,B (swingA H i v) (swingA H i w):=by unfold HBasis;simp only [_root_.sum_apply,liftB_at]
lemma hbasis_smul(H:S.Hierarchy)(B:Carpet S)(c:ℂ): HBasis H (c • B)=c • HBasis H B:=by
    ext1 x; ext1 y; rw [hbasis_apply]; simp only [_root_.smul_apply,hbasis_apply, Finset.smul_sum]
lemma hbasis_pos(H:S.Hierarchy)(P:Carpet S)(v:Active S)(hw:v≠0) (hx:∀ p:Active S,p ≠ 0→0 < (P (starA H p) p).re): 0 < (HBasis H P (starA H v) v).re:=by
    rw [hbasis_apply,Complex.re_sum]; apply Finset.sum_pos _ Finset.univ_nonempty; intro s hu; rw[← swing_stars]; refine hx _ ?_
    intro he; apply hw; have hp:= swing_mul H s⁻¹ s v; rw[he,map_zero,inv_mul_cancel] at hp; refine (show swingA H 1 v=v from Subtype.ext (by rw[swing_act, Table.mirror_one])).symm.trans hp
def Hmean (H:S.Hierarchy)(B:Carpet S): Carpet S:= HBasis H (B+B.flip+flipC (starA H) (B+B.flip))
set_option maxHeartbeats 600000 in
lemma lace_h (H:S.Hierarchy) (B:Carpet S): Hmean H B ∈ laceC H:= by
    let P:= B+B.flip; let V:= P+flipC (starA H) P; let A:= Hmean H B; have hv(i j): P i j=P j i:= add_comm ..
    have hA(s:Signed)(i j): (LiftB (swingA H s) V) (starA H i) (starA H j)=star ((LiftB (swingA H s) V) i j):= by
        simp only [liftB_at,V,_root_.add_apply, ← swing_stars, flipC_apply, star_invol,star_add,star_star]; exact add_comm ..
    let c := (((Fintype.card Signed:ℂ)*4)⁻¹); let P':= HBasis H V; have hp(v x y):P' (swingA H v x) (swingA H v y)=P' x y:=by
       unfold P' HBasis; simp_rw [_root_.sum_apply,liftB_at,← swing_mul]; exact Equiv.sum_comp (Equiv.mulRight v) (fun i=>V (swingA H i x) (swingA H i y))
    have he(i j): P' i j=P' j i:=by
       unfold P' HBasis; simp only [_root_.sum_apply,liftB_at,V,_root_.add_apply,flipC_apply]; exact Finset.sum_congr rfl fun p _=> by rw[hv (swingA _ _ i),hv (starA _ (swingA _ _ i))]
    show Hmean H B ∈ laceC H
    rw [Hmean]; rw [show B+B.flip+flipC (starA H) (B+B.flip) = V from rfl]; show HBasis H V ∈ _
    refine ⟨fun i j=> ?_,fun i j=>?_,fun v i j=>?_⟩
    · exact he i j
    · have hh:P' (starA H i) (starA H j)=star (P' i j):=by unfold P' HBasis; simp only [_root_.sum_apply,star_sum]; exact Finset.sum_congr rfl fun i _=> hA ..
      exact hh
    exact hp v i j

def scannerX(H:S.Hierarchy)(r:ℝ): laceC H:=⟨Hmean H (cine H r),lace_h ..⟩

-- moving orientation unit, finite condition.
lemma lift_laceC (H:S.Hierarchy)(H':S'.Hierarchy)(f:Active S'→ₗ[ℂ] Active S)(hv:∀ x,f (starA H' x)= starA H (f x))(ht:∀ s x,f (swingA H' s x)=swingA H s (f x)) (v:laceC H): LiftB f v.val ∈ laceC H':=by
    obtain ⟨v,hh,hB,hP⟩:= v;dsimp only; exact ⟨fun i j=> hh ..,fun i j=> by simp only [liftB_at,hv,hB],fun s i j=>by simp only [liftB_at,ht,hP]⟩
end
end YM.Trace.Pilot

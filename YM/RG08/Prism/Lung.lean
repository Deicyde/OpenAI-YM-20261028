import YM.RG08.Fold.Fixtures

/-! # Completing-square algebra at finite volume, counting convention, suppressing
    color/face arrays by packing into one type. Γ conditions will use actual tree inverse and
    Schur equations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Prism
open Filter Lattice RG Wilson Forms Pert.Bulk Isles Camera Glyph Room Exterior Function Finset MvPolynomial Matrix Fold
open scoped Classical ContDiff Topology BigOperators Matrix PowerSeries
variable {I J U R O:Type}[Fintype I][Fintype J][Fintype U][Fintype O]

structure Drum (I J U:Type)[Fintype I][Fintype J][Fintype U] where
 C:Matrix J J ℝ -- fine potential K
 N:Matrix U U ℝ
 D:Matrix U J ℝ -- probe
 κ:ℝ
 v:Matrix J I ℝ -- inclusion
namespace Drum
variable (A:Drum I J U)
def total := A.C + (A.κ • (A.Dᵀ*A.D))
def inside := A.vᵀ*A.total*A.v
def foam{I : Type}[Fintype I]:Matrix I I ℝ→Matrix I I ℝ:= fun A=> A⁻¹
def dark := foam A.inside
def g := A.v*A.dark*A.vᵀ
def mean := A.g*(A.κ • A.Dᵀ)
structure Flourishes : Prop where
 symC : A.Cᵀ=A.C
 even : IsUnit A.inside.det
 tied: A.N=A.κ • (1 - A.D*A.mean)
lemma rising (h:A.Flourishes):A.totalᵀ=A.total:=by rw [total,Matrix.transpose_add,Matrix.transpose_smul,transpose_mul,transpose_transpose,h.symC]
lemma symmetry (h:A.Flourishes):A.insideᵀ=A.inside:=by unfold inside; rw [transpose_mul,transpose_mul,transpose_transpose,rising A h,← Matrix.mul_assoc] -- fix
lemma mirrored (h:A.Flourishes):A.darkᵀ=A.dark:=by simp [dark,foam,Matrix.transpose_nonsing_inv,A.symmetry h]
lemma direction (h:A.Flourishes)(i j:I):A.dark i j=A.dark j i:=(congrFun (congrFun (mirrored A h) j) i)
lemma invertible (h:A.Flourishes):A.inside*A.dark=1:=mul_nonsing_inv _ h.even
lemma coating (h:A.Flourishes): A.vᵀ*A.total*A.mean=A.vᵀ*(A.κ • A.Dᵀ):=by
 unfold Drum.mean g
 simp only [← Matrix.mul_assoc]
 rw [← inside,A.invertible h,Matrix.one_mul]
 -- order `1 * A.vᵀ * ... =...` drops.
lemma casing (h:A.Flourishes): A.meanᵀ * A.total * A.mean = A.meanᵀ * (A.κ • A.Dᵀ):=by
 have hT:=congrArg (((A.dark*(A.vᵀ*(A.κ • A.Dᵀ)))ᵀ * ·)) (coating A h) -- Matrix.mul not function?
 simp only [← Matrix.mul_assoc,← Matrix.transpose_mul] at hT; exact hT

-- bilinear conveniences
lemma pairing {I J U:Type}[Fintype I][Fintype J][Fintype U](M:Matrix I J ℝ)(L:Matrix I U ℝ)(x:J→ℝ)(y:U→ℝ):dotProduct (M *ᵥ x) (L *ᵥ y)=dotProduct x ((Mᵀ*L) *ᵥ y):=by
 rw [← vecMul_transpose M, ← Matrix.mulVec_mulVec, ← dotProduct_mulVec]
lemma charge (x:J→ℝ): winB A.C x x+A.κ* dotProduct (A.D*ᵥ x) (A.D*ᵥ x)=winB A.total x x:=by
 unfold total winB; simp only [add_mulVec,smul_mulVec,dotProduct_add,pairing,dotProduct_smul,smul_eq_mul]

private lemma twist (M:Matrix J J ℝ)(h:Mᵀ=M)(x y:J→ℝ):winB M x y=winB M y x:=winery_turn M h ..

lemma completes (h:A.Flourishes)(w:I→ℝ)(x:U→ℝ) :
 let y:=A.v*ᵥ w+A.mean *ᵥ x;
 winB A.C y y+A.κ*dotProduct (x - A.D*ᵥ y) (x - A.D*ᵥ y)=winB A.inside w w+winB A.N x x:=by
 intro y
 have he : winB A.C y y+A.κ*dotProduct (x-A.D*ᵥ y) (x-A.D*ᵥ y)=winB A.total y y+A.κ*dotProduct x x-2*A.κ*dotProduct (A.D*ᵥ y) x:=by
    rw [← charge A y,sub_dotProduct,dotProduct_sub,dotProduct_sub,dotProduct_comm (A.D*ᵥ y) x];ring
 rw [he]
 have hv : winB A.total y y= winB A.inside w w+ 2*dotProduct w ((A.vᵀ*(A.κ • A.Dᵀ))*ᵥ x) + dotProduct x ((A.meanᵀ*(A.κ • A.Dᵀ))*ᵥ x):=by
    unfold y winB inside; rw [mulVec_add,add_dotProduct,dotProduct_add,dotProduct_add,show dotProduct (A.mean*ᵥ x) _=dotProduct (A.v *ᵥ w) (A.total*ᵥ (A.mean *ᵥ x)) from twist _ (A.rising h) (A.mean*ᵥ x) (A.v *ᵥ w)]
    simp_rw [mulVec_mulVec,pairing,← Matrix.mul_assoc,A.coating h,A.casing h];ring
 rw [hv]
 have ht {i:Type}[Fintype i](M:Matrix J i ℝ)(w:i→ℝ):dotProduct w ((Mᵀ*(A.κ • A.Dᵀ))*ᵥ x)= A.κ*dotProduct (A.D*ᵥ(M*ᵥ w)) x:=by
    rw [Matrix.mul_smul,smul_mulVec,dotProduct_smul,smul_eq_mul,←transpose_mul,dotProduct_transpose_mulVec,dotProduct_comm x, mulVec_mulVec] -- theorem arg
 have hx:winB A.N x x=A.κ*dotProduct x x-A.κ*dotProduct (A.D*ᵥ(A.mean*ᵥ x)) x :=by
    rw [winB,h.tied,smul_mulVec,dotProduct_smul,smul_eq_mul,sub_mulVec,one_mulVec,dotProduct_sub,←Matrix.mulVec_mulVec,dotProduct_comm x (A.D*ᵥ(A.mean*ᵥ x))];ring
 unfold y;rw [ht,ht,hx,Matrix.mulVec_add,add_dotProduct];ring
end Drum
end YM.RG08.Prism

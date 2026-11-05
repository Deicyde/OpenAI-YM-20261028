import YM.TraceExtension.Swift.Minor
import YM.TraceExtension.Shepherd.Poise
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Swift
open Function Filter Set Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp Analysis Matrix
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft Xo Zn StressFlux
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {n:Side}
abbrev Bond(n:Side):= Edge (Site n)
def phB(o: Bond n): G.Color→L[ℝ] Link G n:= edgeColor.symm.toContinuousLinearMap ∘L ContinuousLinearMap.single _ (fun _: Bond n=>G.Color) o
abbrev rung (U:Config G n)(o: Bond n)(g:G.Color)(s:ℝ):= input G n (s • phB o g)*U
lemma seatB (U:Config G n)(o:Bond n)(g:G.Color)(s:ℝ):rung U o g s= modify o.1 (posDir o.2) (G.lieExp (s • g)) U:=by
    funext i; unfold StressFlux.modify rung; have hp: (posDir o.2).used o.1 =o:=rfl; rw[hp]; by_cases he:i=o
    · subst i; rw [if_pos rfl];
      rw [Pi.mul_apply,input_color]; simp [phB,posDir]
    rw [if_neg he, Pi.mul_apply,input_color,map_smul, Pi.smul_apply]; simp [phB,he]
abbrev chrom (a:G.ColorIndex): G.Color:= EuclideanSpace.basisFun G.ColorIndex ℝ a
lemma litChrom (a:G.ColorIndex)(u:G.El) : ‖G.adjoint u (chrom a)‖=1:=by rw[G.norm_adjoint]; exact OrthonormalBasis.norm_eq_one ..
lemma zeal(o:Bond n)(p : G.Color)(x: Link G n): dotProduct x (phB o p)= inner ℝ (edgeColor x o) p:=by simp [dotEdge,phB,Pi.single_apply,apply_ite (inner ℝ _)]
lemma bStep(o:Bond n)(i:G.ColorIndex): phB o (chrom i)=bolt (o.1,coord o.2,i):=by
    unfold phB; ext1 ⟨p,a,j⟩; obtain ⟨a,rfl⟩:=axisEquiv.surjective a
    change edgeColor (phB o (chrom i)) (p,a) j= bolt (o.1,coord o.2,i) (p,coord a,j); obtain ⟨x,l⟩:=o; by_cases ht:x=p <;> by_cases hv:a=l <;> by_cases he:i=j <;> simp[bolt,phB,Pi.single_apply, *, coord_iff,chrom] <;> simp_all [eq_comm]
lemma loy (o:Bond n)(u:Coats G n)(p:G.Color): armor u (phB o p)=phB o (G.adjoint (u o.1) p):=by
    apply edgeColor.injective; ext1 i; rw [armor_at]; unfold phB; by_cases h:i=o <;> simp[h]
lemma colours (V:Link G n)(b:G.El) (u:Coats G n) (hh: u=(fun _=>b)) : ∑ i:Lines G n 1,(dotProduct V (armor u (bolt i))) • (armor u (bolt i))=V:=by
    let W:=armor u⁻¹ V
    have ht:armor u W=V:=by apply edgeColor.injective;funext i; rw [armor_at,show edgeColor W i=_ from armor_at ..,← G.adjoint_mul,Pi.inv_apply,mul_inv_cancel,G.adjoint_one]
    rw [← ht]; simp_rw [loyS, ← (armor u).map_smul]; rw[← map_sum]; congr 1; ext1 i; rw[Finset.sum_apply]; simp[dotProduct,bolt,Pi.single_apply]
lemma lumin (u:G.El)(o:Coats G n)(hh:o=(fun _=>u)) (X: Link G n→L[ℝ] Link G n): ∑ i:Lines G n 1,(X (armor o (bolt i))) ⬝ᵥ (armor o (bolt i))=∑ i:Lines G n 1,(X (bolt i)) i:=by
    let A:=Stationary.trench o; have ht:=trench_orthogonal o; let B:= billsM (pocket _) (pocket _) X; let T:= armor o
    have hv (i:Lines G n 1): X (T (bolt i)) ⬝ᵥ T (bolt i)=(Aᵀ*B*A) i i:=by
       let b:=bolt i; have h(d: Matrix (Lines G n 1) (Lines G n 1) ℝ): b ⬝ᵥ (d *ᵥ b)=d i i:=by simp [b,dotProduct,Matrix.mulVec,bolt,Pi.single_apply,sum_dotProduct,mul_ite]
       rw[← h (Aᵀ*B*A)]; change X (T b) ⬝ᵥ T b=b ⬝ᵥ (_ *ᵥ b); rw[Matrix.mul_assoc,← mulVec_mulVec,← mulVec_mulVec,transposes,show A *ᵥ b=T b from bill_pay .., show B *ᵥ _=_ from bill_pay X _]; exact dotProduct_comm ..
    change (∑ i, X (T (bolt i)) ⬝ᵥ T (bolt i))=_; rw[ Finset.sum_congr rfl (fun i _=>hv i)]; change (Aᵀ*B*A).trace=_; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,ht.left,Matrix.one_mul]; refine sum_congr rfl (fun i _=> ?_); unfold B; change (billsM (pocket _) (pocket _) X) i i=_; rw [bill_def,cash_pocket,bockat]
end YM.Trace.Swift

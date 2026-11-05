import YM.TraceExtension.Terrace.Crown
import YM.TraceExtension.Pi.Lens
set_option autoImplicit false
noncomputable section
set_option maxRecDepth 4096
namespace YM.Trace.Terrace.Glade
open Function Filter Finset Lattice RG Wilson Labels Source Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price MergeProof.East Further.CorrectedLift Ward Climb Analysis Work Weir StressFlux
open Further.PhysicalPeriodLimitF933 Shunt PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells Pressure
open Motion
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}
abbrev splitP (s : Signed): Motion ≃ Motion := (Equiv.mulLeft s).prodCongr (Equiv.refl Bool)
abbrev dualP : Motion ≃ Motion:= (Equiv.refl Signed).prodCongr (Equiv.boolNot)
def prev (m:Motion)(a:Axis):= m.1.perm.symm a
def hued (m:Motion)(a:Axis):ℝ:= sign m.1 (prev m a)
abbrev rent:= (Fintype.card Motion:ℝ)⁻¹
lemma rent_pos: 0 < rent:=inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos))
lemma rent_collect (t:ℝ): ∑ _ : Motion,rent*t=t:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,rent]; rw[← mul_assoc,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_pos.ne'),one_mul]
lemma stamp (x:Motion)(a b:Axis) : |hued x a|=1:= by unfold hued sign;split_ifs <;> simp
lemma pigment (x y:Signed)(i:Axis): sign (x*y) i=sign y i*sign x (y.perm i):=by unfold sign; split_ifs <;> first|simp_all|grind
lemma prev_step(x:Motion)(s:Signed) (i:Axis): prev (splitP s x) (s.perm i)=prev x i:=by
   change (s*x.1).perm.symm (s.perm i)= _;rw [Signed.mul_perm]; unfold prev; simp
lemma hue_step(x:Motion)(s:Signed) (i:Axis): hued (splitP s x) (s.perm i)=hued x i*sign s i:=by unfold hued;rw[prev_step]; change sign (s*x.1) _=_;rw [pigment]; unfold prev; congr 2;simp
section reynolds
variable {d:ℕ}(F:Frame G d)
def Prism (m:Motion): Module.End ℝ (F.Coeff) where
   toFun := Motion.patch F m
   map_add' := patch_add F m
   map_smul' a b:=by rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),patch_smul, RingHom.id_apply, RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact congrArg (· • Motion.patch F m b) (scalar_real m a);
lemma shield (u:Motion)(v:F.Coeff) : reflB F (Prism F u v)=Prism F (dualP u) v:=by
    rcases u with ⟨u,a⟩; cases a; · rfl
    exact star_star _
lemma arrow (u:Motion)(s:Signed)(v:F.Coeff): reflA F s (Prism F u v)=Prism F (splitP s u) v:=by
    unfold Prism Motion.patch; simp only[reflA, Equiv.prodCongr_apply,LinearMap.restrictScalars_apply,LinearMap.coe_mk,AddHom.coe_mk,map_mul,Equiv.refl_apply]
    cases hu:u.2 <;> first| simp [hu,Frame.act_mul,act_conj,Signed.inclusionO,show (s*u.1).ortho=s.ortho*u.1.ortho from map_mul Signed.inclusionO ..]|rfl
lemma cardS(c:Motion→ F.Coeff)(A:ℝ)(hc:∀ i,F.coeffSize (c i) ≤ rent*A): F.coeffSize (∑ i,c i) ≤ A:= ((Size.finite F ..).trans (Finset.sum_le_sum fun i _=> hc i)).trans_eq (rent_collect _)
end reynolds
section amap
variable {E:Type*}[AddCommGroup E][Module ℝ E]
def Reed (H:Motion→ Module.End ℝ E) : Module.End ℝ (Axis→ E) where
   toFun v i:= ∑ j:Motion,(rent*hued j i) • H j (v (prev j i))
   map_add' v w:=by ext1; simp[smul_add,Finset.sum_add_distrib]
   map_smul' c v:=by ext1; simp[smul_comm c, Finset.smul_sum]
lemma reedEq (H:Motion→Module.End ℝ E)(v:Axis→ E)(i:Axis): Reed H v i= ∑ j:Motion,(rent*hued j i) • H j (v (prev j i)):=rfl
def Plot (H:Motion→ Module.End ℝ E): Module.End ℝ (Axis → Axis → E) where
   toFun v i j:= ∑ k:Motion,(rent*hued k i*hued k j) • H k (v (prev k i) (prev k j))
   map_add' v w:=by ext1 i; ext1 j; simp[smul_add,sum_add_distrib]
   map_smul' c v:=by ext1 i;ext1 j; simp[smul_comm c,smul_sum]
lemma plotEq(H : Motion→ Module.End ℝ E)(v)(i j): Plot H v i j=∑ k:Motion,(rent*hued k i*hued k j) • H k (v (prev k i) (prev k j)):=rfl
variable (F:Module.End ℝ E)(H:Motion→Module.End ℝ E)
lemma flower (x:Motion→E)(w:Motion→ℝ)(hX:∀ m,F (x m)=x (dualP m))(hx:∀ m,w (dualP m)=w m): F (∑ i:Motion,w i • x i)=∑ i,w i • x i:=by rw[map_sum]; simp_rw [map_smul,hX]; exact Fintype.sum_equiv dualP _ _ (fun i=>by rw[hx])
end amap
section re
lemma blade (F:Frame G 5)(v:Axis→ F.Coeff): Reed (Prism F) v ∈ Bowl F:=by
   constructor
   · intro i; rw[reedEq]; exact flower _ _ _ (fun i=>shield F i _) (fun m=>rfl)
   intro s i; rw[reedEq,reedEq,map_sum,smul_sum];simp_rw [map_smul]; refine Fintype.sum_equiv (splitP s) _ _ (fun x=> ?_); rw [prev_step,hue_step,arrow]; rw[smul_smul]; congr 1; have hs:= sign_sq s i;linear_combination (norm:=ring) -(rent*hued x i)* hs
lemma shard (F:Frame G 4)(v:Axis→ Axis→ F.Coeff) (ht:∀ i j,v i j=v j i): Plot (Prism F) v∈ Cone F:=by
    let H:= Prism F; let P:=Plot H v
    have hs(t:Signed)(i j:Axis): reflA F t (P i j)=(sign t i*sign t j) • P (t.perm i) (t.perm j):=by
        unfold P; rw[plotEq,plotEq,map_sum,smul_sum]; simp_rw [map_smul]; refine Fintype.sum_equiv (splitP t) _ _ (fun x=>?_); unfold H; rw[hue_step,hue_step,prev_step,prev_step,arrow,smul_smul];
        refine congr_arg (· • _) ?_; have he : sign t i^2=1:=sign_sq _ _; have hp:= sign_sq t j; linear_combination (norm:=ring) -(rent*hued x i*hued x j)*( hp+(sign t j)^2 * he)
    refine ⟨fun i j=> ?_, fun i j=> by rw [plotEq]; exact flower _ _ _ (fun i=>shield F i _) (fun m=>rfl),hs⟩
    rw[plotEq,plotEq]; exact Finset.sum_congr rfl (fun b h=>by rw [ht (prev b i),mul_right_comm rent])
variable {d:ℕ}
lemma blade_cost (F:Frame G d)(v:Axis→ F.Coeff)(t:ℝ)(h:∀ i,F.coeffSize (v i) ≤ t)(i:Axis): F.coeffSize (Reed (Prism F) v i) ≤ orbitCost F*t:=by
    rw[reedEq]; apply cardS; intro m; rw [count_smul,Real.norm_eq_abs,abs_mul,stamp _ _ i,mul_one,abs_of_pos rent_pos]
    exact mul_le_mul_of_nonneg_left ((patch_cost ..).trans (mul_le_mul_of_nonneg_left (h (prev m i)) (zero_le_one.trans (orbitCost_one_le ..)))) rent_pos.le
end re
end YM.Trace.Terrace.Glade

import YM.TraceExtension.Cask.Gap
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function
open scoped Classical
variable {V L W I:Type}[DecidableEq V][DecidableEq I][DecidableEq L][DecidableEq W]{n:Side}[Fintype V][Fintype I][Fintype L][Fintype W]{G:Gauge}{R:Rep G n}(C:TourC R V L W)
lemma span_quote (M:Finset I)(S:I→Support n)(f:I→ℝ)(D:ℕ)(a d:ℝ)(h:Hit S D f a d):∀ x,∑ i∈M,(if x∈S i then f i*Real.exp (a*coverNumber D (S i)) else 0)≤ d:= fun _=>Extra.Multi.Budget.cap (h _) _
abbrev Ballot (S:I→Support n) (h:I→Finset V→Prop) := Σ i:I,{p:Finset V// p⊆deer C (S i) ∧ h i p}
-- α+1 on proof. hurdle in ℕ independent.
def bore (p:ℕ)(d q w:ℝ):=4*q*w*Real.exp (d*p)
abbrev orbitP (M d:ℝ)(b:ℕ)(S:I→Support n)(f:I→ℝ)(h:I→Finset V→Prop) (p:Ballot C S h): ℝ:= M*d^(deer C (S p.1)).card*f p.1
lemma brush_hit (w:ℕ) (d:ℝ) (hp:0≤d)(hw:1≤w)(u g v:ℝ)(hu:0≤u)(hg:1≤g)(hv:0≤ v)(k:ℕ)
    (S:I→Support n) (F:I→ℝ)(h:I→Finset V→Prop) [DecidableRel h]
    (he:∀ i,0 ≤ F i) (hf: Hit S w F (d+1) u)(hm:Nat)(hM:1 ≤ hm)
    (hx: (Set.univ:Set V).PairwiseDisjoint C.cap)(hz:∀ i,coverNumber w (C.cap i) ≤ k)(ht:∀ i j,i≠j→64*w*hm+2*w ≤ separation (C.tie i) (C.tie j))(hZ:2*g*Real.exp (d*(k:ℝ)) ≤ Real.exp hm):
    Hit (fun i:Ballot C S h=>bud C i.2.val (S i.1)) w (orbitP C v g w S F h) d (2*v*(Real.exp hm)*u):=by
   let y(i:Ballot C S h):=S i.1; let q:=orbitP C v g w S F h; let V'(t:Support n):=Real.exp (d*coverNumber w t)
   let a(x)(t:I):= if x∈S t then F t*Real.exp ((d+1)*coverNumber w (S t)) else 0
   let A(x)(t:I):=if ∃ i:V,x∈ C.cap i∧ C.tie i∈S t then F t*Real.exp ((d+1)*coverNumber w (S t)) else 0
   have hX (i:Ballot C S h):0 ≤ q i := by unfold q orbitP; exact mul_nonneg (mul_nonneg hv (pow_nonneg (zero_le_one.trans hg) _)) (he _)
   let c:=v*Real.exp hm; have hc: 0 ≤ c:=mul_nonneg hv (Real.exp_pos _).le
   intro x; let b(i:Ballot C S h):= if x∈ bud C i.2.val (S i.1) then q i * V' (bud C i.2.val (S i.1)) else 0
   have hb(i):0 ≤ b i:=by unfold b; split; exact mul_nonneg (hX _) (Real.exp_pos _).le; exact le_rfl
   have hw:∑ i:Ballot C S h,b i ≤ 2*v*Real.exp hm*u:=by
      have hr(i:I): 0 ≤ a x i:= (hf x).1 i; have ha(i):0 ≤ A x i:=by unfold A; split; exact mul_nonneg (he _) (Real.exp_pos _).le; exact le_rfl
      have H(i:I): ∑ j,b ⟨i,j⟩ ≤ c*(a x i+A x i):=by
         let t:=S i;let z:=coverNumber w t;let m:=(deer C t).card; let r:=F i * Real.exp ((d+1)*z)
         by_cases hh:∃ j: {p:Finset V//p⊆deer C t∧h i p},0<b ⟨i,j⟩; swap
         · rw [sum_eq_zero]; exact mul_nonneg hc (add_nonneg (hr _) (ha _)); intro j _; exact le_antisymm (le_of_not_gt fun H=> hh ⟨_,H⟩) (hb _)
         obtain ⟨j,hj⟩:=hh; have hy: x∈bud C j.val t:= Classical.byContradiction fun h'=> hj.ne' (if_neg h')
         have hf':r≤ a x i+A x i:=by
             by_cases h:x∈t; exact le_trans (le_of_eq (if_pos h).symm) (le_add_of_nonneg_right (ha i))
             obtain ⟨k,hk,H⟩:= mem_biUnion.mp ((mem_union.mp hy).resolve_left h); exact le_trans (le_of_eq (if_pos (show ∃ i:V,x∈C.cap i∧C.tie i∈t from ⟨k,H,(mem_filter.mp (j.property.1 hk)).2⟩)).symm) (le_add_of_nonneg_left (hr _))
         apply le_trans _ (mul_le_mul_of_nonneg_left hf' hc)
         let E:=Real.exp (d*((z:ℝ)+ (k:ℝ)*m)); have he'(j:{p:Finset V// p⊆deer C (S i) ∧ h i p}): V' (bud C j.val (S i))≤ E:=by
             have hh: (coverNumber w (bud C j.val (S i)):ℝ) ≤ (z:ℝ)+(k:ℝ)*(m:ℝ):=by exact_mod_cast (bill_b C _ _ j.property.1 _ _ hz).trans (Nat.add_le_add_left (Nat.mul_le_mul_left k (card_le_card j.property.1)) z)
             exact Real.exp_monotone (mul_le_mul_of_nonneg_left hh hp)
         have hN : Fintype.card {p:Finset V//p⊆deer C (S i) ∧h i p} ≤2^m:= by
             rw [← card_powerset]; let f(p: {p:Finset V//p⊆deer C (S i)∧ h i p}): ↥(deer C (S i)).powerset:=⟨p.val,mem_powerset.mpr p.property.1⟩
             simpa only[Fintype.card_coe] using! Fintype.card_le_of_injective f (fun u v h=>Subtype.ext (show u.val=v.val from congr_arg (fun j:↥(deer C (S i)).powerset=> j.val) h))
         have hB : (2*g*Real.exp (d*(k:ℝ)))^m ≤ Real.exp hm*Real.exp z:=by
             refine (pow_le_pow_left₀ (mul_nonneg (mul_nonneg zero_le_two (zero_le_one.trans hg)) (Real.exp_pos _).le) hZ m).trans ?_
             rw[←Real.exp_nat_mul,←Real.exp_add,Real.exp_le_exp]; by_cases H:m≤1
             · have hz' : (m:ℝ) ≤1:=by exact_mod_cast H
               apply le_trans (mul_le_mul_of_nonneg_right hz' (show (0:ℝ)≤hm by positivity)); rw [one_mul]; exact le_add_of_nonneg_right (by positivity)
             have h'm:m*hm≤ z:= (Nat.mul_comm ..).trans_le (billgap hm hM w hw C.tie (deer C t) (by omega) (fun i _ j _=>ht i j) t (by intro k hk; obtain ⟨u,hu,rfl⟩:=mem_image.mp hk; exact (mem_filter.mp hu).2)); have hv:(m:ℝ)*(hm:ℝ) ≤ z:=by exact_mod_cast h'm
             exact hv.trans (le_add_of_nonneg_left (by positivity))
         calc
           _ ≤ ∑ j,q ⟨i,j⟩* E:=sum_le_sum fun j _=> by unfold b; split; exact mul_le_mul_of_nonneg_left (he' j) (hX _); exact mul_nonneg (hX _) (Real.exp_pos _).le
           _ = (Fintype.card {p:Finset V//p⊆deer C (S i) ∧h i p}:ℝ)*(v*g^m*F i*E):=by simp only[q,orbitP,sum_const,nsmul_eq_mul, Finset.card_univ]; rfl
           _ ≤ (2:ℝ)^m*(v*g^m*F i*E):= mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (mul_nonneg (show 0 ≤ v*g^m*F i from mul_nonneg (mul_nonneg hv (pow_nonneg (zero_le_one.trans hg) _)) (he _)) (Real.exp_pos _).le)
           _ = v*F i*Real.exp (d*z)*( (2*g*Real.exp (d*(k:ℝ)))^m) :=by unfold E; simp_rw [mul_add,Real.exp_add,mul_pow]; rw [← Real.exp_nat_mul,show d*((k:ℝ)*m)=(m:ℝ)*(d*k) from by ring]; ring
           _ ≤ v*F i*Real.exp (d*z)*(Real.exp hm*Real.exp z):=mul_le_mul_of_nonneg_left hB (mul_nonneg (mul_nonneg hv (he _)) (Real.exp_pos _).le)
           _ = _:=by unfold c r; rw [add_mul,Real.exp_add,one_mul]; ring
      have hc : ∑ i,A x i ≤ u:=by
         by_cases hh: ∃ i:V,x∈ C.cap i; swap;· rw [sum_eq_zero]; exact hu; intro i _; exact if_neg (fun h=> hh (by obtain ⟨j,h,-⟩:=h; exact ⟨_,h⟩))
         obtain ⟨j,hj⟩:=hh; refine le_trans (sum_le_sum (g:=a (C.tie j)) (fun i _=> ?_)) (Extra.Multi.Budget.cap (hf _) _)
         unfold A; split
         next hu=> obtain ⟨v,hv,H⟩:= hu; obtain rfl:j=v:= of_not_not fun hz=> disjoint_left.mp (hx (Set.mem_univ _) (Set.mem_univ _) hz) hj hv; exact (if_pos H).symm.le
         exact (hf _).1 i
      have hG:∑ i,a x i ≤ u:= Extra.Multi.Budget.cap (hf x) _; rw [Fintype.sum_sigma]; apply (sum_le_sum fun i _=>H i).trans; rw [← mul_sum,sum_add_distrib]; let U:= add_le_add hG hc; exact (mul_le_mul_of_nonneg_left U (by assumption : 0≤c)).trans_eq (by unfold c; ring)
   exact ⟨hb,Summable.of_finite,by rw [tsum_fintype]; exact hw⟩
end YM.Trace.Cask

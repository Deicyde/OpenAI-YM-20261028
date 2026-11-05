import YM.TraceExtension.Foundation.Dilate
import YM.TraceExtension.Quince.Platt
set_option autoImplicit false
noncomputable section
namespace YM.Trace
open Function Filter Set Lattice Wilson RG Pressure Precision Labels Source Push Local Planned.PrimaryIntegral295 PPX Next Next.Free Next.Foundations WardBin Bid StressFlux
open Extra.Histories
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{d n:ℕ}{F:Frame G d}
section slots
lemma powder (v : Key G→₀ℕ): 2*(Finsupp.weight bidegree v).2 ≤ height v:=by
    rw [weight_slot]; unfold height; rw[Finsupp.weight_apply]; unfold Finsupp.sum; dsimp only; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _=>?_ ; rw [mul_comm]; exact Nat.mul_le_mul_left _ (show 2 ≤ generation i by unfold generation; omega)
lemma nbase (F:Frame G d)(h:d≤5)(i:F.Index)(hp:i≠0)(hG:G.Simple):
    4 ≤ (F.grades i).1 ∧ (F.grades i).1≤5 ∧ (F.grades i).2=2:=by
   let P:= F.basis i
   have hz:(F.basis i).val≠0:=fun h=> F.basis.ne_zero i (Subtype.ext h)
   obtain ⟨v,hv⟩:= (Finset.nonempty_iff_ne_empty.mpr (show P.val.support ≠ ∅ by simpa[P] using hz))
   have hy: Finsupp.weight bidegree v=F.grades i:=(pure_grade _ _).1 (F.pure i) (MvPolynomial.mem_support_iff.mp hv)
   have hh:= congr_arg Prod.fst hy; have hV:=powder v; rw [weight_slot] at hh; change height v=(F.grades i).1 at hh; rw [hh,hy] at hV
   have h₁:= (F.bound i).trans h; have he := F.factors_pos i hp
   suffices hm:(F.grades i).2≠1 by omega
   intro ht; obtain ⟨x,hx,hf,H⟩:= low h P; have he:= Low.linear_invariant hG (Low.covariance hx H)
   apply hz; apply eval_ext; intro J
   have hy : -(read J P.val)= read J P.val:=by
       rw[show -(read J P.val)= read ((-1:ℝ) • J) P.val from ?_,H,H]; swap; · rw [read_pure J (F.pure i),ht]; simp [P]
       simp[Low.eval,he]
   change read J P.val= read J 0; rw [map_zero]; linear_combination -hy/2
end slots
section maps
variable {A: Hol G} {T:SectionData F}{k f c π:ℝ} (h:T.Sound A){i j:ℕ}
lemma eve_cols (P:Flight i j)(hp:0<k)(he:d ≤ i)(ht:4 ≤ j)(hl:Bid.pop T)(hm:d≤5)(hG:G.Simple)(hB:Blend π f c) (v:F.Coeff):
    let V:= Seal.donne T h hp ht hl P he hB
    V.map v = F.scaled (c/f) v:=by
   intro V; have hx(i:F.Index)(hi:i≠0): V.map (Size.axis F i)= ((c/f:ℝ)^((F.grades i).2):ℂ) • Size.axis F i:=by
       ext1 k; by_cases hk:(F.grades k).1 ≤ (F.grades i).1
       · have he := through T h P _ hp ht he f c i k hk
         unfold V; rw[Seal.donne_map]; rw[show (matrix T h _ f c (Size.axis F i) k)= _ from he]; by_cases hz:i=k <;> (first| subst k;simp[Size.axis]|simp[Size.axis,hz,Ne.symm hz])
       have h : F.act archV.ortho (V.map (Size.axis F i))= ((-1:ℂ)^(F.grades i).1) • V.map (Size.axis F i):=by
           rw [← map_smul,← orbit_sign]; exact Eq.symm (V.covariant (Size.axis F i) (archV,false))
       have hv := nbase F hm i hi hG; have hn:(F.grades k).1≤5:=(F.bound k).trans hm
       rw [Pi.smul_apply,show Size.axis F i k=0 from Pi.single_eq_of_ne (show k≠i from fun h=>hk (h ▸ le_rfl)) _,smul_zero]; have he : (-1:ℂ)^((F.grades k).1)* _=_:= (sign_rows F _ k).symm.trans (congr_fun h k); change _*_= (-1:ℂ)^((F.grades i).1)* _ at he; rw [show (F.grades k).1=5 from by omega, show (F.grades i).1=4 from by omega] at he; linear_combination -he/2
   conv=>lhs;rw [← Size.sum_axes F v]
   conv=>rhs;rw [← Size.sum_axes F v]
   rw [map_sum,map_sum]; exact Finset.sum_congr rfl (fun i _=>by
      rw [map_smul,map_smul]; apply congr_arg; by_cases hk:i=0; · subst i; change V.map F.e0=F.scaled _ F.e0; rw [V.unit]; simp
      rw[hx i hk, (show F.scaled (c/f) (Size.axis F i)=_ from PPX.scaled_col (F:=F) (c/f) i)];push_cast; rfl)
lemma eve_actual (P:Flight i j)(hp:0<k)(he:d≤ i)(ht:4 ≤ j)(hl:Bid.pop T)(hm:d≤5)(hG:G.Simple)(hB:Blend π f c)(v:F.Coeff)(x:F.Index)(hx:x≠0):let V:= Seal.donne T h hp ht hl P he hB
   V.leads P.L v x=((c/f:ℝ)^2:ℂ)*(P.L.val:ℂ)^(d-(F.grades x).1)*v x:=by
   intro V; change V.map (vowel F P.L v) x=_
   unfold V; rw [eve_cols h P hp he ht hl hm hG hB, ]; simp[vowel]; simp [nbase F hm x hx hG|>.2.2,mul_assoc]
end maps
end YM.Trace

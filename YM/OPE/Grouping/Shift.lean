import YM.OPE.Grouping.Stator
/-!
# Budget of bringing parents to children's bases

Generalizes `Wings` in the pair proof. In the generalized hit estimate there's a small
parameter cost `1/m` when spreading a passive marker after fusion (`m` upper bound on
children per region). Keep the old full estimate unchanged for a marker of arity zero --
then in `hitB`, that term stays on its support, paying no halo.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J S₀ : Type*}[DecidableEq V][Fintype V][DecidableEq S₀][Fintype S₀]{Δ:Fibers S₀ V}{n:Side}{G:Gauge}{B:Census V}
open Ac Extra.Multi Corona
namespace Salt
variable (Z:Salt V S₀ Δ G n)(w:S₀→ℝ)(α η:ℝ)(k M l:ℕ)
def tow (w:S₀→ℝ)(α η:ℝ)(k:ℕ)(i:S₀):= η*w i/ Real.exp (α*k)
lemma towP (hw:∀ i,0<w i)(hp:0<η) i:0<tow w α η k i:= by unfold tow; exact div_pos (mul_pos hp (hw _)) (Real.exp_pos _)
variable (Q:I→ (Bud S₀).Mode)(X:I→Support n)
variable (he:∀ i,(Q i).val.image Z.grain ⊆ X i)(hh:∀ i:S₀, coverNumber M ({Z.focus (Δ.bunch i),Z.grain i}:Support n)≤ k)
local notation "S"=> fun i=>Z.kiln (X i) (Q i)
include he hh
lemma attends (i:I): coverNumber M (Z.kiln (X i) (Q i)) ≤ coverNumber M (X i)+ k*(Q i).val.card:=by
   let p:= (Q i).val; let r (q:Finset S₀):=X i∪ q.image (Z.focus ∘ Δ.bunch)
   have hp(t : Finset S₀)(ht:t⊆p): coverNumber M (r t) ≤ coverNumber M (X i) + k*t.card:=by
     induction t using Finset.induction with
     | empty=> simp [r]
     | insert a b hb ih=>
       have ho : Z.grain a∈X i:= he i (mem_image_of_mem _ (ht (mem_insert_self ..)))
       specialize ih ((subset_insert _ _).trans ht); rw [Finset.card_insert_of_notMem hb,Nat.mul_add,Nat.mul_one,← Nat.add_assoc]
       have h' : r (insert a b)= r b∪ {Z.focus (Δ.bunch a),Z.grain a}:= by
         ext; simp only [r,mem_union,image_insert,comp_apply,mem_insert,mem_singleton]; grind
       have hl: Z.grain a∈ r b:=mem_union_left _ ho
       rw [h']; exact (Corona.meets_sum hl (mem_insert_of_mem (mem_singleton_self _)) M).trans (Nat.add_le_add ih (hh a))
   unfold kiln Fibers.span; rw [image_image]; exact hp _ Finset.Subset.rfl
lemma levels (h:0 ≤ α)(hu:0<η)(hU:η ≤ 1)(hw:∀ i,0<w i)(i:I):
    Real.exp (α*coverNumber M (Z.kiln (X i) (Q i)))*Poly.toll (tow w α η k) (Q i) ≤ η^(Q i).val.card * (Real.exp (α*coverNumber M (X i))*Poly.toll w (Q i)):=by
    let z:=Q i; let j:=z.val.card; let H:=Real.exp (α*k); have hx:0<H^j:=pow_pos (Real.exp_pos _) _
    have he := Z.attends k M Q X he hh i
    have hz : Poly.toll (tow w α η k) z=η^j*Poly.toll w z/H^j:=by simp only [Poly.toll,tow,prod_div_distrib,prod_mul_distrib,prod_const]; rfl
    have hl : Real.exp (α*coverNumber M (Z.kiln (X i) z)) ≤ Real.exp (α*coverNumber M (X i))*H^j := by
       unfold H; rw [← Real.exp_nat_mul,← Real.exp_add]; apply Real.exp_monotone; have hi : (coverNumber M (Z.kiln (X i) z):ℝ) ≤ coverNumber M (X i)+ k*j:=by exact_mod_cast he
       nlinarith only [mul_le_mul_of_nonneg_left hi h]
    calc _ ≤ (Real.exp (α*coverNumber M (X i))*H^j)*Poly.toll (tow w α η k) z:= mul_le_mul_of_nonneg_right hl (Poly.worth (towP w α η k hw hu) z).le
         _ = _:=by rw [hz]; field_simp; rfl
omit hh
variable [Fintype I]
/-- When accounting for many slots with the same new name, the enlargement needs a
cost for *each* possible old location. Use a smaller relative budget in each non-quiet
expanded entry. This lets us spend the same uniform money already purchased for group
birth on the first (unsplit) construction. -/
lemma hitB (h:Occupancy Z.focus l)(F W:I→ℝ)(a g : ℝ)(hx: ∀ i,0 ≤ W i)(hp:0 ≤ a)(hg:0 ≤ g)(hr:Hit X M F α g)
    (m : ℕ) (hm : 0 < m) (hk : ∀ v : V,(Δ.contents v).card ≤ m)
    (hv:∀ i, W i*Real.exp (α*coverNumber M (Z.kiln (X i) (Q i))) ≤ a*(F i*Real.exp (α*coverNumber M (X i))))
    (hy:∀ i, (Q i).val.Nonempty → W i*Real.exp (α*coverNumber M (Z.kiln (X i) (Q i))) ≤
      a/m*(F i*Real.exp (α*coverNumber M (X i)))) : Hit (fun i=>Z.kiln (X i) (Q i)) M W α ((1+l)*a*g):=by
   intro y; let p:= univ.filter (fun j=> Z.focus j=y)
   let w x i:= if x∈X i then F i*Real.exp (α*coverNumber M (X i)) else 0
   let s i:= a*w y i
   let v (j:S₀) i:= a/m*w (Z.grain j) i
   let u (j:V) (i:I) := ∑ x∈Δ.contents j,v x i
   let T i:= s i+∑ j∈p,u j i
   have hA j i :0 ≤ w j i:=(hr j).1 i
   have hB j i :0 ≤ v j i:= mul_nonneg (by positivity) (hA ..)
   have hC j i :0 ≤ u j i:= sum_nonneg fun j _=>hB j _
   have hD i :0 ≤ T i:= add_nonneg (mul_nonneg hp (hA ..)) (sum_nonneg fun _ _=>hC ..)
   refine ⟨fun i=> by dsimp only; split; exact mul_nonneg (hx _) (Real.exp_pos _).le; exact le_rfl,Summable.of_finite,?_⟩; rw [tsum_fintype]
   trans ∑ i, T i
   · refine sum_le_sum fun i _=>?_ ; dsimp only; split; swap; exact hD i
     next hu=>
     by_cases hI:y∈X i
     · unfold T s; refine le_trans ?_ (le_add_of_nonneg_right (sum_nonneg fun j _=> hC ..)); unfold w; rw [if_pos hI]; exact hv i
     obtain ⟨j,hj,H⟩:=mem_image.mp ((mem_union.mp hu).resolve_left hI); have hy': j∈p:=mem_filter.mpr ⟨mem_univ _,H⟩; obtain ⟨c,hc,hc'⟩:= (Δ.spans (Q i) _).mp hj; have hM:= he i (mem_image_of_mem _ hc')
     unfold T; calc
       _ ≤ v c i := by unfold v w; rw [if_pos hM]; exact hy i ⟨c,hc'⟩
       _ ≤ u j i := single_le_sum (fun j _=> hB j i) hc
       _ ≤ ∑ j∈p,u j i:= single_le_sum (fun j _=> hC j i) hy'
       _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hp (hA ..))
   unfold T; rw [sum_add_distrib,sum_comm (f:=fun i j=> u j i)]
   have hc x : ∑ i:I,w x i ≤ g:= Budget.cap (hr x) _
   have hW(j:V): ∑ i,u j i ≤ a*g := by
     unfold u; rw [sum_comm]
     calc _ ≤ ∑ _x∈Δ.contents j,a/m*g := sum_le_sum fun x _=>by unfold v; rw [← mul_sum]; gcongr; exact hc _
          _ ≤ (m:ℝ)*(a/m*g) :=by rw [sum_const,nsmul_eq_mul]; gcongr; exact hk _
          _ = _ := by field_simp
   calc
     _ ≤ a*g + ∑ _j∈p,a*g := add_le_add (by unfold s; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hc y) hp)
       (sum_le_sum (fun j _=> hW j))
     _ ≤ _ := by
       simp only [sum_const,nsmul_eq_mul]; have hy: (p.card:ℝ) ≤ l:= by exact_mod_cast h y
       nlinarith only [mul_le_mul_of_nonneg_right hy (mul_nonneg hp hg)]
end Salt
end YM.MergeProof.Ribbons.Fibers

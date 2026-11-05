import YM.MergeProof.North.Stator
import YM.MultipleContact.Bunch.Focal
import YM.MultipleContact.Bunch.Dew
import YM.MultipleContact.Bunch.Gush
import YM.MultipleContact.Bunch.Sugary
import YM.MultipleContact.Bunch.Stained
import YM.MultipleContact.Bunch.Stator

/- generalized from YM.MergeProof.North.Wings to arbitrary arity -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Finset Function Marker Extra.Trajectories Accent BatchRibbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
open Ac Extra.Multi Corona
namespace Salt
variable (Z:Salt V slot G n)(w:Name V slot→ℝ)(α η:ℝ)(k M l:ℕ)
def tow (w:Name V slot→ℝ)(α η:ℝ)(k:ℕ)(i:Name V slot):= η*w i/ Real.exp (α*k)
lemma towP (hw:∀ i,0<w i)(hp:0<η) i:0<tow w α η k i:= by unfold tow; exact div_pos (mul_pos hp (hw _)) (Real.exp_pos _)
variable (Q:I→ (Aged V slot).Mode)(X:I→Support n)
variable (he:∀ i,(Q i).val.image Z.grain ⊆ X i)(hh:∀ i:V, coverNumber M (Finset.univ.image fun s:slot=>Z.grain (i,s))≤ k)
local notation "S"=> fun i=>Z.kiln (X i) (Q i)
include he hh
lemma attends (i:I): coverNumber M (Z.kiln (X i) (Q i)) ≤ coverNumber M (X i)+ k*(Q i).val.card:=by
   let p:= (Q i).val; let r (q:Finset (Name V slot)):=X i∪ q.image (Z.focus ∘ Prod.fst)
   have hp(t : Finset (Name V slot))(ht:t⊆p): coverNumber M (r t) ≤ coverNumber M (X i) + k*t.card:=by
     induction t using Finset.induction with
     | empty=> simp [r]
     | insert a b hb ih=>
       have ho : Z.grain a∈X i:= he i (mem_image_of_mem _ (ht (mem_insert_self ..))); rcases a with ⟨v,c⟩; specialize ih ((subset_insert _ _).trans ht); rw [Finset.card_insert_of_notMem hb,Nat.mul_add,Nat.mul_one,← Nat.add_assoc]
       let e:=Finset.univ.image fun s:slot=>Z.grain (v,s)
       have h' : r (insert (v,c) b) ⊆ r b∪ e:= by
         unfold r; rw [image_insert]; apply union_subset (subset_union_left.trans subset_union_left)
         exact (Finset.insert_subset_iff).mpr ⟨mem_union_right _ (mem_image_of_mem _ (mem_univ (default:slot))),subset_union_right.trans subset_union_left⟩
       exact (cover_mono h' M).trans ((Corona.meets_sum (mem_union_left _ ho :Z.grain (v,c) ∈ r b)
           (mem_image_of_mem _ (mem_univ c): Z.grain (v,c)∈e) M).trans (Nat.add_le_add ih (hh v)))
   unfold kiln BatchRibbon.span; rw [image_image]; exact hp _ Finset.Subset.rfl
lemma levels (h:0 ≤ α)(hu:0<η)(hU:η ≤ 1)(hw:∀ i,0<w i)(i:I):
    Real.exp (α*coverNumber M (Z.kiln (X i) (Q i)))*Poly.toll (tow w α η k) (Q i) ≤ η^(Q i).val.card * (Real.exp (α*coverNumber M (X i))*Poly.toll w (Q i)):=by
    let z:=Q i; let j:=z.val.card; let H:=Real.exp (α*k); have hx:0<H^j:=pow_pos (Real.exp_pos _) _
    have he := Z.attends k M Q X he hh i
    have hz : Poly.toll (tow w α η k) z=η^j*Poly.toll w z/H^j:=by simp only [Poly.toll,tow,prod_div_distrib,prod_mul_distrib,prod_const]; rfl
    have hl : Real.exp (α*coverNumber M (Z.kiln (X i) z)) ≤ Real.exp (α*coverNumber M (X i))*H^j := by
       unfold H; rw [← Real.exp_nat_mul,← Real.exp_add]; apply Real.exp_monotone; have hi : (coverNumber M (Z.kiln (X i) z):ℝ) ≤ coverNumber M (X i)+ k*j:=by exact_mod_cast he
       nlinarith only [mul_le_mul_of_nonneg_left hi h]
    calc
       _ ≤ (Real.exp (α*coverNumber M (X i))*H^j)*Poly.toll (tow w α η k) z:= mul_le_mul_of_nonneg_right hl (Poly.worth (towP w α η k hw hu) z).le
       _ = _:=by rw [hz]; field_simp; rfl
omit hh
variable [Fintype I]
-- direct neighbor hit by old from roster. no slack in exponent. µ controls focuses only.
lemma hitSeparable (h:Occupancy Z.focus l)(F W:I→ℝ)(a a₁ g : ℝ)(hx: ∀ i,0 ≤ W i)(hp : 0 ≤ a)(hp₁:0 ≤ a₁)(hg:0 ≤ g)(hr:Hit X M F α g)(hv:∀ i, W i*Real.exp (α*coverNumber M (Z.kiln (X i) (Q i))) ≤ a*(F i*Real.exp (α*coverNumber M (X i)))) (hv₁:∀ i,(Q i).val.Nonempty→W i*Real.exp (α*coverNumber M (Z.kiln (X i) (Q i))) ≤ a₁*(F i*Real.exp (α*coverNumber M (X i)))) : Hit (fun i=>Z.kiln (X i) (Q i)) M W α (a*g+l*Fintype.card slot*a₁*g):=by
   intro y; let p:= univ.filter (fun i=> Z.focus i=y)
   let w x i:= if x∈X i then F i*Real.exp (α*coverNumber M (X i)) else 0
   let b i:= a*w y i; let B i:= b i+∑ j∈p,∑ s:slot,a₁*w (Z.grain (j,s)) i
   have hA j i :0 ≤ w j i:=(hr j).1 i
   have hB i :0 ≤ B i:= add_nonneg (mul_nonneg hp (hA ..)) (sum_nonneg fun _ _=>sum_nonneg fun _ _=>mul_nonneg hp₁ (hA ..))
   refine ⟨fun i=> by dsimp only; split; exact mul_nonneg (hx _) (Real.exp_pos _).le; exact le_rfl,Summable.of_finite,?_⟩; rw [tsum_fintype]
   trans ∑ i, B i
   · refine sum_le_sum fun i _=>?_ ; dsimp only; split; swap; exact hB i
     next hu=>
     by_cases hy:y∈X i
     · unfold B b; refine le_trans ?_ (le_add_of_nonneg_right (sum_nonneg fun j _=>sum_nonneg fun _ _=> mul_nonneg hp₁ (hA ..))); unfold w; rw [if_pos hy]; exact hv i -- API maybe argument wrong
     have hL:= (mem_union.mp hu).resolve_left hy; obtain ⟨j,hj,H⟩:=mem_image.mp hL; have hy': j∈p:=mem_filter.mpr ⟨mem_univ _,H⟩; obtain ⟨c,hc⟩:= (spans (Q i) _).mp hj; have hM:= he i (mem_image_of_mem _ hc)
     refine (hv₁ i ⟨_,hc⟩).trans ?_
     have B1:=single_le_sum (f:=fun s=>a₁*w (Z.grain (j,s)) i) (fun _ _=>mul_nonneg hp₁ (hA ..)) (mem_univ c)
     unfold B
     refine (le_trans ?_ (le_trans B1 (single_le_sum (f:=fun j=> ∑ s:slot,a₁*w (Z.grain (j,s)) i) ?_ hy'))).trans (le_add_of_nonneg_left (mul_nonneg hp (hA ..)))
     unfold w; exact (congr_arg (a₁*·) (if_pos hM)).symm.le; exact fun j _=>sum_nonneg fun _ _=>mul_nonneg hp₁ (hA ..)
   unfold B b; rw [sum_add_distrib,sum_comm (f:=fun i j=> ∑ s:slot,a₁*w (Z.grain (j,s)) i)] -- check
   have hc x : ∑ i:I,a*w x i ≤ a*g:=by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (Budget.cap (hr x) _) hp
   have hc₁ x : ∑ i:I,a₁*w x i ≤ a₁*g:=by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (Budget.cap (hr x) _) hp₁
   have hv0 j : ∑ i:I,∑ s:slot,a₁*w (Z.grain (j,s)) i ≤ ∑ _s:slot,a₁*g:=by
      rw [sum_comm]; exact sum_le_sum fun s _=>hc₁ (Z.grain (j,s))
   refine (add_le_add (hc y) (sum_le_sum fun j _=>hv0 _)).trans ?_
   simp only [sum_const,nsmul_eq_mul]
   have hy: (p.card:ℝ) ≤ l:= by exact_mod_cast h y
   rw [Finset.card_univ]
   nlinarith only [mul_le_mul_of_nonneg_right hy (mul_nonneg (mul_nonneg hp₁ hg) (Nat.cast_nonneg (Fintype.card slot)))]
end Salt
end YM.MergeProof.BatchRibbons

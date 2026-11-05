import YM.RG08.Forms.PontChange
import YM.Corona.Fill
import YM.Next.FREE_KERNELS.Bank
import YM.Laurent.Art

/-!
# Removing the bulk periodic box at a fixed step. Unit coordinates (may use packed cell for I).
This chapter uses uniform dominating sums, not an assertion of exact periodization through closed
cycles.
-/
noncomputable section
namespace YM.RG08.Isles
open Forms Pert.Bulk Packets Laurent Finset Function Lattice Filter
open scoped Topology BigOperators ENNReal Classical
set_option autoImplicit false
variable {I : Type} {P:Side}{σ p : ℝ}

/-- Fixed cofinal test tail, no quotient, sufficient to infer coefficient Ward identities.
-/
def chain (i:ℕ):Side:=⟨i+1,by omega⟩
lemma rise:Tendsto (fun i=>(chain i).val) atTop atTop:=by rw [tendsto_atTop_atTop];intro b;exact ⟨b,fun i hi=>by change b ≤ i+1;omega⟩

abbrev Cove (P:Side)(I:Type):=Site P × I

def port (P:Side)(x:Market I):Cove P I:=(wrap P x.1,x.2)
def reach (x:Cove P I):Market I:=(lift x.1,x.2)

@[simp] lemma reaches (x:Cove P I):port P (reach x)=x:=by simp [reach,port]
lemma contacts (x:Market I):∀ᶠ i:ℕ in atTop,reach (port (chain i) x)=x:=by
 filter_upwards [Next.Free.eventually_unfold chain rise x.1] with i hi; simp [reach,port,hi]
lemma reaches_inj : Injective (reach (P:=P) (I:=I)):= LeftInverse.injective (g:=port P) reaches

def walk (x y: Site P):= (Laurent.size (lift (x-y)):ℝ)
def shore (P:Side)(I:Type) : Ground (Cove P I) where
 span x y:= walk x.1 y.1
 stay _:=by simp [walk,Laurent.size,lift]
 left x y:=by
   unfold walk Laurent.size
   congr 1
   apply Finset.sum_congr rfl
   intro i _
   change (ZMod.valMinAbs (x.1 i - y.1 i)).natAbs = (ZMod.valMinAbs (y.1 i - x.1 i)).natAbs
   rw [← neg_sub (y.1 i) (x.1 i), ZMod.natAbs_valMinAbs_neg]
 slope x y z:=by
    unfold walk Laurent.size;push_cast;rw [show x.1-z.1=(x.1-y.1)+(y.1-z.1) from by abel,←Finset.sum_add_distrib];apply sum_le_sum;intro i _;exact_mod_cast (ZMod.natAbs_valMinAbs_add_le ((x.1-y.1) i) ((y.1-z.1) i)).trans (Int.natAbs_add_le ..)

lemma walk_wrap (x y:Cover) : walk (wrap P x) (wrap P y) ≤ sep x y:=by
 unfold walk sep length Laurent.size;push_cast;rw [←map_sub];apply sum_le_sum;intro i _
 exact_mod_cast Lattice.Corona.lap (x-y) i

def native (x:Cove P I):=length (lift x.1)
def abroad (x:Market I):=length x.1
lemma native_nn (x:Cove P I):0≤native x:=by unfold native length; positivity
lemma abroad_nn (x:Market I):0≤abroad x:=by unfold abroad length; positivity
lemma here (z:Cove P I):abroad (reach z)=native z:=rfl
lemma native_port (x:Market I):native (port P x)≤abroad x:=by simpa only [native,port,abroad,walk,sep,map_zero,sub_zero] using (walk_wrap (P:=P) x.1 0)
lemma region (x y:Cove P I):native x≤ (shore P I).span x y+native y:=by
 simpa only [native, length, shore, walk, sub_zero] using
   (shore P I).slope x y ((0, y.2) : Cove P I)

variable [Fintype I]
def weightU (σ:ℝ)(x:Market I):=Real.exp (-σ*abroad x)
lemma weightU_sum (hs:0<σ):Summable (weightU σ:Market I→ℝ):=by
 refine (summable_prod_of_nonneg (fun x=>show 0≤weightU σ (x:Market I) from (Real.exp_pos _).le)).mpr ?_
 refine ⟨fun _=>Summable.of_finite,?_⟩
 simp_rw [tsum_fintype,weightU,abroad,length,sum_const,card_univ,nsmul_eq_mul]
 exact ((Width.compactPay σ hs).2.1).mul_left _

lemma weightU_twice (hs:0<σ):Summable (fun x:Market I × Market I=> weightU σ x.1 * weightU σ x.2):=by
 have hn (x:Market I):0≤weightU σ x:=(Real.exp_pos _).le
 refine (summable_prod_of_nonneg (f:=fun x:Market I×Market I=>weightU σ x.1*weightU σ x.2) (fun x=>mul_nonneg (hn x.1) (hn x.2))).mpr ?_
 refine ⟨fun (x:Market I)=>(weightU_sum (I:=I) hs).mul_left (weightU σ x),?_⟩
 simp_rw [tsum_mul_left];exact (weightU_sum (I:=I) hs).mul_right _

end YM.RG08.Isles

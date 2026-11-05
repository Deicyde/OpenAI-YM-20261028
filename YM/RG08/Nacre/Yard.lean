import YM.RG08.Nacre.Flight

/-! # Triangular transfer of all packets crossing one coupling. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Nacre
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Packets Mount Glyph Room Bloch Quarry Aggregate Steam Spar Symmetry Roost Sedan
open PowerSeries Finset.Nat
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}{r e n k:ℕ}

def square (n:ℕ):= range (n+1)
@[simp] lemma in_square (i n:ℕ) : i∈square n ↔ i ≤ n:=by simp [square]

def fraction (w:ℕ→ℝ)(V:Scroll G):Scroll G:=fun e k=>∑ i∈square e,dues w i k e • V i k

def size (w:ℕ→ℝ)(V:Castle G):Castle G:=fun r e=>∑ i∈square e,dues w i (Mount.rank r) e • V r i
lemma sizeable (w:ℕ→ℝ)(h:prudent w)(V:Castle G)(hv:Fair V): Fair (size w V):=by
 refine ⟨fun r e he=>?_,fun r e=>(completed_galaxy (r:=r) _ _ _ (fun i _=>hv.honor r i) 1 (0:Fin 1)).1⟩
 apply Finset.sum_eq_zero; intro i hi
 by_cases H: Live r i
 · by_cases hx:dues w i (Mount.rank r) e=0; rw [hx,zero_smul]
   obtain ⟨hN,j,hj⟩:=due_even h _ _ _ hx;obtain ⟨hr,t,ht⟩:=H;exact (he ⟨by omega,t+j,by omega⟩).elim
 rw [hv.rests r i H,smul_zero]

private def glitter {X:Type}[AddCommGroup X][Module ℝ X](r i e k:ℕ)(x:X):X:= if i ≤ e ∧ k=e-i+Mount.rank r then x else 0
private abbrev gbed (X:Type)[AddCommGroup X][Module ℝ X] := ℕ→ℕ→X
def globule (F:Castle G)(k:ℕ):gbed (Flake k (Market (Loc G 1))):=fun r i=>completed (F r i) (stick r) k

lemma rim (F:Castle G)(ht:Fair F){i n:ℕ}(he:i ≤ n)(k:ℕ):
 demand F i k=∑ a∈square n,∑ r∈square n,glitter r a i k (globule F k r a):=by
 unfold demand
 have hx (i r a): glitter (X:=Flake k (Market (Loc G 1))) r a i k (globule F k r a)=Mount.flight r a (F r a) i k:=by unfold glitter Mount.flight; split_ifs <;> first | rfl | omega
 simp_rw [hx]
 rw [←Finset.sum_subset (s₁:=square i) (fun q h=>in_square _ _|>.mpr ((in_square _ _|>.mp h).trans he) : square i⊆ square n) (f:=fun a:ℕ=>∑ r∈square n,Mount.flight r a (F r a) i k) (by
   intro j _ hj; unfold Mount.flight;apply Finset.sum_eq_zero;intro r _;rw [if_neg (by simp only [in_square] at hj;omega)])]
 refine Finset.sum_congr rfl fun p hp=>Finset.sum_subset (fun q h=> in_square _ _|>.mpr ((in_square _ _|>.mp h).trans (show p ≤ n from (in_square _ _|>.mp hp).trans he)) : square p⊆ square n) (fun r _ hr=>?_) -- hp in range
 rw [ht.rests r p (by unfold Live; change r∉square p at hr;simp only [in_square] at hr;omega),flight_nil]

-- core identity coefficient-by-coefficient, commuting generator and grade-shift. finite square e.
lemma commute {X:Type}[AddCommGroup X][Module ℝ X](w:ℕ→ℝ)(W:gbed X)(n k:ℕ):
 (∑ a∈square n,∑ r∈square n,glitter (X:=X) r a n k (∑ i∈square a,dues w i (Mount.rank r) a • W r i))
 =∑ i∈square n,dues w i k n • (∑ a∈square n,∑ r∈square n,glitter (X:=X) r a i k (W r a)):=by
 -- both rebase outer a before vs i current by selecting unique inRange selector. extend all to square n
 let S:=square n
 have hg(a r)(ha:a∈square n):glitter r a n k (∑ i∈square a,dues w i (Mount.rank r) a • W r i)= ∑ i∈S,dues w i (Mount.rank r) a • glitter r a n k (W r i):=by
    unfold glitter; split_ifs with h
    · refine Finset.sum_subset (fun i hi=>in_square _ _|>.mpr ((in_square _ _|>.mp hi).trans (in_square _ _|>.mp ha)) : square a ⊆ S) (fun i _ hi=>by rw [dues,if_neg (by simpa using hi),zero_smul])
    simp
 rw [show _ = (∑ a∈S,∑ r∈S, ∑ i∈S, dues w i (Mount.rank r) a • glitter r a n k (W r i)) from Finset.sum_congr rfl fun a ha=>Finset.sum_congr rfl fun r _=>hg a r ha]
 conv_lhs=>rw [Finset.sum_comm]; arg 2; ext r;rw [Finset.sum_comm]
 conv_rhs=>simp only [Finset.smul_sum];arg 2; ext i;rw [Finset.sum_comm]
 rw [show (∑ i∈_,∑ r∈_, ∑ a∈_,dues w i k n • glitter r a i k (W r a)) = ∑ r∈S,∑ a∈S,∑ i∈S,dues w i k n • glitter r a i k (W r a) from ?_]
 swap
 · rw [Finset.sum_comm]; exact sum_congr rfl fun x _=>Finset.sum_comm
 apply Finset.sum_congr rfl
 intro q _
 apply Finset.sum_congr rfl
 intro r _
 by_cases hk : Mount.rank q ≤ k
 swap
 · have hz (t m : ℕ) : glitter q t m k (W q r) = 0 := if_neg (by omega)
   simp only [hz, smul_zero, sum_const_zero]
 obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hk
 by_cases hh:r+d ≤ n
 · rw [Finset.sum_eq_single_of_mem (n-d) (in_square _ _|>.mpr (Nat.sub_le _ _)) (fun b hb hb' =>?_)]
   swap
   · have he:=in_square _ _|>.mp hb;rw [glitter,if_neg (by omega),smul_zero]
   symm
   rw [Finset.sum_eq_single_of_mem (r+d) (in_square _ _|>.mpr hh) (fun i _ hi=>by rw [glitter,if_neg (by omega),smul_zero]),glitter,glitter,if_pos (by omega),if_pos (by omega)]
   apply congrArg (· • W q r)
   unfold dues
   rw [if_pos hh,if_pos (by omega),show n-(r+d)=n-d-r by omega];apply congrArg
   unfold shift;rw [pow_add,pow_add]
   have hv:ratio w ^d * (ratio w)⁻¹ ^d=1:=by rw [←mul_pow,reciprocity,one_pow]
   calc
   _ = ratio w^r*((ratio w)⁻¹)^ (Mount.rank q) * (ratio w ^d * (ratio w)⁻¹ ^d):=by ring
   _ = _:=by rw [hv,mul_one]
 have hleft : (∑ i ∈ S, dues w r (Mount.rank q) i •
     glitter q i n (Mount.rank q + d) (W q r)) = 0 := by
   apply Finset.sum_eq_zero
   intro i hi
   have hin : i ≤ n := (in_square i n).mp hi
   by_cases hri : r ≤ i
   · rw [glitter, if_neg (by omega), smul_zero]
   · rw [dues, if_neg hri, zero_smul]
 have hright : (∑ i ∈ S, dues w i (Mount.rank q + d) n •
     glitter q r i (Mount.rank q + d) (W q r)) = 0 := by
   apply Finset.sum_eq_zero
   intro i hi
   have hin : i ≤ n := (in_square i n).mp hi
   rw [glitter, if_neg (by omega), smul_zero]
 exact hleft.trans hright.symm

lemma sailed (w:ℕ→ℝ)(h:prudent w)(A:Castle G)(hA:Fair A)(e k:ℕ)(hk:0<k):
    demand (Nacre.size w A) e k = fraction w (demand A) e k:=by
 let j:Fin k:=⟨0,hk⟩
 unfold fraction;rw [rim _ (sizeable w h A hA) (le_refl e)]
 have ht (i r): globule (Nacre.size w A) k r i=∑ n∈square i,dues w n (Mount.rank r) i • (globule A k r n):=(completed_galaxy _ _ _ (fun n _=>hA.honor r n) _ j).2
 simp_rw [ht];rw [commute];apply Finset.sum_congr rfl;intro i hi; rw [rim _ hA (in_square _ _|>.mp hi) k]
end YM.RG08.Nacre

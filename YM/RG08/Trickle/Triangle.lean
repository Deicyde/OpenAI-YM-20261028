import YM.RG08.Glyph.Tempo
import YM.RG08.Skiff.Shed

/-! # Differential of the finite log graph. Degree-count independent
of stencil algebras. PEER order bound `n ≤ l+a` supersedes positive-degree
rank roof `≤a+2`. This section never drops scalars (`Fintype I` where needed).
No parity required on marked fields or tags.
-/
noncomputable section
namespace YM.RG08.Trickle
open Function Finset Jetty Skiff Forms Steam MvPolynomial Glyph Cloud
open scoped BigOperators Topology Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I J R:Type}{p q n j k e l m:ℕ}{Γ:Line I}{S:GrainS I}{V:Steam.Grain I}

def brook (f:Pearl)(S:GrainS I):Steam.Grain I:=fun e n=>during f (S e n)
lemma dry(r:ℕ)(hv:Lit l S)(hl:l+e<r)(f:Pearl):brook f S e r=0:=by
 have he: S e r=0:= Classical.not_not.mp fun h=> by have:=hv _ _ h;omega
 unfold brook;rw [he];rfl
lemma drink(he:Lit l S)(hv:Eligible V){Γ:Line I}:Lit l (skate Γ V S j):=fun _ _ h=>(full he hv h).2

lemma during_sum {P:R→Pack n I}(s:Finset R)(f:Pearl):during f (∑ i∈s,P i)=∑ i∈s,during f (P i):=by ext; simp [during,Finset.sum_apply]
lemma during_add(P Q:Pack n I)(f:Pearl):during f (P+Q)=during f P+during f Q:=rfl
lemma during_smul(x:ℝ)(P:Pack n I)(f:Pearl):during f (x • P)=x • during f P:=rfl

lemma rowing (P:Trips I)(V:Steam.Grain I)(j e n:ℕ)(f:Pearl) :
 during f (rungs Γ V P j e n)= unilateral Γ (brook f (P j)) e n+
    ∑ c∈range (n+1),∑ i∈range (j+1),∑ a∈range (e+1),(2:ℝ) • Steam.pair Γ (brook f (P i) a (c+1)) (burn Γ V (j-i) (e-a) (n-c+1)) n:=by
 unfold rungs
 rw [during_add];congr 1
 · unfold shim unilateral;rw [during_smul,clocked]; rfl
 simp_rw [during_sum]
 apply sum_congr rfl;intro c _;apply sum_congr rfl;intro i _; apply sum_congr rfl;intro a _
 unfold Skiff.shift Steam.pair
 split_ifs with he
 · rw [during_smul,smul_smul]; congr 1; ring
   have he2 {p q:ℕ}(h:p=q)(P:Pack p I):during f (ship h P)=move h (during f P):=by subst h;rfl
   rw [he2,reel_stamp];rfl
 · change (0:Flake _ I)=(2:ℝ) • 0; rw [smul_zero]

lemma rushing (Γ:Line I)(V:Steam.Grain I)(P:GrainS I)(j e n:ℕ)(f:Pearl):
 brook f (skate Γ V P (j+1)) e n=((j+1:ℝ)⁻¹) • (unilateral Γ (brook f (skate Γ V P j)) e n+
    ∑ c∈range (n+1),∑ i∈range (j+1),∑ a∈range (e+1),(2:ℝ) • Steam.pair Γ (brook f (skate Γ V P i) a (c+1)) (burn Γ V (j-i) (e-a) (n-c+1)) n):=by change during f _=_;rw [climbs,during_smul, rowing]

def Combed (P:GrainS I):Prop:=∀ f:Pearl,waxed (brook f P)
theorem comb (Γ:Forms.Line I)(V:Steam.Grain I)(h:Combed S)(j:ℕ):Combed (skate Γ V S j):=fun f e n=>by
 cases j with
 | zero=> rw [Skiff.start];exact h f e n
 | succ j=>
   have he2 {R:Type}(s:Finset R)(f:R→Flake n I)(h:∀ i, Forms.Sym (f i)):Forms.Sym (s.sum f):=by
     induction s using Finset.induction_on with
     | empty=> exact Forms.Sym.zero
     | @insert i t hi ih=> rw [Finset.sum_insert hi];exact (h i).add ih
   rw [rushing];apply Forms.Sym.smul;apply Forms.Sym.add
   · exact Forms.Sym.smul (symmetric _) _
   apply he2; intro c;apply he2;intro u;apply he2;intro a;apply Forms.Sym.smul; unfold Steam.pair
   split_ifs; exact Forms.Sym.smul (sym_move _ _ (symmetric _)) _
   exact Forms.Sym.zero

/-- Triangle↔rectangular reindex with a variable terminal diagonal; don't pad by positive
coupling unless polynomial was proven to have the corresponding rank roof. -/
theorem curve [AddCommMonoid R](T:ℕ→ℕ→R)(N B C:ℕ)(hBN:B≤N)(hCN:C≤N)
    (h1:∀ i j,B< i ∨ C< j ∨ N< i+j→T i j=0):
 (∑ n∈range (N+1),∑ i∈range (n+1),T i (n-i))=(∑ i∈range (B+1),∑ j∈range (C+1),T i j):=by
 -- Huge coincidence with finite-cap vacuum proof; use Nat antidiagonal raw or rectangular
 let s:=range (N+1)
 let A:=fun n i j=> if n=i+j then T i j else 0
 have he (n:ℕ)(hn:n≤N):∑ i∈range (n+1), T i (n-i)=∑ i∈s,∑ j∈s,A n i j:=by
    apply Eq.trans ?_ (Finset.sum_subset (range_mono (by omega:n+1≤N+1)) ?_)
    · apply sum_congr rfl;intro i hi
      simp only [mem_range] at hi
      rw [Finset.sum_eq_single_of_mem (n-i) (s:=s) (by simp [s];omega)]
      · exact (if_pos (by omega:n=i+(n-i))).symm
      intro k _ hk;exact if_neg (by omega)
    intro i _ hj; apply sum_eq_zero;intro k _;apply if_neg;simp only [mem_range] at hj;omega
 calc
 _ = ∑ n∈s,∑ i∈s,∑ j∈s,A n i j:=sum_congr rfl fun n hn=>he n (by simpa [s] using hn)
 _ = ∑ i∈s,∑ j∈s,∑ n∈s,A n i j:=by rw [Finset.sum_comm];apply sum_congr rfl;intro j _; exact Finset.sum_comm
 _ = ∑ i∈s,∑ j∈s,T i j:=by
      apply sum_congr rfl;intro i _;apply sum_congr rfl;intro j _
      by_cases hh:i+j≤N
      · rw [sum_eq_single_of_mem (i+j) (by simp [s,hh]) (fun a _ ha=>if_neg ha)];exact if_pos rfl
      rw [h1 i j (Or.inr (Or.inr (by omega)))];apply sum_eq_zero;intro n _;simp [A,h1 i j (Or.inr (Or.inr (by omega)))]
 _ = _:= Eq.symm <| calc
        _ = ∑ i∈range (B+1),∑ j∈s,T i j:=sum_congr rfl fun i _=>sum_subset (range_mono (by omega:C+1≤N+1)) fun j _ hj=>h1 i j (Or.inr (Or.inl (by simp only [mem_range] at hj;omega)))
        _ = _:=sum_subset (range_mono (by omega:B+1≤N+1)) fun i _ hi=>sum_eq_zero fun j _=>h1 i j (Or.inl (by simp only [mem_range] at hi;omega))
 -- h unused drop.

variable [Fintype I]
def shine (l:ℕ)(S:GrainS I)(f:Pearl)(e:ℕ):Inn I:=∑ n∈range (l+e+1),parley (brook f S e n)
def coupon (Γ:Line I)(P Q:Inn I):Inn I:=∑ i,∑ j, Γ i j • (axes I i P*axes I j Q)

lemma timid (S:GrainS I)(h:Combed S)(hv:Lit l S)(Γ:Line I)(hΓ:∀ i j,Γ i j=Γ j i)(e:ℕ)(f:Pearl):
    ∑ n∈range (l+e+1), parley (unilateral Γ (brook f S) e n)=slab (half Γ) (axes I) (shine l S f e):=by
 simp_rw [unital Γ _ _ _ hΓ (h f _ _)]; rw [shine,map_sum]
 let T(n:ℕ):=slab (half Γ) (axes I) (parley (brook f S e n))
 have he(n)(H:l+e<n):T n=0:=by unfold T;rw [dry n hv H f,parley_zero,map_zero]
 have hc:T 0=0:=by simp_rw [T,slab_do,axes,barren,map_zero,smul_zero,Finset.sum_const_zero]
 have hs:T 1=0:=solitary _ (h _ _ _) _
 change ∑ n∈range (l+e+1),T (n+2)=∑ n∈range (l+e+1),T n
 have hshift (N:ℕ):(∑ n∈range N,T (n+2))+(T 1+T 0)=∑ n∈range (N+2),T n:=by rw [Finset.sum_range_succ' T (N+1),Finset.sum_range_succ' (fun n=>T (n+1)) N]; abel
 rw [hs,hc] at hshift; simp only [add_zero] at hshift
 rw [hshift,Finset.sum_range_succ _ (l+e+2),Finset.sum_range_succ _ (l+e+1),he _ (by omega),he _ (by omega),add_zero,add_zero]

lemma combine (F:Flake (p+1) I)(G:Flake (q+1) I)(hF:Forms.Sym F)(hG:Forms.Sym G):parley ((2:ℝ) • Steam.pair Γ F G (p+q))=coupon Γ (parley F) (parley G):=by
 rw [parley_smul,interconnect _ _ _ hF hG];unfold coupon axes; simp_rw [Finset.smul_sum,smul_smul]; unfold half; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>congrArg (· • _) ?_; ring
lemma joint (S:GrainS I)(h:Combed S)(hv:Lit l S)(W:Steam.Grain I)(w:waxed W)(hw:Eligible W)(Γ:Line I)(b k:ℕ)(f:Pearl):
 (∑ n∈range (l+(b+k)+1),∑ i∈range (n+1),parley ((2:ℝ) • Steam.pair Γ (brook f S b (i+1)) (W k (n-i+1)) n))=coupon Γ (shine l S f b) (showV W k):=by
 let P(i:ℕ):=parley (brook f S b i)
 let Q(j:ℕ):=parley (W k j)
 let T:=fun i j=>coupon Γ (P (i+1)) (Q (j+1))
 -- if k+1>l+(b+k) when l+b=0: handle trivial
 by_cases hb:l+b=0
 · have hi(n:ℕ):brook f S b (n+1)=0:=dry (n+1) hv (by omega) f
   simp_rw [hi,Steam.pair_zero_left,smul_zero,parley_zero,Finset.sum_const_zero];rw [shine,hb];simp only [zero_add,range_one,sum_singleton,coupon,axes,barren,zero_mul,smul_zero,sum_const_zero]
 let N:=l+(b+k)
 have he:∀ i j,l+b-1< i ∨ k+1< j ∨ N< i+j→T i j=0:=by
    intro i j hij
    have hh : l+b< i+1 ∨ k+2< j+1:=by dsimp [N] at hij;omega
    rcases hh with hh|hh
    · simp [T,P,dry (i+1) hv hh f,parley_zero,coupon]
    have hh':W k (j+1)=0:=Classical.not_not.mp (fun h=>show False from by have := hw.head _ _ h;omega)
    simp [T,Q,hh',parley_zero,coupon]
 have hi:(∑ n∈range (N+1),∑ i∈range (n+1),parley ((2:ℝ) • Steam.pair Γ (brook f S b (i+1)) (W k (n-i+1)) n))=∑ n∈range (N+1),∑ i∈range (n+1),T i (n-i):=by
    apply sum_congr rfl;intro n _; apply sum_congr rfl;intro i hi
    simp only [mem_range] at hi
    have Hz {p q n:ℕ}(hz:p+q=n)(F:Flake (p+1) I)(G:Flake (q+1) I)(hF:Forms.Sym F)(hG:Forms.Sym G):parley ((2:ℝ) • Steam.pair Γ F G n)=coupon Γ (parley F) (parley G):=by subst hz;exact combine _ _ hF hG
    exact Hz (by omega) _ _ (h _ _ _) (w _ _)
 change _=coupon Γ (∑ n∈range (l+b+1),P n) (∑ n∈range (k+3),Q n)
 change (∑ n∈range (N+1),_)=_
 rw [hi,curve T N (l+b-1) (k+1) (by dsimp [N];omega) (by dsimp [N];omega) he,show l+b-1+1=l+b by omega]; unfold T coupon
 simp_rw [map_sum,Finset.sum_range_succ' (fun n=>axes I _ (P n)) (l+b),Finset.sum_range_succ' (fun n=>axes I _ (Q n)) (k+2),show ∀ i,axes I i (P 0)=0 from fun i=>barren _ _,show ∀ i,axes I i (Q 0)=0 from fun i=>barren _ _, add_zero,Finset.sum_mul,Finset.mul_sum,Finset.smul_sum]
 exact square (range (l+b)) (range (k+2)) univ univ (fun i j a d=> _)

end YM.RG08.Trickle

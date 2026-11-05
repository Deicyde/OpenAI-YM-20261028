import YM.RG08.Forms.Dial

/-!
# Connected formal conditional heat-expansion algorithm

All inputs are joint lower-upper mesh tensors translated to one cell-mesh. Coupling order e,
rank in **potential** variables (both lower & upper), NO slot factorial (ordered tensors), heat
time power j. `burn Γ V` recursively computes coefficients of
       log ( E_{time Γ} exp V(g,A+.,B) )
where Γ has zero entries on variables not integrated. Later substitute A=A_tr B and normalize
any marked series by unmarked denominator. Recursive formula corresponds to the formal
Hamilton-Jacobi heat equation with initial V having V(0)=0; connection to usual Wick pairing
verified on finite data separately. Hide scalar manually after using that equality; on cover it
is generally not defined by whole sum and must stay out of any application using these bounds.
-/
noncomputable section
namespace YM.RG08.Steam
open Forms Finset Function
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false
variable {I:Type}{p q n j e:ℕ}

abbrev Grain (I : Type) := (e n:ℕ) → Flake n I
abbrev Clock (I : Type) := (j:ℕ) → Grain I

/- cast output slots along arithmetic identity. -/
def move {p n:ℕ}(h:p=n)(F:Flake p I):Flake n I:= h ▸ F
lemma moved (d:Ground I)(σ C:ℝ){p n:ℕ}(h:p=n){F:Flake p I}(hF:Held d σ C F):Held d σ C (move h F):=by subst h; exact hF
lemma move_sub {m r:ℕ}(h:m=r)(F F':Flake m I) : move h (F-F')=move h F-move h F':=by subst h; rfl
lemma sym_move {m r:ℕ}(h:m=r)(F:Flake m I)(hF:Sym F) : Sym (move h F):=by subst h;exact hF
lemma move_zero {m r:ℕ}(h:m=r):move h (0:Flake m I)=0:=by subst h;rfl

def unilateral (Γ : Forms.Line I) (S : Grain I) (e n:ℕ) : Flake n I:= (((n:ℝ)+2)*(n+1)/2) • lap Γ (S e (n+2))
def pair (Γ : Forms.Line I)(F:Flake (p+1) I)(G:Flake (q+1) I)(n:ℕ):Flake n I:=
 if h:p+q=n then (((p:ℝ)+1)*(q+1)/2) • move h (bridge Γ F G) else 0

def wheels (Γ : Forms.Line I) (S : Clock I) (j e n:ℕ) : Flake n I:= unilateral Γ (S j) e n+
  ∑ c∈range (n+1),∑ i∈range (j+1),∑ a∈range (e+1),pair Γ (S i a (c+1)) (S (j-i) (e-a) (n-c+1)) n

/-- Recursion via building one time horizon. Cutoff iteration here refers to j (heat time
power), unrelated to UV N. -/
def bank (Γ:Forms.Line I)(V:Grain I):ℕ → Clock I
| 0=>fun i=>if i=0 then V else 0
| t+1=>update (bank Γ V t) (t+1) (fun e n=>((t+1:ℝ)⁻¹) • wheels Γ (bank Γ V t) t e n)

def burn (Γ : Forms.Line I)(V:Grain I) (j:ℕ):Grain I:= bank Γ V j j
variable (Γ:Forms.Line I)(V:Grain I)

lemma early_bank {i j:ℕ}(he:i≤j):bank Γ V j i=burn Γ V i:=by
 induction j, he using Nat.le_induction with
 | base=>rfl
 | succ j hj ih=> rw [bank,update_of_ne (by omega:i≠j+1),ih]

lemma spark : burn Γ V 0=V:= by simp [burn,bank]
lemma blaze (j e n:ℕ):burn Γ V (j+1) e n=((j+1:ℝ)⁻¹) • wheels Γ (burn Γ V) j e n:=by
 rw [burn,bank,update_self]
 congr 1
 unfold wheels
 congr 1
 apply Finset.sum_congr rfl; intro c _
 apply Finset.sum_congr rfl; intro i hi
 simp_rw [early_bank Γ V (show i≤j by simpa [Nat.lt_succ_iff] using hi),early_bank Γ V (Nat.sub_le j i)]

/-- All positive heat coefficients are symmetrized. -/
theorem coal (e n j : ℕ) : Sym (burn Γ V (j+1) e n) := by
 rw [blaze]; apply Sym.smul;unfold wheels;apply Sym.add
 · exact Sym.smul (symmetric _) _
 have sy {M : Type}(S : Finset M)(f:M→Flake n I)(h:∀ x,Sym (f x)) : Sym (S.sum f):=by
  induction S using Finset.induction_on with
  | empty=>simp only [sum_empty];exact Sym.zero
  | @insert a s ha ih=>simp only [sum_insert ha];exact (h a).add ih
 apply sy;intro c;apply sy;intro i;apply sy;intro a
 unfold pair; split_ifs
 · exact Sym.smul (sym_move _ _ (symmetric _)) _
 exact Sym.zero

end YM.RG08.Steam

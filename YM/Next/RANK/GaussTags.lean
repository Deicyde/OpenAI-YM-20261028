import YM.Next.RANK.GaussSubst

/-! Two color positions in different probes never cancel across normal ordering of
*one* vertex. Prove exact Gaussian formula for the corrected normal-order ledger.
Includes telescope through iterated conditional kernel polynomial maps, for later
substitution even on nonlinear input polynomials.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Normal
open Finset Function Finsupp MvPolynomial
open scoped BigOperators Classical

variable {A V Z B : Type*}

def post (i : A) : poly V →ₐ[ℂ] poly (A × V) := rename fun k => (i,k)
@[simp] lemma post_X (i : A) (k : V) : post i (X k)=X (i,k) := rename_X ..
@[simp] lemma post_C (i : A) (c : ℂ) : post i (C (σ:=V) c)= C c := rename_C ..

lemma eta_slit (i : A) (m : A × V→ℂ) (x : poly V) : slit m (post i x)=post i (slit (fun z => m (i,z)) x) := by
  let M : V → (A × V) →₀ ℂ := fun z => single (i,z) 1
  have h : reads M m=fun z => m (i,z) := by ext1 z; simp [M,reads]
  simp_rw [← h,post,labelled]; exact exchange_slit M m x





-- disjoint version of lifting a transformation

def perSlot (M : A → V → Z →₀ ℂ) (z : A × V) : A × Z →₀ ℂ := mapDomain (fun x => (z.1,x)) (M z.1 z.2)
lemma posted (M : A → V → Z →₀ ℂ) (i : A) : (exchange (perSlot M)).comp (post i) = (post i).comp (exchange (M i)) := by
  ext1 v; rw [AlgHom.comp_apply, AlgHom.comp_apply,post_X,exchange_x,exchange_x]
  change linearCombination ℂ X (mapDomain (fun k => (i,k)) (M i v)) = (post i).toLinearMap (linearCombination ℂ X (M i v))
  rw [LinearMap.map_finsupp_linearCombination, Finsupp.linearCombination_mapDomain]; exact congr_arg (fun q : Z → poly (A × Z) => linearCombination ℂ q (M i v)) (funext fun k => (post_X i k).symm)
lemma posts (M : A → V → Z →₀ ℂ) (i : A) (p : poly V) : exchange (perSlot M) (post i p)=post i (exchange (M i) p) := DFunLike.congr_fun (posted ..) p

-- If no covariance to these other vertices, separate before replacing.
variable [DecidableEq A]

def pot (p : Finset A) (x : A → poly V) : poly (A × V) := ∏ i∈p,post i (x i)
def isHome (m : Symmetric (A × V)) := ∀ i j : A,i≠j → ∀ u v, m.cov (i,u) (j,v)=0

variable {K : Symmetric (A × V)} (h : isHome K)

include h in
omit [DecidableEq A] in
private lemma exhausted (i j) (hj : i≠j) (u : V) (P : poly V) : slit (K.cov (i,u)) (post j P)=0 := by
  rw [eta_slit, show (fun k => K.cov (i,u) (j,k)) = 0 from funext (fun v => h _ _ hj u v),slit_zero,map_zero]
include h
private lemma exhausts (i : A) (F : A → poly V) (s : Finset A) (hi : i∉s) (u : V) : slit (K.cov (i,u)) (pot s F)=0 := by
  induction s using Finset.induction_on with
  | empty => exact (slit _).map_one_eq_zero
  | @insert a p hp ih =>
    have h' : i≠a ∧ i∉p := by simpa only [Finset.mem_insert,not_or] using hi
    rw [pot, prod_insert hp]; change slit (K.cov (i,u)) (_* pot p F)=_
    rw [Derivation.leibniz, exhausted h _ _ h'.1,ih h'.2,smul_zero,smul_zero,add_zero]
omit h

include h in
private lemma calm (M : A → Symmetric V) (he : ∀ i a b,K.cov (i,a) (i,b)=(M i).cov a b) (s : Finset A) (F : A → poly V)
    (h1 : milk K (pot s F)=pot s fun i => milk (M i) (F i)) (P : poly V) (i : A) (hi : i∉s) :
    milk K (post i P*pot s F) = post i (milk (M i) P)*pot s (fun i => milk (M i) (F i)) := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [post_C, drink, h1,fine,post_C]
  | add p q hp hq => simp only [_root_.map_add,add_mul,hp,hq]
  | mul_X p u hp =>
    rw [mul_comm p]; simp only [map_mul (post i),post_X, mul_assoc]
    rw [feeds,feeds,hp, Derivation.leibniz, exhausts h i _ s hi u]; simp only [smul_eq_mul,eta_slit,map_add, map_mul (post i),post_X]
    have ht : (fun z => K.cov (i,u) (i,z))=(M i).cov u := funext (he i u)
    rw [ht]; ring

lemma shelter (M : A → Symmetric V) (he : ∀ i a b,K.cov (i,a) (i,b)=(M i).cov a b) (h : isHome K) (s : Finset A) (F : A → poly V) :
    milk K (pot s F)=pot s fun i => milk (M i) (F i) := by
  induction s using Finset.induction_on with
  | empty => simp [pot]
  | @insert i s hi ih =>
    rw [pot,pot,Finset.prod_insert hi,Finset.prod_insert hi]; exact calm h M he s F ih _ i hi

-- use one vertex per marker in T

def self (M : A → Symmetric V) : Symmetric (A × V) where
  cov x y := if x.1=y.1 then (M x.1).cov x.2 y.2 else 0
  symm x y := by
    by_cases h : x.1=y.1
    · simp only [h,↓reduceIte]; exact (M _).symm ..
    rw [if_neg h,if_neg (Ne.symm h)]

lemma barn (M : A → Symmetric V) (Q : Symmetric (A × V)) (m : A × V → ℂ) (P : A → poly V) (s : Finset A) :
    blend Q m (pot s (fun i => milk (-(M i)) (P i)))=blend (Q+ -(self M)) m (pot s P) := by
  have ht : isHome (-(self M)) := by intro i j h1 x y; change -(if i=j then _ else 0)=_; rw [if_neg h1,neg_zero]
  have hg i a b : (-(self M)).cov (i,a) (i,b) = (-(M i)).cov a b := by change -(if i=i then _ else 0)=_; rw [if_pos rfl]; rfl
  rw [← shelter _ hg ht,blend_components, warms, blend_components]

-- Fold in actual old & low covariance; relate b_s to Wick target.

omit [DecidableEq A] in
lemma outpost (v : A → V → B →₀ ℂ) :
    ∀ p : Finset A, ∀ P : A → poly V, exchange (fun z : A × V => v z.1 z.2) (pot p P)=∏ i∈p, exchange (v i) (P i) := by
  intro p P; unfold pot; rw [map_prod]
  apply Finset.prod_congr rfl; intro i _
  apply DFunLike.congr_fun (f:= (exchange (fun z : A × V => v z.1 z.2)).comp (post i))
  ext k; rw [AlgHom.comp_apply,post_X,exchange_x,exchange_x]

/-- On normalized-Wick coefficients before last moment evaluation. -/
lemma lodge (v : A → V → B →₀ ℂ) (M : A → Symmetric V) (Q : Symmetric B) (m : B → ℂ) (P : A → poly V) (s : Finset A) :
    blend Q m (∏ i∈s, exchange (v i) (milk (-(M i)) (P i))) =
      let f (x : A × V) := v x.1 x.2
      blend (scope f Q + -(self M)) (reads f m) (pot s P) := by rw [← outpost, wets]; exact barn M _ _ P s
-- composition of Gaussian polynomial steps. Maps are coefficient-facing.

omit [DecidableEq A]
def pipe (H : A → V →₀ ℂ) (Q : Symmetric A) := (exchange H).toLinearMap.comp (milk Q)
lemma pipes (H : A → V →₀ ℂ) (Q : Symmetric A) (p : poly A) : pipe H Q p = exchange H (milk Q p) := rfl
lemma piped (P : V → B →₀ ℂ) (R : Symmetric V) (H : A → V →₀ ℂ) (Q : Symmetric A) (p : poly A) :
    pipe P R (pipe H Q p)= pipe (fun i => linearCombination ℂ P (H i)) (scope H R + Q) p := by
  have he : (exchange P).comp (exchange H)=exchange (fun i => linearCombination ℂ P (H i)) := by
    ext1 i; rw [AlgHom.comp_apply,exchange_x,exchange_x]
    change (exchange P).toLinearMap (glyph (H i))=linearCombination ℂ MvPolynomial.X (linearCombination ℂ P (H i))
    rw [linearCombination_linearCombination,glyph,LinearMap.map_finsupp_linearCombination]
    apply congr_arg (fun f : V → poly B => linearCombination ℂ f (H i)); funext v; exact exchange_x P v
  rw [pipes,pipes,pipes,prepared,warms]; exact DFunLike.congr_fun he _
end YM.Next.Rank.Normal

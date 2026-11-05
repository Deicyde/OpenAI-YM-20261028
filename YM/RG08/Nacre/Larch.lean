import YM.RG08.Sedan.Fossil
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Adjacent reverse ratio packet of fixed unit couplings.
 Coefficientwise. All odd defects vanish. Coupling resets separate from actual running.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Nacre
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Packets Mount Glyph Room Bloch Quarry Aggregate Steam Spar Symmetry Roost
open PowerSeries Finset.Nat
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {I:Type}

abbrev Essence:= PowerSeries ℝ
abbrev Like (p q:Essence)(n:ℕ):Prop:=∀ k ≤ n,coeff k p=coeff k q
lemma raised {p q:Essence}{n:ℕ}(hp:Like p q n)(i:ℕ):Like (p^i) (q^i) n:=by
 induction i with
 | zero=>intro k _;simp
 | succ i hi=>intro k hk;simp_rw [pow_succ]; exact Room.wired _ (fun _ he=>hi _ (he.trans hk)) (fun _ he=>hp _ (he.trans hk))

-- Ω from ledger, e≥1. r index shifted. boost only positive part.
def factor (w:ℕ→ℝ)(p:Essence)(i:ℕ):Essence:=PowerSeries.X^i*(w i • p^i)
def boost (w:ℕ→ℝ)(p:Essence)(n:ℕ):ℝ:= ∑ i ∈ (range (n+1)).erase 0, coeff n (factor w p i)
def contour (p:Essence)(n:ℕ):ℝ:= ∑ a∈antidiagonal n,if a.1<n∧a.2<n then coeff a.1 p*coeff a.2 p else 0
private lemma relieved (w:ℕ→ℝ)(p:Essence)(n i:ℕ):coeff n (factor w p i)= if i ≤ n then w i*coeff (n-i) (p^i) else 0:=by rw [factor,coeff_X_pow_mul'];split_ifs <;> simp
lemma birch {p:Essence}(h:coeff 0 p=1){n:ℕ}(he:0<n):coeff n (p^2)=2*coeff n p+contour p n:=by
 rw [pow_two,coeff_mul];let f(a:ℕ×ℕ):=if a.1<n∧a.2<n then coeff a.1 p*coeff a.2 p else 0
 have ht (x:ℕ×ℕ)(hx:x∈antidiagonal n):coeff x.1 p*coeff x.2 p=(if x=(0,n) then coeff n p else 0)+(if x=(n,0) then coeff n p else 0)+f x:=by
    by_cases hk:x=(0,n)
    · subst x;simp [h,f,he.ne']
    by_cases hj:x=(n,0)
    · subst x;simp [h,f,he.ne']
    rw [if_neg hk,if_neg hj];unfold f;rw [if_pos,add_zero,zero_add]
    obtain ⟨i,j⟩:=x;have hA:= mem_antidiagonal.mp hx;simp [Prod.ext_iff] at *;omega
 have hg:=Finset.sum_congr (g:=fun x=>coeff x.1 p*coeff x.2 p) (f:=fun x=>(if x=(0,n) then coeff n p else 0)+(if x=(n,0) then coeff n p else 0)+f x) (s₁:=antidiagonal n) rfl (fun i hi=>(ht i hi).symm)
 rw [←hg]; simp only [Finset.sum_add_distrib, sum_ite_eq',HasAntidiagonal.mem_antidiagonal,zero_add,add_zero, ite_true];unfold contour f; ring
-- next(n) uses only p(<n). iterate by bank.
private def seek (w:ℕ→ℝ)(i:ℕ)(p:Essence):ℝ:=(boost w p i-contour p i)/2
private lemma strictly {w:ℕ→ℝ}{p q:Essence}{n:ℕ}(h:∀ k<n,coeff k p=coeff k q): seek w n p=seek w n q:=by
 have ht : contour p n=contour q n:=by unfold contour;refine Finset.sum_congr rfl (fun i _=>?_);split_ifs with he <;>first | rfl | rw [h _ he.1,h _ he.2]
 have heq : boost w p n=boost w q n:=by
    apply Finset.sum_congr rfl;intro i hi
    obtain ⟨h1,h2⟩:= Finset.mem_erase.mp hi
    rw [relieved,relieved];split_ifs with he <;> first | rfl | rw [raised (fun k hk=> h k (by omega) : Like p q (n-i)) i _ le_rfl]
 rw [seek,seek,ht,heq]

def mend (w:ℕ→ℝ):ℕ→Essence
 | 0=>1
 | n+1=> PowerSeries.mk (fun i=>if i=n+1 then seek w i (mend w n) else coeff i (mend w n))
def ratio (w:ℕ→ℝ):Essence:=PowerSeries.mk fun n=> coeff n (mend w n)
lemma heard (w:ℕ→ℝ){e k:ℕ}(ht:k ≤ e): coeff k (ratio w)=coeff k (mend w e):=by
 induction e,ht using Nat.le_induction with
 | base=>simp [ratio]
 | succ e he ih=>simp only [mend,coeff_mk,←ih,if_neg (by omega:k≠e+1)]
lemma hasHead (w:ℕ→ℝ): coeff 0 (ratio w)=1:=by rw [heard w (le_refl _),mend];simp
lemma fixed (w:ℕ→ℝ)(n:ℕ): coeff n ((ratio w)^2)=(if n=0 then 1 else 0)+boost w (ratio w) n:=by
 rw [pow_two] ; cases n with
 | zero=>simp [boost,←pow_two,show constantCoeff (ratio w)=1 from (coeff_zero_eq_constantCoeff_apply _).symm.trans (hasHead w)]
 | succ n=>
   rw [←pow_two,birch (hasHead w) (Nat.succ_pos _),if_neg (Nat.succ_ne_zero _),zero_add,heard w (le_refl _),mend,coeff_mk,if_pos rfl,show seek w (n+1) _=_ from strictly (fun k hk=> (heard w (by omega:k ≤ n)).symm)]
   unfold seek;ring

-- at arbitrary truncation and its lower grades. Turns into equilibrium when evaluating t_i=t_o * ratio.
lemma guaranteed (w:ℕ→ℝ){n e:ℕ}(h:e ≤ n): coeff e ((ratio w)^2)=
 coeff e ((1:Essence)+∑ i∈ (Finset.range (n+1)).erase 0,factor w (ratio w) i):=by
 rw [fixed,map_add,coeff_one,map_sum]; unfold boost;congr 1
 apply Finset.sum_subset (s₁:= (range (e+1)).erase 0) (by intro i hi;simp only [mem_range,mem_erase] at *;omega)
 intro i hi he; rw [factor,coeff_X_pow_mul',if_neg];simp only [mem_range,mem_erase] at *;omega
end YM.RG08.Nacre

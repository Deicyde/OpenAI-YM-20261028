import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! Finite Taylor calculus on a shrinking ball `t*w(x) ≤ δ, t>0`, with a
possibly exponential envelope (for comparing before Gaussian integration).
No infinite series evaluations in the definitions. -/
set_option autoImplicit false
noncomputable section
namespace YM.PertExtension.Series
open Function Filter Set
open scoped Topology ContDiff BigOperators Classical

structure Zone (X : Type*) where
  w : X → ℝ
  high : ∀ x,1 ≤ w x

namespace Zone
variable {X E F R : Type*} (Z : Zone X)
variable [NormedAddCommGroup E][NormedSpace ℝ E]
variable [NormedAddCommGroup F][NormedSpace ℝ F]
variable [NormedRing R][NormedAlgebra ℝ R]

structure Invoice (a : X → E) : Prop where
  exists_bound : ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧ ∀ x, ‖a x‖ ≤ C*(Z.w x)^e
structure Fits (V : X → ℝ)(k : ℕ)(f : ℝ → X → E) : Prop where
  envelope x : 1 ≤ V x
  cost : ∃ (δ C : ℝ) (e : ℕ), 0<δ ∧ 0≤C ∧ ∀ x t, 0<t → t*Z.w x≤δ→ ‖f t x‖≤C*Z.w x^e*V x*t^k
                        
-- Π expressions to keep finite sums explicit before each tensor operation.
def eval (a : ℕ → X → E) (n : ℕ) : ℝ → X → E := fun t x=> ∑ i∈Finset.range (n+1),(t^i) • a i x
structure Built (V : X → ℝ)(f : ℝ → X → E)(a : ℕ → X → E):Prop where
  invoice (n) : Z.Invoice (a n)
  fits (n) : Z.Fits V (n+1) (f-eval a n)

def mul (a b : ℕ → X → R) (k : ℕ) (x : X) := ∑ i∈ Finset.antidiagonal k,a i.1 x*b i.2 x

def TaylorPow (a : ℕ → X → R) : ℕ → ℕ → X → R
  | 0=>fun k x=>if k=0 then 1 else 0
  | s+1=>mul (TaylorPow a s) a

@[simp] lemma eval_zero (n : ℕ) : eval (X:=X) (E:=E) 0 n=0:=by funext t x; simp [eval]
@[simp] lemma eval_add (a b : ℕ → X → E)(n : ℕ) :eval (a+b) n=eval a n+eval b n := by funext t x;simp [eval,smul_add,Finset.sum_add_distrib]
@[simp] lemma eval_neg (a : ℕ → X → E)(n : ℕ) :eval (-a) n= -eval a n := by funext t x;simp [eval,Finset.sum_neg_distrib]
@[simp] lemma eval_sub (a b : ℕ → X → E)(n : ℕ) :eval (a-b) n=eval a n-eval b n := by simp [sub_eq_add_neg]

variable {V V' : X → ℝ} {f g : ℝ → X → E} {a b : X → E}
variable {u v : ℝ → X → R} {A B : X → R} {k l : ℕ}
namespace Invoice
variable {Z}
lemma bounded (C:ℝ)(h : ∀ x, ‖a x‖ ≤ C) : Z.Invoice a := ⟨max C 0,0,(le_max_right ..),fun x => (h x).trans (by simp)⟩
lemma weaken {b : X→F} (h : Z.Invoice a)(hf : ∀ x, ‖b x‖ ≤ ‖a x‖) : Z.Invoice b := by
  obtain ⟨C,e,t,H⟩:= h
  exact ⟨C,e,t,fun x=>(hf x).trans (H x)⟩
protected lemma norm (h : Z.Invoice a) : Z.Invoice fun x=>‖a x‖ := h.weaken (by simp)
protected lemma of_norm (h : Z.Invoice fun x=>‖a x‖) : Z.Invoice a := h.weaken (by simp)
lemma const (a : E) : Z.Invoice fun _=>a := bounded ‖a‖ (fun _=>le_rfl)
lemma add (h : Z.Invoice a)(ht : Z.Invoice b) :Z.Invoice (a+b) := by
  obtain ⟨C,e,f,H⟩:=h; obtain ⟨D,s,r,U⟩:=ht
  refine ⟨C+D,e+s,add_nonneg f r,fun x=>?_⟩ -- replace
  calc
    ‖(a+b) x‖ ≤ ‖a x‖+‖b x‖:=norm_add_le ..
    _ ≤ C*Z.w x^e+D*Z.w x^s:= add_le_add (H x) (U x)
    _ ≤ _ := by rw [add_mul]; gcongr <;> first | exact Z.high _ | omega
lemma mul (h : Z.Invoice A)(ht : Z.Invoice B) :Z.Invoice (A*B) := by
  obtain ⟨C,e,f,H⟩:=h; obtain ⟨D,s,r,U⟩:=ht
  refine ⟨C*D,e+s,mul_nonneg f r,fun x=>?_⟩
  calc
    ‖(A*B) x‖ ≤ ‖A x‖*‖B x‖:= norm_mul_le ..
    _ ≤ (C*Z.w x^e)*(D*Z.w x^s):= mul_le_mul (H x) (U x) (norm_nonneg _) ((norm_nonneg _).trans (H x))
    _ = _ := by rw [pow_add]; ring
lemma fin_sum {ι : Type*}(S : Finset ι)(A : ι → X → E) (h : ∀ i∈S,Z.Invoice (A i)) :Z.Invoice (∑ i∈S,A i) := by
  induction S using Finset.induction_on with
  | empty=>simpa using! (const (Z:=Z) (E:=E) 0)
  | insert i s hi ih=> rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self _ _)).add (ih (fun _ hj=>h _ (Finset.mem_insert_of_mem hj)))
lemma pow (h : Z.Invoice A)(k : ℕ) :Z.Invoice fun x=>A x ^ k := by induction k with
 | zero=> simpa using! (const (Z:=Z) (E:=R) 1)
 | succ k ih=> simp_rw [pow_succ];exact ih.mul h
end Invoice

namespace Fits
variable {Z}
protected lemma zero (hV : ∀ x,1 ≤ V x) (Z : Zone X) (k) : Z.Fits V k (0:ℝ→X→E) := ⟨hV,1,0,0,zero_lt_one,le_rfl,fun x t ht _=> by simp⟩
lemma shift_a {d : ℝ→ X→ F}(h : Z.Fits V k f)(hd':∀ x, 1 ≤ V' x)(hd : ∃ (δ C:ℝ)(e:ℕ),0<δ ∧ 0≤C ∧ ∀ x t, 0<t → t*Z.w x ≤ δ → ‖d t x‖ ≤ (C*Z.w x^e*‖f t x‖) ∧ V x≤V' x) :Z.Fits V' k d:=by
  obtain ⟨δ,C,e,hδ,hc,H⟩:=h.cost; obtain ⟨γ,D,g,hγ,hD,hg⟩:=hd
  refine ⟨hd',min δ γ,C*D,e+g,lt_min hδ hγ,mul_nonneg hc hD,?_⟩
  intro x t ht hm; obtain ⟨he,hE⟩:=hg x t ht (hm.trans (min_le_right ..))
  have hw := Z.high x
  calc
     _ ≤ C*Z.w x^e*V x * t^k * (D*Z.w x^g) := by rw [mul_comm] at he;exact he.trans (mul_le_mul_of_nonneg_right (H x t ht (hm.trans (min_le_left ..))) (by positivity))
     _ ≤ _ := by rw [pow_add];nlinarith [mul_nonneg (sub_nonneg.mpr hE) (show 0 ≤ C*D*(Z.w x ^ e * Z.w x ^ g)*t^k by positivity)]
lemma lift_dominate {d : ℝ→ X→ F}(h : Z.Fits V k f){δ} (hδ : 0<δ)(he : ∀ x t, 0<t → t*Z.w x ≤ δ → ‖d t x‖ ≤ ‖f t x‖) : Z.Fits V k d:= by
  apply h.shift_a h.envelope; exact ⟨δ,1,0,hδ,zero_le_one,fun x t ht hm=>by simpa using he x t ht hm⟩
lemma dominate {d : ℝ→ X→ F}(h : Z.Fits V k f)(he : ∀ x t, ‖d t x‖ ≤ ‖f t x‖) : Z.Fits V k d:= h.lift_dominate zero_lt_one (fun x t _ _=>he x t)
lemma widen (h : Z.Fits V k f)(he : ∀ x,V x ≤ V' x) :Z.Fits V' k f:= by
  apply h.shift_a (fun x=>(h.envelope x).trans (he x)); exact ⟨1,1,0,zero_lt_one,zero_le_one,fun x t _ _=> ⟨by simp,he x⟩⟩
lemma neg (h : Z.Fits V k f) : Z.Fits V k (-f):= h.dominate (by simp)
lemma add (h : Z.Fits V k f) (hg : Z.Fits V k g) : Z.Fits V k (f+g) := by
  obtain ⟨δ,C,e,hδ,hc,H⟩:=h.cost; obtain ⟨γ,D,l,hγ,hD,hl⟩:=hg.cost
  refine ⟨h.envelope,min δ γ,C+D,e+l,lt_min hδ hγ,add_nonneg hc hD,?_⟩
  intro x t ht hm
  calc
    _ ≤ C*Z.w x^e*V x * t^k + D*Z.w x^l*V x*t^k := (norm_add_le ..).trans (add_le_add (H x t ht (hm.trans (min_le_left ..))) (hl x t ht (hm.trans (min_le_right ..))))
    _ ≤ _ := by rw [pow_add]; nlinarith only
        [show 0≤D*(Z.w x^e-1)*Z.w x^l*V x*t^k by have := one_le_pow₀ (Z.high x) (n:=e);have := Z.high x; have := h.envelope x; positivity,
          show 0≤C*(Z.w x^l-1)*Z.w x^e*V x*t^k by have := one_le_pow₀ (Z.high x) (n:=l);have := Z.high x; have := h.envelope x;positivity]
lemma sub (h : Z.Fits V k f) (hg : Z.Fits V k g) : Z.Fits V k (f-g) := by rw [sub_eq_add_neg]; exact h.add hg.neg
lemma fin_sum {ι : Type*}(S : Finset ι) (f : ι → ℝ→X→E) (h : ∀ i∈S,Z.Fits V k (f i)) (hV : ∀ x,1≤V x) :Z.Fits V k (∑ i∈S,f i) := by
  induction S using Finset.induction_on with
  | empty=> simpa using! (Fits.zero (E:=E) hV Z k)
  | insert i s he ih=> rw [Finset.sum_insert he]; exact (h i (Finset.mem_insert_self _ _)).add (ih (fun _ hj=>h _ (Finset.mem_insert_of_mem hj)))
lemma degrade (h : Z.Fits V k f)(hg : l ≤ k) :Z.Fits V l f := by
  obtain ⟨δ,C,e,hδ,hc,H⟩:=h.cost
  refine ⟨h.envelope,min δ 1,C,e,lt_min hδ zero_lt_one,hc,?_⟩
  intro x t ht hm; have hh : t≤1:=(le_mul_of_one_le_right ht.le (Z.high x)).trans (hm.trans (min_le_right ..))
  exact (H x t ht (hm.trans (min_le_left ..))).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht.le hh hg) (by have := Z.high x; have := h.envelope x;positivity))
lemma power (hV : ∀ x,1≤V x)(h : Z.Invoice a)(k : ℕ) :Z.Fits V k fun t x=>t^k • a x := by
   obtain ⟨C,e,hC,H⟩:= h
   exact ⟨hV,1,C,e,zero_lt_one,hC,fun x t ht _=> calc
     _ ≤ ‖a x‖ * t^k := (norm_smul_le ..).trans_eq <| by rw [Real.norm_eq_abs,abs_of_pos (pow_pos ht _),mul_comm]
     _ ≤ _ := by gcongr;exact (H x).trans (le_mul_of_one_le_right ((norm_nonneg _).trans (H x)) (hV x))⟩
lemma power_eval {n : ℕ}{a : ℕ→X→E}(ha : ∀ i≤n, Z.Invoice (a i)) (hV : ∀ x,1≤V x) :Z.Fits V 0 (eval a n) := by
  convert Fits.fin_sum (Finset.range (n+1)) _ (fun i hi=>(power hV (ha i (by simpa [Nat.lt_succ_iff] using hi)) i).degrade (Nat.zero_le _)) hV with t x
  funext t x; simp [eval,Finset.sum_apply]
lemma mul (h : Z.Fits V k u)(hv : Z.Fits V' l v) :Z.Fits (V*V') (k+l) (u*v) := by
  obtain ⟨δ,C,e,hδ,hc,H⟩:=h.cost; obtain ⟨γ,D,l,hγ,hD,hl⟩:=hv.cost
  refine ⟨fun x=> ?_,min δ γ,C*D,e+l,lt_min hδ hγ,mul_nonneg hc hD,?_⟩
  · exact (h.envelope x).trans (le_mul_of_one_le_right (zero_le_one.trans (h.envelope x)) (hv.envelope x))
  intro x t ht hm
  exact (norm_mul_le (u t x) (v t x)).trans (mul_le_mul (H x t ht (hm.trans (min_le_left ..))) (hl x t ht (hm.trans (min_le_right ..))) (norm_nonneg _) ((norm_nonneg _).trans (H x t ht (hm.trans (min_le_left ..)))) |>.trans_eq <| by simp only [pow_add,Pi.mul_apply];ring)
end Fits

namespace Built
variable {Z} {a b : ℕ → X→ E} {A B : ℕ→ X→ R} {c : ℕ→X→F}
theorem priced (hf : Z.Built V f a) :Z.Fits V 0 f := by
  convert ((hf.fits 0).degrade (le_refl 0|>.trans (Nat.zero_le _))).add (Fits.power_eval (n:=0) (V:=V) (fun i _=>hf.invoice i) (hf.fits 0).envelope) using 1
  exact (sub_add_cancel ..).symm
protected lemma add (hf : Z.Built V f a)(he : Z.Built V g b) :Z.Built V (f+g) (a+b) := by
  refine ⟨fun n=> (hf.invoice n).add (he.invoice n),fun n=>?_⟩
  rw [eval_add,show f +g -(eval a n + eval b n) = (f-eval a n)+(g-eval b n) from by abel]
  exact (hf.fits n).add (he.fits n)
protected lemma neg (hf : Z.Built V f a):Z.Built V (-f) (-a):= ⟨fun n=>(hf.invoice n).weaken (by simp), fun n=> by rw [eval_neg,show -f - -eval a n= -(f-eval a n) by abel]; exact (hf.fits n).neg⟩
protected lemma sub (hf : Z.Built V f a)(he : Z.Built V g b) :Z.Built V (f-g) (a-b):=by simp_rw [sub_eq_add_neg]; exact hf.add he.neg
lemma const (a : E)(hV : ∀ x,1≤V x):Z.Built V (fun _ _=>a) (fun i _=>if i=0 then a else 0) := by
  refine ⟨fun n=> by split <;> exact Invoice.const _, fun n=>?_⟩
  convert Fits.zero (E:=E) hV Z (n+1) using 2
  funext t x; simp only [eval,Pi.sub_apply,Pi.zero_apply,smul_ite,smul_zero, ite_true]; simp
lemma fin_sum {ι : Type*} (S : Finset ι) {f : ι → ℝ→X→E} {a : ι→ℕ→X→E}(h : ∀ i∈S,Z.Built V (f i) (a i))(hV : ∀ x,1≤V x) :Z.Built V (∑ i∈S,f i) (∑ i∈S,a i) := by
  induction S using Finset.induction_on with
  | empty=> simpa using! (const (E:=E) (Z:=Z) 0 hV)
  | insert i s hi ih=>rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self _ _)).add (ih fun _ hj=>h _ (Finset.mem_insert_of_mem hj))

omit [NormedAlgebra ℝ R] in
def triangle (W : ℕ×ℕ→ℝ→X→R) (n : ℕ) := ∑ k∈Finset.range (n+1),∑ i∈ Finset.antidiagonal k,W i
omit [NormedAlgebra ℝ R] in
private lemma triangle_eq (I : ℕ×ℕ→ℝ→X→R)(n : ℕ): triangle I n=∑ i∈((Finset.range (n+1) ×ˢ Finset.range (n+1)).filter fun i : ℕ×ℕ=>i.1+i.2 ≤ n),I i:= by
  let S:= (Finset.range (n+1) ×ˢ Finset.range (n+1)).filter fun i : ℕ×ℕ=>i.1+i.2 ≤ n
  let K:= Finset.range (n+1)
  have h (i : ℕ×ℕ) (hi : i∈S) : i.1+i.2∈ K:= Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hi).2)
  change _=∑ i∈S,I i
  rw [← Finset.sum_fiberwise_of_maps_to h I]; unfold triangle
  refine Finset.sum_congr rfl fun i hi=>Finset.sum_congr ?_ fun _ _=>rfl
  ext1 j; simp only [K, Finset.mem_range] at hi; simp only [S,Finset.mem_antidiagonal,Finset.mem_filter,Finset.mem_product,Finset.mem_range];omega
private lemma product_tail (ha : ∀ i,Z.Invoice (A i))(hb : ∀ i,Z.Invoice (B i))(n)(hV : ∀ x,1 ≤ V x) :Z.Fits V (n+1) (eval A n * eval B n - eval (Zone.mul A B) n) := by
  let I (k : ℕ×ℕ) : ℝ→X→R := fun t x=>t^(k.1+k.2) • ((A k.1 x)*(B k.2 x))
  have he : eval (Zone.mul A B) n = triangle I n := by
    funext t x; simp only [eval,triangle,Finset.sum_apply,Zone.mul]
    refine Finset.sum_congr rfl fun i hi=>?_
    rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j hj=> show t^i • (A j.1 x*B j.2 x) = t^(j.1+j.2) • _ from by simp only [(Finset.mem_antidiagonal.mp hj)]
  rw [he, triangle_eq]
  let S:= Finset.range (n+1) ×ˢ Finset.range (n+1); let T:= S.filter fun k : ℕ×ℕ=>n+1 ≤ k.1+k.2
  have hv : (∑ i∈S,I i) = (∑ i∈ S.filter (fun i=>i.1+i.2≤n),I i)+∑ i∈T,I i:=by
    let P:=fun i : ℕ×ℕ=>i.1+i.2≤n
    have h := Finset.sum_filter_add_sum_filter_not S P I
    simpa only [P,T,not_le,← Nat.succ_le_iff] using h.symm
  have ht : ∑ i∈S, I i=eval A n*eval B n := by
    funext t x;dsimp only [eval,Pi.mul_apply,Finset.sum_apply,S]
    rw [Finset.sum_product, Finset.sum_mul];simp_rw [Finset.mul_sum]
    have hI (i : ℕ) (j : ℕ) : I (i,j) t x = t^i • A i x * (t^j • B j x) := by dsimp only [I]; simp [pow_add,smul_smul,mul_comm (t^i) (t^j)]
    simp_rw [Finset.sum_apply,hI]
  rw [← ht]
  change Z.Fits _ _ ((∑ i∈S,I i) - ∑ i∈S.filter (fun i=>i.1+i.2≤n), I i)
  rw [hv, add_sub_cancel_left]
  refine Fits.fin_sum T _ (fun i hi=> (Fits.power hV ((ha i.1).mul (hb i.2)) (i.1+i.2)).degrade (Finset.mem_filter.mp hi).2) hV

lemma prod (ha : Z.Built V u A)(hb : Z.Built V' v B): Z.Built (V*V') (u*v) (Zone.mul A B) := by
  have he : ∀ x,1 ≤ (V*V') x:= fun x=> one_le_mul_of_one_le_of_one_le ((ha.fits 0).envelope _) ((hb.fits 0).envelope _)
  refine ⟨fun i=>?_,fun n=>?_⟩
  · unfold Zone.mul; convert Invoice.fin_sum (Finset.antidiagonal i) _ (fun k _=>(ha.invoice k.1).mul (hb.invoice k.2)) using 1
    ext x; exact (Finset.sum_apply x (Finset.antidiagonal i) (fun k : ℕ×ℕ=>A k.1 * B k.2)).symm
  obtain h₁:= (ha.fits n).mul hb.priced
  have h₂:= (Fits.power_eval (Z:=Z) (V:=V) (n:=n) (fun i _=>ha.invoice i) (ha.fits 0).envelope).mul (hb.fits n)
  rw [zero_add] at h₂
  convert h₁.add h₂ |>.add (product_tail ha.invoice hb.invoice n he) using 1
  funext t x
  simp only [Pi.add_apply,Pi.sub_apply, Pi.mul_apply];noncomm_ring

lemma powers (ha : Z.Built V u A)(k : ℕ) : Z.Built (V^k) (u^k) (TaylorPow A k) := by induction k with
 | zero=> rw [pow_zero,pow_zero];exact const 1 (fun _=>le_rfl)
 | succ k ih => rw [pow_succ,pow_succ]; exact ih.prod ha

end Built
end Zone
end YM.PertExtension.Series

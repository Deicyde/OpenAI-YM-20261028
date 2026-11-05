import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import YM.Push.LOOP_COEFFICIENT.Continuum.Matrix
import YM.Push.LOOP_COEFFICIENT.ContinuumTrace
import YM.Push.LOOP_COEFFICIENT.Thin

/-!
# Absolute convolution prices on finite abelian groups (counting)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Filter Set Matrix Metric Lattice Laurent RG Bloch Wilson Real
open scoped Topology BigOperators Matrix.Norms.L2Operator
variable {ι D : Type} [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D] [AddCommGroup D] {f : ι → D → ℝ} {A : ℝ}

def allowed (ι D : Type) [Fintype ι] [Fintype D] [DecidableEq ι] [DecidableEq D] [AddCommGroup D] := Finset.univ.filter fun a : ι → D => ∑ i, a i = 0
lemma by_marginal (k : ι) (hf : ∀ i j, 0≤f i j) (hA : 1≤A) (h : ∀ i, ∑ j,f i j ≤ A) :
    ∑ a∈allowed ι D, (∏ i, if i=k then 1 else f i (a i)) ≤ A^(Fintype.card ι) := by
  let u (a : ι → D) := update a k 0; let z (i : ι) (v : D) := if i=k then (if v=0 then 1 else 0) else f i v
  have he a : (∏ i, if i=k then 1 else f i (a i)) = ∏ i,z i (u a i) := Finset.prod_congr rfl fun i _ => by by_cases hi : i=k <;> simp [hi,z,u,Function.update_of_ne]
  have hu : Set.InjOn u (allowed ι D) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe,allowed, Finset.mem_filter,Finset.mem_univ,true_and] at ha hb
    have ht i (hi : i≠k) := show a i = b i by simpa [u,Function.update_of_ne hi] using congr_fun hab i
    funext i; by_cases hi : i=k
    · subst i; have hh : ∑ i∈Finset.univ.erase k,a i = ∑ i∈Finset.univ.erase k,b i := Finset.sum_congr rfl fun _ hx => ht _ (Finset.mem_erase.mp hx).1
      rw [← Finset.add_sum_erase _ a (Finset.mem_univ k),hh] at ha; rw [← Finset.add_sum_erase _ b (Finset.mem_univ k)] at hb; exact add_right_cancel (ha.trans hb.symm)
    exact ht i hi
  have hz i v : 0 ≤ z i v := by unfold z; split_ifs <;> simp [hf]
  simp_rw [he]; calc
    _ = ∑ a ∈ (allowed ι D).image u, ∏ i,z i (a i) := (Finset.sum_image hu).symm
    _ ≤ ∑ a : ι → D,∏ i,z i (a i) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => Finset.prod_nonneg fun _ _ => hz ..)
    _ = _ := (Fintype.prod_sum z).symm
    _ ≤ _ := (Finset.prod_le_prod (s:=Finset.univ) (f:=fun i => ∑ j,z i j) (fun _ _ => Finset.sum_nonneg fun _ _ => hz ..) (g:=fun _ => A) fun i _ => by by_cases hi : i=k <;> simp [hi,z,hA,h]).trans_eq (by simp)
lemma pow_product (x : ι → ℝ) (hx : ∀ i,0≤x i) (a : ℝ) : (∏ i,x i)^a = ∏ i,(x i)^a := by
  generalize (Finset.univ : Finset ι)=s; induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi,Real.mul_rpow (hx _) (Finset.prod_nonneg fun j _ => hx j),ih]

omit [Fintype D] [DecidableEq D] [AddCommGroup D] in
lemma omission_identity (hf : ∀ i j,0≤f i j) {w p : ι → ℝ} (hw : ∀ i, 0≤w i) (he : ∀ i, p i * (∑ k, if i=k then 0 else w k) = 1) (x : ι → D) :
    ∏ k, (∏ i, if i=k then 1 else (f i (x i))^(p i))^(w k) = ∏ i,f i (x i) := by
  simp_rw [fun k => pow_product _ (fun i => show (0:ℝ) ≤ if i=k then 1 else (f i (x i))^(p i) by split <;> first | exact zero_le_one | exact Real.rpow_nonneg (hf ..) _) (w k),Finset.prod_comm (f:=fun k i => (if i=k then 1 else (f i (x i))^(p i))^(w k))]
  refine Finset.prod_congr rfl fun i _ => ?_
  conv_rhs => rw [← Real.rpow_one (f i _),← he i,Real.rpow_mul (hf ..),Real.rpow_sum_of_nonneg (Real.rpow_nonneg (hf ..) _) (fun j _ => show 0 ≤ if i=j then 0 else w j by split <;> simp [hw])]
  exact Finset.prod_congr rfl fun j _ => by by_cases h : i=j <;> simp [h]
lemma young (hf : ∀ i j,0≤f i j) {w p : ι → ℝ} (hw : ∀ i,0≤w i) (ht : ∑ k,w k=1) (he : ∀ i,p i*(∑ k,if i=k then 0 else w k)=1) (hA : 1≤A) (hb : ∀ i, ∑ j,(f i j)^(p i) ≤ A) :
    ∑ a∈allowed ι D, ∏ i,f i (a i) ≤ A^(Fintype.card ι) := by
  simp_rw [← omission_identity hf hw he]; apply (Finset.sum_le_sum (fun z _ => Real.geom_mean_le_arith_mean_weighted Finset.univ w (fun k => ∏ i,if i=k then 1 else (f i (z i))^(p i)) (fun _ _ => hw _) ht (fun k _ => Finset.prod_nonneg fun i _ => by split; simp; exact Real.rpow_nonneg (hf ..) _))).trans
  rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]; convert (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (by_marginal (f:= fun i j => (f i j)^p i) k (fun i j => Real.rpow_nonneg (hf ..) _) hA hb) (hw k))) using 1; rw [← Finset.sum_mul,ht,one_mul]

variable {n : ℕ}
lemma sum_allowed (F : (Fin (n+1) → D) → ℝ) : ∑ a∈allowed (Fin (n+1)) D,F a = ∑ x : Fin n → D, F (Fin.cons (-(∑ i,x i)) x) := by
  rw [allowed,Finset.sum_filter,← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => D)), Fintype.sum_prod_type, Finset.sum_comm]; simp [Fin.sum_univ_succ, ← eq_neg_iff_add_eq_zero, Fin.consEquiv]

omit [DecidableEq D] [AddCommGroup D] in
lemma mixed_power {x f : D → ℝ} {s t u A B : ℝ} (hx : ∀ j,0≤ x j) (hf : ∀ j,0≤ f j) (hs : 0≤s) (ht : 0≤t) (hs' : s+t=1)
    (hx' : ∑ j,(x j)^u ≤ A) (hf' : ∑ j,(f j)^(2:ℕ) ≤ B) : ∑ j,(x j)^(u*s)*(f j)^(2*t:ℝ) ≤ s*A + t*B := by
  simp_rw [Real.rpow_mul (hx _),Real.rpow_mul (hf _), Real.rpow_two]; exact (Finset.sum_le_sum (g:=fun j => s*(x j)^u + t*(f j)^2) fun _ _ => Real.geom_mean_le_arith_mean2_weighted hs ht (Real.rpow_nonneg (hx _) _) (sq_nonneg _) hs').trans (by rw [Finset.sum_add_distrib, ← Finset.mul_sum,← Finset.mul_sum]; gcongr)
end YM.Push.Loops.Block

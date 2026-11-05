import YM.WilsonBulk.Heat.Duality

/-!
# Assembling ∂t identities at finite e

Cashes pay into polynomial ring. ∂_x variables keeping layout. Capture all
nonnegative exponents e. `range` includes up to e+2 valence, absorb maybe
known vanishing. Next reassemble/coefficient exp.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical ENNReal BigOperators
open Function Equiv Finset
variable {A X : Type} {n m e d : ℕ}
lemma diagonals [AddCommMonoid A] (f : ℕ→ℕ→A) (d : ℕ) :
    ∑ i : Split d, f (l i) (r i)= ∑ p∈antidiagonal d, f p.1 p.2 := by
  rw [← sum_attach (antidiagonal d)]
  rfl
lemma by_pairs [AddCommMonoid X] (f : ℕ→ℕ→ X) {a b d : ℕ} (hw : a+b≤d) (h : ∀ x y,a<x ∨ b<y → f x y=0) :
    ∑ i∈range (d+1), ∑ k : Split i,f (l k) (r k) = ∑ i∈range (a+1),∑ j∈range (b+1),f i j := by
  let t := (range (a+1)) ×ˢ range (b+1); let p (z:ℕ×ℕ) := f z.1 z.2; let g (z:ℕ×ℕ) := z.1+z.2
  have hT i : ∑ z∈antidiagonal i,p z=∑ z ∈ t with g z=i,p z := by
    symm; refine sum_subset (fun x hx => mem_antidiagonal.mpr (mem_filter.mp hx).2) (fun i hi hn=>?_) -- i shadow
    · apply h; simp only [t, mem_filter,g,mem_product,mem_range,mem_antidiagonal] at *; omega
  simp_rw [diagonals f]
  change ∑ i∈range (d+1), (∑ z∈antidiagonal i,p z)=_
  simp_rw [hT]
  rw [sum_fiberwise_of_maps_to (by rintro x hx; simp only [t,mem_product,mem_range,g] at *; omega)]
  exact sum_product' .. -- inspect

lemma permute_three {ι κ μ R : Type} [AddCommMonoid R] (s : Finset ι) (t : Finset κ) (q : Finset μ) (a : ι→κ→μ→R) :
    ∑ i∈s,∑ j∈t,∑ k∈q,a i j k = ∑ j∈t,∑ k∈q,∑ i∈s,a i j k := by rw [sum_comm]; exact sum_congr rfl (fun i _=> sum_comm)

variable {α : Type} [Fintype α]
open MvPolynomial (X C pderiv)
abbrev allowed (e : ℕ) := range (e+3)
def capsule (e : ℕ) (u : Frames α) : Formula α := ∑ n∈allowed e,script (u n)

lemma lap_summed (G : Page α 2) (e : ℕ) {u : Frames α} (hu : ∀ n,Regular (u n)) (hr : ∀ n,e+2<n→ u n=0) :
    capsule e (fun n=> lap G (u (n+2)))=laplace G (capsule e u) := by
  unfold capsule allowed; simp_rw [map_sum]; rw [sum_range_succ' (fun i=>laplace G (script (u i))), sum_range_succ' (fun i=> laplace G (script (u (i+1))))]
  rw [laplace_scalar,laplace_linear _ _ (hu _),add_zero,add_zero]; symm
  simp_rw [fold_lap G _ (hu _)]
  -- rank cast in sums
  refine sum_subset (range_mono (show e+1≤e+3 by omega)) (fun i hv hh=>?_)
  simp [hr (i+2) (by simp only [mem_range] at hh; omega)]
lemma air_summed (G : Page α 2) (u v : Frames α) (hu : ∀ n, Regular (u n)) (hv : ∀ n,Regular (v n))
    (a b : ℕ) (hd : ∀ n,a+2<n→u n=0) (he : ∀ n,b+2<n→v n=0) {d : ℕ} (hp : a+b=d) :
    capsule d (fun n=> ∑ i : Split n,escort (finCongr (parts i)) (bridge G (u (l i+1)) (v (r i+1))))=airing G (capsule a u) (capsule b v) := by
  unfold capsule; simp_rw [script_sum,script_escort, ← fold_air _ _ _ (hu _) (hv _),airing_sum_l,airing_sum_r]
  let f p q:=airing G (script (u p)) (script (v q)); let g p q:=f (p+1) (q+1)
  change (∑ i∈range (d+3),∑ j:Split i,g (l j) (r j))=∑ i∈range (a+3),∑ j∈range (b+3), f i j
  rw [sum_range_succ' (fun i=> ∑ j∈range (b+3), f i j)]
  simp_rw [sum_range_succ' (fun j=> f _ j),show ∀ i,f i 0=0 from fun i=> air_scalar_right G (v 0) _,show ∀ j,f 0 j=0 from fun _=> air_scalar_left G (u 0) _, add_zero]; rw [sum_const_zero, add_zero]
  refine by_pairs g (a:=a+1) (b:=b+1) (d:=d+2) (by omega) ?_
  intro x y h; unfold g f; rcases h with h|h
  · simp [hd _ (show a+2<x+1 by omega)]
  simp [he _ (show b+2<y+1 by omega)]

lemma equation (G : Page α 2) {I : Record α} (hi : Based I) (hs : FrameBound I) (d e : ℕ) :
    let f t i:= capsule i (immerse G I false t i)
    ((d+1:ℕ):ℝ) • f (d+1) e= laplace G (f d e)+∑ i : Split e,∑ j : Split d,airing G (f (l j) (l i)) (f (r j) (r i)) := by
  intro f; have hr t i n:= immerse_bounded G false hs t i n; have hv t i n:= immerse_regular G false hi t i n
  conv_lhs => arg 2; unfold f capsule; simp only [restore,Bool.false_eq_true,and_false,↓reduceIte,script_scale, script_plus,script_sum]
  rw [← Finset.smul_sum, smul_inv_smul₀ (by positivity : ((d+1:ℕ):ℝ)≠0), sum_add_distrib, ← lap_summed G e (hu:=hv d e) (hr:=hr d e)]
  congr 1; rw [permute_three]; apply sum_congr rfl; intro i _; refine sum_congr rfl fun j _=>?_
  unfold f; rw [← air_summed G _ _ (hv (l j) (l i)) (hv (r j) (r i)) (l i) (r i) (hr (l j) (l i)) (hr (r j) (r i)) (parts i)];
  simp only [capsule,torpedo, script_sum]
end YM.WilsonBulk.Sheet

import YM.WilsonBulk.Recast.Fees
import YM.WilsonBulk.Heat.Paid

/-!
# Coefficient quote reagents: quantitative overlap lip using exact polynomial prefix
  order n = **strict** cutoff. Formal sums Wick curvature & ratio yarn; doesn't charge rescaling
  of `L` across all continuation steps; see Warping. Use Tariff smart encapsulation for checking
  polynomials; no independence of step top-path constructor. These real quotes don't assert
  equality of absolute-vector L² frames.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Recall
open PowerSeries Function Filter Equiv Finset Sheet
open scoped Topology BigOperators ENNReal Classical
variable {A B : Type} {x y x' y' p q r s δ η : ℝ} {n m i j e : ℕ} {u v z k u' v' r' : Word}
structure Reel (δ p x y : ℝ) : Prop where
  cost : |x| ≤ p
  due : |y| ≤ p
  movement : |x-y| ≤ δ*p
  radiusM : 0≤δ
namespace Reel
variable (h : Reel δ p x y)
include h
lemma nonneg : 0 ≤ p := (abs_nonneg _).trans h.cost
lemma more (he : p≤q) (hy : δ ≤ η) : Reel η q x y := ⟨h.cost.trans he,h.due.trans he,h.movement.trans (mul_le_mul hy he h.nonneg (h.radiusM.trans hy)),h.radiusM.trans hy⟩
omit h in
lemma penny (h : |x| ≤ p) (he : 0 ≤ δ) : Reel δ p x x := ⟨h,h,by rw [sub_self,abs_zero]; exact mul_nonneg he ((abs_nonneg x).trans h),he⟩
omit h in
lemma zero (he : 0 ≤ p) (h : 0 ≤ δ) : Reel δ p 0 0:= penny (abs_zero.le.trans he) h
lemma plus (he : Reel δ q x' y') : Reel δ (p+q) (x+x') (y+y') := by
  refine ⟨(abs_add_le ..).trans (add_le_add h.cost he.cost), (abs_add_le ..).trans (add_le_add h.due he.due),?_, h.radiusM⟩
  rw [add_sub_add_comm,mul_add]; exact (abs_add_le ..).trans (add_le_add h.movement he.movement)
lemma neg : Reel δ p (-x) (-y) := ⟨by simpa using h.cost, by simpa using h.due, by rw [show -x- -y= -(x-y) from by abel,abs_neg]; exact h.movement,h.radiusM⟩
lemma sub (hv : Reel δ q x' y') : Reel δ (p+q) (x-x') (y-y') := by simpa only [sub_eq_add_neg] using h.plus hv.neg
lemma scale (t : ℝ) : Reel δ (|t| * p) (t*x) (t*y) := by
  refine ⟨by rw [abs_mul]; gcongr; exact h.cost, by rw [abs_mul]; gcongr; exact h.due, ?_, h.radiusM⟩
  rw [← mul_sub,abs_mul,mul_left_comm]; exact mul_le_mul_of_nonneg_left h.movement (abs_nonneg _)
lemma prod (he : Reel δ q x' y') : Reel δ (2*(p*q)) (x*x') (y*y') := by
  have h' (x y : ℝ) (hh : |x| ≤ p) (hy : |y| ≤ q) : |x*y| ≤ p*q:= by rw [abs_mul]; exact mul_le_mul hh hy (abs_nonneg _) h.nonneg
  have hp := le_mul_of_one_le_left (mul_nonneg h.nonneg he.nonneg) one_le_two
  refine ⟨(h' _ _ h.cost he.cost).trans hp,(h' _ _ h.due he.due).trans hp, ?_,h.radiusM⟩
  rw [show x*x'-y*y'=(x-y)*x'+y*(x'-y') from by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,show δ*(2*(p*q))=δ*p*q+p*(δ*q) from by ring]
  exact add_le_add (mul_le_mul h.movement he.cost (abs_nonneg _) (mul_nonneg h.radiusM h.nonneg)) (mul_le_mul h.due he.movement (abs_nonneg _) h.nonneg)
omit h in
lemma gather (S : Finset A) (y u v : A→ℝ) (h : 0≤δ) (hi : ∀ i∈S,Reel δ (y i) (u i) (v i)) : Reel δ (∑ i∈S,y i) (∑ i∈S,u i) (∑ i∈S,v i) := by
  induction S using Finset.induction with
  | empty=> simp; exact zero le_rfl h
  | insert i s h' ih=> simp_rw [sum_insert h']; exact (hi i (mem_insert_self ..)).plus (ih fun i h=>hi _ (mem_insert_of_mem h))
end Reel
structure Album (n : ℕ) (δ p : ℝ) (u v : Word) : Prop where
  pay (i : ℕ) : i<n → Reel δ p (coeff i u) (coeff i v)
  nonneg : 0≤ p
  radiusM : 0≤ δ
namespace Album
variable (h : Album n δ p u v)
include h
lemma reform (he : Steps n u u') (hf : Steps n v v') : Album n δ p u' v' := ⟨fun i hi=>by rw [← he i hi, ← hf i hi]; exact h.pay i hi, h.nonneg,h.radiusM⟩
lemma more (hg : m ≤ n) (he : δ ≤ η) (hy : p≤ q) : Album m η q u v := ⟨fun j hj=> (h.pay j (lt_of_lt_of_le hj hg)).more hy he,h.nonneg.trans hy,h.radiusM.trans he⟩
lemma plus (he : Album n δ q u' v') : Album n δ (p+q) (u+u') (v+v') := ⟨fun i hi=>by simp only [map_add]; exact (h.pay i hi).plus (he.pay i hi), add_nonneg h.nonneg he.nonneg,h.radiusM⟩
lemma sub (he : Album n δ q u' v') : Album n δ (p+q) (u-u') (v-v') := ⟨fun i hi=>by simp only [map_sub]; exact (h.pay i hi).sub (he.pay i hi), add_nonneg h.nonneg he.nonneg,h.radiusM⟩
lemma scale (t : ℝ) : Album n δ (|t| * p) (t • u) (t • v) := ⟨fun i hi=> by simp only [coeff_smul,smul_eq_mul]; exact (h.pay i hi).scale _,mul_nonneg (by positivity) h.nonneg,h.radiusM⟩
def purse (n : ℕ) (p q : ℝ) := (n:ℝ)*(2*(p*q))
omit h in
lemma purse_nn (x : ℕ) (hp : 0≤p) (hq : 0≤q) : 0 ≤ purse x p q := by unfold purse; positivity
lemma prod (he : Album n δ q u' v') : Album n δ (purse n p q) (u*u') (v*v') := by
  refine ⟨fun i hi=>?_, purse_nn n h.nonneg he.nonneg,h.radiusM⟩; rw [coeff_mul,coeff_mul]
  let S:= antidiagonal i; have hx (j : ℕ × ℕ) (hj:j∈S) : Reel δ (2*(p*q)) (coeff j.1 u*coeff j.2 u') (coeff j.1 v*coeff j.2 v') := by have h': j.1+j.2=i:= mem_antidiagonal.mp hj; exact (h.pay _ (by omega)).prod (he.pay _ (by omega))
  refine (Reel.gather S _ _ _ h.radiusM hx).more ?_ le_rfl; unfold purse S; rw [sum_const, Nat.card_antidiagonal,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by norm_num) (mul_nonneg h.nonneg he.nonneg)); exact_mod_cast hi -- ≤ mismatch
omit h
lemma one (n : ℕ) (he : 0 ≤ δ) : Album n δ 1 1 1 := by refine ⟨fun i hi=> ?_,zero_le_one,he⟩; rw [coeff_one]; split; exact Reel.penny (by norm_num) he; exact Reel.zero zero_le_one he
lemma zero (he : 0 ≤ δ) : Album n δ 0 0 0:= ⟨fun i hi=>by simp only [map_zero]; exact Reel.zero le_rfl he, le_rfl,he⟩
lemma sum (s : Finset A) (p : A→ℝ) (u v : A→ Word) (h : 0≤δ) (he : ∀ i∈s,Album n δ (p i) (u i) (v i)) : Album n δ (∑ i∈s,p i) (∑ i∈s,u i) (∑ i∈s,v i) := by
  induction s using Finset.induction with
  | empty=> simp; exact zero h
  | insert i s hs ih=> rw [sum_insert hs,sum_insert hs,sum_insert hs]; apply (he i (mem_insert_self ..)).plus (ih fun i h=> he _ (mem_insert_of_mem h))
-- length powers upper

def port (n : ℕ) (p : ℝ) : ℕ →ℝ
| 0=>1
| k+1=>purse n (port n p k) p
include h
lemma powers (i : ℕ) : Album n δ (port n p i) (u^i) (v^i) := by
  induction i with
  | zero=> rw [pow_zero,pow_zero]; exact one _ h.radiusM
  | succ i ih=> rw [port,pow_succ,pow_succ]; exact ih.prod h
end Album
open Album (purse port purse_nn)
lemma large_pow {f g : ℝ→ℝ} (h : Tariff f) (he : Tariff g) (n : ℕ) : Tariff fun x=> purse n (f x) (g x) := (Tariff.const (n:ℝ) (by positivity)).prod ((Tariff.const _ (by norm_num)).prod (h.prod he))
lemma orbit_tariff (n i : ℕ) {f : ℝ→ℝ} (h : Tariff f) : Tariff fun x=> port n (f x) i := by
  induction i with
  | zero=> exact Tariff.const _ zero_le_one
  | succ i ih=> simp only [port]; exact large_pow ih h _
lemma Quote_pencil (g g' r r' : Word) (he : e-i<n) (h : Album n δ p g g') (hh : Album n δ q r r') : Reel δ (purse n (port n p i) (port n q j)) (pencil g r e j i) (pencil g' r' e j i) := ((h.powers i).prod (hh.powers j)).pay _ he
lemma port_nn (n i : ℕ) (h : 0≤ p) : 0 ≤ port n p i:= orbit_tariff n i Tariff.one |>.1 p h
-- bar single-expression exact |

def tabBar (n : ℕ) (p q : ℝ) := ∑ i∈range n, (2*(port n p i*q))
lemma bar_tag {f g : ℝ→ℝ} (h : Tariff f) (he : Tariff g) : Tariff (fun x=> tabBar n (f x) (g x)):= Tariff.gather _ fun i _=>(Tariff.const (2:ℝ) (by norm_num)).prod ((orbit_tariff n i h).prod he)
lemma albumBar (h : Album n δ p u v) (he : Album n δ q u' v') : Album n δ (tabBar n p q) (bar u u') (bar v v') := by
  have hh (i:ℕ) : 0 ≤ 2*(port n p i*q) := mul_nonneg (by norm_num) (mul_nonneg (port_nn _ i h.nonneg) he.nonneg)
  refine ⟨fun i hi=>?_, sum_nonneg (fun i _=> hh i),h.radiusM⟩
  have hi' : Reel δ (∑ j∈range (i+1),2*(port n p j*q)) (coeff i (1*bar u u')) (coeff i (1*bar v v')):= by
    rw [bar_terms,bar_terms]; simp_rw [mul_one]; exact Reel.gather _ _ _ _ h.radiusM fun j hj=> ((h.powers j).pay _ (by omega)).prod (he.pay _ (by rw [mem_range] at hj; omega))
  rw [one_mul,one_mul] at hi'; exact hi'.more (sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun i _ _=>hh i)) le_rfl

end Recall
end YM.WilsonBulk

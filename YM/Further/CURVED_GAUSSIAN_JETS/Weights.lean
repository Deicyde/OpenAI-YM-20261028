import YM.Further.CURVED_GAUSSIAN_JETS.Jets
import YM.Further.CURVED_GAUSSIAN_JETS.Rows
import YM.Next.FREE_KERNELS.Curl

/-!
# Joint distance and direction-weight calculus for the ordered kernel jets

Use `r - m ε` distance rate at total order m, with ε paid from
kernel width, NOT from a derivative radius depending on the size of
the torus. The single external direction-weight function isn't
recentered when terms are multiplied. `moves` e.g. polynomial
position weights (`polynomial` below). Both orientations paid at all
stages. Spectrum is a separate charge.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Jets
open Function Filter Set Matrix Lattice Wilson RG Precision Progress.StationaryScenes
open Green (wt wt_pos wt_triangle wt_symm)
open Rows (Bill)
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff Classical
variable {I : Type*} {n c : Side} {G : Gauge}
structure Weights (a : I → Site n) where
  τ : I → ℝ
  fee : ℝ
  budget : ℝ
  nonneg (i) : 0≤τ i
  room : 0 < fee
  price : 1≤budget
  moves (i j) : τ j ≤ budget*wt fee (a i) (a j)*τ i

namespace Weights
variable {a : I → Site n} (s : Weights a)
def width (r : ℝ) (m : ℕ) := r-m*s.fee
def pay (m : ℕ) := (2:ℝ)^m * s.budget^m
lemma pay_pos (k : ℕ) : 0 < s.pay k := by unfold pay; have := s.price; positivity
lemma goes (i j : I) (m : ℕ) : s.τ j ^ m ≤ s.budget^m * wt (m*s.fee) (a i) (a j)*s.τ i ^ m := by
  have he := pow_le_pow_left₀ (s.nonneg j) (s.moves i j) m
  rw [mul_pow,mul_pow,wt,←Real.exp_nat_mul,←mul_assoc] at he; exact he
lemma width_le (r : ℝ) (m k : ℕ) (hm : m≤k) : s.width r k ≤ s.width r m := by unfold width; gcongr; exact s.room.le

def restrict {X : Type*} (e : X → I) : Weights (a ∘ e) := {
  τ:=s.τ ∘ e,fee:=s.fee,budget:=s.budget,
  nonneg:=fun i=>s.nonneg (e i),room:=s.room,price:=s.price,moves:=fun i j=>s.moves (e i) (e j)}

def uniform (a : I → Site n) (ε : ℝ) (hε : 0<ε) : Weights a where
  τ _ := 1
  fee := ε
  budget := 1
  nonneg _ := zero_le_one
  price := le_rfl
  room := hε
  moves i j := by simp [wt,(mul_nonneg hε.le (Nat.cast_nonneg (separation (a i) (a j))))]

def spice (m : ℕ) (ε : ℝ) := (m.factorial:ℝ)*Real.exp ε / ε^m
lemma spicy (m : ℕ) {ε x : ℝ} (hε : 0<ε) (hx : 0≤x) : (1+x)^m ≤ spice m ε*Real.exp (ε*x) := by
  have h := Real.pow_div_factorial_le_exp (ε*(1+x)) (by positivity) m
  rw [mul_pow,div_le_iff₀ (by positivity),mul_add,Real.exp_add,mul_one] at h
  rw [spice,div_mul_eq_mul_div,le_div_iff₀ (by positivity)]; linarith only [h]

/-- E τ for separation. Pre- or post-L changes of native lattice for
`moves` need their own proof if the points aren't in the same torus;
weights themselves can be supplied by other constructions too. -/
def polynomial (a : I → Site n) (o : Site n) (q : ℕ) (ε : ℝ) (hε : 0<ε) : Weights a where
  τ i := (1+(separation o (a i):ℝ))^q
  fee := ε
  budget := spice q ε
  nonneg _ := by positivity
  room := hε
  price := by simpa using spicy q hε (le_refl (0:ℝ))
  moves i j := by
    have ht : (separation o (a j) : ℝ) ≤ (separation o (a i):ℝ)+separation (a i) (a j) := by exact_mod_cast separation_triangle o (a i) (a j)
    have hi := Nat.cast_nonneg (α:=ℝ) (separation o (a i)); have hj := Nat.cast_nonneg (α:=ℝ) (separation (a i) (a j))
    calc
      _ ≤ ((1+(separation (a i) (a j):ℝ))*(1+separation o (a i)))^q := by gcongr; nlinarith only [ht,hi,hj]
      _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right (spicy q hε hj) (by positivity)

variable [Fintype I] {A B : Table I} {r C D : ℝ} {l m k : ℕ}
def Costs (r : ℝ) (m : ℕ) (A : Table I) (C : ℝ) := ∀ i, ∑ j, wt (s.width r m) (a i) (a j)*|A i j| ≤ C*s.τ i^m
def Bank (r : ℝ) (m : ℕ) (A : Table I) (C : ℝ) := s.Costs r m A C ∧ s.Costs r m A.transpose C
variable {s}
lemma zero_order (h : Bill a r A C) : s.Bank r 0 A C := by simpa only [Bank,Costs,width,Nat.cast_zero, zero_mul,sub_zero,pow_zero,mul_one] using! h
lemma zero (hc : 0≤C) : s.Bank r k (0:Table I) C := by constructor <;> intro i <;> simpa using mul_nonneg hc (pow_nonneg (s.nonneg i) k)
lemma Bank.mono (h : s.Bank r k A C) (hc : C≤D) : s.Bank r k A D := by
  have he i := mul_le_mul_of_nonneg_right hc (pow_nonneg (s.nonneg i) k)
  exact ⟨fun i => (h.1 i).trans (he i), fun i => (h.2 i).trans (he i)⟩
lemma Bank.slow (h : s.Bank r k A C) {t : ℝ} (ht : t≤r) : s.Bank t k A C := by
  have hh {A : Table I} (h : s.Costs r k A C) : s.Costs t k A C := by
    intro i; apply (Finset.sum_le_sum (fun j _=>?_)).trans (h i)
    unfold wt width; gcongr
  exact ⟨hh h.1,hh h.2⟩
lemma Bank.plus (ha : s.Bank r k A C) (hb : s.Bank r k B D) : s.Bank r k (A+B) (C+D) := by
  have he {A B : Table I} (ha : s.Costs r k A C) (hb : s.Costs r k B D) : s.Costs r k (A+B) (C+D) := by
    intro i; rw [add_mul]; apply le_trans _ (add_le_add (ha i) (hb i)); rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _=> ?_; rw [←mul_add]; exact mul_le_mul_of_nonneg_left (abs_add_le ..) (wt_pos ..).le
  exact ⟨he ha.1 hb.1,he ha.2 hb.2⟩
lemma Bank.transpose (ha : s.Bank r k A C) : s.Bank r k A.transpose C := ⟨ha.2,ha.1⟩
lemma Bank.scale (ha : s.Bank r k A C) (x : ℝ) : s.Bank r k (x • A) (|x| *C) := by
  have he {A : Table I} (h : s.Costs r k A C) : s.Costs r k (x • A) (|x| *C) := fun i=> by
    simpa only [Costs, Finset.mul_sum, Matrix.smul_apply,smul_eq_mul, abs_mul,mul_left_comm (wt ..) |x|,mul_assoc |x| C] using
      mul_le_mul_of_nonneg_left (h i) (abs_nonneg x)
  exact ⟨he ha.1,he ha.2⟩
lemma Bank.neg (ha : s.Bank r k A C) : s.Bank r k (-A) C := by simpa only [neg_one_smul,abs_neg,abs_one,one_mul] using ha.scale (-1)
lemma Costs.prod (ha : s.Costs r l A C) (hb : s.Costs r m B D) (hD : 0≤D) (hk : l+m≤k) (he : 0≤s.width r k) :
    s.Costs r (l+m) (A*B) (s.budget^k*(C*D)) := by
  intro i
  let w (m : ℕ) (i j : I) := wt (s.width r m) (a i) (a j)
  have hh := he.trans (s.width_le _ _ _ hk)
  have hm j x : w (l+m) i j ≤ w (l+m) i x * w m x j := (wt_triangle hh ..).trans (mul_le_mul_of_nonneg_left
      (by unfold w wt; gcongr; exact s.width_le r _ _ (by omega)) (wt_pos ..).le)
  have ht j : w (l+m) i j * wt (m*s.fee) (a i) (a j) = w l i j := by unfold w wt; rw [←Real.exp_add]; unfold width; push_cast; congr 1; ring
  have hg j : w (l+m) i j * s.τ j ^ m ≤ w l i j * (s.budget^k * s.τ i^m) := calc
    _ ≤ w (l+m) i j * ((s.budget^m * wt (m*s.fee) (a i) (a j))*s.τ i^m) := mul_le_mul_of_nonneg_left (s.goes i j m) (wt_pos ..).le
    _ ≤ w (l+m) i j * ((s.budget^k * wt (m*s.fee) (a i) (a j))*s.τ i^m) := by
      gcongr; exact (wt_pos ..).le; exact pow_nonneg (s.nonneg _) _; exact (wt_pos ..).le; exact s.price; omega
    _ = _ := by rw [←ht]; ring
  calc
    _ ≤ ∑ j, ∑ x, (w (l+m) i x * |A i x|)*(w m x j * |B x j|) := by
      refine Finset.sum_le_sum fun j _=> ?_; rw [Matrix.mul_apply]
      apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) (wt_pos ..).le).trans
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun x _=> (by rw [abs_mul]; exact (mul_le_mul_of_nonneg_right (hm j x) (by positivity)).trans_eq (by ring))
    _ ≤ ∑ x,(w (l+m) i x * |A i x|) * (D*s.τ x^m) := by
      rw [Finset.sum_comm]; simp only [← Finset.mul_sum]
      exact Finset.sum_le_sum fun x _=>mul_le_mul_of_nonneg_left (hb x) (mul_nonneg (wt_pos ..).le (abs_nonneg _))
    _ ≤ ∑ x, (w l i x*|A i x|) * (D*s.budget^k*s.τ i^m) := by
      apply Finset.sum_le_sum; intro x _
      calc
        _ = (w (l+m) i x*s.τ x ^ m) * (|A i x| *D) := by ring
        _ ≤ _ := (mul_le_mul_of_nonneg_right (hg x) (by positivity)).trans_eq (by ring)
    _ ≤ _ := by
      rw [←Finset.sum_mul, pow_add]; exact (mul_le_mul_of_nonneg_right (ha i) (mul_nonneg (mul_nonneg hD (pow_nonneg (by linarith [s.price]) _)) (pow_nonneg (s.nonneg _) _))).trans_eq (by ring)
lemma Bank.prod (ha : s.Bank r l A C) (hb : s.Bank r m B D) (hc : 0≤C) (hd : 0≤D) (hk : l+m≤k) (he : 0≤s.width r k) :
    s.Bank r (l+m) (A*B) (s.budget^k*(C*D)) := ⟨ha.1.prod hb.1 hd hk he, by rw [transpose_mul, Nat.add_comm l,mul_comm C]; exact hb.2.prod ha.2 hc (by omega) he⟩
lemma Costs.restrict {Y : Type*} [Fintype Y] (e : Y ↪ I) (ha : s.Costs r k A C) : (s.restrict e).Costs r k (A.submatrix e e) C := by
  intro i; apply le_trans _ (ha (e i)); calc
    _ = ∑ j ∈ Finset.univ.map e,wt (s.width r k) (a (e i)) (a j)*|A (e i) j| := Eq.symm (Finset.sum_map ..)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _=>mul_nonneg (wt_pos ..).le (abs_nonneg _)
lemma Bank.restrict {Y : Type*} [Fintype Y] (e : Y ↪ I) (ha : s.Bank r k A C) : (s.restrict e).Bank r k (A.submatrix e e) C := ⟨ha.1.restrict e,ha.2.restrict e⟩
lemma Costs.here (h : s.Costs r k A C) (i j : I) : wt (s.width r k) (a i) (a j) * |A i j| ≤ C*s.τ i^k :=
    (Finset.single_le_sum (f:=fun j=>wt (s.width r k) (a i) (a j) * |A i j|) (fun _ _=>mul_nonneg (wt_pos ..).le (abs_nonneg _)) (Finset.mem_univ j)).trans (h i)
lemma Costs.entry (h : s.Costs r k A C) (hr : 0≤s.width r k) (i j : I) : |A i j| ≤ C*s.τ i^k :=
    le_trans (le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_exp (mul_nonneg hr (Nat.cast_nonneg _)))) (h.here i j)

lemma from_points {m : ℕ} {b : ℝ} (he : b<r) (hh : Push.Uniform.Multiplicity a m)
    (h : ∀ i j, wt (s.width r k) (a i) (a j)*|A i j| ≤ C*s.τ i^k) (hc : 0≤C) :
    s.Costs b k A (C * (m:ℝ)*Push.Uniform.countCost (r-b)) := by
  intro i
  have heq j : wt (s.width b k) (a i) (a j) = wt (s.width r k) (a i) (a j)*Push.Uniform.Decay (r-b) (a i) (a j) := by unfold wt Push.Uniform.Decay width; rw [←Real.exp_add]; congr 1; ring
  simp_rw [heq,mul_right_comm _ (Push.Uniform.Decay ..)]
  apply le_trans (Finset.sum_le_sum (fun j _=> mul_le_mul_of_nonneg_right (h i j) (Push.Uniform.decay_pos ..).le))
  rw [←Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left (hh.count a (sub_pos.mpr he) _) (mul_nonneg hc (pow_nonneg (s.nonneg i) _))).trans_eq (by ring)

variable {Q : Directions G c → Prop}
lemma share_bank (l : Word G c) (f : Word G c → Word G c → Table I) (hd : ∀ d∈l,Q d)
    (h : ∀ b t : Word G c, b.length+t.length=l.length → (∀ d∈b,Q d) → (∀ d∈t,Q d) → s.Bank r k (f b t) C) :
    s.Bank r k (share l f) (2^l.length*C) := by induction l generalizing f C with
  | nil => simpa only [List.length_nil,pow_zero,one_mul,share] using h [] [] rfl (by simp) (by simp)
  | cons d l ih =>
    rw [List.length_cons,pow_succ,mul_assoc,two_mul C,share]; apply ih _ (fun i hi => hd _ (by simp [hi]))
    have he : Q d := hd _ (by simp)
    intro b t hh hb ht; exact (h (d::b) t (by simp; omega) (by simpa [he] using hb) ht).plus (h b (d::t) (by simp; omega) hb (by simpa [he] using ht))

variable {A B : Field G c I} {U : Config G c} {v : Word G c}
lemma product_bank {j : ℕ} (ha : Good A j U) (hb : Good B j U) (hc : 0≤C) (hd : 0≤D)
    (hle : v.length ≤ j) (hdir : ∀ i∈v,Q i)
    (h : ∀ x : Word G c, x.length≤v.length → (∀ i∈x,Q i) → s.Bank r (l+x.length) (jet x A U) C ∧ s.Bank r (m+x.length) (jet x B U) D)
    (hv : l+m+v.length ≤ k) (he : 0≤s.width r k) : s.Bank r (l+m+v.length) (jet v (fun V => A V*B V) U) (s.pay k*C*D) := by
  rw [jet_prod ha hb hle]
  apply Bank.mono (C:=2^v.length*(s.budget^k*(C*D))) _ ((mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : v.length ≤ k))
    (mul_nonneg (pow_nonneg (by linarith [s.price]) _) (mul_nonneg hc hd))).trans_eq (by unfold pay; ring))
  exact share_bank v _ hdir fun x y hxy hx hy => by
    have hh := ((h x (by omega) hx).1).prod ((h y (by omega) hy).2) hc hd (k:=k) (by omega) he
    rwa [show l+x.length+(m+y.length)=l+m+v.length by omega] at hh
end Weights
end YM.Further.CurvedGaussianJets.Jets

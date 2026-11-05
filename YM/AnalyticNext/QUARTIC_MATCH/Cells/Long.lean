import YM.AnalyticNext.QUARTIC_MATCH.Cells.Homotopy
import YM.Exterior.Complex
import YM.Laurent.Art


/-!
# Width for real unanchored arrays. Single leg estimate

Use pairwise exponential majorant uniform on every translate. When converting to
weighted absolute sums may shrink exponent by a fixed factor. All costs independent
of block size, path cap and Wilson indices (given the strip). Vector coefficients
permitted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.BoxChain
open Lattice Exterior Function Finset Topology Laurent Filter
open scoped Topology BigOperators

variable {I V : Type*}

def move {R : Type*} [AddCommGroup R] (b : Four R) (x : Cell R) : Cell R := (x.1+b,x.2)

def Cohere {R : Type*} [AddCommGroup R] (A : ArrayC I R V) := ∀ (b : Four R) X, A (move b ∘ X)=A X

@[simp] lemma move_zero {R : Type*} [AddCommGroup R] (X : I → Cell R) : move 0 ∘ X=X := funext fun i => by simp [move]
lemma moved {R : Type*} [AddCommGroup R] [DecidableEq I] (b : Four R) (X : I → Cell R) (i : I) (x : Cell R) :
    move b ∘ update X i x = update (move b ∘ X) i (move b x) := by
  funext j; by_cases h : j=i <;> simp [h]

variable [NormedAddCommGroup V]

def cost (σ : ℝ) (x y : Cover) := Real.exp (-σ*size (x-y))

lemma cost_size (σ : ℝ) (x y : Cover) : 0 ≤ cost σ x y := (Real.exp_pos _).le

structure Pricing (A : ArrayC I ℤ V) (σ C : ℝ) : Prop where
  same : Cohere A
  rate : 0 < σ
  cap : 0 ≤ C
  each (X) (i j : I) : ‖A X‖ ≤ C * cost σ (X i).1 (X j).1

variable {A D : ArrayC I ℤ V} {σ η C B : ℝ}
namespace Pricing
lemma widen (h : Pricing A σ C) (hp : 0<η) (hx : η≤σ) (hc : C≤B) : Pricing A η B :=
    ⟨h.same,hp,h.cap.trans hc,fun X i j => (h.each X i j).trans <| by
      unfold cost; gcongr; exact h.cap.trans hc⟩
lemma add (h : Pricing A σ C) (g : Pricing D σ B) : Pricing (A+D) σ (C+B) :=
    ⟨fun b X => congr_arg₂ (·+·) (h.same b X) (g.same b X), h.rate,add_nonneg h.cap g.cap,fun X i j => by
      rw [Pi.add_apply,add_mul]; exact (norm_add_le _ _).trans (add_le_add (h.each X i j) (g.each X i j))⟩
lemma neg (h : Pricing A σ C) : Pricing (-A) σ C := ⟨fun b X => congr_arg Neg.neg (h.same b X),h.rate,h.cap,
    fun X i j => by rw [Pi.neg_apply,norm_neg]; exact h.each X i j⟩
lemma sub (h : Pricing A σ C) (g : Pricing D σ B) : Pricing (A-D) σ (C+B) := sub_eq_add_neg A D ▸ h.add g.neg
lemma zero (h : 0<σ) : Pricing (0 : ArrayC I ℤ V) σ 0 := ⟨fun _ _ => rfl,h,le_rfl,fun _ _ _ => by simp⟩
end Pricing

variable [DecidableEq I] {l j : I}

/-- Per-fixed-mask absolute. -/
def bill (σ : ℝ) := (2*((1+σ)/σ))^(Fintype.card Axis)
lemma accounted {σ : ℝ} (b : Cover) (he : 0 < σ) : RG.SumBudget (fun x => cost σ x b) (bill σ) := by
  obtain ⟨hs,hh,hv⟩ := Width.compactPay (α:=Axis) σ he
  let E := Equiv.subRight b
  exact ⟨fun i => hs _, E.summable_iff.mpr hh, (E.tsum_eq _).le.trans hv⟩
lemma billed (h : 0<σ) : 0 < bill σ := by unfold bill; positivity

lemma Pricing.sum_leg (h : Pricing A σ C) (hj : j≠l) (X : I → Cell ℤ) (S : Finset Axis) :
    Summable fun x : Cover => ‖peek l X A (x,S)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ ((accounted (X j).1 h.rate).2.1.mul_left C)
  intro x; simpa only [peek,update_self, update_of_ne hj] using h.each (update X l (x,S)) l j

/-- Mask changes no cost, a position unit step pays exp(2σ). -/
lemma Pricing.shift (h : Pricing A σ C) (l i j : I) (X : I → Cell ℤ) (S : Finset Axis) (x : Cover)
    (he : size (x-(X l).1)≤1) :
    ‖peek l X A (x,S)‖ ≤ (Real.exp (2*σ)*C) * cost σ (X i).1 (X j).1 := by
  let Z := update X l (x,S)
  have hy (j : I) : size ((Z j).1-(X j).1)≤1 := by
    by_cases H : j=l
    · subst j; simpa only [Z,update_self]
    simp [Z,H,Laurent.size]
  apply (h.each Z i j).trans
  rw [mul_comm _ C,mul_assoc]; apply mul_le_mul_of_nonneg_left _ h.cap
  unfold cost; rw [← Real.exp_add]; refine Real.exp_monotone ?_
  have hw : size ((X i).1-(X j).1)≤size ((Z i).1-(Z j).1)+2 := by
    calc
      _ = size (((Z i).1-(Z j).1) + ((Z j).1-(X j).1) + -((Z i).1-(X i).1)) := by congr 1; abel
      _ ≤ _ := by have hu := size_add ((Z i).1-(Z j).1) ((Z j).1-(X j).1)
                  apply le_trans (size_add _ _); rw [size_neg]
                  have h₁ := hy i; have h₂ := hy j; omega
  have hh : (size ((X i).1-(X j).1):ℝ)≤(size ((Z i).1-(Z j).1):ℝ)+2 := by exact_mod_cast hw
  nlinarith [h.rate]

variable [NormedSpace ℝ V]
lemma norm_sign (S : Finset Axis) (i : Axis) : ‖sign S i‖=1 := by simp [sign,parity]

lemma Cohere.smaller (h : Cohere A) (l : I) : Cohere (lower l A) := by
  intro b X
  rw [lower_at,lower_at]; refine sum_congr rfl fun i _ => ?_
  simp only [sect_at, move, Function.comp_apply]
  split
  · rfl
  have he (x : Cell ℤ) : peek l (move b ∘ X) A (move b x) = peek l X A x := by rw [peek,← moved]; exact h ..
  rw [show (X l).1 + b - step i = (X l).1-step i+b by abel]
  exact congr_arg _ (congr_arg₂ (·-·) (he ((X l).1-step i, _)) (he ((X l).1, insert i (X l).2)))

def debit (σ : ℝ) : ℝ := 8*Real.exp (2*σ)
lemma debit_pos (σ : ℝ) : 0 ≤ debit σ := by unfold debit; positivity

lemma Pricing.smaller (h : Pricing A σ C) (l : I) : Pricing (lower l A) σ (debit σ*C) := by
  refine ⟨h.same.smaller l,h.rate, mul_nonneg (debit_pos _) h.cap,fun X i j => ?_⟩
  let E := (Real.exp (2*σ)*C)*cost σ (X i).1 (X j).1
  have he : ∀ k : Axis, ‖sect k (peek l X A) (X l)‖ ≤ E+E := by
    intro k; rw [sect_at]; split
    · rw [norm_zero]; have ht : 0 ≤ E := mul_nonneg (mul_nonneg (Real.exp_pos _).le h.cap) (cost_size ..); positivity
    rw [norm_smul,norm_sign,one_mul]
    have hx : size ((X l).1-step k-(X l).1) ≤ 1 := by
      rw [sub_right_comm,sub_self,zero_sub,size_neg]; simp [size,apply_ite Int.natAbs]
    exact (norm_sub_le ..).trans (add_le_add (h.shift l i j X _ _ hx)
      (h.shift l i j X _ _ (by simp [Laurent.size])))
  rw [lower_at]; apply ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _ => he i))).trans_eq
  unfold debit E; simp [Axis]; ring

lemma far_triangle (x y z : Cover) : size (x-z) ≤ size (x-y)+size (y-z) := by
  convert size_add (x-y) (y-z) using 2; abel

lemma size_update_le (b x : Cover) (i : Axis) (j : ℤ) (he : (x i-b i).natAbs≤(j-b i).natAbs) :
    size (x-b)≤size (update x i j-b) := by
  apply Finset.sum_le_sum; intro k _
  by_cases h : k=i
  · subst k; simpa
  simp [h]

def operate (u l : I) (i : Axis) (A : ArrayC I ℤ V) (X : I → Cell ℤ) :=
    fillRay (X u).1 i (peek l X A) (X l)

/-- Cost a single primitive call, before polynomial budgets. -/
def overhead (σ : ℝ) := bill (σ/3)
lemma overhead_pos (h : 0<σ) : 0 < overhead σ := billed (by linarith)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [DecidableEq I] in
lemma along_present {b : Cover} (x : Cover) (i : Axis) (S : Finset Axis) (F Q : Cell ℤ → V)
    (h : F ∘ move b = Q) (j : ℤ) : along i (x+b) S F j = along i x S Q (j - b i) := by
  have he : move b (update x i (j-b i),S)=(update (x+b) i j,S) := by
    unfold move; congr 1; ext k; by_cases h : k=i <;> simp [h]
  unfold along; rw [← he,← h]; rfl

lemma Cohere.smooth (hh : Cohere A) (j l : I) (i : Axis) : Cohere (operate j l i A) := by
  intro b X; unfold operate
  have ht : peek l (move b ∘ X) A ∘ move b=peek l X A := by
    funext x; change A (update _ l (move b x)) = _
    rw [← moved]; exact hh ..
  let S := (X l).2
  unfold fillRay; simp only [move,comp_apply]; split
  · simp only [Pi.add_apply]; congr 1
    have he : along i ((X l).1+b) (S.erase i) (peek l (move b ∘ X) A) =
        fun y => along i (X l).1 (S.erase i) (peek l X A) (y - b i) := funext <| along_present _ _ _ _ _ ht
    rw [he,Ray.translate]
  rfl


namespace Pricing
omit [NormedSpace ℝ V] in
/-- Pairwise estimate on farther terms of that line. -/
private lemma atNext (h : Pricing A σ C) (hj : j≠l) (i r : I) (X : I → Cell ℤ) (x : Cover) (S : Finset Axis)
    (ht : size ((X l).1-(X j).1) ≤ size (x-(X j).1)) :
    ‖peek l X A (x,S)‖ ≤ C*cost (σ/4) (X i).1 (X r).1 * cost (σ/3) x (X j).1 := by
  let Z := update X l (x,S)
  let m := size (x-(X j).1)
  have hz := h.each Z l j
  simp only [Z,update_self, update_of_ne hj] at hz
  let d k := size ((X k).1-(X j).1)
  have hx (k : I) : ‖A Z‖ ≤ C*Real.exp (-σ*d k) := by
    by_cases hg : k=l
    · subst k
      apply hz.trans; unfold cost d; apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) h.cap; exact mul_le_mul_of_nonpos_left (Nat.cast_le.mpr ht) (neg_nonpos.mpr h.rate.le)
    simpa only [d,cost, show Z k = _ from (update_of_ne hg _ _ : Z k = X k),
      show Z j = X j from update_of_ne hj _ _] using h.each Z k j
  let N := max (max (d i) (d r)) m
  have hy : ‖A Z‖≤ C * Real.exp (-σ*N) := by
    unfold N; rw [max_def]; split
    · exact hz
    rw [max_def]; split
    · exact hx r
    exact hx i
  apply hy.trans; rw [mul_assoc,cost,cost,← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) h.cap
  have h₁ : size ((X i).1-(X r).1) ≤ 2*N := by
    have hl : size ((X j).1-(X r).1)=d r := by rw [← size_neg ( (X j).1-_),neg_sub]
    have he := far_triangle (X i).1 (X j).1 (X r).1
    rw [hl] at he
    change _ ≤ d i+d r at he
    unfold N; omega
  have hn : 0 < σ := h.rate
  have hp : (m:ℝ)≤N := Nat.cast_le.mpr (le_max_right ..)
  have hi : (size ((X i).1-(X r).1):ℝ)≤ 2*(N:ℝ) := by exact_mod_cast h₁
  change -σ*↑N ≤ _ + -(σ/3)*m
  have : 0 ≤ (N:ℝ) := by positivity
  nlinarith

theorem fills (h : Pricing A σ C) (hj : j≠l) (a : Axis) :
    Pricing (operate j l a A) (σ/4) (overhead σ * C) := by
  have he := h.rate
  refine ⟨h.same.smooth j l a,by positivity,mul_nonneg (overhead_pos he).le h.cap,?_⟩
  intro X i k
  let p := cost (σ/4) (X i).1 (X k).1
  unfold operate fillRay; split
  · let R := along a (X l).1 (((X l).2).erase a) (peek l X A)
    let b := (X j).1 a; let f := (X l).1 a
    let U m := update (X l).1 a m
    have hx (m : ℤ) (h : (f-b).natAbs ≤ (m-b).natAbs) : size ((X l).1-(X j).1) ≤
        size (U m-(X j).1) := size_update_le _ _ _ _ h
    have hh (m : ℤ) (ha : (f-b).natAbs ≤ (m-b).natAbs) : ‖R m‖ ≤ C*p*cost (σ/3) (U m) (X j).1 :=
      atNext h hj i k X _ _ (hx _ ha)
    have ht : Injective U := fun j k h => by simpa [U] using congr_fun h a
    let M y := cost (σ/3) y (X j).1
    have hb := accounted (X j).1 (show 0<σ/3 by linarith)
    have hu : Summable M := hb.2.1
    have hr : 0 ≤ C*p := mul_nonneg h.cap (cost_size ..)
    have hy (G : ℤ → V) (hg : ∀ i, ‖G i‖ ≤ C*p*M (U i)) : ‖∑' i,G i‖ ≤ overhead σ*C*p := by
      have ho := (hu.comp_injective ht).mul_left (C*p)
      have hs := Summable.of_nonneg_of_le (fun i => norm_nonneg (G i)) hg ho
      refine ((norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hg ho)).trans ?_
      change (∑' x,(C*p)*M (U x)) ≤ _
      rw [tsum_mul_left,show _*C*p=C*p*overhead σ by ring]
      exact mul_le_mul_of_nonneg_left ((tsum_comp_le_tsum_of_inj hu (fun i => cost_size ..) ht).trans hb.2.2) hr
    rw [norm_smul,norm_sign,one_mul]; unfold Ray.solution; split
    · rename_i hm
      unfold Ray.rest; apply hy; intro m; split
      · rename_i hz; change b≤f at hm; change f<m at hz; exact hh m (by omega)
      rw [norm_zero]; exact mul_nonneg hr (cost_size ..)
    rename_i hm; rw [norm_neg]; unfold Ray.head; apply hy; intro m; split
    · rename_i hz; change ¬ b≤f at hm; change m≤f at hz; exact hh m (by omega)
    rw [norm_zero]; exact mul_nonneg hr (cost_size ..)
  rw [norm_zero]; exact mul_nonneg (mul_nonneg (overhead_pos he).le h.cap) (cost_size ..)
end Pricing
end YM.AnalyticNext.QuarticMatch.BoxChain

import YM.MultiNext.VACUUM_STABILITY.Words


set_option warningAsError false

/-!
# Root prices on the actual 4-tori

Converts per-anchor prices of the log elimination / local placements to true hit prices at all
points. Count wrapping supports too, independent of period. Exponent gap five chosen for simple
constants. Only one-time, inside the step before successive mergers.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi.Vacuum.Hits
open RG Lattice Wilson Filter Finset Function MeasureTheory Text  Corona
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I : Type*} {n : Side}

def stride (M : ℕ) := 8*(M+1)

lemma cover_pos (X : Support n) (M : ℕ) (hh : X.Nonempty) : 0 < coverNumber M X := by
  apply Nat.pos_of_ne_zero; intro he
  have hs := Corona.pays X M; rw [he,zero_mul] at hs
  exact ((Finset.card_pos.mpr hh).not_ge hs)

lemma distance (X : Support n) (M : ℕ) {x y : Site n} (hx : x ∈ X) (hy : y ∈ X) :
    separation x y ≤ coverNumber M X * stride M := by
  refine (Corona.extent X M hx hy).trans ?_
  have ht := cover_pos X M ⟨x,hx⟩
  unfold stride; nlinarith

def commission {n : Side} (M : ℕ) (x y : Site n) := Real.exp (-5*((separation x y/stride M:ℕ):ℝ))

def toll (M : ℕ) := 2*(3*(stride M:ℝ))^4

lemma toll_pos (M : ℕ) : 0 < toll M := by unfold toll stride; positivity

lemma tariffs {n : Side} (M : ℕ) (x : Site n) : ∑ y : Site n, commission M x y ≤ toll M := by
  let K := stride M; have hk : 1 ≤ K := by unfold K stride; omega
  let t := fun y => separation x y / K
  let S (v : ℕ) := Finset.univ.filter (fun y : Site n => t y = v)
  have ht (v : ℕ) : (S v).card ≤ (3*K*(v+1))^4 := by
    have hh : S v ⊆ halo ((v+1)*K) {x} := by
      intro i hi; have h := (mem_filter.mp hi).2; apply halo_spec.mpr
      exact ⟨x,by simp,le_of_lt ((Nat.div_lt_iff_lt_mul hk).mp (by change t _ < _; omega))⟩
    refine (card_le_card hh).trans ((Corona.halo_size ..).trans ?_); rw [card_singleton,one_mul]
    gcongr; nlinarith
  have hE : Real.exp (-5) ≤ 1/32 := by
    have h : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    rw [Real.exp_neg,inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have he := pow_le_pow_left₀ (show (0:ℝ) ≤ 2 by norm_num) h 5; rw [← Real.exp_nat_mul] at he; norm_num at *; exact he
  let W := (3*(stride M:ℝ))^4
  have hn : 0 ≤ W := by unfold W; positivity
  have hC (v : ℕ) : (∑ i∈S v, commission M x i) ≤ W * (1/2:ℝ)^v := by
    have hv i (hi : i∈S v) : commission M x i = Real.exp (-5) ^ v := by
      unfold commission; rw [show separation x i/stride M=v from (mem_filter.mp hi).2,← Real.exp_nat_mul,mul_comm]
    calc
      _ = ((S v).card:ℝ) * Real.exp (-5) ^ v := by
        simp only [← nsmul_eq_mul, ← sum_const]; exact sum_congr rfl hv
      _ ≤ ((3*K*((v:ℝ)+1))^4) * Real.exp (-5) ^ v := by
        gcongr; exact_mod_cast ht v
      _ ≤ ((3*K*(2:ℝ)^v)^4) * Real.exp (-5) ^ v := by
        gcongr; exact_mod_cast Nat.lt_two_pow_self (n:=v)
      _ = W * (16*Real.exp (-5))^v := by
        rw [mul_pow,←pow_mul, Nat.mul_comm v, pow_mul]
        conv_rhs => rw [mul_pow]
        unfold W K
        ring
      _ ≤ _ := by gcongr; linarith
  let B := (Finset.univ : Finset (Site n)).image t
  calc
    _ = ∑ v ∈ B, ∑ i ∈ S v, commission M x i :=
      (sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem t hi) _).symm
    _ ≤ ∑ v ∈ B, W * (1/2:ℝ)^v := sum_le_sum fun v _ => hC v
    _ ≤ W * 2 := by
      rw [← mul_sum]; apply mul_le_mul_of_nonneg_left _ hn
      exact (summable_geometric_two.sum_le_tsum B (by intros; positivity)).trans_eq tsum_geometric_two
    _ = _ := mul_comm ..

lemma exempt (X : Support n) (x y : Site n) (h : x ∈ X) (hh : y ∈ X) (M : ℕ) (N : ℕ)
    (hl : coverNumber M X ≤ N) (a : ℝ) (ha : 0 ≤ a) : Real.exp (a*coverNumber M X) ≤
    commission M x y * Real.exp ((a+5)*N) := by
  unfold commission; rw [← Real.exp_add]; apply Real.exp_monotone
  have hx := Nat.le_trans (distance X M h hh) (Nat.mul_le_mul_right (stride M) hl)
  have he : 0 < stride M := by unfold stride; omega
  have hs : (((separation x y/stride M:ℕ):ℝ)) ≤ N := by
    exact_mod_cast (Nat.le_trans (Nat.div_le_div_right hx) ((Nat.mul_div_left N he).le) : _)
  have ht := mul_le_mul_of_nonneg_left (show (coverNumber M X:ℝ) ≤ N from by exact_mod_cast hl) ha
  linarith

/-- No grouping by spatial support in the series. Disjoint-anchor price alone
at stronger exponent suffices for a hit price. -/
def PlacedCost (o : I → Site n) (q : I → ℕ) (g : I → ℝ) (a c : ℝ) := ∀ x : Site n,
    SumBudget (fun i => if o i=x then g i * Real.exp (a*q i) else 0) c

lemma everyone {o : I → Site n} {q : I → ℕ} {g : I → ℝ} {M : ℕ} {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hG : ∀ i, 0 ≤ g i) (X : I → Support n) (hX : ∀ i, o i∈X i) (hb : ∀ i, coverNumber M (X i) ≤ q i)
    (hh : PlacedCost o q g (a+5) c) : Ac.Hit X M g a (toll M*c) := by
  intro y
  let k (x : Site n) i := commission M y x * (if o i=x then g i * Real.exp ((a+5)*q i) else 0)
  have h x : SumBudget (k x) (commission M y x*c) := permit_mul (hh _) (Real.exp_pos _).le
  have hK : SumBudget (fun i => ∑ x, k x i) (toll M*c) := by
    refine ⟨fun i => sum_nonneg fun j _ => (h j).1 i,summable_sum fun j _ => (h j).2.1,?_⟩
    rw [Summable.tsum_finsetSum (fun i _ => (h i).2.1)]
    exact (sum_le_sum fun i _ => (h i).2.2).trans (by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right (tariffs ..) hc)
  refine Absolute.compare hK ?_ ?_
  · intro i; split
    · exact mul_nonneg (hG i) (Real.exp_pos _).le
    exact le_rfl
  intro i; split
  · rename_i he
    apply le_trans _ (single_le_sum (f:=fun j => k j i) (fun j _ => (h j).1 i) (mem_univ (o i)))
    unfold k; rw [if_pos rfl,mul_left_comm]
    exact mul_le_mul_of_nonneg_left (exempt (X i) y (o i) he (hX _) M _ (hb i) a ha) (hG i)
  exact hK.1 i
end YM.Multi.Vacuum.Hits

import YM.Bid.Fuels
import YM.Corona.Fill

/-! Geometry for summing response jets independently of number of sites. -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Wilson Lattice Function Filter Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators

/-- Cost side uses native, not covering-space distance between copy centers. -/
def Spaced {V : Type*} {n : Side} (f : V → Site n) (B : ℕ) :=
    ∀ i j,i≠j → B^2 ≤ separation (f i) (f j)

lemma Spaced.injective {V : Type*} {n : Side} {B : ℕ} {f : V → Site n} (h : Spaced f B) (hp : 0 < B) :
    Injective f := by
  intro i j he
  by_contra H
  have hz := h i j H; rw [he,separation_self] at hz
  exact (pow_pos hp 2).not_ge hz

namespace Convoy
variable {V : Type*} [Fintype V] [DecidableEq V] {n : Side} {B : ℕ} (f : V → Site n)

def linkFare (f : V → Site n) (B : ℕ) (x y : V) := Real.exp (- (separation (f x) (f y) : ℝ)/(256*B))

private lemma outlay (hh : Spaced f B) (hB : 8 ≤ B) (p : V) (hu : Real.exp (- (B:ℝ)/256) ≤ 1/32) :
    (∑ i ∈ Finset.univ.erase p, linkFare f B p i) ≤
      (5 * (B:ℝ)^2)^4 * Real.exp (- (B:ℝ)/256) * 2 := by
  let S := Finset.univ.erase p
  let d (i : V) := separation (f p) (f i)
  let t (i) := d i/(B^2)-1
  let L k := S.filter (fun i => t i=k)
  let K (k : ℕ) := (k+2)*B^2
  have ht : 0 < B := Nat.pos_of_ne_zero (by omega)
  have he (i) (k) (hk : i∈L k) : (k+1)*B^2 ≤ d i ∧ d i ≤ K k := by
    obtain ⟨hi,he⟩ := mem_filter.mp hk
    have hv := hh p i (Ne.symm (mem_erase.mp hi).1)
    have h : 1 ≤ d i / B^2 := (Nat.le_div_iff_mul_le (by positivity : 0<B^2)).mpr
      (by simpa only [one_mul] using hv)
    unfold t at he
    have hl : d i / B^2=k+1 := by omega
    constructor
    · rw [← hl]; exact Nat.div_mul_le_self ..
    apply Nat.le_of_lt
    change _ < (k+2)*B^2
    exact (Nat.div_lt_iff_lt_mul (by positivity)).mp (by omega)
  have hz (k) : (L k).card ≤ (5*B^2*(k+1))^4 := by
    calc
      _ ≤ (halo (K k) {f p}).card := card_le_card_of_injOn f (fun i hi =>
        halo_spec.mpr ⟨f p,by simp,(he _ _ hi).2⟩) (hh.injective ht).injOn
      _ ≤ _ := (Corona.halo_size ..).trans (by
        rw [card_singleton,one_mul]; apply pow_le_pow_left₀ (by omega)
        unfold K; nlinarith)
  let q := Real.exp (- (B:ℝ)/256)
  let W := (5*(B:ℝ)^2)^4*q
  have hq : 0 < q := Real.exp_pos _
  have hf (i : V) (k) (hk : i ∈ L k) : linkFare f B p i ≤ q^(k+1) := by
    unfold linkFare q
    rw [← Real.exp_nat_mul]
    refine Real.exp_monotone ?_
    have hx : ((↑(k+1:ℕ):ℝ)*(B:ℝ)^2) ≤ (d i:ℝ) := by exact_mod_cast (he i k hk).1
    apply (div_le_iff₀ (by positivity)).2
    change - (d i:ℝ) ≤ _
    nlinarith
  have hC (k) : (∑ i∈L k, linkFare f B p i) ≤ W * ((1/2:ℝ)^k) := by
    calc
      _ ≤ ∑ _i∈L k,q^(k+1) := sum_le_sum fun i hi => hf i k hi
      _ ≤ ((5*(B:ℝ)^2 * ((k:ℝ)+1))^4)*q^(k+1) := by
        rw [sum_const,nsmul_eq_mul]; gcongr
        exact_mod_cast hz k
      _ ≤ _ := by
        have hy : (k:ℝ)+1 ≤ (2:ℝ)^k := by exact_mod_cast Nat.lt_two_pow_self (n:=k)
        calc
          _ ≤ ((5*(B:ℝ)^2 * (2:ℝ)^k)^4)*q^(k+1) := by gcongr
          _ = W * (((2:ℝ)^4*q)^k) := by
            unfold W; rw [mul_pow, show ((2:ℝ)^k)^4 = ((2:ℝ)^4)^k by rw [← pow_mul, ← pow_mul, Nat.mul_comm],
              mul_pow]; ring
          _ ≤ _ := by
            change q ≤ _ at hu
            apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0 ≤ 2^4*q)
              (by linarith) _) (by unfold W; positivity)
  let M := S.image t
  calc
    _ = ∑ k∈M, ∑ i∈L k, linkFare f B p i :=
      (sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem t hi) _).symm
    _ ≤ ∑ k∈M, W * ((1/2:ℝ)^k) := sum_le_sum fun i _ => hC i
    _ ≤ W*2 := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by unfold W; positivity)
      exact (summable_geometric_two.sum_le_tsum M (by intros; positivity)).trans_eq tsum_geometric_two

lemma launch : ∀ᶠ B : ℕ in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V] (n : Side)
    (f : V → Site n), Spaced f B → ∀ p,
      (∑ i ∈ Finset.univ.erase p, linkFare f B p i) ≤ 1/16 := by
  have hs : Tendsto (fun B : ℕ => (B:ℝ)/256) atTop atTop := Tendsto.atTop_div_const (by norm_num)
    tendsto_natCast_atTop_atTop
  have he : Tendsto (fun B : ℕ => Real.exp (- (B:ℝ)/256)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
  have hpow := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 8 |>.comp hs
  have hv : Tendsto (fun B : ℕ => (5 * (B:ℝ)^2)^4 * Real.exp (- (B:ℝ)/256)*2) atTop (𝓝 0) := by
    let C : ℝ := 2*256^8*5^4
    convert (hpow.const_mul C) using 1
    · ext B; simp only [Function.comp_apply, neg_div]; unfold C; ring
    rw [mul_zero]
  filter_upwards [eventually_ge_atTop 8, he.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/32)),
    hv.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/16))] with B hb H ℓ V _ _ n f hh p
  exact (outlay f hh hb p H).trans ℓ
end Convoy
end YM.Multi

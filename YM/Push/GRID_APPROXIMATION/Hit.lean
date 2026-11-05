import Mathlib.RingTheory.Nilpotent.Exp
import YM.Ac.Tree
import YM.Corona.Fit
import YM.Next.EXTRACTION.Tails
import YM.Work.B04

/-!
# Convert rooted mark costs to required k-birth hit bounds

Use ONE exponential reserve in cover units; price C polynomial in B and
independent of period, may be charged at delays. For use buying `Ac.forest`
which charges another reserve. Need anchors actually contained in the same
support; doesn't count erased terms with too small fictive support there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox.Attach
open RG Lattice Wilson Lattice.Corona Cells MeasureTheory Measure Function Filter Finset Ac Marker Overlay 
open scoped Topology BigOperators
variable {G : Gauge} {n : Side} {V ι : Type*} [Fintype V]

-- Price not chosen sharp.
def leg (B : ℕ) := 6*B+2
lemma leg_pos (B : ℕ) : 0<leg B := by unfold leg; omega

def polyExp (i : ℕ) : ℝ := (((i+1):ℕ):ℝ)^4 * Real.exp (- (i:ℝ))
def hitConstant (B : ℕ) := (((leg B*2+1 :ℕ):ℝ)^4)*(∑' i:ℕ, polyExp i)

lemma polyExp_pos (i : ℕ) : 0<polyExp i := by unfold polyExp; positivity
lemma polyExp_summable : Summable polyExp := by
  have he := Real.summable_pow_mul_exp_neg_nat_mul 4 (by norm_num : (0:ℝ) < 1)
  have ht := (summable_nat_add_iff 1).mpr he
  refine Summable.congr (ht.mul_right (Real.exp 1)) ?_
  intro i
  rw [mul_assoc,← Real.exp_add]; unfold polyExp; congr 2; push_cast; ring


lemma distance_charge (A : Support n) (B : ℕ) (x y : Site n) (hx : x∈A) (hy : y∈A) :
    separation x y/leg B ≤ coverNumber B A := by
  have he := Corona.extent A B hx hy
  have hc : 0<coverNumber B A := Nat.pos_of_ne_zero fun h => by
    have ht := pays A B; rw [h,zero_mul] at ht
    exact Nat.not_le_of_gt (Finset.card_pos.mpr ⟨_,hx⟩) ht
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (leg_pos B)).mpr
  unfold leg; nlinarith

lemma all_marks (o : V → Site n) (ho : Injective o) (x : Site n) (B : ℕ) :
    ∑ i, Real.exp (- ((separation x (o i)/leg B:ℕ):ℝ)) ≤ hitConstant B := by
  classical
  let L := leg B; let p (i : V) := separation x (o i)/L
  let s := Finset.univ.image p
  let f (i : ℕ) := Real.exp (-(i:ℝ))
  have he (j : ℕ) : ∑ i ∈ Finset.univ.filter (fun i => p i=j), f (p i) ≤
      (((L*2+1:ℕ):ℝ)^4)*polyExp j := by
    let T := Finset.univ.filter (fun i => p i=j)
    let r := (j+1)*L
    have hT : T.image o ⊆ halo r ({x}:Support n) := by
      intro y hy; obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      have ht := (mem_filter.mp hi).2
      refine halo_spec.mpr ⟨x,mem_singleton_self _,?_⟩
      have hp : p i < j+1 := ht ▸ Nat.lt_succ_self _
      exact ((Nat.div_lt_iff_lt_mul (leg_pos B)).mp hp).le
    have hw := (card_le_card hT).trans (halo_size {x} r)
    rw [card_singleton, one_mul, Finset.card_image_of_injective _ ho] at hw
    have hg : T.card ≤ (j+1)^4*(L*2+1)^4 := hw.trans (by rw [←mul_pow]; gcongr; dsimp only [r]; nlinarith)
    calc
      _ = ∑ _i∈T,f j := Finset.sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
      _ = T.card*f j := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (((j+1)^4*(L*2+1)^4:ℕ):ℝ)*f j := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; exact_mod_cast hg
      _ = _ := by unfold f polyExp; push_cast; ring
  change ∑ i,f (p i) ≤ _
  calc
    _ = ∑ j ∈ s, ∑ i ∈ Finset.univ.filter (fun i => p i=j), f (p i) := by
      rw [Finset.sum_fiberwise_eq_sum_filter univ s p (fun i => f (p i))]
      have ht : univ.filter (fun i => p i∈s)=univ := by ext i; simp [s]
      rw [ht]
    _ ≤ ∑ j∈s, (((L*2+1:ℕ):ℝ)^4)*polyExp j := Finset.sum_le_sum fun j _ => he j
    _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left
                     (polyExp_summable.sum_le_tsum s fun i _ => (polyExp_pos i).le) (by positivity)

/-- Abstract conversion. Index can be infinite. Require one cover reserve.
No contribution from terms identically zero. -/
lemma root_to_hit (X : ι → Support n) (B : ℕ) (o : V → Site n) (h : Injective o)
    (f : ι → ℝ) (hf : ∀ i,0≤f i) [DecidableEq V] (v : ι → Finset V) (a γ : ℝ) (hγ : 0≤γ)
    (he : ∀ i,0<f i → ∃ j∈v i, o j∈X i)
    (hr : ∀ j, SumBudget (fun i => if j∈v i then f i*Real.exp ((a+1)*coverNumber B (X i)) else 0) γ) :
    Hit X B f a (hitConstant B*γ) := by
  classical
  intro x
  let C i := if x∈X i then f i*Real.exp (a*coverNumber B (X i)) else 0
  let w (i : V) := Real.exp (-((separation x (o i)/leg B:ℕ):ℝ))
  let D (i : V) j := if i∈v j then f j*Real.exp ((a+1)*coverNumber B (X j)) else 0
  have hg (i : V) j : 0≤ w i*D i j := mul_nonneg (Real.exp_pos _).le ((hr i).1 j)
  have hx j : 0≤ C j := by unfold C; split; exacts [mul_nonneg (hf j) (Real.exp_pos _).le,le_rfl]
  have hm j : C j ≤ ∑ i : V,w i*D i j := by
    by_cases hu : x∈X j ∧ 0<f j
    · obtain ⟨i,hi,hp⟩ := he j hu.2
      apply le_trans _ (single_le_sum (fun i _ => hg i j) (mem_univ i))
      unfold C D w; rw [if_pos hu.1,if_pos hi,mul_left_comm,← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (hf j)
      apply Real.exp_monotone; have hn := distance_charge _ B _ _ hu.1 hp
      have hb : (((separation x (o i)/leg B):ℕ):ℝ) ≤ coverNumber B (X j) := by exact_mod_cast hn
      linarith
    have h0 : C j=0 := by
      unfold C; split
      next he => rw [show f j=0 by specialize hf j; push Not at hu; exact le_antisymm (hu he) hf,zero_mul]
      next he => exact rfl
    rw [h0]; exact Finset.sum_nonneg fun i _ => hg i j
  have hsum (s : Finset ι) : ∑ i∈s,C i ≤ hitConstant B*γ := by
    refine (Finset.sum_le_sum fun i _ => hm i).trans ?_
    rw [Finset.sum_comm]
    apply le_trans _ (mul_le_mul_of_nonneg_right (all_marks o h x B) hγ)
    rw [Finset.sum_mul]; refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left
      ((((hr i).2.1).sum_le_tsum s (fun j _ => (hr i).1 j)).trans (hr i).2.2) (Real.exp_pos _).le
  have hS := summable_of_sum_le hx hsum
  exact ⟨hx,hS,hS.tsum_le_of_sum_le hsum⟩
end YM.Push.GridApprox.Attach

import YM.Shoot.Reach

/-!
# Conditional one-family production

No claims that an Issues for any family exists.

History retains EXACTLY
one path; actual RG can depend on N,R even at level m=0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG.Shoot
open Lattice Supply Wilson Filter Set Function
open scoped Matrix.Norms.Frobenius BigOperators ContDiff Topology

variable {G : Gauge} {a : Levels G}

private def βCost (a : Levels G) : ℕ → ℝ
  | 0 => 0
  | m+1 => βCost a m+(a.params (m+1)).drift

lemma trajectory (H : History G) (hh : ∀ i j, H.β i j 0=H.levels.clock.bar)
    (ht : ∀ N p j, j<N → H.Transfer N p j) : H.Running := by
  let A := H.levels.clock
  have hd (N p i : ℕ) (hi : i≤N) : |H.β N p i-A.hatBeta i|≤βCost H.levels i := by
    induction i with
    | zero => simp [hh,A,Calendar.hatBeta,βCost]
    | succ i ih =>
      calc
        _ = |(H.β N p i-A.hatBeta i)+(H.β N p (i+1)-H.β N p i-G.slopeConstant*Real.log (H.S.block i).val)| := by
          congr 1; unfold Calendar.hatBeta; rw [Schedule.scale_succ]; unfold A History.S Levels.S; ring
        _ ≤ _ := (abs_add_le ..).trans (add_le_add (ih (le_trans (Nat.le_succ _) hi)) ((ht N p i hi).2))
  intro ε he
  have hh' : Tendsto (fun m => ((A.J (m+1):ℝ)^2)⁻¹) atTop (𝓝 0) := by
    have hz := H.levels.fits.deep.comp (tendsto_add_atTop_nat 1)
    exact tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (n:=2) (by decide)).comp (tendsto_natCast_atTop_atTop.comp hz))
  obtain ⟨j,hj⟩ := eventually_atTop.mp (hh'.eventually (ge_mem_nhds (half_pos he)))
  have hu (i : ℕ) (hi : j ≤ i) : βCost H.levels i ≤ βCost H.levels j + (ε/2)*(H.S.scale i-H.S.scale j) := by
    induction i,hi using Nat.le_induction with
    | base => rw [sub_self,mul_zero,add_zero]
    | succ i hi ih =>
      have hg : 0 < Real.log (H.S.block i).val := Real.log_pos (by
        have H0 := H.S.block_large i
        exact_mod_cast (show 1 < (H.S.block i).val from lt_of_lt_of_le (by norm_num) H0))
      have hy := (div_le_iff₀ hg).mp ((H.levels.fits.driftSmall i).trans (hj i hi))
      rw [βCost,Schedule.scale_succ]; linarith
  have hb := (H.S.divergent.const_mul_atTop (half_pos he)).eventually_ge_atTop (βCost H.levels j)
  filter_upwards [eventually_ge_atTop j,hb] with i hi hz
  intro N p hn
  apply (hd N p i hn).trans ((hu i hi).trans ?_)
  have hb : βCost H.levels j ≤ (ε/2)*H.S.scale i := hz
  nlinarith [mul_nonneg he.le (scale_nn H.levels j)]

/-- Invoke this instead of choosing `H` repeatedly inside client estimates. -/
def Recipe.make (_ : Recipe a) (T : ℕ → ∀ p, Trail a p) : History G := ⟨a,T⟩

namespace Recipe
variable (R : Recipe a)

def Stays (T : ℕ → ∀ p, Trail a p) := ∀ N p : ℕ, Competes R p N 0 (T N p)

/-- Concretizes assembly of histories: every object is tied to the same
represented trajectory. Levels not inferred; no forgetting extra stationarity
when rebasing lower demands.
-/
lemma races (h : G.Simple) (H : ∀ N p, R.Issues N p) (hA : Drifting a) :
    ∃ T, R.Stays T ∧ (R.make T).Selected := by
  choose f hf hZ using fun N p => successful p N (H N p) h hA
  let X := R.make f
  have he (N p m : ℕ) (hm : m≤N) : Lives R N m p (f N p m) := ((hf N p).prices m (Nat.zero_le _) hm).1
  have ht (N p m) (hm : m<N) : X.Transfer N p m :=
    ⟨((hf N p).persists m (Nat.zero_le _) hm).link, ((hf N p).persists m (Nat.zero_le _) hm).drift⟩
  refine ⟨f,hf,?_⟩
  exact {
    path_shared := fun N p q m hm ↦ (he N p m hm).path.trans (he N q m hm).path.symm
    represents := fun N p m hm ↦ ⟨(he N p m hm).point, (he N p m hm).clip,
      (he N p m hm).valid, ((hf N p).prices m (Nat.zero_le _) hm).2⟩
    starts := fun N p ↦ ⟨(hf N p).fromTop.scalars,(hf N p).fromTop.raw⟩
    steps := ht
    reaches := hZ
    running := trajectory X hZ ht }
end Recipe
end YM.RG.Shoot

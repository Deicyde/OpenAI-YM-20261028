import YM.Extra.MULTISOURCE_TRAJECTORIES.Probes
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Filters
import YM.Push.CORRECTED_COLUMNS.Program
import YM.Push.FINITE_DETECTION.Variables
import YM.Push.STATIONARY_UNIFORM.Calculus

/-!
# Affording  at the actual geometry

Variable positions and chart sizes; a polynomial in those *independent*
inputs. First, even prices for noncommuting powers without paying exponential
in the slot paths. This is still local, do not spend on any remainder!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift
open Filter Function Set Lattice Wilson Labels RG Cells Source Source.Drops Extraction
open Push.Uniform Push.Corrected Push.CutoffProjectors
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

-- Use only at 1≤x. Loose enough to apply before h,θ.
structure Fund where
  base : ℝ
  height : ℕ
  effective : 1 ≤ base

namespace Fund
variable (Q : Fund)
def rents (R : ℝ) := Q.base * R^Q.height
lemma rated {R : ℝ} (h : 1 ≤ R) : 1 ≤ Q.rents R := one_le_mul_of_one_le_of_one_le Q.effective (one_le_pow₀ h)
lemma gain {R : ℝ} (h : 1 ≤ R) : 0 < Q.rents R := zero_lt_one.trans_le (Q.rated h)

def flat (c : ℝ) : Fund := ⟨max 1 c,0,le_max_left ..⟩
def first : Fund := ⟨1,1,le_rfl⟩
lemma cash (c x : ℝ) : c ≤ (flat c).rents x := by simp [rents,flat]
@[simp] lemma invested (x : ℝ) : first.rents x=x := by simp [first,rents]

def bump (a b : Fund) : Fund := ⟨a.base+b.base, a.height+b.height,le_add_of_le_of_nonneg a.effective (zero_le_one.trans b.effective)⟩
def twin (a b : Fund) : Fund := ⟨a.base*b.base, a.height+b.height,one_le_mul_of_one_le_of_one_le a.effective b.effective⟩
def lots (a : Fund) (n : ℕ) : Fund := ⟨a.base^n,a.height*n,one_le_pow₀ a.effective⟩

lemma daily (a b : Fund) (x : ℝ) (h : 1 ≤ x) : a.rents x + b.rents x ≤ (bump a b).rents x := by
  unfold rents; simp only [bump,add_mul]; refine add_le_add ?_ ?_
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h (by omega)) (zero_le_one.trans a.effective)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h (by omega)) (zero_le_one.trans b.effective)
@[simp] lemma family (a b : Fund) (x : ℝ) : (twin a b).rents x=a.rents x*b.rents x := by unfold twin rents; simp only [pow_add]; ring
@[simp] lemma dues (a : Fund) (x : ℝ) (n : ℕ) : (lots a n).rents x=(a.rents x)^n := by simp [lots,rents,pow_mul,mul_pow]



end Fund

namespace Growth
open Fund
variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing X] [NormedAlgebra ℝ X] {f g : E → X} {n : ℕ}

lemma limited {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (h : ContDiffAt ℝ ω f x) (n : ℕ) : ∃ b : Fund, ∀ R : ℝ, 1 ≤ R → Allows n f x (b.rents R) := by
  obtain ⟨c,-,H⟩ := exists_allows (s:={x}) isCompact_singleton (fun y hy => (mem_singleton_iff.mp hy).symm ▸ h) n
  exact ⟨flat c,fun R _ => (H x (mem_singleton x)).mono (cash c R)⟩
lemma combines (n : ℕ) (a b : Fund) : ∃ c : Fund, ∀ R : ℝ, 1 ≤ R →
    composeCost n (a.rents R) (b.rents R) ≤ c.rents R := by
  refine ⟨twin (twin (flat (n.factorial:ℝ)) a) (lots (bump (flat 1) b) n),fun R h => ?_⟩
  rw [family,family,dues]; unfold composeCost
  refine mul_le_mul ?_ ?_ (pow_nonneg (add_nonneg zero_le_one (gain b h).le) _) (mul_nonneg ((Fund.flat _).gain h).le (a.gain h).le)
  · exact mul_le_mul_of_nonneg_right (cash _ _) (a.gain h).le
  exact pow_le_pow_left₀ (add_nonneg zero_le_one (gain b h).le) ((add_le_add_left (cash 1 _) _).trans (daily _ _ R h)) _

private lemma local_le (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f*g) 0‖ ≤ ∑ i ∈ Finset.range (n+1),
      (n.choose i:ℝ) * ‖iteratedFDeriv ℝ i f 0‖* ‖iteratedFDeriv ℝ (n-i) g 0‖ := by
  obtain ⟨s,hx,ho,hf'⟩ := open_patch hf
  obtain ⟨t,hy,hp,hg'⟩ := open_patch hg
  have hm : 0 ∈ s∩t := ⟨hx,hy⟩
  have H := norm_iteratedFDerivWithin_mul_le (hf'.mono inter_subset_left) (hg'.mono inter_subset_right) (ho.inter hp).uniqueDiffOn hm (n:=n) le_top
  change ‖iteratedFDerivWithin ℝ n (f*g) (s∩t) 0‖ ≤ _ at H
  simpa only [iteratedFDerivWithin_of_isOpen _ (ho.inter hp) hm] using H

private lemma product_step {a b : ℝ} (hf : Allows (n+1) f 0 a) (hg : Allows n g 0 b) (he : f 0=1) :
    ‖iteratedFDeriv ℝ (n+1) (f*g) 0‖ ≤ 2^(n+1)*a*b + ‖iteratedFDeriv ℝ (n+1) g 0‖ := by
  have hs := hf.analytic.sub (g:=(fun _ : E => (1:X))) contDiffAt_const
  have hu := hg.analytic
  have hh : f*g=(f-1)*g+g := by simp [sub_mul]
  rw [hh,iteratedFDeriv_add_apply (f:=(f-1)*g) ((hs.mul hu).of_le le_top) (hu.of_le le_top)]
  apply (norm_add_le ..).trans
  refine add_le_add_left ((local_le (f:=f-1) hs hu (n+1)).trans ?_) _
  calc
    _ ≤ ∑ i∈Finset.range (n+1+1), ((n+1).choose i:ℝ)*a*b := by
      refine Finset.sum_le_sum fun i hi => ?_
      by_cases he' : i=0
      · subst i
        rw [norm_iteratedFDeriv_zero]; simp [he,hf.nonneg,hg.nonneg,mul_nonneg]
      have hp : i ≤ n+1 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have h : ‖iteratedFDeriv ℝ i (f-1) 0‖ ≤ a := by
        rw [iteratedFDeriv_sub_apply (hf.analytic.of_le le_top) (show ContDiffAt ℝ (↑i:ℕ∞ω) (1:E → X) 0 from contDiffAt_const)]
        change ‖iteratedFDeriv ℝ i _ _-iteratedFDeriv ℝ i (fun _ => (1:X)) _‖ ≤ _
        rw [iteratedFDeriv_const_of_ne he', Pi.zero_apply, sub_zero]
        exact hf.norm_le _ hp
      exact mul_le_mul (mul_le_mul_of_nonneg_left h (by positivity)) (hg.norm_le _ (by omega))
        (norm_nonneg _) (mul_nonneg (by positivity) hf.nonneg)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose,Nat.cast_pow, Nat.cast_ofNat]

-- Input bound per factor can itself be polynomial. Useful across varying
-- cell paths and on the bigger chart. Arbitrary domain dimension, incl s=0.
variable (X)
theorem series (k : ℕ) (a : Fund) : ∃ b : Fund, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ), 1 ≤ R → ∀ L : List (E → X), (L.length:ℝ) ≤ R → (∀ f∈L, f 0=1 ∧ Allows k f 0 (a.rents R)) →
      Allows k L.prod 0 (b.rents R) := by
  induction k with
  | zero =>
    refine ⟨flat ‖(1:X)‖,fun E _ _ R h L _ hf => ?_⟩
    -- use centered products
    have he (L : List (E → X)) (ha : ∀ f∈L, f 0=1 ∧ Allows 0 f 0 (a.rents R)) : L.prod 0=1 ∧ ContDiffAt ℝ ω L.prod 0 := by
      induction L with
      | nil => exact ⟨rfl,contDiffAt_const⟩
      | cons f L ih =>
        obtain ⟨hp,hl⟩ := ih fun _ hv => ha _ (List.mem_cons_of_mem _ hv)
        obtain ⟨hx,hf⟩ := ha f List.mem_cons_self
        exact ⟨show f 0 * L.prod 0=1 from by rw [hp,hx,one_mul],hf.analytic.mul hl⟩
    exact ⟨(he L hf).2,fun i hi => by obtain rfl : i=0 := Nat.le_zero.mp hi; rw [norm_iteratedFDeriv_zero,(he L hf).1]; exact cash ..⟩
  | succ n ih =>
    obtain ⟨b,hb⟩ := ih
    let z := twin (twin (flat ((2:ℝ)^(n+1))) a) b
    let c := bump b (twin first z)
    refine ⟨c,fun E _ _ R h L ht H => ?_⟩
    have hx (L : List (E → X)) (ht : (L.length:ℝ) ≤ R) (he : ∀ f∈L, f 0=1 ∧ Allows (n+1) f 0 (a.rents R)) : Allows n L.prod 0 (b.rents R) :=
      hb E R h L ht fun f hf => ⟨(he f hf).1,(he f hf).2.order (Nat.le_succ _)⟩
    have hg (L : List (E → X)) (ht : (L.length:ℝ) ≤ R) (he : ∀ f∈L, f 0=1 ∧ Allows (n+1) f 0 (a.rents R)) :
        ‖iteratedFDeriv ℝ (n+1) L.prod 0‖ ≤ (L.length:ℝ)*z.rents R := by
      induction L with
      | nil =>
        change ‖iteratedFDeriv ℝ (n+1) (fun _ : E => (1:X)) 0‖ ≤ _
        rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _), Pi.zero_apply]; simp
      | cons f Q ih =>
        have hh (g) (hq : g∈Q) := he g (List.mem_cons_of_mem _ hq)
        have hu : (Q.length:ℝ) ≤ R := le_trans (by exact_mod_cast List.IsSuffix.length_le (show Q <:+ f :: Q from List.suffix_cons ..)) ht
        obtain ⟨hp,hf⟩ := he f List.mem_cons_self
        rw [List.prod_cons]; refine (product_step hf (hx Q hu hh) hp).trans ((add_le_add (b:=z.rents R) ?_ (ih hu hh)).trans_eq ?_)
        · unfold z; rw [family,family]; apply mul_le_mul_of_nonneg_right _ (b.gain h).le
          exact mul_le_mul_of_nonneg_right (cash ..) (a.gain h).le
        simp; ring
    let x := (hx L ht H)
    refine ⟨x.analytic,fun i hi => ?_⟩
    rcases (show i ≤ n ∨ i=n+1 from by omega) with hi|hi
    · exact (x.norm_le i hi).trans ((le_add_of_nonneg_right ((twin first z).gain h).le).trans (daily _ _ _ h))
    subst i
    refine (hg L ht H).trans ((mul_le_mul_of_nonneg_right ht (z.gain h).le).trans ?_)
    unfold c; apply le_trans ?_ (daily _ _ R h); rw [family first z,invested]; exact le_add_of_nonneg_left (b.gain h).le
end Growth
end YM.Further.CorrectedLift

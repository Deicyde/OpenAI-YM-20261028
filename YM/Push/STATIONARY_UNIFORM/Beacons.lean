import YM.Next.FOUNDATIONS.LinkBounds
import YM.Push.STATIONARY_UNIFORM.Calculus

/-!
# Counting coefficients of locally supported analytic scores

E.g., after summing such a score over the lattice, to prove strict
invertibility estimates we need to keep two locations (the two derivatives).
This also lets us vary the Hessian on a uniform sup ball of fields or pay
actual cubic/quartic tensor sums. Jets nonfactorial. Supports may wrap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Filter Function Set Metric Lattice
open scoped Topology ContDiff BigOperators Classical

section Finite
variable {n : Side} {ι E F : Type} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev Positions (ι : Type) := ι → ℝ

def bolt {ι : Type} (i : ι) : Positions ι := Pi.single i 1
@[simp] lemma norm_bolt (i : ι) : ‖bolt i‖ = 1 := by change ‖(LinearIsometry.single ℝ (fun _ : ι => ℝ) i) 1‖ = _; simp

def entry (f : Positions ι → E) (p : Positions ι) {k : ℕ} (q : Fin k → ι) :=
  iteratedFDeriv ℝ k f p (fun i => bolt (q i))

variable {p : Positions ι} {N : ℕ} {y : Site n} {a α K C D : ℝ} {l : ι → Site n}
    {f g : Positions ι → E}

lemma entry_bound {k : ℕ} (q : Fin k → ι) : ‖entry f p q‖ ≤ ‖iteratedFDeriv ℝ k f p‖ := by
  simpa only [norm_bolt,Finset.prod_const_one,mul_one] using!
    (iteratedFDeriv ℝ k f p).le_opNorm (fun i => bolt (q i))

lemma iter_lin_at {ι κ : Type} [NormedAddCommGroup ι] [NormedSpace ℝ ι] [NormedAddCommGroup κ] [NormedSpace ℝ κ]
    {L : ι →L[ℝ] κ} {f : κ → E} {k} {x : ι} (hf : ContDiffAt ℝ (k:ℕ) f (L x)) :
    iteratedFDeriv ℝ k (f ∘ L) x =
      (iteratedFDeriv ℝ k f (L x)).compContinuousLinearMap (fun _ => L) := by
  have h : ContDiffAt ℝ (k:ℕ) (fun t => f (L x + t)) 0 :=
    (show ContDiffAt ℝ (k:ℕ) f (L x+0) by simpa using hf).comp (f:=fun t => L x+t) 0 (contDiffAt_const.add contDiffAt_id)
  have he := Next.Foundations.jets_linear L h
  rw [iteratedFDeriv_comp_add_left, add_zero, show ((fun t => f (L x+t)) ∘ L) = fun y => (f ∘ L) (x+y) from funext fun i => by simp,
    iteratedFDeriv_comp_add_left,add_zero] at he; exact he

/-- Only ask locality on the indicated set. -/
def Requests {H : Type} (s : Set (Positions ι)) (f : Positions ι → H) (l : ι → Site n) (y : Site n) (R : ℕ) : Prop :=
  ∀ v∈s, ∀ w∈s, (∀ i, separation y (l i) ≤ R → v i=w i) → f v=f w

lemma Requests.zero {k R : ℕ} {s : Set (Positions ι)} (h : Requests s f l y R)
    (hs : s∈𝓝 p) (hf : ContDiffAt ℝ (k:ℕ) f p) (q : Fin k → ι) (i : Fin k)
    (he : ¬ separation y (l (q i)) ≤ R) : entry f p q = 0 := by
  let A : Positions ι →L[ℝ] Positions ι := ContinuousLinearMap.pi fun j =>
    if separation y (l j) ≤ R then ContinuousLinearMap.proj j else 0
  let g (x : Positions ι) := f (p+x)
  have ht : ∀ᶠ x in 𝓝 (0 : Positions ι), p+x∈s := by
    apply ContinuousAt.preimage_mem_nhds (f:=fun x => p+x) (by fun_prop)
    simpa using hs
  have hh : g =ᶠ[𝓝 0] g ∘ A := by
    have hp : Tendsto A (𝓝 0) (𝓝 0) := by simpa using (A.continuous.continuousAt (x:=0)).tendsto
    filter_upwards [ht,hp.eventually ht] with x hx hX
    apply h _ hx _ hX
    intro j hj; simp [A,hj]
  have hd : iteratedFDeriv ℝ k g 0 = iteratedFDeriv ℝ k f p := by unfold g; rw [iteratedFDeriv_comp_add_left,add_zero]
  unfold entry
  rw [← hd,(hh.iteratedFDeriv (𝕜:=ℝ) k).eq_of_nhds]
  have hu := Next.Foundations.jets_linear A (f:=g) (k:=k)
    ((show ContDiffAt ℝ (k:ℕ) f (p+0) by simpa using hf).comp (f:=fun x => p+x) 0 (contDiffAt_const.add contDiffAt_id))
  rw [hu, ContinuousMultilinearMap.compContinuousLinearMap_apply]; apply ContinuousMultilinearMap.map_coord_zero (i:=i)
  funext j; by_cases hj : separation y (l j) ≤ R
  · have ht : j ≠ q i := fun hz => he (hz ▸ hj)
    simp [A,hj,bolt,ht]
  simp [A,hj]

def spanSites {k : ℕ} (l : ι → Site n) (y : Site n) (q : Fin k → ι) := ∑ i, separation y (l (q i))

def Beacon (l : ι → Site n) (a : ℝ) (N : ℕ) (f : Positions ι → E) (y : Site n) (p : Positions ι) (C : ℝ) :=
  ∀ (k : ℕ), k ≤ N → ∀ q : Fin k → ι, ‖entry f p q‖ ≤ C * Real.exp (-a * spanSites l y q)

theorem Allows.beacon {s : Set (Positions ι)} {r : ℕ} (h : Allows N f p C)
    (hr : Requests s f l y r) (hp : s∈𝓝 p) (ha : 0 ≤ a) : Beacon l a N f y p (C*Real.exp (a*(N*r:ℕ))) := by
  intro k hk q
  by_cases he : ∀ i, separation y (l (q i)) ≤ r
  · have hz : spanSites l y q ≤ N*r := (Finset.sum_le_sum (g:=fun _ => r) (fun j _ => he j)).trans
      (by simp [Nat.mul_le_mul_right r hk])
    rw [mul_assoc, ← Real.exp_add]
    refine ((entry_bound q).trans (h.norm_le _ hk)).trans (le_mul_of_one_le_right h.nonneg (Real.one_le_exp ?_))
    have ht : (spanSites l y q:ℝ) ≤ ((N*r:ℕ):ℝ) := by exact_mod_cast hz
    linarith [mul_le_mul_of_nonneg_left ht ha]
  push Not at he
  obtain ⟨i,hi⟩ := he
  rw [hr.zero hp (h.analytic.of_le le_top) q i (not_le.mpr hi), norm_zero]; have := h.nonneg; positivity

lemma Beacon.mono (h : Beacon l a N f y p C) (he : C≤D) : Beacon l a N f y p D :=
  fun _ hk q => (h _ hk q).trans (mul_le_mul_of_nonneg_right he (by positivity))

lemma Beacon.add (hf : ContDiffAt ℝ ω f p) (hg : ContDiffAt ℝ ω g p) (h : Beacon l a N f y p C) (h' : Beacon l a N g y p D) :
    Beacon l a N (fun x => f x + g x) y p (C+D) := by
  intro k hk q
  rw [show entry (fun x => f x+g x) p q = entry f p q+entry g p q from by
    unfold entry; rw [show (fun x => f x+g x) = f+g from rfl, iteratedFDeriv_add_apply (hf.of_le le_top) (hg.of_le le_top)]; rfl,add_mul]
  exact (norm_add_le ..).trans (add_le_add (h _ hk _) (h' _ hk _))

lemma Beacon.comp {g : E → F} (hf : ContDiffAt ℝ ω f p) (h : Beacon l a N f y p C) (hp : 0 ≤ C)
    (hg : Allows N g (f p) D) : Beacon l a N (fun z => g (f z)) y p
      ((∑ i∈Finset.range (N+1), (Fintype.card (OrderedFinpartition i):ℝ))* (D*(1+C)^N)) := by
  intro k hk q
  let T := Real.exp (-a*spanSites l y q)
  let M := D * (1+C)^N * T
  let v (i) := bolt (q i)
  have H (c : OrderedFinpartition k) : ‖((ftaylorSeries ℝ g (f p)).compAlongOrderedFinpartition
      (ftaylorSeries ℝ f p) c) v‖ ≤ M := by
    let U (i : Fin c.length) := entry f p (q ∘ c.emb i)
    have he := (iteratedFDeriv ℝ c.length g (f p)).le_opNorm U
    change ‖iteratedFDeriv ℝ c.length g (f p) U‖ ≤ _
    apply he.trans; apply le_trans (mul_le_mul (hg.norm_le _ (c.length_le.trans hk))
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => h _ ((c.partSize_le i).trans hk) _)) (by positivity) hg.nonneg)
    rw [Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin, ← Real.exp_sum, ← Finset.mul_sum, ← Nat.cast_sum]
    have ht : ∑ i, spanSites l y (q ∘ c.emb i) = spanSites l y q := c.sum_sigma_eq_sum (fun i => separation y (l (q i)))
    rw [ht, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hg.nonneg) (by positivity)
    refine (pow_le_pow_left₀ hp (show C≤1+C by linarith) _).trans (pow_le_pow_right₀ (by linarith) (c.length_le.trans hk))
  change ‖iteratedFDeriv ℝ k (g ∘ f) p v‖ ≤ _
  rw [iteratedFDeriv_comp hg.analytic hf le_top, FormalMultilinearSeries.taylorComp, sum_apply]
  apply le_trans ((norm_sum_le ..).trans (Finset.sum_le_sum (fun c _ => H c)))
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; unfold M T; rw [← mul_assoc]
  have hh := hg.nonneg
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun i _ => Nat.cast_nonneg (Fintype.card (OrderedFinpartition i))) (Finset.mem_range.mpr (show k < N+1 by omega))) (by positivity)) (by positivity)
end Finite
end YM.Push.Uniform

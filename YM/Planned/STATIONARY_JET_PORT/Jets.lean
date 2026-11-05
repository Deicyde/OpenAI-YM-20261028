import YM.Push.STATIONARY_UNIFORM.Beacons

set_option warningAsError false

/-!
# Joints for real finite-order tensors, in the `Scatter` conventions

In particular for differentiating inverse Hessians (and the log determinant
without ever taking a volume-power estimate of `det`). Distances are ALWAYS
in the native `Site n` put on these indices by the user, so may wrap; cost
per intermediate index uses actual multiplicities there. `Cable` carries a
row and a column as well as all jet slots; a `some` thread can keep track of
one more slot (e.g. from first differentiating an identity of functions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Push.Uniform Filter Function Set Metric Lattice Matrix
open scoped Topology ContDiff BigOperators Classical

section Peel
variable {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Positions ι → E} {p : Positions ι}

lemma peel (hf : ContDiffAt ℝ ω f p) {k : ℕ} (q : Fin (k+1) → ι) :
    entry f p q = entry (fun y => fderiv ℝ f y (bolt (q (Fin.last k)))) p
      (fun i : Fin k => q i.castSucc) := by
  let d := q (Fin.last k)
  let L := ContinuousLinearMap.apply ℝ E (bolt d)
  unfold entry
  rw [show (fun y => fderiv ℝ f y (bolt d)) = L ∘ fderiv ℝ f from rfl,
    L.iteratedFDeriv_comp_left (hf.fderiv_right (m:=ω) (by simp)) le_top,
    iteratedFDeriv_succ_apply_right]
  rfl

lemma peel_snoc (hf : ContDiffAt ℝ ω f p) {k : ℕ} (q : Fin k → ι) (d : ι) :
    entry (fun y => fderiv ℝ f y (bolt d)) p q =
      entry f p (Fin.snoc (α:=fun _ : Fin (k+1) => ι) q d) := by rw [peel hf]; simp

lemma ev_peel (hf : ContDiffAt ℝ ω f p) {k : ℕ} (q : Fin (k+1) → ι)
    {g : Positions ι → E} (he : (fun y => fderiv ℝ f y (bolt (q (Fin.last k)))) =ᶠ[𝓝 p] g) :
    entry f p q = entry g p (fun i : Fin k => q i.castSucc) := by
  rw [peel hf]; unfold entry; rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
end Peel

section Beacon
variable {ι E F : Type} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : Side} {x : Site n} {l : ι → Site n} {a C D : ℝ} {N : ℕ} {p : Positions ι}
    {f : Positions ι → E} {g : Positions ι → F}

lemma beacon_pair (hf : ContDiffAt ℝ ω f p) (hg : ContDiffAt ℝ ω g p)
    (h : Beacon l a N f x p C) (h' : Beacon l a N g x p C) :
    Beacon l a N (fun y => (f y,g y)) x p C := by
  intro k hk q
  have he : entry (fun y => (f y,g y)) p q = (entry f p q,entry g p q) := by
    unfold entry; rw [iteratedFDeriv_prodMk hf hg le_top]; rfl
  rw [he,Prod.norm_def]; exact max_le (h _ hk _) (h' _ hk _)

lemma beacon_scale (b : ℝ) (hf : ContDiffAt ℝ ω f p) (h : Beacon l a N f x p C) :
    Beacon l a N (fun y => b • f y) x p (|b| * C) := by
  intro k hk q
  rw [show entry (fun y => b • f y) p q = b • entry f p q from by
    unfold entry; rw [show (fun y => b • f y) = b • f from rfl,
      iteratedFDeriv_const_smul_apply (hf.of_le le_top)]; rfl, norm_smul,mul_assoc,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (h _ hk _) (abs_nonneg _)

abbrev mul2 (x : ℝ × ℝ) : ℝ := x.1*x.2
lemma twoJetPurchase (N : ℕ) : ∃ K : ℝ, 0<K ∧ ∀ x∈closedBall (0 : ℝ × ℝ) 1,
    Allows N mul2 x K := by
  have ha : ContDiff ℝ ω mul2 := contDiff_fst.mul contDiff_snd
  obtain ⟨K,h,H⟩ := exists_allows (isCompact_closedBall (0 : ℝ × ℝ) 1) (fun x _ => ha.contDiffAt (x:=x)) N
  exact ⟨1+K,by positivity,fun x hx => (H x hx).mono (le_add_of_nonneg_left zero_le_one)⟩
def unitTwo (N : ℕ) : ℝ := Classical.choose (twoJetPurchase N)
lemma twoJetCert (N : ℕ) : 0<unitTwo N ∧ ∀ x∈closedBall (0 : ℝ × ℝ) 1, Allows N mul2 x (unitTwo N) :=
  Classical.choose_spec (twoJetPurchase N)

def partitionsBill (N : ℕ) : ℝ := ∑ i∈Finset.range (N+1), (Fintype.card (OrderedFinpartition i):ℝ)
lemma partitionsBill_one (N : ℕ) : 1 ≤ partitionsBill N := by
  -- contribution at 0
  have he : (0 : ℕ) < Fintype.card (OrderedFinpartition 0) := Fintype.card_pos_iff.mpr ⟨OrderedFinpartition.atomic 0⟩
  refine (show (1:ℝ) ≤ (Fintype.card (OrderedFinpartition 0):ℝ) by exact_mod_cast he).trans ?_
  exact Finset.single_le_sum (f:=fun i => (Fintype.card (OrderedFinpartition i):ℝ)) (fun i _ => Nat.cast_nonneg _) (Finset.mem_range.mpr (Nat.zero_lt_succ N))

def fusion (N : ℕ) : ℝ := partitionsBill N * (unitTwo N * (1+1)^N)
lemma fusion_pos : 0 < fusion N := mul_pos (lt_of_lt_of_le zero_lt_one (partitionsBill_one N))
  (mul_pos (twoJetCert N).1 (pow_pos (by norm_num) _))

lemma beacon_mul {f g : Positions ι → ℝ} (hf : ContDiffAt ℝ ω f p) (hg : ContDiffAt ℝ ω g p)
    (h : Beacon l a N f x p C) (h' : Beacon l a N g x p D) (hC : 0<C) (hD : 0<D) :
    Beacon l a N (fun y => f y*g y) x p (fusion N*C*D) := by
  have normed {f : Positions ι → ℝ} {C : ℝ} (hf : ContDiffAt ℝ ω f p)
      (h : Beacon l a N f x p C) (hC : 0<C) : Beacon l a N (fun y => C⁻¹*f y) x p 1 := by
    simpa only [smul_eq_mul,abs_of_pos (inv_pos.mpr hC), inv_mul_cancel₀ hC.ne'] using beacon_scale C⁻¹ hf h
  let A y := (C⁻¹*f y,D⁻¹*g y)
  have he : ContDiffAt ℝ ω A p := (contDiffAt_const.mul hf).prodMk (contDiffAt_const.mul hg)
  have hA : Beacon l a N A x p 1 := beacon_pair (contDiffAt_const.mul hf) (contDiffAt_const.mul hg)
    (normed hf h hC) (normed hg h' hD)
  have hp : A p∈closedBall 0 1 := by
    rw [mem_closedBall_zero_iff]; simpa only [entry,iteratedFDeriv_zero_apply, spanSites,
      Fin.sum_univ_zero,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using hA 0 (Nat.zero_le _) Fin.elim0
  have ht := (twoJetCert N).2 (A p) hp
  have hh := hA.comp he zero_le_one ht
  have H := beacon_scale (C*D) (ht.analytic.comp (f:=A) p he) hh
  have hed : (fun y => (C*D) • mul2 (A y)) = (fun y => f y*g y) := by
      funext y; unfold mul2 A; simp only [smul_eq_mul]; field_simp
  dsimp [Function.comp_def] at H
  change Beacon l a N (fun y => (C*D) • mul2 (A y)) x p (|C*D| * fusion N) at H
  rw [hed,abs_of_pos (mul_pos hC hD), show C*D*fusion N = fusion N*C*D by ring] at H; exact H
end Beacon
end YM.Planned.JetPort

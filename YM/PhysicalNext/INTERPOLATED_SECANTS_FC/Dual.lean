import YM.Complex.Gaps
import YM.Overlay.Engine
import YM.Pressure.Seeds
import YM.Push.ABSOLUTE_SUMS.Basic
import YM.Push.ABSOLUTE_SUMS.Breadth
import YM.Slice.Gate
import YM.Vac.Treasury

/-!
# Summable horizontal receipts from finite tests, without differentiating a series

At a given beta, a batch of differentiated coefficient costs may be supplied for all
V and lists simultaneously but need NOT dominate the differentiated costs at the next beta.
Take finite signed linear combinations at *independent* test fields/directions first; recover
per-address boxes for actual secants with a common rate. Here `tax` includes hit/anchor
indicators and all requested support weights (even on difference or dead labels).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc
open Function Filter Set Lattice RG Push.AbsoluteSums
open scoped Topology BigOperators Classical

private lemma interval_price {a b c d : ℝ} {f : ℝ → ℝ} {M : ℝ} (hab : a < b) (ha : c ≤ a) (hb : b ≤ d)
    (hf : ContinuousOn f (Icc c d)) (hg : ∀ t∈ Ioo c d, DifferentiableAt ℝ f t ∧ |deriv f t| ≤ M) :
    |f b-f a| ≤ (b-a) * M := by
  obtain ⟨v,hv,he⟩ := exists_deriv_eq_slope f hab (hf.mono (Icc_subset_Icc ha hb))
    (fun t ht => (hg t (Ioo_subset_Ioo ha hb ht)).1.differentiableWithinAt)
  have h := (hg v (Ioo_subset_Ioo ha hb hv)).2
  rw [he, abs_div, abs_of_pos (sub_pos.mpr hab)] at h
  rw [mul_comm]; exact (div_le_iff₀ (sub_pos.mpr hab)).1 h

theorem interval_cost {a b c d : ℝ} {f : ℝ → ℝ} {M : ℝ} (ha : a∈Icc c d) (hb : b∈Icc c d)
    (hf : ContinuousOn f (Icc c d)) (hg : ∀ t∈ Ioo c d, DifferentiableAt ℝ f t ∧ |deriv f t| ≤ M) :
    |f b-f a| ≤ |b-a| * M := by
  rcases lt_trichotomy a b with hab|rfl|hab
  · rw [abs_of_pos (sub_pos.mpr hab)]
    exact interval_price hab ha.1 hb.2 hf hg
  · simp only [sub_self, abs_zero, zero_mul, le_refl]
  rw [abs_sub_comm (f b), abs_sub_comm b, abs_of_pos (sub_pos.mpr hab)]
  exact interval_price hab hb.1 ha.2 hf hg

section Dual
variable {ι κ : Type*}
/-- Support/anchor currencies to be tested on finite sublists. -/
structure Tax (ι κ : Type*) where
  cost : κ → ι → ℝ
  nonneg x i : 0 ≤ cost x i
  visible i : ∃ x, 0 < cost x i

namespace Tax
variable (p : Tax ι κ)
variable {U : ι → Type*} {M D : ℝ}

structure Credits (c : ι → ℝ) (M : ℝ) : Prop where
  positive i : 0 ≤ c i
  pays x : SumBudget (fun i => p.cost x i * c i) M

variable {p}

lemma Credits.add {c M d N} (h : p.Credits c M) (h' : p.Credits d N) :
    p.Credits (fun i => c i+d i) (M+N) :=
  ⟨fun i => add_nonneg (h.positive _) (h'.positive _),fun x => by simpa only [← mul_add] using budget_plus (h.pays x) (h'.pays x)⟩
lemma Credits.relax {c M M'} (h : p.Credits c M) (he : M ≤ M') : p.Credits c M' :=
  ⟨h.positive,fun x => budget_loosen (h.pays x) he⟩

variable (p)
/-- Common per-address boxes for a batch (all tests), charged at the declared meters. -/
def Box (f : ∀ i, U i → ℝ) (M : ℝ) := ∃ c, p.Credits c M ∧ ∀ i u, |f i u| ≤ c i

def Dual (f : ∀ i, U i → ℝ) (M : ℝ) := ∀ (x : κ) (s : Finset ι) (u : ∀ i, U i) (e : ι → ℝ),
    (∀ i∈s, |e i| ≤ p.cost x i) → |∑ i∈s, e i * f i (u i)| ≤ M

variable {p} {f : ∀ i, U i → ℝ}

theorem Box.dual (h : p.Box f M) : p.Dual f M := by
  obtain ⟨c,hc,h⟩ := h
  intro x s u e he
  refine (Finset.abs_sum_le_sum_abs _ _).trans <| le_trans (Finset.sum_le_sum (g:=fun i => p.cost x i * c i) ?_)
    (budget_sum (hc.pays x) s)
  intro i hi; rw [abs_mul]; exact mul_le_mul (he i hi) (h i _) (abs_nonneg _) (p.nonneg _ _)

theorem Dual.unsigned (h : p.Dual f M) (x : κ) (s : Finset ι) (u : ∀ i, U i) :
    ∑ i∈s, p.cost x i * |f i (u i)| ≤ M := by
  let e (i : ι) := if 0 ≤ f i (u i) then p.cost x i else -p.cost x i
  have he i : |e i| = p.cost x i := by unfold e; split <;> simp [abs_of_nonneg (p.nonneg x i)]
  simp_rw [show ∀ i, p.cost x i * |f i (u i)| = e i * f i (u i) from fun i => by
    unfold e; split
    · next he => rw [abs_of_nonneg he]
    next he => rw [abs_of_nonpos (le_of_not_ge he),neg_mul,mul_neg]]
  exact (le_abs_self _).trans (h x s u e fun i _ => (he i).le)

theorem unsigned_box [∀ i, Nonempty (U i)]
    (h : ∀ (x : κ) (s : Finset ι) (u : ∀ i, U i), ∑ i∈s, p.cost x i * |f i (u i)| ≤ M) : p.Box f M := by
  let C i := sSup (range (fun u => |f i u|))
  let v (i : ι) := Classical.choice (inferInstance : Nonempty (U i))
  have hc (i : ι) (u : U i) : |f i u| ≤ C i := by
    obtain ⟨x,hx⟩ := p.visible i
    refine le_csSup ⟨M / p.cost x i,?_⟩ (mem_range_self u)
    rintro a ⟨w,rfl⟩
    simpa only [le_div_iff₀ hx,mul_comm (|_|),Finset.sum_singleton,update_self] using! h x {i} (update v i w)
  refine ⟨C,⟨fun i => (abs_nonneg _).trans (hc i (v i)),fun x => budget_of_sum
    (fun i => mul_nonneg (p.nonneg x i) ((abs_nonneg _).trans (hc i (v i)))) (fun s => ?_)⟩,hc⟩
  suffices ht : ∀ (s : Finset ι) (M : ℝ), (∀ (u : ∀ i,U i), ∑ i∈s,p.cost x i * |f i (u i)| ≤ M) →
      ∑ i∈s,p.cost x i * C i ≤ M by exact ht s M (h x s)
  intro s; induction s using Finset.induction_on with
  | empty => intro M h; simpa using h v
  | @insert i s hi ih =>
    intro M h
    simp only [Finset.sum_insert hi] at h ⊢
    have he (a : U i) : ∑ j∈s, p.cost x j * C j ≤ M - p.cost x i * |f i a| := by
      apply ih
      intro u; rw [le_sub_iff_add_le']
      convert h (update u i a) using 1
      simp only [update_self]; congr 1
      exact Finset.sum_congr rfl fun j hj => by rw [update_of_ne (by rintro rfl; contradiction) a u]
    rcases (p.nonneg x i).eq_or_lt with h0|h0
    · simpa [← h0] using he (v i)
    rw [← le_sub_iff_add_le,mul_comm,← le_div_iff₀ h0]
    exact csSup_le (range_nonempty _) fun m ⟨a,hm⟩ => by rw [← hm, le_div_iff₀ h0,mul_comm (|_|)]; linarith only [he a]

theorem Dual.box [∀ i, Nonempty (U i)] (h : p.Dual f M) : p.Box f M := unsigned_box h.unsigned



lemma Box.relax (h : p.Box f M) {M' : ℝ} (he : M ≤ M') : p.Box f M' :=
  let ⟨c,h,h'⟩ := h; ⟨c,h.relax he,h'⟩

lemma Box.add {g : ∀ i,U i → ℝ} (h : p.Box f M) (he : p.Box g D) :
    p.Box (fun i u => f i u+g i u) (M+D) :=
  let ⟨_,hc,h⟩ := h; let ⟨_,hc',he⟩ := he
  ⟨_,hc.add hc',fun i u => (abs_add_le ..).trans (add_le_add (h i u) (he i u))⟩

variable [∀ i, Nonempty (U i)]


/-! Uniform dominating list over a whole trajectory of bounded beta. The sorting argument
is needed: there needn't be a single worst pair which maximizes every ledger entry. -/
section Uniform
variable {T : Type*} (β : T → ℝ) {g : T → ∀ i, U i → ℝ}
    (hD : 0 ≤ D)
    (hM : ∀ t : T, p.Box (g t) M)
    (h : ∀ t t' : T, p.Box (fun i u => g t i u - g t' i u) (D * |β t-β t'|))
omit [∀ i, Nonempty (U i)] in
include hD hM h in
private lemma unified_sum (X : Finset T) (hX : X.Nonempty) {a b : ℝ} (hp : ∀ v∈X, β v ∈ Icc a b)
    (o : κ) (s : Finset ι) (u : ∀ i,U i) (t : ι → T) (ht : ∀ i∈s,t i∈X) :
    ∑ i∈s, p.cost o i * |g (t i) i (u i)| ≤ M + D*(b-a) := by
  induction X using Finset.strongInduction generalizing b t with
  | H X ih =>
    obtain ⟨v,hv,Hv⟩ := X.exists_max_image β hX
    rcases Finset.eq_empty_or_nonempty (X.erase v) with hz|he
    · have hm i (hi : i∈s) : t i=v := by
        by_contra hw
        exact Finset.notMem_empty _ (hz ▸ Finset.mem_erase.mpr ⟨hw,ht i hi⟩)
      rw [Finset.sum_congr rfl fun i hi => by rw [hm i hi]]
      exact ((hM v).dual.unsigned o s u).trans (le_add_of_nonneg_right (mul_nonneg hD
        (sub_nonneg.mpr ((hp v hv).1.trans (hp v hv).2))))
    obtain ⟨v',hv',Hv'⟩ := (X.erase v).exists_max_image β he
    let t' i := if t i = v then v' else t i
    have h₁ := ih _ (Finset.erase_ssubset hv) he (fun w hw => ⟨(hp w (Finset.mem_of_mem_erase hw)).1,Hv' w hw⟩) t'
      (fun i hi => by unfold t'; split <;> first | exact hv' | next hh => exact Finset.mem_erase.mpr ⟨hh,ht i hi⟩)
    have h₂ := (h v v').dual.unsigned o (s.filter (fun i => t i=v)) u
    rw [abs_of_nonneg (sub_nonneg.mpr (Hv v' (Finset.mem_of_mem_erase hv')))] at h₂
    calc
      _ ≤ ∑ i∈s,(p.cost o i * |g (t' i) i (u i)| +
          if t i=v then p.cost o i * |g v i (u i) - g v' i (u i)| else 0) := Finset.sum_le_sum (fun i hi => by
          unfold t'; split_ifs with H
          · rw [H,← mul_add]
            apply mul_le_mul_of_nonneg_left _ (p.nonneg o i)
            simpa [add_comm] using abs_add_le (g v i (u i) - g v' i (u i)) (g v' i (u i))
          exact (add_zero _).symm.le)
      _ ≤ M + D*(β v'-a) + D*(β v-β v') := by rw [Finset.sum_add_distrib,← Finset.sum_filter]; exact add_le_add h₁ h₂
      _ ≤ M + D*(b-a) := by nlinarith [(hp v hv).2]

include hD hM h in
theorem unified [Nonempty T] {a b : ℝ} (hp : ∀ t, β t ∈ Icc a b) :
    ∃ c, p.Credits c (M+D*(b-a)) ∧ ∀ t i u, |g t i u| ≤ c i := by
  obtain ⟨c,hc,he⟩ := unsigned_box (p:=p) (M:=M+D*(b-a)) (f:=fun i (v : T × U i) => g v.1 i v.2) (fun o s v =>
    unified_sum β hD hM h (insert (Classical.choice (inferInstance : Nonempty T)) (s.image (fun i => (v i).1))) (Finset.insert_nonempty ..)
      (fun t _ => hp t) o s (fun i => (v i).2) (fun i => (v i).1) fun i hi => Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi))
  exact ⟨c,hc, fun t i u => he i (t,u)⟩
end Uniform
end Tax
end Dual
end YM.PhysicalNext.InterpolatedSecantsFc

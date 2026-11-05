import YM.Extra.SOURCE_HISTORIES.LocalDebt

/-!
# One-level orbit superposition on paid columns (countable all
remainder addresses). Derives whole-column local bounds from the
analytical sockets, with all sums/kernels actually integrable.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Lattice Wilson RG Source Function Filter Set MeasureTheory Bid Labels Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ} {ι : Type*}
variable {F : Labels.Frame G d} (B : SectionData F) (H : History G) (N p m : ℕ) (A : Hol G)

theorem atom_mono {B : SectionData F} {H : History G} {N p m} {A : Hol G} {f x} {c₁ c₂ t₁ t₂ : ℝ}
    (h : PaidAtom B H N p m A f x c₁ t₁) (he : c₁ ≤ c₂) (ht : t₁ ≤ t₂) : PaidAtom B H N p m A f x c₂ t₂ := by
  obtain ⟨x,hx⟩ := h
  refine ⟨x,fun y => ?_⟩
  obtain ⟨hh,P,hP,hq,hc,hR⟩ := hx y
  exact ⟨hh.trans he,P,hP,hq,rem_mono hc ht,hR⟩

theorem atom_total [Nonempty ι] [Countable ι] {f : ι → Config G (H.S.side (m+1) p) → ℂ}
    {u : ι → F.Coeff} {s t : ι → ℝ} (hp : H.Selected) (hM : m ≤ N)
    (he : ∀ i, PaidAtom B H N p m A (f i) (u i) (s i) (t i))
    (hf : Dominated f) (hm : ∀ i,Measurable (f i))
    (h : Summable fun i => F.coeffSize (u i)) (hs : Summable s) (ht : Summable t) :
    PaidAtom B H N p m A (fun U => ∑' i, f i U) (∑' i, u i) (∑' i, s i) (∑' i, t i) := by
  unfold PaidAtom at he
  simp only at he
  choose x Hx using he
  choose hy P hP hF hC hD using (show ∀ i (y : Motion), _ from fun i y => Hx i y)
  let r := Motion.patch F
  have h₁ (y : Motion) : Summable fun i => F.coeffSize (r y (x i)-r y (u i)) := .of_nonneg_of_le
    (fun i => Work.G08.size_nonneg F _) (fun i => hy i y) hs
  have h₂ (y : Motion) : Summable fun i => F.coeffSize (r y (u i)) := .of_nonneg_of_le
    (fun i => Work.G08.size_nonneg F _) (fun i => patch_cost F y (u i)) (h.mul_left (orbitCost F))
  have h₃ (y : Motion) : Summable fun i => F.coeffSize (r y (x i)) := .of_nonneg_of_le
    (fun i => Work.G08.size_nonneg F _) (fun i => Work.G08.size_triangle F (r y _) (r y (u i)))
    ((h₂ y).add (h₁ y))
  have hx : Summable fun i => F.coeffSize (x i) := by simpa only [r,patch_id] using h₃ Motion.nil
  have hr (y) : HasSum (fun i => r y (x i)) (r y (∑' i, x i)) := patch_series F y (Size.series F hx).of_norm.hasSum
  have Hq (y) : HasSum (fun i => r y (u i)) (r y (∑' i, u i)) := patch_series F y (Size.series F h).of_norm.hasSum
  let v := Real.sqrt (H.levels.clock.forcedAllowance m)
  have hv : 0 < v := Real.sqrt_pos.2 (forcedPos ..)
  refine ⟨∑' i, x i,fun y => ?_⟩
  let Q := fun i => P i y
  have hi i : (Q i).x=r y (x i) := hP i y
  refine ⟨?_,merge (code ι) Q, ?_, merge_format _ Q (fun i => hF i y),
    (merge_budget (code _) Q hv (fun i => hC i y) ht).1, funext fun V => ?_⟩
  · rw [show Motion.patch F y (∑' i, x i)-Motion.patch F y (∑' i,u i) = _ from ((hr y).sub (Hq y)).tsum_eq.symm]
    exact (Size.bound F (h₁ y)).trans ((h₁ y).tsum_le_tsum (fun i => hy i y) hs)
  · simp_rw [merge,hi]
    exact (hr y).tsum_eq
  have hw : Summable fun i => F.coeffSize ((Q i).x) := by simp_rw [hi]; exact h₃ y
  rw [← (merge_density (code ι) Q hv (hp.represents N p m hM).good (fun i => hC i y) ht hw B V).tsum_eq]
  unfold Q dance
  simp_rw [hD, dance]
  rw [blast_sum H N p m d hf hm, scalar_tsum]

end YM.Extra.Histories

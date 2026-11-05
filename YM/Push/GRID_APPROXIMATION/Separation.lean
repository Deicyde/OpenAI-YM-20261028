import YM.Push.GRID_APPROXIMATION.Draw

/-!
# Eventually this finite grid pair really uses distinct h cells

Order: at fixed i<j, t eventually sufficient, then take actual ordered
cutoff upper limits. The stronger used estimate applies even where projections
tie provided actual cells distinct. t spacings identical to `flash`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson MeasureTheory Function Filter Set Cells OS
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {ι κ : Type*}

def offset (x : ι → Cover) (t i : ℕ) := fun l => x l + (fun _ => (t:ℤ)*i)

variable [Fintype ι] [Fintype κ]

lemma real_pair {x : ι → Cover} {y : κ → Cover} (hx : Injective x) (hy : Injective y)
    (i j : ℕ) (hij : i<j) : ∀ᶠ t : ℕ in atTop, Injective (Sum.elim (offset x t i) (offset y t j)) := by
  have he (a : ι) (b : κ) : ∀ᶠ t : ℕ in atTop, offset x t i a ≠ offset y t j b := by
    let n : ℤ := x a timeAxis - y b timeAxis
    filter_upwards [eventually_gt_atTop n.natAbs] with t ht e
    have hu : 0 ≤ (t:ℤ) := by omega
    have hv : (i:ℤ)+1 ≤ (j:ℤ) := by omega
    have hm : n < (t:ℤ) := by omega
    have hh := congr_fun e timeAxis
    change x a timeAxis + (t:ℤ)*i=y b timeAxis+(t:ℤ)*j at hh
    unfold n at hm
    linarith only [hm,hh,mul_le_mul_of_nonneg_left hv hu]
  filter_upwards [eventually_all.mpr fun a => eventually_all.mpr (he a)] with t hh
  rintro (a|a) (b|b) h
  · exact congr_arg Sum.inl (hx (add_right_cancel h))
  · exact (hh a b h).elim
  · exact (hh b a h.symm).elim
  exact congr_arg Sum.inr (hy (add_right_cancel h))

lemma wrap_late (S : Schedule) (h : ℕ) (x : ι → Cover) (hx : Injective x) :
    ∀ᶠ p : ℕ in atTop, Injective (wrap (S.side h p) ∘ x) := by
  have he : Tendsto (fun p => (S.side h p).val) atTop atTop := by
    refine tendsto_atTop_mono (f:=fun p => (S.period p).val) ?_ S.period_strict.tendsto_atTop
    intro p
    exact le_mul_of_one_le_right (Nat.zero_le _) (S.denominator h).property
  have hv (i : ι) : ∀ᶠ p : ℕ in atTop, lift (wrap (S.side h p) (x i)) = x i := by
    have ht (a : Axis) : ∀ᶠ p : ℕ in atTop, -((S.side h p).val : ℤ)< 2*x i a ∧ 2*x i a≤(S.side h p).val := by
      filter_upwards [he.eventually (eventually_gt_atTop (2*(x i a).natAbs))] with p hp
      omega
    filter_upwards [eventually_all.mpr ht] with p hp using lift_eq_iff.mpr ⟨rfl,hp⟩
  filter_upwards [eventually_all.mpr hv] with p hp a b h
  apply hx; calc
    _ = _ := (hp a).symm
    _ = _ := congr_arg Lattice.lift h
    _ = _ := hp b

lemma spent_shifts {h : ℕ} {v : ι → C.book.Token} {w : κ → C.book.Token}
    (Z : ∀ i, Figures C (v i) h) (D : ∀ i, Figures C (w i) h)
    {f : Extraction.Order} (H : C.Makes) (hz : ∀ i, (Z i).Gives f) (hd : ∀ i, (D i).Gives f) (q)
    {x : ι → Cover} {y : κ → Cover} (hx : Injective x) (hy : Injective y) (i j : ℕ) (hij : i<j) :
    ∀ᶠ t : ℕ in atTop, f.late fun N p =>
      ‖moment (C.beta N p) (placed Z (offset x t i) q N p * placed D (offset y t j) q N p)-
        moment (C.beta N p) (literal h v (offset x t i) N p * literal h w (offset y t j) N p)‖ ≤ expense (combined Z D) q := by
  have he := spent_pair Z H D hz hd q
  unfold Extraction.Order.late at *
  filter_upwards [real_pair hx hy i j hij] with t ht
  filter_upwards [he,f.per.cofinal.eventually (wrap_late C.S h _ ht)] with k hk hp
  filter_upwards [hk] with a ha using ha _ _ hp

end YM.Push.GridApprox

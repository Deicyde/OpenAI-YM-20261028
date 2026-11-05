import YM.Bid.Kitchen

/-!
# Budget for the forced startup merger

The estimate is an absolute one (no equality of densities or cancellation).
Use the `Buys` weights on the joint alphabet; keep one left price for every
pellet. Thus the entire budget can be taken from the tree hit sum, using
`Ac.Spark` connectivity with the *same* full footprints used by `addr`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.H02
open RG Lattice Ovens Ovens.Pipes Function
open scoped BigOperators

theorem answer : YM.Bid.H02 := by
  classical
  intro G n X d F δ u κ γ v P hquote _ hbuy
  obtain ⟨hγ, hκ, hvol⟩ := hbuy.margin
  obtain ⟨f, hf, hr, hh⟩ := hbuy.certificate
  let w := Real.exp (-κ)
  have hw : 0 ≤ w := (Real.exp_pos _).le
  let price : Ovens.Label → ℝ := fun l => l.elim (fun _ => w) (fun _ => 1)
  have hp0 (l : Ovens.Label) : 0 ≤ price l := by
    cases l
    · exact hw
    · exact zero_le_one
  have hp1 (l : Ovens.Label) : price l ≤ 1 := by
    cases l
    · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hκ)
    · exact le_rfl
  let e := fun i : ℕ => (F i).val
  let b := fun i : ℕ => w * ∏ l ∈ e i, f l
  refine ⟨b, ?_, ?_⟩
  · intro i
    have hprod : 0 ≤ ∏ l ∈ e i, f l := Finset.prod_nonneg fun l _ => hf l
    have hb : 0 ≤ b i := mul_nonneg hw hprod
    refine ⟨hb, fun U => ?_⟩
    change ‖solid F P d i U‖ ≤ b i
    unfold solid
    split
    · rw [norm_prod]
      have hgain : ∏ l ∈ e i, price l ≤ w := by
        obtain ⟨j, hj⟩ := (F i).property.1
        have hmem : Sum.inl j ∈ e i := by simpa [e, lefts] using hj
        calc
          _ ≤ ∏ l ∈ ({Sum.inl j} : Finset Ovens.Label), price l :=
            Finset.prod_le_prod_of_subset_of_le_one (Finset.singleton_subset_iff.mpr hmem)
              (fun l _ => hp0 l) (fun l _ _ => hp1 l)
          _ = w := by rw [Finset.prod_singleton]; rfl
      calc
        _ ≤ ∏ l ∈ e i, (price l * f l) := Finset.prod_le_prod
            (fun _ _ => norm_nonneg _) (fun l _ => by simpa only [price,w,Real.norm_eq_abs] using hr l U)
        _ = (∏ l ∈ e i, price l) * ∏ l ∈ e i, f l := Finset.prod_mul_distrib
        _ ≤ b i := mul_le_mul_of_nonneg_right hgain hprod
    · rwa [norm_zero]
  · intro x
    let R := Ac.roots X.patch P.B f P.supportExponent x
    have hR : SumBudget R (Real.exp γ - 1) :=
      Ac.forest X.patch P.B P.exponent_pos.le hf hh hvol hγ x
    have hinj : Injective e := Subtype.val_injective.comp F.injective
    -- The charge at x is exactly w times this subseries of the forest.
    have heq : (fun i => if x ∈ ((fused F P d).forced i).support then
          P.mass ((fused F P d).forced i).support (b i) else 0) =
        (fun i => w * R (e i)) := by
      funext i
      have hs : Ac.Spark X.patch (e i) := (F i).property.2.1
      by_cases hx : x ∈ (e i).biUnion X.patch
      · simp only [fused, addr, skin, ← show e i = (F i).val from rfl, hx, if_true,
          R, Ac.roots, hs, and_self, BudgetPoint.mass, b]
        exact mul_left_comm ..
      · simp [fused, addr, skin, ← show e i = (F i).val from rfl, R, Ac.roots, hx]
    rw [heq]
    have hs : Summable (fun i => R (e i)) := hR.2.1.comp_injective hinj
    refine ⟨fun i => mul_nonneg hw (hR.1 _), hs.mul_left w, ?_⟩
    have hl : (∑' i, R (e i)) ≤ ∑' s, R s :=
      Summable.tsum_le_tsum_of_inj e hinj (fun s _ => hR.1 s) (fun _ => le_rfl) hs hR.2.1
    rw [tsum_mul_left]
    exact (mul_le_mul_of_nonneg_left (hl.trans hR.2.2) hw).trans hquote
end YM.Work.H02

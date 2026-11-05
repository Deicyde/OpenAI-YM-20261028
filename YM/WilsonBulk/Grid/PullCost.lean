import YM.WilsonBulk.Grid.Cross

/-! Iteration strength estimate for all `advanceC` differences of cross-kernels
on a given demand. At unchanged rank 2 need third differences (or first on curvature). -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open Push.AbsoluteSums RG Finset Work.F08 Precision
open MultiNext.SignedSource.Newt MultiNext.SignedSource
open Pert.Bulk
open scoped Topology BigOperators Classical

variable {L c f : Side} {α β γ : Type} {H B θ σ : ℝ}
variable {T U : Cross L α β} {K : Row γ α} {j : β} {i : α} {q : γ}
  {p : Cover → ℝ} {g : Cover → ℝ} {r : Site L} {s : Finset Cover}

section

-- allowing different fees at order 0 and d. Order zero used only qualitatively
lemma exchange_priceTest {C w : ℝ} (z : Site L) (i : α) (j : β)
    (ht : 0 ≤ θ) (hp : Width θ B p) (hw : 0 ≤ w) (h : T.strip w C) (s : Finset Cover) (g : Cover → ℝ) :
    ∑ y∈s, routed (carry z) p (fun a => T (arrives z a,i) j) y * g y =
      ∑' a, p a * priceTest z T i j s g a := by
  have hb := paths_safe (show 0 ≤ (min θ w) from le_min ht hw)
    (carry_size z) (hp.mono (min_le_left ..) le_rfl)
    (fun a => (h (arrives z a,i) j).mono (min_le_right ..) le_rfl)
  simp_rw [priceTest,routed,read_offset, Finset.mul_sum, ← mul_assoc,← tsum_mul_right]
  rw [Summable.tsum_finsetSum (fun i _=> ?_)]
  exact (((hb.prod_symm.prod_factor i).of_norm).mul_right _)

lemma pay_step {d : ℕ} (hθ : 0< θ) (hσ : 0≤σ) (hp : Width θ B p) (hb : Blind d p)
    {W w : ℝ} (h : T.strip w W) (hw : 0 ≤ w) (hH : 0≤ H)
    (hh : ∀ l : List Axis, l.length = d → (advanceC L T l).strip σ H)
    (hc : σ / L.val ≤ θ / 2) (hL : Odd L.val) :
    Width σ (outlay θ σ d * H * B) (routed (carry r) p (fun a => T (arrives r a, i) j)) := by
  refine via_dual fun s g hg => ?_
  rw [exchange_priceTest _ _ _ hθ.le hp hw h s g]
  let u := priceTest r T i j s g
  have hx := budget_pairing hp
    (mul_nonneg (outlay_nonneg θ σ (d:=d) hθ.le) hH) (test_remainder (r:=r) (i:=i) (j:=j) hθ hL hσ hH hc hg hh)
  have hy := hb.erase u
  have hc' a : p a * u a = p a * Newt.tail d u a + p a * Newt.take d u a := by rw [Newt.tail,mul_sub,sub_add_cancel]
  change ‖∑' a, p a * u a‖ ≤ _
  rw [tsum_congr hc',Summable.tsum_add hx.2.1.of_norm hy.summable,hy.tsum_eq,add_zero]
  exact (norm_tsum_le_tsum_norm hx.2.1).trans hx.2.2

lemma pay_fineCompose [Fintype α] {d : ℕ} (hθ : 0< θ) (hσ : 0≤σ) (hp : K.strip θ B)
    (hb : ∀ i j, Blind d (K i j))
    {W w : ℝ} (h : T.strip w W) (hw : 0 ≤ w) (hH : 0≤ H)
    (hh : ∀ l : List Axis, l.length = d → (advanceC L T l).strip σ H)
    (hc : σ / L.val ≤ θ / 2) (hL : Odd L.val) :
    (fineCompose K T).strip σ (Fintype.card α * (outlay θ σ d * H * B)) := by
  rintro ⟨z,i⟩ j
  exact width_sum_finite fun l => pay_step hθ hσ (hp i l) (hb i l) h hw hH hh hc hL

end

section pull
variable [Fintype α] [Fintype γ] (Q : Cross L γ β)

/-- legs need NOT agree, preserve poles when taking divided differences. -/
def twoPull (K : Row γ α) (T : Cross L α β) : Row β β := composeRows (transRows Q) (fineCompose K T)
variable {Q}
lemma twoPull_bound {d : ℕ} {U w W : ℝ}
    (hθ : 0< θ) (hσ : 0 ≤ σ) (hQ : Q.strip σ U)
    (hP : K.strip θ B) (hb : ∀ i j, Blind d (K i j))
    (h : T.strip w W) (hw : 0≤ w) (hH : 0≤ H)
    (hh : ∀ l : List Axis, l.length = d → (advanceC L T l).strip σ H)
    (hc : σ / L.val ≤ θ / 2) (hL : Odd L.val) :
    (twoPull Q K T).strip σ
      ((L.val:ℝ)^4 * (Fintype.card γ*Fintype.card α:ℝ) * U * outlay θ σ d * H * B) := by
  unfold twoPull; convert strip_compose hσ (strip_trans hQ) (pay_fineCompose hθ hσ hP hb h hw hH hh hc hL) using 1
  rw [show Fintype.card (Co L γ) = L.val^4 * Fintype.card γ by simp [Co]]; push_cast; ring

variable {N : Row γ α} {X : Ratio c f} {A : Cross X.count γ β} {A' : Cross X.count α β}
lemma twoPull_acts {V W : ℝ} (hσ : 0≤ σ) (hH : N.strip σ H) (h : A.strip σ V)
    (h' : A'.strip σ W) :
    (twoPull A N A').acts c = (installed X A).transpose * (N.acts f * installed X A') := by
  unfold twoPull; rw [acts_compose hσ (strip_trans h) (strip_fine hσ hH h'), acts_trans,
    ← installed_fine X hσ hH h']
  -- reindex summation
  ext i j
  rw [Matrix.mul_apply,Matrix.mul_apply]; symm
  exact (Equiv.sum_comp (splitCo X γ) (fun x => A.acts c x i * ((fineCompose N A').acts c) x j))

end pull
end YM.WilsonBulk

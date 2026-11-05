import YM.Next.FOUNDATIONS.Primary
import YM.Push.GRID_APPROXIMATION.Separation

/-!
# Actual flash coverage (`Grid.Covering.Works`)

Quantitative off-diagonal cross billing on the given Wilson law. Pay even
when the two alternatives at the SAME copy would overlap, as long as their
individual placement functions are injective (which is all we charge in
each monomial pair). Take ordinary, not reflection-positive, products for
this bill. Gives sum of four small errors. Covers n=0.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson MeasureTheory Function Filter Set Cells OS
open scoped Topology BigOperators

section price
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

private def bi (A B : X → ℂ) := ∫ U, (A*B) U ∂μ

private lemma swapped (A B C D : X → ℂ) (ha : Envelope A) (hb : Envelope B)
    (hc : Envelope C) (hd : Envelope D) :
    bi μ (A-B) (C-D) = (bi μ A C-bi μ A D)-(bi μ B C-bi μ B D) := by
  have hi {A B : X → ℂ} (hA : Envelope A) (hB : Envelope B) : Integrable (fun x => A x* B x) μ :=
    (hA.mulC hB).integrableC _
  have he : Integrable (fun x => A x*C x-A x*D x) μ := (hi ha hc).sub (hi ha hd)
  have hh : Integrable (fun x => B x*C x-B x*D x) μ := (hi hb hc).sub (hi hb hd)
  unfold bi; simp only [Pi.mul_apply,Pi.sub_apply]; simp_rw [sub_mul,mul_sub]
  rw [integral_sub he hh,integral_sub (hi ha hc) (hi ha hd),integral_sub (hi hb hc) (hi hb hd)]

private lemma realPrice {A B C D E F J K : X → ℂ}
    (ha : Envelope A) (hb : Envelope B) (hc : Envelope C) (hd : Envelope D)
    (he : Envelope E) (hf : Envelope F) (hj : Envelope J) (hk : Envelope K)
    (hp : ∀ x, star ((A-B) x) = (A-B) x) {a b c d : ℝ}
    (h₁ : ‖bi μ A C - bi μ E J‖ ≤ a) (h₂ : ‖bi μ A D - bi μ E K‖ ≤ b)
    (h₃ : ‖bi μ B C - bi μ F J‖ ≤ c) (h₄ : ‖bi μ B D - bi μ F K‖ ≤ d) :
    |(∫ x, ((A-B) x).re * ((C-D) x).re ∂μ) - ∫ x, ((E x-F x)*(J x-K x)).re ∂μ| ≤ (a+b)+(c+d) := by
  have ht {A B C D : X → ℂ} (ha : Envelope A) (hb : Envelope B) (hc : Envelope C) (hd : Envelope D) :
      (∫ x, ((A x-B x)*(C x-D x)).re ∂μ) = (bi μ (A-B) (C-D)).re :=
    integral_re (((ha.subC hb).mulC (hc.subC hd)).integrableC μ)
  have hl (x) : ((A-B) x).re * ((C-D) x).re=((A x-B x)*(C x-D x)).re := by
    have hh : ↑((A-B) x).re=((A-B) x) := Complex.conj_eq_iff_re.mp (hp x)
    change _ = (((A-B) x)*((C-D) x)).re; conv_rhs => rw [← hh]
    simp
  simp_rw [hl]; rw [ht ha hb hc hd,ht he hf hj hk, ← Complex.sub_re]
  apply (Complex.abs_re_le_norm _).trans
  rw [swapped μ A B C D ha hb hc hd,swapped μ E F J K he hf hj hk]
  rw [show (bi μ A C- _ - (bi μ B C- _)) - (bi μ E J-bi μ E K-(bi μ F J-bi μ F K))=
      (bi μ A C-bi μ E J)-(bi μ A D-bi μ E K) - ((bi μ B C-bi μ F J)-(bi μ B D-bi μ F K)) by abel]
  exact (norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add h₁ h₂))
    ((norm_sub_le ..).trans (add_le_add h₃ h₄)))
end price

variable {G : Gauge} {C : Family G} {n h : ℕ}

def flipCover (x : Fin n → Cover) : Fin n → Cover := (Signed.mirror timeAxis).act ∘ x
def flipTokens (v : Fin n → C.book.Token) := C.book.move (Signed.mirror timeAxis) ∘ v

variable {v : Fin n → C.book.Token} (x : Fin n → Cover)
variable (Z : ∀ i, Figures C (v i) h) (D : ∀ i, Figures C (flipTokens (C:=C) v i) h)

def flashPlot (q N p t i : ℕ) := placed Z (offset x t i) q N p - placed D (offset (flipCover x) t i) q N p

def receiptPrice (q) := (expense (combined Z Z) q + expense (combined Z D) q) +
    (expense (combined D Z) q+expense (combined D D) q)

variable {f : Extraction.Order} (hz : ∀ i, (Z i).Gives f) (hd : ∀ i, (D i).Gives f)

def cover : Grid.Covering h v x where
  plots q N p t i U := (flashPlot x Z D q N p t i U).re
  reserve q := limitPrice Z q + limitPrice D q
  small := receiptPrice Z D
  grows := by
    have e1 := expense_zero (combined Z D) (combined_gives Z D hz hd)
    have e0 := expense_zero (combined Z Z) (combined_gives Z Z hz hz)
    have e2 := expense_zero (combined D Z) (combined_gives D Z hd hz)
    have e3 := expense_zero (combined D D) (combined_gives D D hd hd)
    simpa only [add_zero] using! ((e0.add e1).add (e2.add e3))

lemma covers (H : C.Makes) (hx : Injective x) : (cover x Z D hz hd).Works h v x f := by
  have hh : Injective (flipCover x) := (Signed.act_injective _).comp hx
  constructor
  · intro q t i
    have ha := placed_free Z hz q
    have hb := placed_free D hd q
    unfold Extraction.Order.late at *
    filter_upwards [ha,hb] with k hk hk'
    filter_upwards [hk,hk'] with j hj hj'
    dsimp only [cover,flashPlot]
    exact ⟨Complex.continuous_re.measurable.comp (((hj _).1.subC (hj' _).1).meas), fun U =>
      (Complex.abs_re_le_norm _).trans ((norm_sub_le ..).trans (add_le_add ((hj _).2 U).2 ((hj' _).2 U).2))⟩
  intro q i j hij
  filter_upwards [spent_shifts Z Z H hz hz q hx hx i j hij,spent_shifts Z D H hz hd q hx hh i j hij,
    spent_shifts D Z H hd hz q hh hx i j hij,spent_shifts D D H hd hd q hh hh i j hij] with t ha hb hc hw
  have he := placed_free Z hz q; have hf := placed_free D hd q
  unfold Extraction.Order.late at *
  filter_upwards [ha,hb,hc,hw,he,hf] with k uk vk wk kk ek fk
  filter_upwards [uk,vk,wk,kk,ek,fk] with l a b c d e F
  let E m := literal h v (offset x t m) (f.mesh l) (f.per k)
  let J m := literal h (flipTokens (C:=C) v) (offset (flipCover x) t m) (f.mesh l) (f.per k)
  have hl m U : Grid.flash h v x (f.mesh l) (f.per k) t m U = E m U - J m U := rfl
  have hE m : Envelope (E m) := literal_env ..
  have hJ m : Envelope (J m) := literal_env ..
  unfold Grid.bill; simp_rw [hl]; dsimp only [cover,flashPlot,receiptPrice]
  exact realPrice (law G _ (C.beta (f.mesh l) (f.per k))) (e _).1 (F _).1 (e _).1 (F _).1 (hE i) (hJ i) (hE j) (hJ j)
    (fun U => by simp only [Pi.sub_apply,star_sub, ((e _).2 _).1, ((F _).2 _).1]) a b c d
end YM.Push.GridApprox

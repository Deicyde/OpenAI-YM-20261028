import YM.Bid.Fetch
import YM.Next.EXTRACTION.Raw
import YM.Next.FOUNDATIONS.Primary
import YM.Push.RELAY_DIFFERENCE.Estimate
import YM.Work.I01

/-!
# Component estimates to spend on the copied *density*

Component fiscal interface for the residual multi-source problem. In addition
to the single-step comparison estimates in Matching need true estimates at
rank ≥2 on the marker representations. Spend an input of support exponent at
each use IN THAT SINGLE OUTPUT MAJORANT, not to continue at successively
shrinking exponents. The work of actually achieving those exponents step after
step very much remains to be done. Note derivative/grain/cost conventions of
`Stubs`; require those exact positive charges. Use the frozen `Worth` and
schedule from Matching.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Filter RG Wilson Extraction Extraction.Lease Labels Lattice Cells Marker Overlay Stock Bid Mix
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {C : Family G} {N p i d : ℕ} {F : Trial C} {n : Side}

structure Prices where
  sep : ℝ
  separation : 1 ≤ sep
  /-- Radius = coin / singleton envelope. -/
  coin : ℕ → ℝ
  legal i : 0 < coin i
  /-- Provisional step radius is previous (=finer) radius / bill.
  E.g. B*L^d etc. Can price flexibly incl direct conditional bounds. -/
  bill : ℕ → ℝ
  bills i : 0 < bill i
  reserve : ℕ → ℝ
  saved i : 0 ≤ reserve i
  bulk : ℕ → ℝ
  flag : ℕ → ℝ
  bulk_pay i : 0 ≤ bulk i ∧ bulk i ≤ 1
  flag_pay i : 0 ≤ flag i ∧ flag i ≤ 1

/-- Increase factor in the allowance of a raw rank-2+ budget. -/
def hope (δ : ℝ) (b : ℕ) := Real.exp (δ*b/64)
/-- Factor of radius change at *each marker*. -/
def gain (δ : ℝ) (b : ℕ) := Real.exp (δ*b/128)

namespace Prices
variable (P : Prices)

def rate (C : Family G) (E : ℝ) (N i : ℕ) := P.coin i/escrow C N i E
lemma rate_pos {E : ℝ} (h : 0 < E) : 0 < P.rate C E N i := div_pos (P.legal _) (escrow_pos h)

/-- Local price. Scales across ANY neighbor, buy under the calendar
(including boundary of changes). At constant positive reserve, polynomial
bounds in coarse-hat are sufficient. -/
def buys (C : Family G) (i : ℕ) :=
    P.coin i * P.bill i * gainChart C.path (i+1) i ≤ P.coin (i+1) * gain (P.reserve i) (C.path.levels.clock.coverSize i)

lemma receives {E : ℝ} (h : 0 < E) (hi : P.buys C i) :
    P.rate C E N i ≤ P.rate C E N (i+1)/P.bill i * gain (P.reserve i) (C.path.levels.clock.coverSize i) := by
  let B := C.path.levels.clock.coverSize i
  let T := gainChart C.path
  let b := P.bill i
  have he (n k) : 0 < T n k := Real.exp_pos _
  have hh : T N i = T (i+1) i * T N (i+1) := by
    unfold T gainChart; rw [←Real.exp_add]; ring_nf
  have hx (i') : P.rate C E N i' = P.coin i'*T N i'/E := by dsimp only [rate,escrow,T]; rw [div_div_eq_mul_div]
  change P.coin i*b*T (i+1) i ≤ _ at hi
  have hp : 0 < b := P.bills i
  rw [hx,hx, hh]
  refine (le_trans ?_ ((mul_le_mul_of_nonneg_right hi (show 0 ≤ (T N (i+1) / (b*E)) by apply (div_pos (he ..) (mul_pos hp h)).le)))) |>.trans ?_
  · apply le_of_eq; field_simp
  change _ ≤ P.coin (i+1)*T N (i+1)/E/b*_
  apply le_of_eq; field_simp


end Prices

/-! ### Stubs sums in the actual Census -/

lemma scale_budget {ι : Type*} {a b : ℝ} {p : ι → ℝ} (h : 0≤a) (hp : SumBudget p b) :
    SumBudget (fun i => a*p i) (a*b) := by
  refine ⟨fun i => mul_nonneg h (hp.1 i),hp.2.1.mul_left _,?_⟩
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hp.2.2 h
lemma lower_budget {ι : Type*} {a b : ℝ} {p q : ι → ℝ} (hp : SumBudget p a)
    (hb : a ≤ b) (hx : ∀ i,0 ≤ q i) (ht : ∀ i,q i ≤ p i) : SumBudget q b := by
  have he := hp.2.1.of_nonneg_of_le hx ht
  exact ⟨hx,he,(he.tsum_le_tsum ht hp.2.1).trans (hp.2.2.trans hb)⟩

section Book
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {A : Rep G n} {L : Bands R A}

/-- Separate bulk and hit, e.g. when using `varkappa⁻¹`-discounted force
estimates. Same grain labels in input and output when assessed. -/
def Mixed (T : Stubs L) (w δ h f : ℝ) :=
    (∀ i : V, SumBudget (fun j => if ranked (L.rays j)=true ∧ i∈(L.rays j).val then T.crown (fun _ => w) δ j else 0) h) ∧
    (∀ i : V, SumBudget (fun j : ℕ×ℕ => if ranked (L.marks j.1 j.2)=true ∧ i∈(L.marks j.1 j.2).val
      then T.cord (fun _ => w) δ j else 0) f)

omit [Fintype V] in
lemma mixed_funded (T : Stubs L) (w δ h f : ℝ) (hh : h ≤ 1) (hf : f ≤ 1) (he : Mixed T w δ h f) :
    T.funded (fun _ => w) δ true 1 := by
  refine ⟨fun i => lower_budget (he.1 i) hh (he.1 i).1 (fun _ => le_rfl),
    fun i => lower_budget (he.2 i) hf (he.2 i).1 (fun _ => le_rfl)⟩

omit [Fintype V] in
private lemma solo_toll {x : V} {i : R.Mode} (h : ranked i = false) (hx : x∈i.val) (w : ℝ) :
    Poly.toll (fun _ => w) i = w := by
  have he : i.val.card < 2 := by simpa [ranked] using h
  have hp := Finset.card_pos.mpr ⟨x,hx⟩
  simp [Poly.toll,show i.val.card=1 from by omega]

variable (T : Stubs L)

omit [Fintype V] in
/-- From UNWEIGHTED singleton estimates, which must be in the actual
array, into fiscal receipts when granted the same envelope used for mixed
at that level. Here h≤E is where G09 gets spent. -/
theorem singleton_price {u E h : ℝ} (hu : 0 < u) (hE : 0 < E) (he : h ≤ E)
    (hq : ∀ i,‖L.units i‖ ≤ h/u) (H : T.funded (fun _ => 1) 0 false (h/u)) :
    (∀ i, u/E*‖L.units i‖ ≤ 1) ∧ T.funded (fun _ => u/E) 0 false 1 := by
  let w := u/E
  have hw : 0 ≤ w := (div_pos hu hE).le
  have hp : w*(h/u) ≤ 1 := calc
    _ ≤ w*(E/u) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he hu.le) hw
    _ = 1 := by unfold w; field_simp
  refine ⟨fun i => (mul_le_mul_of_nonneg_left (hq i) hw).trans hp,?_,?_⟩
  · intro i; let g (q) j := if ranked (L.rays j)=false ∧ i∈(L.rays j).val then T.crown (fun _ => q) 0 j else 0
    change SumBudget (g w) _
    rw [show g w = (fun j => w * g 1 j) by
      funext j; unfold g Stubs.crown
      split_ifs with h
      · rw [solo_toll h.1 h.2,solo_toll h.1 h.2,one_mul]
      rw [mul_zero]]
    have hx : SumBudget (fun j => w * g 1 j) (w*(h/u)) := scale_budget hw (H.1 i)
    exact ⟨hx.1,hx.2.1,hx.2.2.trans hp⟩
  intro i; let g (q) (j : ℕ × ℕ) := if ranked (L.marks j.1 j.2)=false ∧ i∈(L.marks j.1 j.2).val then T.cord (fun _ => q) 0 j else 0
  change SumBudget (g w) _
  rw [show g w = (fun j => w * g 1 j) by
    funext j; unfold g Stubs.cord
    split_ifs with h
    · rw [solo_toll h.1 h.2,solo_toll h.1 h.2,one_mul]
    rw [mul_zero]]
  have hx : SumBudget (fun j => w * g 1 j) (w*(h/u)) := scale_budget hw (H.2 i)
  exact ⟨hx.1,hx.2.1,hx.2.2.trans hp⟩

/-- Spend support reserve, *leaving* a gain in cost (so target step
may require very small mixed cap even when absorbing radius change).
`Hope` uses minimal rank 2. Continue at the unchanged LEVEL-bought exponent
in `loaf` (don't call a next step with depleted reserve). -/
private lemma mixed_cost (h : Stubs.far (A:=L)) {u w δ x : ℝ} (hu : 0 < u) (hw : 0 < w)
    (hr : 0 ≤ δ) (he : w ≤ u * gain δ A.p.B) {v : R.Mode} (hv : ranked v = true)
    (X : Support n) (hg : 0 ≤ x) (hp : 0 < x → ∀ i ∈ v.val, L.origins i ∈ X) :
    let price (r a : ℝ) := Poly.toll (fun _ => r) v*loaf A.p X a x
    0 ≤ price w 0 ∧ price w 0 ≤ (hope δ A.p.B)⁻¹ * price u δ := by
  let k := v.val.card
  let B := A.p.B
  let D := coverNumber B X
  intro price
  have hx : ∀ q : ℝ, Poly.toll (fun _ => q) v=q^k := fun q => by simp [Poly.toll,k]
  refine ⟨mul_nonneg (Poly.worth (fun _ => hw) _).le (mul_nonneg (Real.exp_pos _).le hg),?_⟩
  rcases eq_or_lt_of_le hg with hb|hb
  · simp [price,loaf, ← hb]
  have hk : 2 ≤ k := by simpa [ranked] using hv
  have hl : 8 ≤ B := by
    obtain ⟨i,-,j,-,he'⟩ := Finset.one_lt_card.1 (show 1 < v.val.card from hk)
    exact (h i j he').1
  have compact : B*k ≤ 64*D := by
    refine Work.I01.answer n V L.origins B hl v.val ?_ hk X ?_
    · intro i _ j _ hi; simpa only [sq] using (h i j hi).2
    intro a ha; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha; exact hp hb i hi
  have hh : (B:ℝ) * k ≤ 64*D := by exact_mod_cast compact
  let g : ℝ := δ*B/128
  have hi : (k:ℝ)*g ≤ δ*D - δ*B/64 := by
    have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
    unfold g; have hδ : 0 ≤ δ*B := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left hh hr,mul_le_mul_of_nonneg_right hk' hδ]
  have ht : w^k ≤ u^k * Real.exp ((k:ℝ)*g) := by
    rw [Real.exp_nat_mul,←mul_pow]; exact pow_le_pow_left₀ hw.le he k
  dsimp only [price,loaf,hope]; rw [hx,hx, ← Real.exp_neg]
  refine (mul_le_mul_of_nonneg_right (ht.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone hi) (pow_nonneg hu.le _)))
    (mul_nonneg (Real.exp_pos _).le hb.le)).trans_eq ?_
  rw [add_mul, Real.exp_add, Real.exp_sub]
  simp only [zero_mul, Real.exp_zero]; unfold B D
  field_simp
  rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]; dsimp only [B]; ring_nf

/-- Improve ranks simultaneously without changing any support address. -/
theorem mixed_pay (A' : L.Active) (h : Stubs.far (A:=L)) {u w δ c d : ℝ} (hu : 0 < u) (hw : 0 < w)
    (hr : 0 ≤ δ) (he : w ≤ u * gain δ A.p.B) (hp : Mixed T u δ (hope δ A.p.B*c) (hope δ A.p.B*d)) : Mixed T w 0 c d := by
  let r := hope δ A.p.B
  have hR : 0 < r := Real.exp_pos _
  have transform {ι : Type} {f g : ι → ℝ} {s : ℝ} (hh : SumBudget g (r*s))
      (hf : ∀ i,0≤ f i ∧ f i ≤ r⁻¹*g i) : SumBudget f s := by
    apply lower_budget (scale_budget (inv_pos.mpr hR).le hh) ?_ (fun i => (hf i).1) (fun i => (hf i).2)
    rw [←mul_assoc,inv_mul_cancel₀ hR.ne', one_mul]
  constructor
  · intro i
    refine transform (hp.1 i) fun j => ?_
    split_ifs with hv
    · exact mixed_cost h hu hw hr he hv.1 _ (T.nonnegative _) (fun _ => A'.pins j)
    exact ⟨le_rfl, (mul_zero _).symm.le⟩
  intro i
  refine transform (hp.2 i) fun j => ?_
  split_ifs with hv
  · exact mixed_cost h hu hw hr he hv.1 _ (T.usable j) (fun ht => A'.retained j.1 j.2 (T.paid j ht))
  exact ⟨le_rfl, (mul_zero _).symm.le⟩
end Book
end YM.Push.RelayDifference

import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Boards
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Currencies

/-!
# Fixed-L price of the actual transforms

Explicit order of commitments. All volume factors go through the **same**
constant at this patch price (not adjusted to actual torus, evaluated before
∀ sufficiently large x). `Certified` gives Q, window Schur, gap kept numerically
for Q, covariance and determinant data on the actual fog, at every correct
D' test, even for fine seeds not realized by a fine field. No Book at
incompatible output masks. H is only a Teller input, no inverse assumption
at this call. Not a pre-L price; especially not computing α or its rate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Filter Function Set Matrix Lattice RG Pressure Tree Wilson
open Next.SectorChange FreeResolvent
open scoped Topology BigOperators Classical

lemma price_discount {ι X : Type} [Fintype ι] [DecidableEq ι] {W : ι→Set ι} {D : Cost X} {p A v C q q'}
    (h : Priced D p W A v C q) (hp : q ≤ q') : Priced D p W A v C q' where
  root := h.root
  gram := h.gram
  paid := h.paid
  rate := h.rate
  coupon := h.coupon.trans hp
  kernel := h.kernel
  inverse := h.inverse
  columns := h.columns
  shift u hu := (h.shift u hu).mono le_rfl (mul_le_mul_of_nonneg_right hp (attenuation_pos hu).le)
  mix := h.mix.mono le_rfl hp

section exp
/-- Repeated use across patch prices. -/
def currency (b : ℝ) (B : ℕ) := Real.exp (-b*B)
lemma currency_pos (b : ℝ) (B : ℕ) : 0 < currency b B := Real.exp_pos _
lemma currency_small {b : ℝ} (hb : 0<b) : Tendsto (currency b) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).const_mul_atTop_of_neg (neg_lt_zero.mpr hb))
lemma currency_eventual {b b' : ℝ} (h : b < b') (C : ℝ) : ∀ᶠ B : ℕ in atTop,C * currency b' B ≤ currency b B := by
  have hp : Tendsto (fun B => C*currency (b'-b) B) atTop (𝓝 0) := by simpa using (currency_small (sub_pos.mpr h)).const_mul C
  filter_upwards [hp.eventually (ge_mem_nhds zero_lt_one)] with B hb
  have he : currency b' B = currency (b'-b) B * currency b B := by unfold currency; rw [← Real.exp_add]; ring_nf
  rw [he, ← mul_assoc]; exact mul_le_of_le_one_left (currency_pos ..).le hb

/-- A sufficient delay for the `x∈pocket` hit sum, exp gates only.
Can eat every polynomial overhead at this point too, but retain lens
multiples BEFORE doing so. -/
lemma worth {θ b d L V C : ℝ} (a : ℝ) (l n : ℕ) (hv : 0 ≤ V) (hl : 0 ≤ L) (hc : 0 ≤ C) (hb : θ<b)
    (ht : d < b-θ*(n+1+l:ℕ)) : ∀ᶠ B in atTop, pass L (currency b B) a θ l B < 1 ∧
      totalCost n L V C (currency b B) a θ l B ≤ currency d B := by
  let A := Real.exp (a*tilePrice l)
  let K := V*C*L^n * A^(n+2)
  let r : ℝ := b-θ*(n+1+l:ℕ)
  have he B : pass L (currency b B) a θ l B=L*A*currency (b-θ) B := by
    unfold pass A
    rw [show currency (b-θ) B = currency b B * Real.exp (θ*B) by unfold currency; rw [← Real.exp_add]; ring_nf]; ring
  have hm B : permitCost n L V C (currency b B) a θ l B=K*currency r B := by
    have hi : currency r B = currency b B * Real.exp (θ*B)^(n+1+l) := by
      unfold currency; rw [← Real.exp_nat_mul, ← Real.exp_add]; unfold r; ring_nf
    rw [hi]; unfold permitCost K A; ring
  have hp : Tendsto (fun B => pass L (currency b B) a θ l B) atTop (𝓝 0) := by
    simp_rw [he]; simpa using! (currency_small (sub_pos.mpr hb)).const_mul (L*A)
  filter_upwards [hp.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2)),currency_eventual ht (2*K)] with B hH hx
  change pass L _ a θ l B ≤ 1/2 at hH
  refine ⟨by linarith only [hH],?_⟩
  unfold totalCost; rw [hm]
  have h1 : 0 ≤ K := by unfold K A; positivity
  have h2 := inv_anti₀ (by norm_num : (0:ℝ)<1/2) (show 1/2 ≤ 1-pass L (currency b B) a θ l B by linarith only [hH])
  apply le_trans _ hx
  exact (mul_le_mul_of_nonneg_left h2 (mul_nonneg h1 (currency_pos r B).le)).trans_eq (by ring)
end exp

namespace Physical
variable {G : Gauge} {c f : Side} {S : StepData c f}

def parcel (G : Gauge) (S : StepData c f) (l : ℕ) (a v C b d : ℝ) (B n : ℕ) :=
    Ac.Hit (inventory (place S (G:=G)) l B (n:=n)) B (ticket (place S) B v C (currency b B)) a (currency d B)

/-- Joint Book. Actual mask predicates, fixed physical record. All
constants *uniform after L*, independent of occurrences. Doesn't say log Q
itself is small. `Certified.geometry` used even for remote lettering.
Widths of any increments etc. (separate tasks) must be bought compatibly. -/
structure Certified (S : StepData c f) (T : Tube G S) (x : ℝ) (v C η b : ℝ) : Prop where
  basis : 120 ≤ radiusB x
  geometry : Next.SectorChange.span S.patch x ≤ radiusB x/50
  precision : 0 < η
  small : currency b (radiusB x) < 1
  text (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c) :
    A.flags=RG.flags (temp x) V →
      let Q := Rows.gram T x V k (shots S x) A F
      Schur.Gapped Q η ∧ Q.PosDef ∧ (fog A F T x V k).PosDef ∧
        Priced (native c) (place S) (windows S x) (AFull T A F x V k) v C (currency b (radiusB x))

  /-- Sensitivity recuts (on the actual full precision). Doesn't
  retroactively change the selected fog. -/
  wider (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c) :
    A.flags=RG.flags (temp x) V → ∀ W : Key G f→Set (Key G f), Schur.Bars W (place S) (radiusB x/60) →
      Priced (native c) (place S) W (AFull T A F x V k) v C (currency b (radiusB x)) ∧
      (Schur.clouded W (AFull T A F x V k)).PosDef

private lemma pours_of {α : Type} [Fintype α] (p : α → Site c) (A : Square α)
    {s K : ℝ} (hk : 0 ≤ K) (h : (native c).Schur p p s K A) : Schur.Pours A p p s K := by
  refine ⟨hk,h.rows.bound,fun j => ?_⟩
  change ∑ i, (native c).weight s (p i) (p j)*|A i j| ≤ K
  have ht : ∀ i, (native c).weight s (p i) (p j)=(native c).weight s (p j) (p i) := fun i => Cost.weight_symm ..
  -- rewriting a symmetric function generically can rewrite both ways
  convert h.cols.bound j using 1
  exact Finset.sum_congr rfl fun i _ => congr_arg (fun x => x*|A i j|) (ht i)

/-- Compatibility tests in Marked, Client use this estimate. -/
theorem late_price (H : Teller G) (P : Patch) (l : ℕ) (hl : 1≤l) (hB : P.Branches H.bind G) {a : ℝ} (ha : 0 ≤ a) :
    ∃ v C η b d : ℝ, 0<v ∧ 1≤C ∧ 0 < η ∧ 0<b ∧ 0<d ∧ ∀ᶠ x in atTop,
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → H.Funds S T →
        Certified S T x v C η b ∧ parcel G S l a v C b d (radiusB x) 0 ∧ parcel G S l a v C b d (radiusB x) 1 := by
  obtain ⟨s,M,η,u,J,hs,hM,hη,-,-,hQ⟩ := opaqueCost G P H hB
  let L := max M 1
  let h := min η 1
  let Y := safeRate s L h
  let m := Y/2
  let v := m/2
  let U := ceiling G P (Y-m)
  let C := max L (U*(min (h/2) 1)⁻¹)
  have hL : 0 ≤ L := le_trans hM (le_max_left ..)
  have hh : 0 < h := lt_min hη zero_lt_one
  have hy : 0 < Y := rate_pos hs hL hh
  have hs' : Y<s := rate_lt hs
  have hm : 0 < m := half_pos hy
  have hm' : m<Y := half_lt_self hy
  have hu : 0 ≤ U := ceiling_nn ..
  have hv : 0 < v := half_pos hm
  have hv' : v<m := half_lt_self hm
  have hc : 1 ≤ C := (show 1≤L from le_max_right ..).trans (le_max_left ..)
  let R := (m-v)/120
  let b := R/2
  let d := b/2
  let θ := (b/4)/(l+2:ℕ)
  have hr : 0<R := div_pos (sub_pos.mpr hv') (by norm_num)
  have hb : 0<b := half_pos hr
  have hd : 0<d := half_pos hb
  have ht : 0<θ := div_pos (by positivity) (by positivity)
  have he : θ*(l+2:ℕ)=b/4 := div_mul_cancel₀ _ (by positivity)
  have ht' : θ<b := by nlinarith only [he,hb, mul_le_mul_of_nonneg_left (show 1≤((l+2:ℕ):ℝ) by exact_mod_cast (show 1≤l+2 by omega)) ht.le]
  let S₀ := ceiling G P v
  let S' := ceiling G P θ
  have hy (n : ℕ) (hn : n≤1) := worth a l n (show 0≤S' from ceiling_nn ..) (show 0≤S₀ from ceiling_nn ..)
    (zero_le_one.trans hc) ht' (show d<b-θ*(n+1+l:ℕ) by
      have ho : θ*(n+1+l:ℕ) ≤ b/4 := by rw [← he]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show n+1+l≤l+2 by omega)) ht.le
      unfold d; linarith)
  refine ⟨v,C,η,b,d,hv,hc,hη,hb,hd,?_⟩
  obtain ⟨b₀,C₀,u₀,-,-,-,hWin⟩ := Schur.windows hs hh hL (ceiling G P) (ceiling_nn P G)
  have htail : Tendsto (fun x : ℝ => radiusB x/60) atTop atTop := by
    apply Filter.tendsto_atTop.mpr; intro n
    filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (60*n)] with x hx; omega
  filter_upwards [hQ, Work.E01.radiusB_tendsto.eventually (currency_eventual (show b<R from half_lt_self hr) (C^4)),
    Work.E01.radiusB_tendsto.eventually_ge_atTop 120, small_span P,
    Work.E01.radiusB_tendsto.eventually (hy 0 (by omega)),Work.E01.radiusB_tendsto.eventually (hy 1 le_rfl), htail.eventually hWin] with x hx h₁ h₂ h₃ h₄ h₅ hW
  intro c f S T he' hy' hF
  have ht (s : ℝ) (h : 0<s) : (native c).Volume (place S (G:=G)) s (ceiling G P s) := he' ▸ audience S G h
  set q := currency b (radiusB x)
  have hq : q < 1 := by
    have hi : 0<radiusB x := by omega
    unfold q currency; exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hb) (by positivity))
  have hn (n : ℕ) (hn : n≤1) (hr : pass S₀ q a θ l (radiusB x) < 1) (he : totalCost n S₀ S' C q a θ l (radiusB x) ≤ currency d (radiusB x)) :
      parcel G S l a v C b d (radiusB x) n := by
    intro s
    obtain ⟨hp,hv,hl⟩ := Counting.passports hv.le (zero_le_one.trans hc) (currency_pos b (radiusB x)).le
      (show 0<radiusB x by omega) hl ha (show 0 ≤ θ from ‹0<θ›.le) (ceiling_nn P G v)
      (ht _ hv) (ht _ ‹0 < θ›) hr n s
    exact ⟨hp,hv,hl.trans he⟩
  have hAny (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c) (hz : A.flags=RG.flags (temp x) V)
      (W : Key G f→Set (Key G f)) (H : Schur.Bars W (place S) (radiusB x/60)) :
      Priced (native c) (place S) W (AFull T A F x V k) v C q ∧ (Schur.clouded W (AFull T A F x V k)).PosDef := by
    obtain ⟨hP,hG,hA,-,-⟩ := hx S T he' hy' hF A F k V hz
    obtain ⟨hX,hN⟩ := blueprint T A F x V k hP hG
    constructor
    · refine price_discount (tilted_price hL hs hh hv.le hv'.le (hm'.le.trans hs'.le) hu hc
        (le_max_left ..) (le_max_right ..) hX hN (a_pos _ _ _ k hA) (ht (Y-m) (sub_pos.mpr hm')) (fun i=>H i i (by simp))
        (R:=(↑(radiusB x / 60):ℝ)) ?_) ?_
      · intro i j hij
        have hh : radiusB x / 60 ≤ separation (place S i) (place S j) := Nat.le_of_not_ge (mt (H i j) hij)
        exact show (↑(radiusB x /60):ℝ) ≤ (separation (place S i) (place S j):ℝ) from by exact_mod_cast hh
      apply le_trans _ h₁
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_monotone; unfold R
      have hg : (radiusB x:ℝ) ≤ 120* ((radiusB x / 60:ℕ):ℝ) := by exact_mod_cast (show radiusB x ≤ 120*(radiusB x/60) by omega)
      nlinarith only [mul_le_mul_of_nonneg_left hg (sub_nonneg.mpr hv'.le)]
    let z:=place S (G:=G); let Q:=AFull T A F x V k
    have hr : Schur.Pours Q z z s L := pours_of _ _ hL hX
    have hp : Schur.Gapped Q h := fun i => by rw [Schur.sumSq_dot]; exact hN.lower _
    have hu : Schur.Revenue z (ceiling G P) := fun x he y => (ht x he).bound y
    exact (hW z Q W hu hr (Matrix.isHermitian_iff_isSymm.mp (a_pos T A F k hA).1) hp H).2.2
  refine ⟨⟨h₂, he'.symm ▸ h₃,hη,hq,?_, hAny⟩,hn 0 (by omega) h₄.1 h₄.2,hn 1 le_rfl h₅.1 h₅.2⟩
  intro A F k V hz Q
  obtain ⟨-,hG,hA,-,he⟩ := hx S T he' hy' hF A F k V hz
  exact ⟨hG,hA,he,(hAny A F k V hz (windows S x) (fun _ _ => near_contains h₂)).1⟩
end Physical
end YM.AnalyticBridge.RelativeLogdet

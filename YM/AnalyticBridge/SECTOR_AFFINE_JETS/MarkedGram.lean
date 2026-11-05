import YM.AnalyticBridge.SECTOR_AFFINE_JETS.EntryBounds
import YM.Next.PHASE.Seats
import YM.Push.FREE_RESOLVENT.BlockRate
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Tier



/-!
# Marked `TestD` bundles for the actual D & its Gram

Keep both row and column prices in physical counting. Prices in the uptake
statements are uniform over periods. Real jets in the *V inputs*, not on
frame and sector-table changes. It's `Next.SectorChange.fog` that will consume
these Gram estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine

open Filter Function Set Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next.Fluctuations YM.Next.SectorChange
open YM.Next.SectorChange.Rows YM.Next.SectorChange.Wisps YM.Next.SectorChange.Tier
open YM.Push.Uniform (Allows bolt)
open YM.FreeResolvent (Mark Bundle native Gap)
open YM.FreeResolvent.TestD Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {P : Patch} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S} {x : ℝ}

section rates
variable {ι κ : Type} [Fintype ι] [Fintype κ] {d γ C δ : ℝ} {k : ℕ}

/-- Position marks right from the anchored derivative indices. This will
also pay derivatives on polynomial-growth directions. -/
abbrev Polar (B : PriceCoords G c) (a : ι → Site c) (b : κ → Site c) (Q : PriceCoords G c → Matrix ι κ ℝ)
    (k : ℕ) (s M : ℝ) := Bundle bolt (marks G c s) (native c) a b Q B k s M

lemma marks_le (G : Gauge) (hd : d ≤ δ) (l : List (Coord G c)) (x : Site c) :
    (marks G c d).pay l x ≤ (marks G c δ).pay l x := by
  induction l with
  | nil => rfl
  | cons b l h =>
    exact mul_le_mul ((native c).weight_mono hd _ _) h ((marks G c d).pay_pos ..).le
      ((marks G c δ).pos ..).le

lemma demark {Q : Matrix ι κ ℝ} {a : ι → Site c} {b : κ → Site c} {l : List (Coord G c)}
    (hp : Mark.Bill (marks G c δ) (native c) a b l γ C Q) (hd : d ≤ δ) :
    Mark.Bill (marks G c d) (native c) a b l γ C Q := by
  refine ⟨⟨fun i => le_trans ?_ (hp.row.rows i)⟩, ⟨fun j => le_trans ?_ (hp.col.rows j)⟩⟩
  all_goals
    exact mul_le_mul_of_nonneg_right (marks_le _ hd _ _) (Finset.sum_nonneg fun _ _ =>
      mul_nonneg ((native c).weight_nn ..) (abs_nonneg _))

lemma Polar.toBundle {B : PriceCoords G c} {Q : PriceCoords G c → Matrix ι κ ℝ} {a : ι → Site c}
    {b : κ → Site c} (hp : Polar B a b Q k δ C) (hd : d ≤ δ) :
    Bundle bolt (marks G c d) (native c) a b Q B k δ C :=
  ⟨hp.smooth,fun l h => demark (hp.bound l h) hd⟩

lemma thin {B : PriceCoords G c} {Q : PriceCoords G c → Matrix ι κ ℝ}
    {a : ι → Site c} {b : κ → Site c} (hp : Polar B a b Q k δ C) {j : ℕ} (hj : j ≤ k) (hd : d ≤ δ) (h : C ≤ γ) :
    Polar B a b Q j d γ :=
  ⟨smooth_of_le hp.smooth hj,fun _ hl => (demark (hp.bound _ (hl.trans hj)) hd).mono hd h⟩

end rates

/- `Tier.*` costs really just use shape. Pass-through here so callers
see no f,c. Enlarge to ≥1 for convenience. -/

def priceFiber (P : Patch) (G : Gauge) (s : ℝ) :=
  let D (x : ℝ) := ((Fintype.card G.ColorIndex:ℝ) * (Fintype.card (Site P.L) * Fintype.card Axis)) * wealth x
  let K (x : ℝ) := (Fintype.card G.ColorIndex:ℝ) * ((Fintype.card Signed:ℝ) *
    ((Fintype.card Bool * Fintype.card PlaqAxes * Fintype.card (Site P.L) * wealth x) +
      Fintype.card Axis * wealth x))
  max 1 (max (D s) (K s))

lemma priceFiber_pos (P : Patch) (G : Gauge) (s : ℝ) : 0 < priceFiber P G s := zero_lt_one.trans_le (le_max_left ..)
lemma priceFiber_def (S : StepData c f) (G : Gauge) (s : ℝ) :
    priceFiber S.patch G s = max 1 (max (keyFee S G s) (slotFee S G s)) := rfl

lemma fiber_volume (S : StepData c f) (G : Gauge) {s : ℝ} (hs : 0 < s) (A : Stores S) (F : Forest S.ratio) (x : ℝ) :
    (native c).Volume (front A F (x:=x) (G:=G)) s (priceFiber S.patch G s) ∧
      (native c).Volume (Wisps.down S (G:=G)) s (priceFiber S.patch G s) := by
  rw [priceFiber_def S G s]
  exact ⟨⟨fun i => (front_price s hs A F G i).trans ((le_max_left ..).trans (le_max_right ..))⟩,
    ⟨fun i => (down_price s hs S G i).trans ((le_max_right ..).trans (le_max_right ..))⟩⟩

def paramPrice (G : Gauge) (s : ℝ) := max 1 (YM.FreeResolvent.torusPay (Axis×G.ColorIndex) s)
lemma param_pos (G : Gauge) (s : ℝ) : 1 ≤ paramPrice G s := le_max_left ..
lemma param_volume (G : Gauge) (c : Side) {s : ℝ} (hs : 0 < s) :
    (native c).Volume (coordRoot (G:=G) (c:=c)) s (paramPrice G s) := by
  exact (((YM.FreeResolvent.volume c (Axis × G.ColorIndex) s hs)).comp
    (Equiv.prodAssoc (Site c) Axis G.ColorIndex).injective).le (le_max_right ..)

abbrev profileD (T : Tube G S) (x : ℝ) (V : Config G c) (A : Stores S) (F : Forest S.ratio) (k : S.Choices)
    (B : PriceCoords G c) := move T x (field V B) k (shots S x) A F

abbrev profileGram (T : Tube G S) (x : ℝ) (V : Config G c) (A : Stores S) (F : Forest S.ratio) (k : S.Choices)
    (B : PriceCoords G c) := Rows.gram T x (field V B) k (shots S x) A F

private lemma analytic_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι κ : Type} [Fintype ι] [Fintype κ]
    {Q : E → Matrix ι κ ℝ} {x : E} (h : ∀ i j, ContDiffAt ℝ ω (fun y => Q y i j) x) : ContDiffAt ℝ ω Q x := by
  let L : (ι → κ → ℝ) ≃L[ℝ] Matrix ι κ ℝ := (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  apply L.contDiff.contDiffAt.comp x (show ContDiffAt ℝ ω (fun x i j => Q x i j) x from
    contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr (h i))

lemma gram_analytic (T : Tube G S) (x : ℝ) (k : S.Choices) (A : Stores S) (F : Forest S.ratio)
    {V : Config G c} {B : PriceCoords G c} (h : ContDiffAt ℝ ω (profileD T x V A F k) B) :
    ContDiffAt ℝ ω (profileGram T x V A F k) B := by
  let Q := profileD T x V A F k
  let J := Bundle.switch (Rows.Receipt G S) (Rows.In x A F (G:=G))
  change ContDiffAt ℝ ω (fun y => (J ∘ Q) y * Q y) B
  exact prod_smooth (J.contDiff.contDiffAt.comp B h) h

lemma account_D (G : Gauge) (P : Patch) (Pt : Teller G) (hk : P.Branches Pt.bind G) (n : ℕ) :
    ∃ r d M : ℝ, 0<r ∧ 0<d ∧ 0<M ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P →
    100*(1+radiusB x) ≤ c.val → Pt.Funds S T → ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices),
    A.flags=RG.flags (temp x) V → ∀ B : PriceCoords G c, ‖B‖≤ r →
      Polar B (Wisps.down S) (Wisps.front A F) (profileD T x V A F k) n d M ∧
        ContDiffAt ℝ ω (profileD T x V A F k) B := by
  obtain ⟨r,d,M, hr, hd, hm,H⟩ := moves_priced G P Pt hk n
  refine ⟨r,d,priceFiber P G d*M,hr,hd,mul_pos (priceFiber_pos ..) hm,?_⟩
  filter_upwards [H] with x hx
  intro c f S T hp hs ht A F V k hv B hB
  let a := Wisps.down S (G:=G); let b := front A F (x:=x) (G:=G)
  have h i j := hx S T hp hs ht A F V hv B hB k i j
  have he : ContDiffAt ℝ ω (profileD T x V A F k) B :=
    analytic_entries (fun i j => (h i j).smooth)
  refine ⟨⟨he.of_le le_top,fun l hl => ?_⟩,he⟩
  obtain ⟨hm',hN⟩ := fiber_volume S G hd A F x
  let D := native c
  have h1 : D.Volume b (2*d-d) (priceFiber P G d) := by rw [← hp,show 2*d-d=d by ring]; exact hm'
  have h2 : D.Volume a (2*d-d) (priceFiber P G d) := by rw [← hp,show 2*d-d=d by ring]; exact hN
  refine Mark.Bill.of_entry h1 h2 hm.le (fun i j => ?_) (fun i j => ?_)
  · have hh := (h i j).each (a i) (.inl rfl) l hl
    rw [← entry bolt l (he.of_le le_top)]; exact hh
  have hh := (h i j).each (b j) (.inr rfl) l hl
  rw [D.weight_symm,← entry bolt l (he.of_le le_top)]; exact hh

theorem input_polar (G : Gauge) (P : Patch) (Pt : Teller G) (hk : P.Branches Pt.bind G) (n : ℕ) :
    ∃ r s M : ℝ, 0<r ∧ 0<s ∧ 0<M ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P →
    100*(1+radiusB x) ≤ c.val → Pt.Funds S T → ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices),
    A.flags=RG.flags (temp x) V → ∀ B : PriceCoords G c, ‖B‖≤r →
      ContDiffAt ℝ ω (profileD T x V A F k) B ∧
      Polar B (Wisps.down S) (Wisps.front A F) (profileD T x V A F k) n s M ∧
      Polar B (Wisps.front A F) (Wisps.front A F) (profileGram T x V A F k) n s M := by
  obtain ⟨r,d,M, hr, hd, hm,H⟩ := account_D G P Pt hk n
  let C := max M (YM.FreeResolvent.tagPrice 1 n M M)
  let γ := d/(n+1:ℕ)
  have hg : 0<γ := div_pos hd (by positivity)
  have ht : γ+n*γ ≤ d := by
    have he : γ*(n+1:ℕ)=d := div_mul_cancel₀ _ (by positivity : (n+1:ℕ) ≠ (0:ℝ))
    push_cast at *; linarith only [he]
  have hσ : γ ≤ d := (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hg.le)).trans ht
  refine ⟨r,γ,C,hr,hg,hm.trans_le (le_max_left ..),?_⟩
  filter_upwards [H] with x hx
  intro c f S T hp hf hT A F V k ha B hB
  obtain ⟨hb,hD⟩ := hx S T hp hf hT A F V k ha B hB
  refine ⟨hD, thin hb le_rfl hσ (le_max_left ..),?_⟩
  have hw := Polar.toBundle hb hσ
  exact (hw.transpose.multiply hw (Mark.position_move _ _ hg.le) hg.le le_rfl hm.le hm.le hg.le ht).mono le_rfl (le_max_right ..)

end YM.AnalyticBridge.SectorAffine

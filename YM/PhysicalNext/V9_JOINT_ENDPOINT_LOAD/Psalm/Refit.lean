import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Hiring
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Recitals

/-! # Enlarging *before* choosing café/d and investments to
accommodate the authentic brake branch on the same subsequent data as
the surrounding sector & joint payment. Not transferring anti-monotone
`Rates` to a bigger radius; REBUY positive kernel permissions, regulator
vouchers and the affine ledger (already provided at any fixed aperture). -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm.Refit
open Function Filter Lattice RG Wilson Pressure Tree Precision Bid Exterior Bloch
    Next Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.SectorMeasure.Presented SectorNext.Remainder SectorNext.Remainder.Affine
    AnalyticBridge.AnnulusRatioInsertions AnalyticBridge.AnnulusRatioInsertions.FS AnalyticBridge.AnnulusRatioInsertions.Portfolio
    Heir Clockwork Testing RG.Supply Push.PriceCompiler Shoot Heir.Suite
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {V : ChartRatio G}

lemma enlarges (Pt : Teller G) (V : ChartRatio G) (hV : LocalRatio V) (N : Side) (w y : ℝ) (hw : 0<w) :
    ∃ K E : ℝ, y≤K ∧ 0<K ∧ 0<E ∧ ∀ᶠ x : ℝ in atTop, Aperture Pt N w K x ∧ Sponsored V Pt N w K E x := by
  obtain ⟨A,H,hA,-,h⟩ := openings Pt V hV N w hw
  let K := max A y; have hK : 0<K := hA.trans_le (le_max_left ..)
  obtain ⟨B,r,hB,hr,hR,hL⟩ := ratio_price hV
  have hr' := first_pos G
  refine ⟨K,B,le_max_right ..,hK,hB,?_⟩
  filter_upwards [h, Work.E01.fiery_le G N (4*K), (Work.E01.largeT_tendsto G N).eventually (gt_mem_nhds (by positivity : 0 < min r (min (firstRadius G) 1)))] with x ⟨hx,h⟩ h₁ h₂
  obtain ⟨ht,-,-,hs,hx⟩ := hx
  let d := K*fiery G x N
  have hd : 0 < d := mul_pos hK ht
  have h₃ : 4*d < min r (min (firstRadius G) 1) := by rw [show 4*d=4*K*fiery G x N from (mul_assoc ..).symm]; exact h₁.trans_lt h₂
  rw [lt_min_iff,lt_min_iff] at h₃
  have h₄ : 2*d < firstRadius G := by linarith only [hd,h₃.2.1]
  have ha : A*fiery G x N ≤ d := mul_le_mul_of_nonneg_right (le_max_left ..) ht.le
  obtain ⟨_,_,_,_,h⟩ := h
  constructor
  · refine ⟨ht,hd,(by change d<_; linarith only [hd,h₄]),hs, fun c f S T hN hF hT => ?_⟩
    obtain ⟨hs,hx⟩ := hx c f S T hN hF hT
    refine ⟨hs, fun D F O A U k W hU hW p hp => ?_⟩
    obtain ⟨X,a,h,hX⟩ := hx D F O A U k W hU hW p hp
    exact ⟨X,a,h.trans (le_max_left ..),hX⟩
  refine ⟨(by change d≤1; linarith only [h₃.2.2,hd]),h₄,h₃.1.trans hR,fun a ha => (hL a (ha.trans h₃.1.le)).2.2,fun c f S T he hF hT O F k W B₀ q => ?_⟩
  obtain ⟨hm,hn⟩ := h c f S T he hF hT O F k W B₀ q
  constructor
  · intro u hU hb e hx y z; obtain ⟨a,ht,hβ,hχ,hX,-⟩ := hm u hU hb e hx
    refine ⟨a,ht.trans ha,hβ,hχ,hX,fun q => ?_⟩
    have hY : z=G.lieExp a := by change u e * y⁻¹=G.lieExp a; change G.lieExp a * y=u e at hX; rw [← hX]; group
    change patched q d z=a; rw [hY,patched_agrees q hd (show d<firstRadius G by linarith only [hd,h₄]) (ht.trans ha)]
  intro hX β hβ0
  obtain ⟨g,hQ,hQ'⟩ := hn hX β hβ0
  exact ⟨⟨g.nativePos,hβ0,(meanLog_cont O F T x W k q d hT hd h₄).measurable,(fun u hU hz i => let ⟨a,hz,hm,hu⟩:= g.core u hU hz i; ⟨a,hz.trans ha,hm,hu⟩),hV,hd,h₃.1.trans hR⟩,hQ,hQ'⟩

lemma counters (Z : ChartRatio G) (hZ : LocalRatio Z) (P : Teller G) : ∃ i : ℕ, ∀ N : Side, i≤N.val → ∀ᶠ w : ℝ in atTop,
    ∀ r : ℝ, ∃ κ K E, r ≤ K ∧ ∀ (l D n : ℕ) (B e' : ℝ), 0≤B → ∀ᶠ x : ℝ in atTop, Budget P N w κ Z K E l D n B e' x := by
  obtain ⟨i,h⟩ := before_local P
  refine ⟨i,fun N hi => ?_⟩; filter_upwards [h N hi] with w hw r
  obtain ⟨hm,κ,hκ,hb⟩ := hw
  obtain ⟨K,E,hv,hK,hE,h⟩ := enlarges P Z hZ N w r hm
  obtain ⟨C,hC,hc⟩ := AnalyticBridge.AnnulusRatioInsertions.slots Z (L:=N) hZ
  refine ⟨κ,K,E,hv,fun l D n B e' hB => ?_⟩
  by_cases ht : ∃ P0 : Patch,P0.L=N ∧ P0.J=P.j
  swap
  · filter_upwards [h] with x hx
    exact ⟨hm,hκ,hK,hE.le,hB,hx.1,hx.2,fun P0 hr hg => (ht ⟨P0,hr,hg⟩).elim,fun c f S T hs _ hx => (ht ⟨S.patch,hs,hx.atStep⟩).elim⟩
  obtain ⟨P0,h0,h1⟩ := ht
  let H := AnalyticBridge.AnnulusRatioInsertions.tally C E N l + (Dress.tagCurrency P0 l+B*(vans N l:ℝ)+e')
  filter_upwards [h,hb (2*K) H D n] with x hx he
  refine ⟨hm,hκ,hK,hE.le,hB,hx.1,hx.2,?_,he.2⟩
  intro S0 hi ht
  have hh : P0 = S0 := by cases P0; cases S0; congr <;> first | exact h1.trans ht.symm | exact h0.trans hi.symm
  have hβ (β : ℝ) (hl : β ∈ Set.Icc (Scales.y G N x/2) (2*Scales.y G N x)) : 0<β :=
    lt_of_lt_of_le (div_pos (by linarith only [he.1.1]) (by norm_num)) hl.1
  exact ⟨H,C,he.1,hC.le,fun β hh => hc _ _ he.1.1.le (hβ β hh) hh.2, hh ▸ le_refl _⟩

def Begins (Q : Teller G) (Z : ChartRatio G) (N : Side) := ∀ᶠ w : ℝ in atTop, ∀ r, ∃ b : Cafe, r ≤ b.r ∧ Outlet b Q N w Z
lemma starts (Z : ChartRatio G) (hZ : LocalRatio Z) (P : Teller G) : ∃ i : ℕ, ∀ N : Side, i≤N.val → Begins P Z N := by
  obtain ⟨i,h⟩ := counters Z hZ P
  refine ⟨i,fun N hi => ?_⟩; obtain ⟨L,η,hη,hL,H⟩ := hail P N
  filter_upwards [h N hi] with w hw r; obtain ⟨κ,K,E,hk,hx⟩ := hw r
  exact ⟨⟨K,E,η,L,κ⟩,hk, fun l D n e' => ((hx l D n (packageCost (G:=G) η L) e' (mul_nonneg (Nat.cast_nonneg _) (perSlot_pos hη hL))).and H).mono fun x h => ⟨hη,hL,h.2,h.1⟩⟩

variable {s : Sheet G} {K : MapPrices} {Z : ChartRatio G}
def First (s : Sheet G) (K : MapPrices) (Z : ChartRatio G) := ∀ j i, StepStages j i → s.first ≤ i → ∀ L : Side, s.floorL j ≤ L.val → Begins (query s K j i) Z L
lemma first (s : Sheet G) (K : MapPrices) (hZ : LocalRatio Z) : ∃ m : ℕ → ℕ, s.floorL ≤ m ∧ ∀ g, m ≤ g → First {s with floorL:=g} K Z := by
  choose N hN using fun j i : ℕ => starts Z hZ (query s K j i)
  refine ⟨fun j=>max (s.floorL j) (fromMax N j), fun j=>le_max_left ..,fun g hg j i hj _ L hL => hN j i L ((le_fromMax N hj).trans ((le_max_right ..).trans ((hg j).trans hL)))⟩

def requestW (Z : Rolls s) (C : Programs s) (Bt : Baton G) (j i : ℕ) := if h : StepStages j i ∧ s.first ≤ i then battle (C j i) Bt (Clockwork.patch Z h.1 h.2) s.kernel else 0
lemma widths {D : Rolls s} (C : Programs s) (Bt : Baton G) (h : First s K Z) : ∃ h : ℕ → ℕ → ℝ, ∀ w : ℕ → ℕ → ℝ, h ≤ w →
    ∃ b : ℕ → ℕ → Cafe, requestW D C Bt ≤ w ∧ ∀ j i, StepStages j i → s.first ≤ i →
      2*storeCost (C j i) ≤ (b j i).r ∧ Outlet (b j i) (query s K j i) (D.L j) (w j i) Z := by
  have he (j i : ℕ) : ∃ h : ℝ, ∀ w : ℝ, h ≤ w → requestW D C Bt j i ≤ w ∧ ∃ b : Cafe, StepStages j i → s.first ≤ i →
      2*storeCost (C j i) ≤ b.r ∧ Outlet b (query s K j i) (D.L j) w Z := by
    by_cases hi : StepStages j i ∧ s.first ≤ i
    · obtain ⟨y,hy⟩ := eventually_atTop.mp (h j i hi.1 hi.2 (D.L j) (D.large j).need)
      exact ⟨max (requestW D C Bt j i) y,fun w hw => ⟨(le_max_left ..).trans hw,(hy w ((le_max_right ..).trans hw) _).imp fun _ he _ _ => he⟩⟩
    exact ⟨_,fun w h => ⟨h,⟨1,1,1,1,1⟩,fun a b=>False.elim (hi ⟨a,b⟩)⟩⟩
  choose h he using he
  refine ⟨h,fun w hw => ?_⟩
  choose b hb using fun j i => (he j i (w j i) (hw j i)).2; exact ⟨b,fun j i => (he _ _ _ (hw j i)).1,hb⟩
end YM.PhysicalNext.JointLoad.Psalm.Refit

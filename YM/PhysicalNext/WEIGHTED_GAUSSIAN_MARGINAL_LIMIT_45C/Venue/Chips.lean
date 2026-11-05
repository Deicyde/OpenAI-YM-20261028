import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Venue.Width

/-!
# Reissuing pronouncements on *every* collection of link colors

Use `Remote.chip_repair` and mean `focused` on neighborhoods in the
bigger charged patch, before geometric comparisons. One W reference
on every one from the original career. Costs after tier,K. Fill tree
thaws on all endpoints simultaneously, never combining claims over
independent axial gauges.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Venue
open AnalyticBridge.LocalGaussianLaws
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent Remote Lift Extra.Iteration.Scales MeasureTheory Local
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

private lemma alter (G : Gauge) (P : Patch) (x A R t : ℝ) (hR : 1≤R) (ht : 0≤t) (hA : 0 ≤ A) :
    matter G P x A (R*t) ≤ matter G P x (R*A) t := by
  let y := R*A; have hx : A ≤ y := le_mul_of_one_le_left hA hR
  let z := wiggle x y t; have hz : wiggle x A (R*t)=z := by unfold z wiggle y; ring
  have h0 : 0≤ z := wiggle_nonneg _ (hA.trans hx) ht
  unfold matter; rw [hz]; apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pieces_nonneg ..) (Nat.cast_nonneg _))
  change (A+z)*z+z*A ≤ (y+z)*z+z*y
  gcongr

-- Front α and *both* estimates common. Transaction after all params.
theorem aperture (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (r : ℕ) (R : ℝ) (hR : 1≤R) :
    ∀ᶠ x : ℝ in atTop,∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Booth Pt S T →
    Larger (G:=G) S → 100*(1+vista r x)≤c.val →
    ∀ (A : Stores S) (o : Site c), Clears A x o (vista r x) → ∀ V : Config G c, A.flags = RG.flags (temp x) V →
    ∀ (Q : Dir G c), AgreeNear id o (vista r x) V (represent Q) → ‖Q‖ ≤ R*clearanceFare x →
    paid S (replica S.ratio V) o (vista r x) (R*clearanceFare x) → ∀ (F : Forest S.ratio) (k : S.Choices) (q : Chi)
      (d : ℝ) (g : Geometry) (Y : LinkArray G (Frozen A x F)),
    let a:= portrait T A F k x V g q d Y; let b := portrait_head T F Q; let Z:= bareStores S
    let M := panoramic T A F k x V g; let K:= panoramic T Z F k x 1 g; let s:=official A F (x:=x) (G:=G)
    ∀ i : In x A F (G:=G), separation o (front A F i)≤vista r x /4 →
      |a i - b (loadLink A F x i)| ≤ x^(-(7/8):ℝ) ∧
        ∀ j : In x A F (G:=G), |M j i-K (s j) (s i)| ≤ x^(-(1/4):ℝ) := by
  obtain ⟨A,X,s,E,N,M,τ,δ,hA,hX,hs,hE,hN,hM,hτ,hδ,H⟩ := focused G P Pt.bind Pt hp rfl
  obtain ⟨C,δ',hC,hδ',HC⟩ := chip_repair G P Pt.bind Pt.top.clip Pt.top.paths hp Pt.top.paths_pos.le
  obtain ⟨Ω,hΩ,hh⟩ := Next.SectorChange.Gap.not_flat G P Pt hp
  obtain ⟨D,hD,hM'⟩ := Next.SectorChange.Gap.stood G P Pt
  have hR' := zero_le_one.trans hR
  filter_upwards [H, pay_mean G P R A X s E N M τ hR' hs hτ hA hX (zero_le_one.trans hN) (zero_le_one.trans hM) hE,
    (boundary_limited R hR').eventually (ge_mem_nhds (lt_min hδ' hδ)),Work.E01.radiusB_tendsto.eventually_ge_atTop 200,small_span P,
    hh,fares G P (R*C) (by positivity) (η:=Ω) (H:=D) (δ:=δ') hΩ hD hδ'] with x H he hr hY hP HN hG c f S T H0 HP hL hT B o hx V hB Q hz hu hv F k q d g y
  intro a b Z m K w i hi
  let L := radiusB x; let t:= R*clearanceFare x
  have hX0 : 100*(1+L)≤c.val := (Nat.mul_le_mul_left _ (Nat.add_le_add_left (vista_large r x) _)).trans hT
  have ht := hG.1
  have h : 0≤t := mul_nonneg hR' ht
  obtain ⟨p,H1,H2,H3,H4⟩:= relocate r B o hx V Q hz hv _ hi
  constructor
  · have h := H _ h (hr.trans (min_le_right ..)) S T H0 HP hX0 B p F H2 V hB Q hu H4 H3 k q d y i H1 g
    exact h.trans he
  intro j
  have hw : FreeResolvent.Gap (Rows.gram T x V k (shots S x) B F) Ω := ⟨HN _ _ H0 hX0 HP.1 B F k V hB⟩
  have hj : FreeResolvent.Gap (Rows.gram T x (1:Config G c) k (shots S x) Z F) D := ⟨hM' S T H0 (by rw [← H0]; exact hL.2.1) (by omega) HP.1 x Z F k⟩
  obtain ⟨W,U,hD',-⟩ := HP.1.feeds
  have haD : (census G P x (R*C) Ω D) ≤ x^(-(1/4):ℝ) := hG.2.2
  have hz : clockChip G S x t 0 Ω D C ≤ x^(-(1/4):ℝ) := by
    refine le_trans ?_ haD; rw [← H0,census,clockChip]; simp only [add_zero]; dsimp only [slotCount,LocalJet.chips]
    gcongr; exact alter G S.patch x C R _ hR ht hC
  exact (HC t h (hr.trans (min_le_left ..)) S H0 HP.1.knobs T W Pt.top.width HP.1.high hD' x p L V (by omega) H4 k B F g Ω D 0 hΩ hD le_rfl H2 hw hj _ _ (by unfold boxCharge; unfold L; omega)).trans hz
end YM.PhysicalNext.WeightedGaussianMarginal45C.Venue

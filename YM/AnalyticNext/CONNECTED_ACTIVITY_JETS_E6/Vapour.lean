import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.District

/-!
# Exact recoupling of compulsory products on a layout

Overlap by 500B tested halos; consuming through 304B uses transition
fixed-L radius. Each product retains its chosen membership in A,V, and so
is identical on full products EVEN when vanishing at tagged paths. Mean
orientation term summed before using. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {l : ℕ} (X : Coat T F) {Y : Finset (Stores S)}

lemma arranges (h : Layout X.seeds l X.B Y) (hv : 500≤l) (u : Directions G f)
    (R : Rep G f) (Ñ : ChartRatio G) (a : ℝ) (hp : 100 ≤ X.B) :
    X.steamLog R Ñ a X.seeds u = ∑ A ∈ Y, X.steamLog R Ñ a A u := by
  let B:=X.B
  have hv₁ : 500*X.B ≤ l*X.B := Nat.mul_le_mul_right _ hv
  have hZ₁ : 200*X.B ≤ l*X.B := by omega
  have hr := fun s => h.streamed _ hZ₁ s
  have hC (s : Signed) : X.assigned X.seeds u s=∑ i∈Y,X.assigned i u s := (hr s).price_sum _
  have hI (s : Signed) := (hr s).price_sum (X.extracted X.μ s)
  have ht : X.quoteNear X.seeds u=∑ A∈Y,X.quoteNear A u := by
    unfold quoteNear Oriented.averaged; simp_rw [hC]
    rw [sum_comm]; rw [Finset.mul_sum]
  have hh : X.far_bills X.seeds = ∑ A∈Y,X.far_bills A := by
    unfold far_bills Oriented.averaged; simp_rw [hI]; rw [sum_comm,Finset.mul_sum]
  have hz := (h.plaza_sub (304*X.B) (by omega) X).price_sum (X.gentry Ñ a u)
  have hv := (h.wraps (200*X.B) (by omega)).price_sum (X.condensation)
  have hd : Layout.Split Y (X.pens X.seeds) X.pens := (h.wraps (10*X.B) (by omega)).filtered (fun i => i∉F.trunks)
  unfold steamLog; rw [ht,hh,hz,hv,← hd.union, Finset.card_biUnion hd.split]; push_cast
  simp only [sum_add_distrib, sum_sub_distrib,Finset.sum_mul, mul_add,Finset.mul_sum]

private lemma mandatory_match (h : Layout X.seeds l X.B Y) (hv : 500≤l) (b : Stores S) (hh : b∈Y) :
    let o := b.dome (300*X.B)
    (∀ i∈ readFine o S,i∈b.costs ↔ i∈X.seeds.costs) ∧ ∀ i∈readBonds o, i∈b.aisles ↔ i∈X.seeds.aisles := by
  intro o
  have ht p (he : p∈Packets.seeds S X.seeds) (hp : ¬Disjoint o (Packets.points S p)) : p∈Packets.seeds S b := by
    refine h.points_join hh he (fun H => hp (H.mono_left (Lattice.Corona.halo_mono
      (Nat.mul_le_mul_right X.B (show 300≤l by omega)) (Finset.Subset.refl _))))
  constructor <;> intro i hi
  · have he X : Sum.inl i ∈ Packets.seeds S X ↔ _ := inl_mem_disjSum
    exact ⟨fun H => (he _).mp (h.fuses _ hh ((he _).mpr H)),fun H => (he _).mp
      (ht _ ((he _).mpr H) (mem_filter.mp hi).2)⟩
  have he X : Sum.inr (Sum.inl i) ∈ Packets.seeds S X ↔ i∈X.aisles := by simp [Packets.seeds]
  exact ⟨fun H => (he _).mp (h.fuses _ hh ((he _).mpr H)),fun H => (he _).mp
    (ht _ ((he _).mpr H) (mem_filter.mp hi).2)⟩

lemma cultures (h : Layout X.seeds l X.B Y) (hv : 500≤l) (U : Config G f) (W : ℝ) (hp : 100≤X.B) :
    Mask.profiles X.seeds X.χ (300*X.B) X.x W U X.k X.V=∏ A∈Y, Mask.profiles A X.χ (300*X.B) X.x W U X.k X.V := by
  let t := 300*X.B
  have hZ : 2+t ≤ l*X.B := by
    unfold t; have ht := Nat.mul_le_mul_right X.B hv; omega
  have hf := (h.subFace t hZ).price_prod (fun i => Mask.fine X.seeds X.χ i X.t U)
  have hz := (h.subPin t hZ).price_prod (fun i => Mask.noise X.seeds X.χ i X.t W U X.k X.V)
  unfold Mask.profiles; dsimp only; rw [hf,hz, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro i hi
  obtain ⟨hC,hY⟩ := mandatory_match X h hv i hi
  apply congr_arg₂ (· * ·) <;> apply prod_congr rfl <;> intro j hj
  · by_cases hm : j∈i.costs <;> simp [Mask.fine,← hC j hj,hm,Coat.t]
  by_cases hm : j∈i.aisles <;> simp [Mask.noise,← hY j hj,hm,Coat.t]

lemma mates (h : Layout X.seeds l X.B Y) (hv : 500≤l) (U : Config G f) (hp : 100≤X.B) :
    Mask.tickets X.seeds (300*X.B) U X.k =∏ A∈Y, Mask.tickets A (300*X.B) U X.k := by
  have ht := Nat.mul_le_mul_right X.B hv
  unfold Mask.tickets; dsimp only
  rw [(h.sectors (d:=300*X.B) (by omega)).price_prod,(h.subPin (300*X.B) (by omega)).price_prod,← prod_mul_distrib]

lemma vents (h : Layout X.seeds l X.B Y) (hv : 500≤l) (u : Directions G f) (hp : 100≤X.B)
    (R : Rep G f) (Ñ : ChartRatio G) (l' : Finset ℕ) (W a : ℝ) (hM : X.manifest) :
    (∏ Z∈Y, X.Pack R Ñ l' W a Z u)= X.steam R Ñ l' W a X.seeds u := by
  have ht := Layout.collects h T hM rfl rfl hv
  have he : (∏ Z∈Y, X.Pack R Ñ l' W a Z u)=∏ Z∈Y,X.steam R Ñ l' W a Z u :=
    Finset.prod_congr rfl fun Z hZ => if_pos (ht Z hZ)
  rw [he]; unfold steam
  symm
  have h₁ : 500*X.B≤l*X.B := Nat.mul_le_mul_right _ hv
  have hz : ∀ t, t ≤ 400*X.B → t≤ l*X.B := by omega
  have hh : ∀ d, d ≤304*X.B → 2+d≤l*X.B := by omega
  let v := X.input u
  dsimp only; rw [X.cultures h hv _ W hp,X.mates h hv _ hp, X.arranges h hv _ _ Ñ a hp, Real.exp_sum]
  unfold Contract.order Coat.enforce
  rw [(h.subFine (300*X.B) (hz _ (by omega))).price_prod,(h.plaza_sub (304*X.B) (hh _ le_rfl) X).price_prod]
  simp only [prod_mul_distrib]
end YM.ConnectedActivityE6.Coat

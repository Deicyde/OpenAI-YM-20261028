import YM.FullVolume.Sector.Shook
/-! Gaussian toll with width restoration. Lease all b:Clock not reloading if ξ' tiny post. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
structure Margin (G:Gauge)(L:Side)(x α δ:ℝ) :Prop where
    hp:0<α
    notes: δ * (2*(Animals.ballCost (radiusB x):ℝ)* (Itinerary.density L:ℝ)*Fintype.card G.ColorIndex) ≤ α
lemma pocketsC (G : Gauge) (L:Side) {α:ℝ} (h:0<α): ∀ᶠ x in atTop, Margin G L x α (thaw G L x):=by
  have hh: Rate G L 0 (fun x=>2*(Animals.ballCost (radiusB x):ℝ)*(Itinerary.density L:ℝ)* Fintype.card G.ColorIndex):= by
    have ht:= Census.width_rate G L 1 0; simp only [one_mul,add_zero] at ht; exact ((ht.mul_left 2).mul_right _).mul_right _
  have ht := (Rate.power (a:=-(1/128)) |>.mul hh).below (by norm_num) α h; filter_upwards [ht] with x hx; exact ⟨h,(le_abs_self _).trans hx⟩
namespace Margin
lemma painter {G L X α δ} (H:Margin G L X α δ)(he:S.patch.L=L) (Y:Support c) (h:0≤δ): (1+δ)^(2*((lensS (edgesM S Y (radiusB X)) G).card)) ≤ Real.exp (α*coverNumber (radiusB X) Y):=by
  let I:= edgesM S Y (radiusB X); let J:= lensS I G
  let n:=2*J.card
  let Z:=coverNumber (radiusB X) Y
  have ht: (I.card:ℝ) ≤ Y.card*(Itinerary.density S.patch.L:ℝ):= by
    let P := Finset.univ.filter fun i:Bond f=> atEdge S i∈Y; have hh : I⊆P:=fun i hi=> Finset.mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 _ (by simp)⟩
    exact_mod_cast (card_le_card hh).trans (perch S Y)
  have hk: (Y.card:ℝ) ≤ (Z:ℝ)*(Animals.ballCost (radiusB X):ℝ):= by unfold Z; exact_mod_cast brood Y _
  have hx : n=(2*I.card*Fintype.card G.ColorIndex):= by simp only [n,J,lensS,Finset.card_product,Finset.card_univ]; ring
  have hp: (n:ℝ) ≤ Z * (2*(Animals.ballCost (radiusB X):ℝ)*(Itinerary.density L:ℝ)*Fintype.card G.ColorIndex):= by
    rw [hx]; push_cast; rw [he] at ht; have hp:=mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg (α:=ℝ) (Itinerary.density L))
    apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ht.trans hp) (show 0≤(2:ℝ) by norm_num)) (Nat.cast_nonneg _)); exact le_of_eq (by ring)
  have he : δ * (n:ℝ) ≤ α*Z := by nlinarith only [mul_le_mul_of_nonneg_left hp h, mul_le_mul_of_nonneg_right H.notes (Nat.cast_nonneg (α:=ℝ) Z)]
  apply (pow_le_pow_left₀ (show 0≤1+δ by linarith) ((add_comm ..).trans_le (Real.add_one_le_exp δ)) n).trans
  rw [← Real.exp_nat_mul]; exact Real.exp_monotone ((mul_comm ..).trans_le he)
end Margin
-- moment costs (quantities call V,flow). only charge poly footprint once. Constant at actual p.
structure Lake (G:Gauge)(L:Side)(p:ℝ)(j:ℕ)(A:ℝ→ℝ)(n:ℕ): Prop where
  pay : ∀ (x a b e:ℝ), 1≤e→0≤a→ a≤e*(Animals.ballCost (radiusB x):ℝ)*(Itinerary.density L:ℝ) → b=a*Fintype.card G.ColorIndex→
      (1+a+b+b)^j*(1+b*(2*Real.exp (p*(j:ℝ)^2/2))) ≤ |A x| * e^n
namespace Lyre
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
local notation "δ'"=> radiusB x₀
local notation "p'"=> payE o.eta o.gap o.ample (Census.tubularPrice G L)
def fieldP (X:Support c):= X -- edit
variable {V:ℝ→ℝ} (W':Lake G L (payE o.eta o.gap o.ample (Census.tubularPrice G L)) (K*j*2) V k)
-- polynomial bounds including H.shape. integral hV with alarm via L².
include W'
lemma fares {X:Coat T F} (hX:X.x=x₀) (hχ:X.χ=χ)(hp:X.width=o.K) (hm:X.manifest) (i:Molecule S):
    let e:=(X.catastrophe (o.ξ/2) R.beta (blaze i))
    let f(z:Air f G):= Flux.facescale (stampD (H:=H) i) z^(K*j)
    Integrable (e.indicator f) X.dice ∧ (∫ x,e.indicator f x ∂ X.dice)≤ ((1+|V x₀|)*(1+H.shapeW i)^k)*M.pole.stencil.rad^(blaze i).card := by
  intro e f'
  have h:= H.laws.data; have hk:= (h.localP F X hX hp hm).sails
  let T':=stampD (H:=H) i; let g:= 1+H.shapeW i; let p:=1+ |V x₀|
  have hg: 1≤g:= le_add_of_nonneg_right (H.positive_volume _)
  have hv: 1≤p:=le_add_of_nonneg_right (abs_nonneg _)
  have ht : MeasurableSet e:= Poll.sounded ..
  have hΨ: Integrable (fun x=> f' x^2) X.dice := by unfold f'; simp_rw [← pow_mul]; exact (Flux.globes T' hk _).1
  have hJ: (T'.card:ℝ)≤g*(Animals.ballCost (radiusB x₀):ℝ)* (Itinerary.density L:ℝ):= by
    have he:= crewsC H i; rw [h.funds.length_eq] at he; apply he.trans; unfold g; gcongr; linarith
  have hz : ((lensS T' G).card:ℝ)=(T'.card:ℝ)* Fintype.card G.ColorIndex := by simp [lensS]
  have hy := W'.pay x₀ (T'.card:ℝ) ((lensS T' G).card:ℝ) g hg (Nat.cast_nonneg _) hJ hz
  have hv' := (Flux.globes T' hk (K*j*2)).2.trans hy
  have hD:= (Flux.globes T' hk (K*j)).1
  let v:=M.pole.stencil
  have hE: (∫ x,f' x^2 ∂ X.dice)≤(p*g^k)^2:=by
    unfold f'; simp_rw [← pow_mul]; exact hv'.trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans hg) _)).trans (le_self_pow₀ (one_le_mul_of_one_le_of_one_le hv (one_le_pow₀ hg)) (by omega)))
  exact ⟨hD.indicator ht,Flux.divideC X.dice f' hD _ (by positivity) e ht (by rw [← pow_mul,_root_.mul_comm (blaze i).card,pow_mul]; exact v.ship F X hX hp hχ hm (blaze i)) (pow_nonneg v.awake _) hΨ hE⟩
end Lyre
end YM.ConnectedActivityE6.Empire

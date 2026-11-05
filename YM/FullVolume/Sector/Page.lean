import YM.FullVolume.Sector.Gym
/-! Gaussian scalp pressure.Determinant with marginal dimensions. -/
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
namespace Lyre
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
local notation "ψ" => U.pole
variable (X : Coat T F)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U₀:E→ Config G c} {s:E} (hx:X.x=x₀)(he:X.width=o.K)(hv:X.χ=χ)(hm:X.manifest)(hy:U₀ s=X.V)(hU:Mode U₀ s j u)
variable (z:Air f G)
local notation "Λ" => U.pole
local notation "β"=> R.beta
local notation "w₀"=> radiusB x₀
local notation "I₀" => X.input (worldZ X β z)
local notation "f₀" => fun i=> steer X A (worldZ X β z) (U₀ i)
local notation "z₀" => fun i=> course X A β z (U₀ i)
local notation "Yd"=> fun i=> vary X (U₀ i)
section scalars
variable (I : Finset (Bond f)) (c':ℝ) (hc:1≤c')
local notation "μ'"=> circuit (lensS I G) X.relating
local notation "z'"=> swim (lensS I G) z
def markL (c':ℝ) := Alabaster.walk (μ') c' z'
lemma present : markL X z I c'= c'^((lensS I G).card)*Real.exp ((1-c'^2)*(dotProduct (WithLp.ofLp z') ((μ')⁻¹ *ᵥ (WithLp.ofLp z'))/2)):=by
  unfold markL Alabaster.walk; rw [temper (μ') (z') c']; rw [show Fintype.card (↥(lensS I G))= (lensS I G).card from Fintype.card_coe _]; have ht:= fullFuel (μ') z'; field_simp
include hc
lemma propi (ht:X.relating.PosDef): 0≤ markL X z I c' ∧ markL X z I c'≤c'^((lensS I G).card):= by
  have hp:(μ').PosDef:= ht.submatrix Subtype.val_injective; have h:0 ≤ dotProduct (WithLp.ofLp z') ((μ')⁻¹ *ᵥ (WithLp.ofLp z')):= hp.posSemidef.inv.dotProduct_mulVec_nonneg _
  rw [present]; have he:0≤c':=zero_le_one.trans hc
  exact ⟨by positivity,mul_le_of_le_one_right (pow_nonneg he _) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (div_nonneg h (by norm_num))))⟩
lemma vigor : facescale I (c' • z)≤ c'*facescale I z:=by
  have ha:0≤c':= zero_le_one.trans hc
  unfold facescale; simp_rw [PiLp.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg ha,← Finset.mul_sum]; nlinarith [le_mul_of_one_le_left (show 0 ≤ 1+(I.card:ℝ)+(lensS I G).card by positivity) hc]
end scalars
-- Frame exponent independent V on world scaling. Reconstruct.
variable (I : Finset (Bond f))
abbrev printScale (I : Finset (Bond f)) (t:ℝ) (Y:Config G c) := markL X z I (U.pole.flow t)*scalp I X Y (U.notes t).beta A ((Λ).flow t • z)
include M
lemma stripe (Z:Config G c) {i:ℝ} (hi:|i|≤6*v) : printScale (U:=U) (A:=A) X z I i Z= scalp I X Z R.beta A z*(Λ).flow i^((lensS I G).card)*Real.exp ((Λ).sqcost i*draftI X I R.beta A Z z):=by
  have ht:= U.seats i hi; have hc:0 < U.pole.flow i:= zero_lt_one.trans_le (Λ|>.moves i hi |>.1); have hg:= M.pole.solid
  let t:=(circuit (lensS I G) X.relating)⁻¹; let x:= swim (lensS I G) z; let y:= dotProduct (WithLp.ofLp x) (t *ᵥ (WithLp.ofLp x))/2
  have hv: draftI X I R.beta A X.V z=y:= by unfold draftI; rw [Silica.home X hg z (U.seats i hi|>.pos)]; rfl
  have hh:=sail ht X I z Z A b hg; dsimp only at hh; rw [U.pitch i hi,hv] at hh
  unfold printScale; rw [present X z I, hh]; unfold Fold.sqcost
  rw [show ((1-U.pole.flow i^2)*draftI X I R.beta A Z z)= (1-U.pole.flow i^2)*y+(1-U.pole.flow i^2)*(draftI X I R.beta A Z z-y) from by ring, Real.exp_add]; unfold y x t; ring
abbrev price (G : Gauge)(δ:ℝ)(j:ℕ):ℝ:= (FullVolume.Ray.Fold.charge j)*(1+δ)^(2*((lensS I G).card))
include M hx he hv hm hy hU
lemma chargeD : Weigh j s v (price I G δ j) (L'* (2^K)* facescale I z^K) (fun i x=> printScale (U:=U) (A:=A) X z I i (U₀ x)):= by
  let P x:= scalp I X (U₀ x) R.beta A z; let G' x:= draftI X I R.beta A (U₀ x) z; let n:=(lensS I G).card
  let f:= Fold.jet (Λ) P G' n; have h t (ht:|t|≤6*v): (fun x=> printScale (U:=U) (A:=A) X z I t (U₀ x))= f t := funext fun x=> stripe M X z I _ ht
  obtain ⟨hp,hH⟩:= ((M.pole.rays F X hx he hv hm E U₀ s hy hU).2 z).2 I
  have hh:= (Λ).full.2.2; have ha : 1 ≤ facescale I z := (Flux.expenses ..).1; have hF:=M.pole.pos
  have hv': Weigh j s v (Fold.charge j*(1+δ)^n *((1+δ)^n)) (L'* (2^K)*facescale I z^K) f := by
    apply Fold.scores hp.smooth hH (by positivity) (by positivity)
    intro i; let a:=v*(Λ).seat (G' s) i
    change Brush j _ _ (f a) s; rw [← h a (U.away ..)]
    obtain ⟨hU',hh'⟩:= (Λ).moves a (U.away ..)
    let t:=(Λ).flow a
    have hD:= ((M.plot a (U.away ..)).rays F X hx he hv hm E U₀ s hy hU).2 (t • z)|>.2 I|>.1
    obtain ⟨hv',he'⟩:= propi X z I _ hU' (H.laws.data.localP F X hx he hm).sails.fullC
    have hz:= hD.smul (markL X z I t); rw [Real.norm_of_nonneg hv',mul_one] at hz
    refine hz.climb (he'.trans (pow_le_pow_left₀ (zero_le_one.trans hU') hh' n)) ?_
    rw [mul_assoc L',← mul_pow]; refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (Flux.expenses ..).1) ?_ K) hF
    exact (vigor z I t hU').trans (mul_le_mul_of_nonneg_right (by have h':= hh'.trans (add_le_add_right (Λ).active 1); exact h'.trans (by norm_num)) (zero_le_one.trans ha))
  exact (hv'.loses (le_of_eq (by unfold price; rw [two_mul,pow_add]; ring)) le_rfl).cong (fun i hi=>EventuallyEq.of_eq (h _ (U.lay hi)))
end Lyre
end YM.ConnectedActivityE6.Empire

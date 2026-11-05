import YM.FullVolume.Sector.Fizz
/-! Orbit to all payload values.(Likely phase.Price). -/
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
namespace Tune
variable (U:Tune H v δ)
-- continuation of raw labels. Reimburse Sales optional once.
local notation "Λ" => U.pole
local notation "t'"=> U.notes
local notation "B₀" => radiusB x₀
local notation "Q'" => stella Q
local notation "A'" => topStorm S.patch
variable {p:Lyre.Signal 0} {ν:ℝ}
local notation "g"=> Q.goal L x₀
local notation "g₀"=> plainP U p ν
local notation "g₁"=> totalP U p ν
variable {α:ℝ} (hc:Clear Q L μ ν x₀ v p) (hr:Lyre.Clarity H 0 C δ ν) (hM:Margin G L x₀ α δ) (hv:2≤v)
local notation "f'"=> U.incomeK α ν p
variable (X:Coat T F) (hx:X.x=x₀)(he:X.width=o.K) (hm:X.manifest) (k:Finset ℕ) (i:Molecule S)
-- all marginal Bochner currency
lemma income_pos (α ν) (p:Lyre.Signal 0)(i:Molecule S):0≤ U.incomeK α ν p i:=by
  unfold incomeK weightK; rw [← U.swell]; exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (prod_nonneg fun i _=> U.propense _) (pow_nonneg H.pos _))
include hx he hm hc hr hM
lemma hier : Rebar v (fun t=> X.attains (U.notes t) Q.table W o.a k Q.halo i) (U.incomeK α ν p i):=by
  let V:= (F.order G).prod X.dice
  let I:= Lyre.stampD (H:=H) i; let J:= lensS I G; let p0:= J.card
  let u z:= Pond.swim J z
  let A(t:ℝ) (x:F.Slice G × Air f G):= Lyre.markL X x.2 I ((Λ).flow t) * U.content X k i t x
  let Sk:= X.catastrophe o.ξ R.beta (blaze i)
  let D:=(1+δ)^p0; let gP:=(∏ j∈i,g₀ j); let L (p:F.Slice G × Air f G):=Sk.indicator (fun _=> D*gP) p.2
  have hP:= H.laws.data; have hv: X.relating.PosDef:= (hP.localP F X hx he hm).sails.fullC
  have hf (t:ℝ)(ht:t∈sun): Integrable (A t) V ∧ X.attains (U.notes t) Q.table W o.a k Q.halo i=∫ p,(A t p) ∂V:=by
    have hh:= U.lay ht; let Y:=U.beams t hh; let a:= (Λ).flow t; have hk:= Y.laws; let D:=X.body (U.notes t) Q.table W o.a k Q.halo i
    have hb : StronglyMeasurable D := (X.body_b Q.table_exists (show Intake P T X.x (U.notes t) from hx.symm ▸ hk.intake) (by rw [hx,he]; exact hk.data.access) o.a k _ _).stronglyMeasurable
    have hs: J=podium S G (Y.unionP i) X.B:= by unfold J I Lyre.stampD; rw [Flux.chargedU,U.stage t hh,show X.B=B₀ from congr_arg _ hx]
    have he' (u v:Air f G) (h:swim J u=swim J v) (p:F.Slice G): D (p,u)=D (p,v):=by
      let Y':=X.wrapY p; rw [hs] at h; exact Y.concord i Y' Y' ⟨Village.refl ..,(observe _).mp h,fun _ _=>Iff.rfl⟩ hx (Finset.Subset.refl _)
    exact root_lens X J hv hb he' (Y.integrated X hx he hm k i) a (by unfold a; exact zero_lt_one.trans_le ((Λ).moves t hh).1) -- omitted
  have hs:MeasurableSet Sk:= Poll.sounded ..
  have hX:Integrable L V:= ((integrable_const _).indicator hs).comp_snd _
  have hθ:=Λ|>.full.2.2
  have hk (x:F.Slice G × Air f G):Scout v (fun t=> A t x) (L x):=by
    have h:= (U.glass_w X I x.2 hv).multiplies (gains U X k i hc hr hx he hm x); by_cases hp:x.2∈Sk
    · rw [show L x=D*gP from Set.indicator_of_mem hp _, ← show D * (Sk.indicator (fun _=> gP) x.2)=D*gP from congr_arg _ (Set.indicator_of_mem hp _)]; exact h
    rw [show L x=0 from Set.indicator_of_notMem hp (fun _=> _ : Air f G→ℝ)]; apply h.enlarged; change D*Sk.indicator (fun _=>gP) x.2≤_; rw [Set.indicator_of_notMem hp,mul_zero]
  refine ⟨U.normed,U.income_pos ..,fun w t he₁=>?_⟩
  let T p:= FullVolume.Ray.trace w (fun t=> A t p); have ht:0≤ t := (norm_nonneg _).trans (he₁ 0)
  have hf' (i:↑sun) : Integrable (fun x=> w i • A i.val x) V:= ((hf _ i.2).1).smul (w i)
  have hu : Integrable T V:= integrable_finsetSum _ (fun i _=>hf' i)
  rw [show FullVolume.Ray.trace w _= ∫ p,T p ∂ V from ?_]; swap
  · unfold T FullVolume.Ray.trace; rw [integral_finsetSum _ (fun i _=> hf' i)]; apply sum_congr rfl; intro y hy; dsimp only; rw [integral_smul (w y), (hf _ y.2).2]
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono hu.norm (hX.const_mul t) (fun i=> (hk i).beam _ _ he₁)).trans; rw [integral_const_mul]; apply mul_le_mul_of_nonneg_left _ ht
  have hh : (∫ p,L p ∂V)= X.dice.real Sk * (D*gP):=by -- edit
    have he (i:F.Slice G) : ∫ z,L (i,z) ∂X.dice=X.dice.real Sk*(D*gP):= integral_indicator_const (D*gP) hs
    unfold V; rw [integral_prod _ hX]; simp_rw [he,integral_const,probReal_univ,one_smul]
  rw [hh]; unfold incomeK weightK; rw [← U.swell]; change _ ≤ _*(gP*_)
  set a:=X.dice.real Sk; have hδ : a ≤ H.alarms^(blaze i).card:= ((H.quotes F X hx he hm).2.2.2 (blaze i)).1; have hD:D≥0:=by unfold D; positivity
  have hu:0≤ gP:=by unfold gP; exact prod_nonneg fun i _=> U.propense _
  have hx: (1:ℝ) ≤ 1+δ:=le_add_of_nonneg_right hθ
  let f:= Real.exp (α*coverNumber B₀ (H.unionP i)); have hZ:D≤f:= (pow_le_pow_right₀ hx (show p0≤2*p0 from (by omega))).trans (hM.painter hP.funds.length_eq (H.unionP i) hθ)
  exact (mul_le_mul hδ (mul_le_mul_of_nonneg_right hZ hu) (mul_nonneg hD hu) (pow_nonneg H.pos _)).trans_eq (by ring)
end Tune
end YM.ConnectedActivityE6.Empire

import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Candor

/-! # Actual dictionary diagram on the shared visual field -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Formal
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open AnalyticBridge.Sharp AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace YM.PhysicalNext.Dictionary.Formal ENNReal
open Wires Geo Notify Voice Voice.Check Voice.Defenses Parcel Shipment Lobbies SectorNext.Reconnect SectorNext.Reconnect.Words
open Finset hiding card
variable {G : Gauge} {c f : Side} {S : StepData c f} {I : Type} [DecidableEq I]
    (D : AnalyticBridge.LocalGaussian.Desk G S) (h : Lit D) (F : Forest S.ratio) (A : Stores S) (k₀ k : S.Choices) (V : Config G c) (Z : Art I D) (H : Shipment.Valid D I Z) (s : ℝ) (m : Finset I)
local notation "K₀"=>icons D Z
local notation "L₀"=>stars D F k₀
local notation "B₀"=>theater D Z h F k₀ V
local notation "H₀"=>chosen D F k₀ A k

/-- Denotes the actual *uncensored* marker formula (no artificial
unmarked-first insertion or multiple uses); reference value on every
mode. For actual input correspondence see Bands & Quiet adapters. -/
def carrier (U : Config G f) : ℂ := ∑' i,caption D Z m i U

theorem quiet (U : Config G f) : carrier D Z (∅) U=(↑(D.input.eval U) : ℂ) := by
  let f₁ i:=caption D Z ∅ i U; let e (b : Finset ℕ) : Head I := (∅,∅,b,∅)
  have ht: Injective e := fun i j he=>(by simpa [e] using he)
  have hn (i) (hx:f₁ i≠0) : i∈Set.range e := by
    have hp : introits D Z ∅ i ∧ D.labels.admissible D.input.p U (team i) := of_not_not (fun hp=>hx (if_neg hp))
    have hh (t) (h : t∈ emissions i) : token D Z t=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun k hk=>
      Finset.notMem_empty _ (hp.1.1.1 ▸ (Finset.mem_biUnion.mpr ⟨t,h,hk⟩)))
    have hl : menu i= ∅:=Finset.eq_empty_iff_forall_notMem.mpr (fun j hj=> (hp.1.2.2.1 j hj).ne_empty (hh (.inr (.inl j)) ((emissions_at i _).mpr hj)))
    have hr : torn i= ∅:=Finset.eq_empty_iff_forall_notMem.mpr (fun j hj=> (hp.1.2.2.2 j hj).2.ne_empty (hh (.inr (.inr j)) ((emissions_at i _).mpr hj)))
    have h₁ : coin i= ∅:=Finset.eq_empty_iff_forall_notMem.mpr (fun j hj=>Finset.singleton_ne_empty j
      (show _=∅ from hh (.inl j) ((emissions_at i _).mpr hj)))
    exact ⟨team i, Prod.ext h₁.symm (Prod.ext hl.symm (Prod.ext rfl hr.symm))⟩
  let a:=Real.exp (D.input.exponent U)
  have he (b : Finset ℕ) : f₁ (e b)= (↑(a * D.labels.gasOccurrence D.input.p b U):ℂ) := by
    have h₁ : introits D Z ∅ (e b) := by
      unfold introits Formal.signal emissions; simp [e,coin,Fleet.pure,menu,torn]
    unfold f₁ caption edition lookup Shipment.answer Activities.gasOccurrence
    by_cases hh:D.labels.admissible D.input.p U b
    · simp only [h₁,team,e,hh, true_and,↓reduceIte,torn,Finset.notMem_empty,exists_const]
      unfold outward a; simp [coin,menu,Desk.labels]
    simp [h₁,e,team,hh]
  unfold carrier
  change ∑' i, f₁ i=(D.input.eval U:ℂ)
  rw [← ht.tsum_eq hn]; simp_rw [he]
  unfold Rep.eval Activities.gas
  rw [← Complex.ofReal_tsum (fun c=>a*_), tsum_mul_left]

/-- Complex analogue of the normalized body. -/
def living (uPAGE : (H₀).Visual) := (↑(Ground.staple D F k₀ k V A uPAGE):ℂ)*carrier D Z m ((H₀).hard V uPAGE)

include H in
lemma atlas (uPAGE : (H₀).Visual) (hc : (H₀).Clearing V)
    (hs : Summable (fun Q=> plume D Z s h F k₀ V A m Q k uPAGE)) :
    HasSum (fun Q=>plume D Z s h F k₀ V A m Q k uPAGE) (living D F A k₀ k V Z m uPAGE) := by
  let f Q := plume D Z s h F k₀ V A m Q k uPAGE
  have he := (diagram D Z s h H F k₀ V A m hc.flags k uPAGE _).mpr hs.hasSum -- H not included
  have hp := headings D h F A k₀ k V Z s m uPAGE hc he
  simp_rw [report D h F A k₀ k V Z H s m _ uPAGE hc] at hp
  have ht := hp.tsum_eq; rw [tsum_mul_left] at ht
  unfold living carrier; rw [ht]
  exact hs.hasSum

-- holder for just the price inputs on THAT stencil for the complex
-- spelling. All analytic cost. No analytical premise on full plume
-- or any physical Keep/Canvas equivalence.
structure Letters (b : Ensign S I→ℝ) : Prop where
  nonneg i : 0≤b i
  total : Summable b
  every k i : Integrable (fun y=>‖lines D Z s h F k₀ V i k y‖) ((B₀).paper i k)
  toll k i : (∫ y,‖lines D Z s h F k₀ V i k y‖ ∂(B₀).paper i k) ≤ b i

private lemma inside {Ω Y : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Countable Y] (F : Y → Ω → ℂ) (h : ∀ i,Integrable (fun x=> ‖F i x‖) μ)
    (hs : Summable (fun i=> ∫ x,‖F i x‖ ∂μ)) : ∀ᵐ x ∂μ,Summable (fun i=> ‖F i x‖) := by
  let v i x := ENNReal.ofReal (‖F i x‖)
  have ht i : AEMeasurable (v i) μ := ENNReal.continuous_ofReal.measurable.comp_aemeasurable (h i).1.aemeasurable
  have he i : ∫⁻ x,v i x ∂μ=ENNReal.ofReal (∫ x,‖F i x‖ ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (h i) (Eventually.of_forall fun x=>norm_nonneg _)).symm
  have hm : ∫⁻ x,∑' i,v i x ∂μ < ⊤ := by
    rw [lintegral_tsum ht]; simp_rw [he, ←ENNReal.ofReal_tsum_of_nonneg (fun i=> integral_nonneg (μ:=μ) fun x=>norm_nonneg (F i x)) hs]
    exact ENNReal.ofReal_lt_top
  have hI : AEMeasurable (fun x=>∑' i,v i x) μ := AEMeasurable.ennreal_tsum ht
  filter_upwards [ae_lt_top' hI hm.ne] with x hx
  · exact tsum_enorm_ne_top_iff_summable_norm.mp (by simpa only [v,ofReal_norm] using hx.ne)

variable [Countable I] {b : Ensign S I→ℝ}
lemma postings (hx : (stars D F k₀).Available V) (hb : Letters D h F k₀ V Z s b) (hc : (H₀).Clearing V) :
    let fn := fun Q (i : (H₀).Visual)=>‖plume D Z s h F k₀ V A m Q k i‖
    let μ:= (L₀).climate V A k
    (∀ Q, Integrable (fn Q) μ) ∧ Summable (fun Q=> ∫ y,fn Q y ∂μ) := by
  intro fn μ
  let d : (B₀).Script:= fun i k y=>‖lines D Z s h F k₀ V i k y‖
  let v (Q : Finset (Ensign S I)) := ∏ i∈Q,b i
  have he Q : Integrable (fn Q) μ ∧ (∫ y,fn Q y ∂μ) ≤ v Q := by
    by_cases hj:(K₀).Makes A m Q
    · have hf : fn Q=(B₀).imprint d hc.flags hj k := by
        funext y; unfold fn plume; rw [dif_pos ⟨hc.flags,hj⟩]; exact norm_prod ..
      rw [hf]
      obtain ⟨hi,ht⟩:=(B₀).valued hx k (fun i=>hb.every k i) hc.flags hj (ψ:=d)
      exact ⟨hi,ht.trans_le (Finset.prod_le_prod (fun i _ => integral_nonneg (fun y=>norm_nonneg _)) (fun i _=> hb.toll k i))⟩
    unfold fn plume; simp_rw [dif_neg (fun (ht : A.flags=RG.flags (temp D.betaHat) V ∧ (K₀).Makes A m Q)=>hj ht.2), norm_zero, integral_zero]
    exact ⟨integrable_zero ..,prod_nonneg (fun i _=>hb.nonneg i)⟩
  exact ⟨fun i=>(he i).1,(summable_finsetProd_of_summable_nonneg hb.nonneg hb.total).of_nonneg_of_le
    (fun i=> integral_nonneg (fun _=>norm_nonneg _)) (fun i=>(he i).2)⟩

include H
/-- The price-conditional **physical** HasSum in the true law. -/
theorem dictionary (hx : (stars D F k₀).Available V) (hb : Letters D h F k₀ V Z s b) (hc : (H₀).Clearing V) : ∀ᵐ y ∂(L₀).climate V A k,
    HasSum (fun Q=>plume D Z s h F k₀ V A m Q k y) (living D F A k₀ k V Z m y) := by
  obtain ⟨hl,hS⟩:=postings D h F A k₀ k V Z s m hx hb hc
  let g Q y:= plume D Z s h F k₀ V A m Q k y
  filter_upwards [inside g hl hS] with y he
  exact atlas D h F A k₀ k V Z H s m y hc (he.of_norm)
end YM.PhysicalNext.Dictionary.Formal

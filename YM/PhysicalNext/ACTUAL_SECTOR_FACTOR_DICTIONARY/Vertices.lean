import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Applications
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Meters
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Postage


/-! Signs/attachments of raw rows and supports conditional and across
the physical stencil guards, before discounts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Voice
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussian.Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify
variable {G : Gauge} {c f : Side} {S : StepData c f} (d : AnalyticBridge.LocalGaussian.Desk G S)
local notation "M" => till d.betaHat
local notation "P" => d.tube
local notation "q₀" => d.broadCut
local notation "x" => d.betaHat
local notation "B" => radiusB d.betaHat

def hinge (S : StepData c f) : Spot.Shape c f → Site c := Sum.elim (fun i=>S.ratio.parent i.1) (Sum.elim Prod.fst (Sum.elim Prod.fst (Sum.elim Prod.fst (Sum.elim Prod.fst Prod.fst))))

def duties (i : Spot.Shape c f) (V : Config G c) (U : Config G f) (k : S.Choices) :=
    let Q := S.prediction U k; let t := fiery G x S.patch.L; let r:= temp x
    match i with
    | .inl i => (P).workF M U V t r i
    | .inr (.inl i) => (P).workI M Q V r i
    | .inr (.inr (.inl i)) => (P).workC M V r i
    | .inr (.inr (.inr (.inl i))) => (P).workN M V r i
    | .inr (.inr (.inr (.inr (.inl i)))) => (P).workL M U Q V r i
    | .inr (.inr (.inr (.inr (.inr i)))) => (P).workD M V r i

def shares (s : Signed) (i : Spot.Shape c f) : Formula G S ℝ := fun F A b k V p =>
    match i with
    | .inl i => ∑ t : Bool,debit d d.g (s,Sum.inl (i,t)) F A b k V p
    | .inr (.inl i) => debit d d.g (s,Sum.inr i) F A b k V p
    | .inr (.inr _) => 0

def dues (s : Signed) (i : Spot.Shape c f) : Formula G S ℝ := fun F A b k V p=> duties d i (pull s 0 V)
  (pull s 0 (skin d F A b k V p)) (choice s k)

def coin (i : Spot.RowPosts c f) : Formula G S ℝ := fun F A b k V p =>
    -d.input.beta * ((Fintype.card Signed:ℝ)⁻¹ * (dues d i.1 i.2 F A b k V p-shares d i.1 i.2 F A b k V p))

private lemma duty_meas (h : d.Valid) {Y : Type*} [MeasurableSpace Y] (i : Spot.Shape c f) (k : S.Choices)
    {V : Y → Config G c} {U : Y → Config G f} (hv : Measurable V) (hu : Measurable U) :
    Measurable (fun y=> duties d i (V y) (U y) k) := by
  obtain ⟨p,hp⟩ := h.funds
  have hQ := (S.prediction_meas (funds_branch hp) k).comp hu
  rcases i with i|i|i|i|i|i
  · exact Fabric.fine hp (temp_nonneg _) _ hu hv _
  · exact Fabric.bond hp (temp_nonneg _) hv hQ _
  · exact (Fabric.levels (R:=M) hp (temp_nonneg d.betaHat) hu hv hQ i).1
  · exact Fabric.moment hp (temp_nonneg _) hv i
  · exact (Fabric.levels (R:=M) hp (temp_nonneg _) hu hv hQ i).2.1
  exact (Fabric.levels (R:=M) hp (temp_nonneg _) hu hv hQ i).2.2

lemma due_care (h : Route.Badge.App d) (s : Signed) (i : Spot.Shape c f) : Care d {s.act (hinge S i)} (dues d s i) := by
  obtain ⟨D,hD⟩:=h.valid.funds
  constructor
  · intro F A b k
    have he := (continuous_pull s 0).measurable.comp (Print.printed_meas P x q₀ d.radius d.g hD k A F h.valid.positive h.enough)
    exact duty_meas d h.valid i (choice s k) ((continuous_pull s 0).measurable.comp measurable_fst) he
  intro F F' A A' b b' k k' V V' p p' H
  let z:=hinge S i; let w:=s.act z
  have hz : w∈({w}:Support c) := Finset.mem_singleton_self _
  have h0 : Shields (ambient d {w}) w (4*B+2) := (covers_shield (40*B) hz).shrink (by have ht := h.aperture.scale; omega)
  have hm := Meters.with_components P x (pull s 0 V) (pull s 0 V') (pull s 0 (skin d F A b k V p))
    (pull s 0 (skin d F' A' b' k' V' p')) (choice s k) (choice s k') h.aperture z
    (read_turn s z (4*B) _ _ (Geo.Reads.visit H.fields h0)) (pulled_near _ _ s z (4*B)
      (anchored (daily d h H w hz) (by have := h.aperture.scale; omega))) (TagNe.pull s z (4*B) k k' (Geo.Reads.way H.fields h0))
  rcases i with i|i|i|i|i|i
  · exact hm.1 i rfl
  · exact hm.2.1 i rfl
  · exact (hm.2.2.1 i rfl).1
  · exact hm.2.2.2 i rfl
  · exact (hm.2.2.1 i rfl).2.1
  exact (hm.2.2.1 i rfl).2.2

lemma share_care (h : Route.Badge.App d) (s : Signed) (i : Spot.Shape c f) : Care d {s.act (hinge S i)} (shares d s i) := by
  rcases i with i|i|i
  ·
    have he (j : Bool) := dispatch d h d.g (s,Sum.inl (i,j))
    refine ⟨fun F A b k=> Finset.measurable_fun_sum (Finset.univ:Finset Bool) (fun j _=> (he j).noted F A b k), fun H=>?_⟩
    exact Finset.sum_congr rfl fun j _=> (he j).comp H
  · exact dispatch d h d.g (s,Sum.inr i)
  exact Care.constant 0

theorem coin_care (h : Route.Badge.App d) (i : Spot.RowPosts c f) : Care d {i.1.act (hinge S i.2)} (coin d i) :=
    let H:=due_care d h i.1 i.2; let K := share_care d h i.1 i.2
    ⟨fun F A b k=>measurable_const.mul (measurable_const.mul ((H.noted F A b k).sub (K.noted F A b k))),
      fun p=>congr_arg (fun t : ℝ=> -d.input.beta * ((Fintype.card Signed:ℝ)⁻¹ * t)) (congr_arg₂ HSub.hSub (H.comp p) (K.comp p))⟩

lemma agreed_coin (h : Route.Badge.App d) (i : Spot.RowPosts c f) (k k₀ : S.Choices) (b : Finset ℕ)
    (F : Forest S.ratio) {A : Stores S} (V : Config G c) (hv : A.flags=RG.flags (temp d.betaHat) V) (p : Refs G f) :
    coin d i F A b k V p=(chosen d F k₀ A k).residualFee V (Print.see x A F p) i := by
  let hl := debits d h k V hv p d.g (F:=F)
  obtain ⟨C,hC⟩:=h.earns A F V hv; obtain ⟨η,hη,hP⟩:=h.gaps A F V k hv
  have he := Print.painted P x q₀ d.radius d.g k V h.aperture hC hη hP p
  change skin d F A b k V p = (chosen d F k₀ A k).hard V (Print.see x A F p) at he
  unfold coin residualFee impression dues; rw [he]
  rcases i with ⟨s,i|i|i|i|i|i⟩
  · simp only [shares,duties]
    simp_rw [hl]; rfl
  · unfold duties shares; dsimp only; rw [hl]; rfl
  all_goals
    unfold duties shares; dsimp only; rw [sub_zero] <;> rfl
end YM.PhysicalNext.Dictionary.Voice

import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Crop

/-! Issue Notice on every Badge of the component construction. The
extensions given take no flag argument from outside X even on fields
outside A's masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.Sharp AnalyticBridge.LocalGaussian
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

namespace Route.Badge
open Print Geo Completion Wires
variable {G : Gauge} {c f : Side} {S : StepData c f}
    (d : AnalyticBridge.LocalGaussian.Desk G S) (F : Forest S.ratio) (H : Next.SectorChange.Gaussian.Table (Key F G))
    (A : Stores S) (k : S.Choices)
    {X : Support c} (b : Badge S d.betaHat X)

open Schur
/-- Just the kernel receipts needed to issue dictionary, on V-heading
of deployment. They are proof-index free (the data & extensions don't
use these parameters), even off Clearing. Pack larger purchases in
subsequent modules. -/
structure App (d : AnalyticBridge.LocalGaussian.Desk G S) : Prop where
  valid : d.Valid
  aperture : Map.Aperture S d.tube d.betaHat
  enough : 2*d.radius<firstRadius G
  earns (A : Stores S) (F : Forest S.ratio) (V : Config G c) : A.flags=RG.flags (temp d.betaHat) V → ∃ C, Authorized A V F d.betaHat C
  gaps (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices) : A.flags=RG.flags (temp d.betaHat) V → ∃ η, 0<η ∧
    Gapped (Rows.gram d.tube d.betaHat V k (shots S d.betaHat) A F) η

def idAt (i : (b.Hues d F A ⊕ b.Cool d F A) × G.ColorIndex) : Full G f :=
    Wires.active d.betaHat A F ((b.lens d F H A k).slot i)

lemma shirred (i) : Physical.place S (b.idAt d F H A k i) ∈ b.near :=
  let t := b.tone d F A i.1
  (Finset.mem_filter.mp (show t.val∈b.tests F A from t.property)).2.2.1
lemma authority (i) : Shields X (Physical.place S (b.idAt d F H A k i)) (20*radiusB d.betaHat) :=
  fun _ ht => b.sewn (halo_spec.mpr ⟨_,b.shirred d F H A k i,ht⟩)


def stage (V : Config G c) : Curtain.Chart G (b.Hues d F A) (b.Cool d F A) :=
  (cloudX d.tube d.betaHat k V A F).submatrix (b.idAt d F H A k) (b.idAt d F H A k)

def center (V : Config G c) (Y : LinkArray G (b.Test d F A)) : Curtain.Coordinates G (b.Hues d F A) (b.Cool d F A) := fun i =>
  let j:=b.idAt d F H A k i
  outlook d.tube d.betaHat d.broadCut d.radius k V (b.embed d F A (Y,0)).1 A F j.1 j.2

private lemma self_read {V V' : Config G c} (hv : Agrees X V V') : Physical.Reads X A A F F V V' k k :=
  ⟨hv,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>Iff.rfl,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl⟩

lemma cloud_earned (V : Config G c) (h : App d) (he : A.flags=RG.flags (temp d.betaHat) V)
    (i j : Rows.In d.betaHat A F (G:=G)) :
    cloudX d.tube d.betaHat k V A F (Wires.active d.betaHat A F i) (Wires.active d.betaHat A F j)=fog A F d.tube d.betaHat V k i j := by
  obtain ⟨C,hC⟩ := h.earns A F V he
  obtain ⟨η,hη,hP⟩ := h.gaps A F V k he
  have hp := cloudX_exact d.tube d.betaHat h.aperture k V A F hC hη hP
  refine (congr_fun (congr_fun hp (Wires.active d.betaHat A F i)) (Wires.active d.betaHat A F j)).trans ?_
  simp only [Physical.CFull,Matrix.submatrix_apply,Wires.active,finger,Equiv.symm_apply_apply]
  rfl
/-- Literal local optics at this retained k. -/
def offer (h : App d) : Notice (b.lens d F H A k) where
  C := b.stage d F H A k
  m := b.center d F H A k
  stores V V' hv := by
    ext i j
    exact cloudX_read d.tube d.betaHat h.aperture (self_read F A k hv) _ _ ((b.authority d F H A k j).shrink (by omega))
  views V V' hv := by
    funext Y i
    unfold center; dsimp only; rw [beam_bias d.tube d.betaHat _ _ (self_read F A k hv) h.aperture _ ((b.authority d F H A k i).shrink (by omega))
      (show Yreads S X (b.embed d F A (Y,0)).1 (b.embed d F A (Y,0)).1 from fun _ _ _=>rfl)]
  meet V hv := by
    ext i j; exact (cloud_earned d F A k V h hv.flags ((b.lens d F H A k).slot i) ((b.lens d F H A k).slot j)).symm
  arrive V Y hv := by
    obtain ⟨C,hC⟩ := h.earns A F V hv.flags
    obtain ⟨η,hη,hP⟩ := h.gaps A F V k hv.flags
    let x := d.betaHat
    let P : Refs G f := backdrop x A F (Y,0)
    let Z := b.embed d F A (Y ∘ (b.lens d F H A k).held,0)
    funext i
    have hh := congr_arg Prod.fst (rollback x A F (Y,0))
    have he : Wires.iced P.1 A x F=Y := hh
    unfold center; dsimp only
    have hx := b.snap d F H A k (Y,0)
    have ht := b.authority d F H A k i
    have hz : Yreads S X P.1 Z.1 := hx.frost
    rw [show (b.embed d F A (Y ∘ (b.lens d F H A k).held,0)).1=Z.1 from rfl,
      ← beam_bias d.tube d.betaHat d.broadCut d.radius (self_read F A k (V:=V) (X:=X) (fun _ _ _=>rfl)) h.aperture _ (ht.shrink (by omega)) hz]
    unfold idAt; rw [Wires.station _ _ _ _ h.aperture hC hη hP P.1 _,he]; rfl
  recorded i j := cloudX_meas d.tube d.betaHat k A F h.aperture.branched _ _
  marks := by
    obtain ⟨P,hP⟩ := h.valid.funds
    let r := fun p : Config G c × LinkArray G (b.Test d F A) => b.embed d F A (p.2,0)
    have hr : Measurable r := (b.embed_meas d F A).comp (measurable_snd.prodMk measurable_const)
    have ht := (Wires.herald d.tube d.betaHat d.broadCut d.radius hP k A F h.valid.positive h.enough).comp (measurable_fst.prodMk
      (measurable_fst.comp hr))
    apply measurable_pi_lambda; intro i
    let j:=b.idAt d F H A k i
    have hh := (measurable_pi_apply j.1).comp ht
    have hz : Continuous (fun x : G.Color=>x j.2) := PiLp.continuous_apply ..
    exact hz.measurable.comp hh
end Route.Badge
end YM.PhysicalNext.Dictionary

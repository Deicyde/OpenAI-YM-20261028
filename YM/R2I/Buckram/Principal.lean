import YM.R2I.Buckram.Color
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Level
/-! # Early principal stream, inherits τ of EVERY subcollection; actual nonlinear part (`glyph`) included -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism
open WardBin.Lies Push.PriceCompiler Foramen Gate
open Packets Art Gas Ursell Trees Multiple Letter OmitClusters Stained March Shield Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {p j n m k : ℕ} {L : Side} {V : Config G c}
variable {d A α t C w M N v q r η W μ x b : ℝ} {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : Rep G f}
variable (H : Cash W x μ L Q o α T R)

open ConnectedActivityE6.Buckram
-- p predicate on original Reg
structure Huts (H : Cash W x μ L Q o α T R) (D : Record) (v : ℕ→Prop) (q' κ χ : Chi) (ε : ℝ) (B : BudgetPoint) (t c c' : ℝ) : Prop where
  principal : ∃ s : ℕ→ℝ, (∀ i, let f := announced H D q' κ ε i; B.Regular (plate H i).support f ∧ B.supBounds (plate H i).site (plate H i).support f (s i)) ∧
    Footprint.Anchored (fun i=> (plate H i).site) (fun i=> if v i then s i else 0) (fun i=>coverNumber B.B (plate H i).support) t c
  remains : ∃ s : ℕ→ℝ, Footprint.Anchored (fun i=> (plate H i).site) (fun i=> if v i then s i else 0) (fun i=> coverNumber B.B (plate H i).support) t c' ∧
    ∀ i, B.Regular (plate H i).support (glyph H D q' κ χ ε i) ∧
      (coverNumber B.B (plate H i).support ≤ B.B → B.supBounds (plate H i).site (plate H i).support (glyph H D q' κ χ ε i) (s i))

section issuance
variable (G : Gauge) (hG : G.Simple) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (p n : ℕ)
    (C : Libretto G n) (D' : Record) (hD' : D'.ε ≤ 1/4) (hn : 2≤n) (χ κ : Chi) (W : ℝ) (o : ConnectedActivityE6.Target.Order G W) (η : ℝ) (R₀ : ℕ) (he : 0 ≤ η)
include hG hD hD' hn he

lemma gowns : ∃ e : ℝ→ℝ, Rate G L (-(1/2)) e ∧ ∀ᶠ s in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L s S T →
      ∀ (R : Rep G f) (Q : ConnectedActivityE6.Target G P) (μ α:ℝ) (H:Cash W s μ L Q o α T R) (B:BudgetPoint),
        B.B=radiusB s→ B.power=p→ Plays C D' B R.p P T s → Q.halo+5 ≤ R₀ → ∀ C' : ℝ, Release.accepts R₀ R.p.supportExponent η L → Release.Quotation C p R₀ R.p.supportExponent η C' →
        Lute.Plented C D' B R.p L R₀ s (gStep R.beta)→ ∀ (j:ℕ), n≤ j → ∀ (A b d t Y B₀ r v q : ℝ) (k : ℕ), Captain H j Y d v t A b r B₀ q k χ → ∀ q ε z k, Disburse R z k → Huts H D' z q κ χ ε B η (C'/L.val*k) (|e s| *k) := by
  obtain ⟨E,hE,hq⟩:= royaltyB G P L D hD n p C D' hn W o χ κ hD'
  let e x:= |E x| * expatriate L η R₀ /L.val
  refine ⟨e,(by unfold e; simp_rw [div_eq_mul_inv]; exact ((absolut hE).mul_right _).mul_right _),?_⟩
  filter_upwards [hq] with s hh c f S T hS hs R Q μ α H B ht hb hV hv C' hA hC hB j hJ A b d t Y B₀ r v q k N q' ε p' t' hK
  have hf:=H.laws.intake; let K := S.patch.L; have hE:S.patch.L=L:= H.laws.data.funds.length_eq
  have h₀ : 0<gStep R.beta:= inv_pos.mpr (Real.sqrt_pos.mpr hf.positive); let σ:=scroll H D' κ hv
  obtain ⟨τ,hτ,hT,hZ⟩:= hK.common hf
  let u := gStep R.beta; let t i := τ i* Lute.returnFee C D' B R.p K (R.activities.reg i).support R₀ s u
  have hq i := (σ i).choirs (q:=q') (d:=ε) hG hV (JointLoad.Heir.Seed.family hf.cap.labels.regular i) (hτ i) h₀.le (show (σ i).Played n u _ from ⟨fun _=> guard_silent κ h₀ (mul_pos D'.guards R.p.threshold_pos)⟩)
  have htτ i := hq i
  have he i : announced H D' q' κ ε i= _ := arithmetic H D' q' κ ε hv i
  have h₂ i : B.Regular (plate H i).support (announced H D' q' κ ε i) ∧ B.supBounds (plate H i).site (plate H i).support (announced H D' q' κ ε i) (t i) := (he i).symm ▸ htτ i
  have hz i : 0 ≤ t i:= (h₂ i).2.1
  let v i:= if p' i then τ i else 0; let w i:= if p' i then t i else 0
  have hew i : w i=v i * Lute.returnFee C D' B R.p K (R.activities.reg i).support R₀ s u:= by unfold w v; split <;> simp [t]
  have hvZ i: 0 ≤ v i:= hZ.nonneg i
  refine ⟨⟨t,h₂,fun i=>?_⟩, ⟨fun i=> τ i*|E s|, ?_,?_⟩⟩
  · rw [show L.val=S.patch.L.val from by rw [hE]]
    apply Release.spread S.ratio _ _ _ (fun i=> mul_nonneg (show 0 ≤ w i by unfold w; split; exact hz _; exact le_rfl) (Real.exp_pos _).le) hZ (by linarith only [hC.nonneg]) (fun i=> ?_)
    let g:= R.activities.reg i
    change w i * Real.exp _ ≤ _
    rw [mul_comm,hew]
    exact hC.prices S D' B R.p g.support (plate H i).support u s hb rfl (hE ▸ hA) (σ i).fields ht (by rw [ht]; exact hV.rehearsed.weft.cover) (by rw [hV.rehearsed.temp_eq]; exact hV.rehearsed.tensions.coarse) h₀.le (hE ▸ hB) (v i) (hvZ i)
  · rw [abs_of_nonneg (show 0≤e s by unfold e expatriate; positivity)]
    rw [show (fun i=> if p' i then τ i*|E s| else 0)=fun i=> v i*|E s| from funext fun i=> by unfold v; split <;> simp]
    exact landing H hv B hV ht (by assumption) hA hvZ _ hZ |E s| (abs_nonneg _)
  intro i; have hK:B.order≤j:= hV.rehearsed.test.le.trans hJ
  refine ⟨legal H D' q' κ χ ε hV i N hK (h₂ i).1, fun hx=>round H D' q' κ χ ε hV i N hK ht (h₂ i).1 (mul_nonneg (hτ i).1 (abs_nonneg _)) hx ?_⟩
  intro U hU z hz T' h' hα
  simp only [Function.comp_def, glyph]; simp_rw [lily]
  apply average H (κ:=κ) q' ε N hV i T' hU hG (hτ i) (E s)
  intro F Y
  have ht':= hT (R.activities.reg i).site; have hv : τ i ≤ incomingE G L s := by
    rw [← hE]; exact (R.p.loMass _ _ (hτ i).1).trans (by simpa using budget_single ht' i)
  have hχ : (foyer H i F χ U Y).manifest := planted_valid (Greenbelt.prism T s χ o.K U F) _
  exact hh c f S T hS hs R Q μ α H F _ i rfl rfl rfl rfl hχ B ht hb hV (plate H i).support (Key (R.activities.reg i).support s F)
     (mapcase H i F) q' ε (τ i) _ (plate H i).anchor (ht ▸ hx) hU (grove H i Y F hU hV.rehearsed.temp_eq) (hτ i) hv z hz T' h' (hb ▸ hα) -- edit
end issuance
end YM.PhysicalNext.Repeat.Brim

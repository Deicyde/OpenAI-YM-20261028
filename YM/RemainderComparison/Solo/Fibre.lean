import YM.RemainderComparison.Halo.Tome
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Level
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Young

/-!
 # Seats at single legacy expense. Before final projections.

 The prescription is only a step record. Uses Simple, actual E at every contributing
 occurrence, on waxed Coat, not requiring all representatives of E have
 indicated SMALLER budget. Thus keep canonical cuts, don't perturb μ/covariance/slices.
 For ANY requested tail floating value error, constants and operations conditional
 on stitch receipts from construction; post-L Σ transfer.
 -/
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
open YM.RemainderComparison
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {p j n m k : ℕ} {L : Side} {V : Config G c}
variable {d A α t C w M N v q r η W μ x b : ℝ} {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : Rep G f}
variable (H : Cash W x μ L Q o α T R)

structure Scores (B : BudgetPoint)(H:Cash W x μ L Q o α T R)(χ : Chi)(E:Set ℕ) (C ε:ℝ):Prop where
   grants : ∃ w:ℕ→ℝ, (∀ i∈ E, B.Regular (plate H i).support (fun V=>stream H χ V (icon H i)) ∧
           (coverNumber B.B (plate H i).support ≤ B.B → B.supBounds (plate H i).site (plate H i).support (fun V=>stream H χ V (icon H i)) (w i))) ∧
           (∀ i∉E,w i=0)∧ (∀ i,0 ≤ w i) ∧ Footprint.Anchored (fun i=>(plate H i).site) w (fun i=>coverNumber B.B (plate H i).support) ε C
variable {E:Set ℕ}{τ:ℕ→ℝ}{δ:ℝ}
lemma named (hp:Halo.Presents R E τ δ) : ∀ x:Site f,SumBudget (fun i=> if (R.activities.reg i).site=x then R.p.mass (R.activities.reg i).support (τ i) else 0) δ :=by
   intro x; convert hp.backed x using 1; ext i; simp [BudgetPoint.mass,Raw.regularExtra,mul_comm]
section issuance
variable (G : Gauge) (hG : G.Simple) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (p n : ℕ)
    (C : Libretto G n) (D' : Record) (hD' : D'.ε ≤ 1/4) (hn : 2≤n) (χ κ : Chi) (W : ℝ) (o : ConnectedActivityE6.Target.Order G W) (η : ℝ) (R₀ : ℕ) (he : 0 ≤ η)
include hG hD hD' hn he κ
lemma scored : ∃ e : ℝ→ℝ, Rate G L (-(1/2)) e ∧ ∀ᶠ s in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L s S T →
      ∀ (R : Rep G f) (Q : ConnectedActivityE6.Target G P) (μ α:ℝ) (H:Cash W s μ L Q o α T R) (B:BudgetPoint),
        B.B=radiusB s→ B.power=p→ Plays C D' B R.p P T s → Q.halo+5 ≤ R₀ → ∀ C' : ℝ, Release.accepts R₀ R.p.supportExponent η L → Release.Quotation C p R₀ R.p.supportExponent η C' →
        Lute.Plented C D' B R.p L R₀ s (gStep R.beta)→ ∀ (j:ℕ), n≤ j → ∀ (A b d t Y B₀ r v q : ℝ) (k : ℕ), Captain H j Y d v t A b r B₀ q k χ →
       ∀ (U:Set ℕ)(τ:ℕ→ℝ)(δ:ℝ), Halo.Presents R U τ δ → δ ≤ incomingE G L s → Scores B H χ U ((C'/L.val+|e s|)*δ) η:=by
  obtain ⟨E,hE,hq⟩:= royaltyB G P L D hD n p C D' hn W o χ κ hD'
  let e x:= |E x| * expatriate L η R₀ /L.val
  refine ⟨e,(by unfold e; simp_rw [div_eq_mul_inv]; exact ((absolut hE).mul_right _).mul_right _),?_⟩
  filter_upwards [hq] with s hh c f S T hS hs R Q μ α H B ht hb hV hv C' hA hC hB j hJ A b d t Y B₀ r v q k N U τ δ Hp hδ
  have hf:=H.laws.intake; let K:=S.patch.L; have hL:S.patch.L=L:= H.laws.data.funds.length_eq
  have h₀ : 0<gStep R.beta:= inv_pos.mpr (Real.sqrt_pos.mpr hf.positive); let σ:=scroll H D' κ hv
  let q i:=announced H D' χ κ 0 i
  let w i:=τ i* Lute.returnFee C D' B R.p S.patch.L (R.activities.reg i).support R₀ s (gStep R.beta)
  have hp i (hi:i∈U) : B.Regular (plate H i).support (q i)∧ B.supBounds (plate H i).site (plate H i).support (q i) (w i) :=by
    unfold q; rw [arithmetic H D' χ κ 0 hv i]; have hm: (σ i).Played n (gStep R.beta) (D'.ε*R.p.threshold) :=⟨fun t=> guard_silent κ h₀ (mul_pos D'.guards R.p.threshold_pos)⟩
    exact Script.choirs (σ i) hG hV (Seed.family hf.cap.labels.regular i) (Hp.marked i hi) h₀.le hm -- check
  have hq i:= hC.prices S D' B R.p _ _ _ _ hb rfl (hL.symm ▸ hA) (σ i).fields ht (by rw [ht]; exact hV.rehearsed.weft.cover) (by rw [hV.rehearsed.temp_eq]; exact hV.rehearsed.tensions.coarse) h₀.le (hL.symm ▸ hB) (τ i) (Hp.pay i)
  have hZ i (hi:i∉U): w i=0:=by unfold w; rw [Hp.missed i hi,zero_mul]
  have hB i:0 ≤ w i:=by by_cases he:i∈U; exact (hp i he).2.1; rw [hZ i he]
  have ht' : Footprint.Anchored (fun i=>(plate H i).site) w (fun i=>coverNumber B.B (plate H i).support) η (C'/L.val*δ):= by
     rw [show L.val=S.patch.L.val from congr_arg Subtype.val hL.symm]; exact Release.spread S.ratio _ _ _ (fun i=> mul_nonneg (hB _) (Real.exp_pos _).le) (named Hp) (by linarith only [hC.nonneg]) (fun i => (mul_comm ..).le.trans (hq i))
  have h i:= Hp.pay i; let t i:=τ i*|E s|
  have hΓ i (hi:i∈U) : B.Regular (plate H i).support (glyph H D' χ κ χ 0 i) ∧ (coverNumber B.B (plate H i).support ≤ B.B → B.supBounds (plate H i).site (plate H i).support (glyph H D' χ κ χ 0 i) (t i)):=by
    have hK:B.order≤j:= hV.rehearsed.test.le.trans hJ
    refine ⟨legal H D' χ κ χ 0 hV i N hK (hp i hi).1, fun hx=>round H D' χ κ χ 0 hV i N hK ht (hp i hi).1 (mul_nonneg (h i) (abs_nonneg _)) hx ?_⟩
    intro U hU z hz T' h' hα
    simp only [Function.comp_def, glyph]; simp_rw [lily]
    apply average H (κ:=κ) χ 0 N hV i T' hU hG (Hp.marked i hi) (E s)
    intro F Y
    have hv : τ i ≤ incomingE G L s := (Hp.roof _).trans hδ
    have hχ : (foyer H i F χ U Y).manifest := planted_valid (Greenbelt.prism T s χ o.K U F) _
    exact hh c f S T hS hs R Q μ α H F _ i rfl rfl rfl rfl hχ B ht hb hV (plate H i).support (Key (R.activities.reg i).support s F)
       (mapcase H i F) χ 0 (τ i) _ (plate H i).anchor (ht ▸ hx) hU (grove H i Y F hU hV.rehearsed.temp_eq) (Hp.marked i hi) hv z hz T' h' (hb ▸ hα)
  have hF : Footprint.Anchored (fun i=>(plate H i).site) t (fun i=>coverNumber B.B (plate H i).support) η (|e s| *δ) :=by
    rw [abs_of_nonneg (show 0≤e s by unfold e expatriate; positivity)]
    exact landing H hv B hV ht (by assumption) hA h _ (named Hp) |E s| (abs_nonneg _)
  refine ⟨t+w,fun i hi=> ?_,fun i hi=> by unfold w t; rw [Pi.add_apply,Hp.missed i hi]; ring,fun i=>add_nonneg (show 0≤t i from mul_nonneg (h _) (abs_nonneg _)) (hB _),?_⟩
  · obtain ⟨hh,hF⟩:=hΓ i hi; rw [show (fun V=>stream H χ V (icon H i))=(glyph H D' χ κ χ 0 i)-q i from ?_]
    · exact ⟨AnalyticBridge.CouplingShape.reg_sub hh (hp i hi).1, fun he=> AnalyticBridge.CouplingShape.sup_sub hh (hp i hi).1 (hF he) (hp i hi).2⟩ -- namespace
    ext; simp [glyph,q]
  intro y; convert budget_plus (hF y) (ht' y) using 1; swap; · ring
  ext i; dsimp; split_ifs <;> ring
end issuance
end YM.PhysicalNext.Repeat.Brim

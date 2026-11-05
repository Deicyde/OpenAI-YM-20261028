import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Found
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Lit
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Lode

/-! # First-order inheritance at real calendar S levels. Price after *subtracting* V9.

At exact INPUT α legacy-occurrence. Supplies sharp early cost (principal
 portion at U_E/L × intake; need turned L choice) for surviving singles.
 Full P+3 must still fit later transitions. Does not redraw Forest or μ.
 Same θ average on Auth. Consume alongside Cohorts. -/
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

section projection
variable (hR : Q.halo+5≤n) (B : BudgetPoint) {C₀ : Libretto G p} {D : Record} (h : Plays C₀ D B R.p P T x)
variable (hb : B.B=radiusB x) (ha : 0 ≤ t)
include hR ha h hb

def expatriate (L : Side) (t : ℝ) (n : ℕ) := (L.val:ℝ)^5*Real.exp (Release.base t n)
lemma landing (hp : Release.accepts n R.p.supportExponent t L) {τ : ℕ → ℝ} (ht : ∀ i, 0≤τ i) (e : ℝ) (hL : ∀ o : Site f, SumBudget (fun i => if (R.activities.reg i).site=o then R.p.mass (R.activities.reg i).support (τ i) else 0) e) (g : ℝ) (hg : 0≤g) :
    Footprint.Anchored (fun i=> (plate H i).site) (fun i=>τ i*g) (fun i=>coverNumber B.B (plate H i).support) t
      ((g*expatriate L t n)/(L.val:ℝ)*e) := by
  have he:=H.laws.data.funds.length_eq; rw [show expatriate L t n=expatriate S.patch.L t n from by rw [he],show L.val=S.patch.L.val from by rw [he]]; intro y
  let p:= fun i=> τ i*g*Real.exp (t*coverNumber B.B (plate H i).support)
  have hℓ : 0 < (S.patch.L.val:ℝ):= by positivity
  refine Release.spread S.ratio _ _ p (fun i=>by unfold p; have hv:=ht i; positivity) hL (show 0≤g*expatriate S.patch.L t n by unfold expatriate; positivity) (fun i=> ?_) y
  let c := coverNumber R.p.B (R.activities.reg i).support
  let a:= Release.base t n; let C:=t*coverNumber B.B (plate H i).support
  have hh: C≤ a+R.p.supportExponent*c:= (Release.compressed ha (he.symm ▸ hp) (billboard H hR i) hb (by rw [hb]; exact h.rehearsed.weft.cover)).trans (add_le_add_right (mul_le_mul_of_nonneg_right (half_le_self R.p.exponent_pos.le) (Nat.cast_nonneg _)) _)
  have hk:=ht i; unfold BudgetPoint.mass p expatriate
  refine (mul_le_mul_of_nonneg_left (Real.exp_monotone hh) (mul_nonneg hk hg)).trans_eq ?_
  rw [Real.exp_add]; change τ i*g*(Real.exp (Release.base t n)*Real.exp (R.p.supportExponent*c)) = g*((S.patch.L.val:ℝ)^5*Real.exp (Release.base t n))*((S.patch.L.val:ℝ)⁻¹)^5*(Real.exp (R.p.supportExponent*c)*τ i); field_simp
end projection

structure Houses (H : Cash W x μ L Q o α T R) (D : Record) (q' κ χ : Chi) (ε : ℝ) (B : BudgetPoint) (t c c' : ℝ) : Prop where
  principal : ∃ s : ℕ→ℝ, (∀ i, let f := announced H D q' κ ε i; B.Regular (plate H i).support f ∧ B.supBounds (plate H i).site (plate H i).support f (s i)) ∧
    Footprint.Anchored (fun i=> (plate H i).site) s (fun i=>coverNumber B.B (plate H i).support) t c
  remains : ∃ s : ℕ→ℝ, Footprint.Anchored (fun i=> (plate H i).site) s (fun i=> coverNumber B.B (plate H i).support) t c' ∧
    ∀ i, B.Regular (plate H i).support (glyph H D q' κ χ ε i) ∧
      (coverNumber B.B (plate H i).support ≤ B.B → B.supBounds (plate H i).site (plate H i).support (glyph H D q' κ χ ε i) (s i))

section issuance
variable (G : Gauge) (hG : G.Simple) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (p n : ℕ)
    (C : Libretto G n) (D' : Record) (hD' : D'.ε ≤ 1/4) (hn : 2≤n) (χ κ : Chi) (W : ℝ) (o : ConnectedActivityE6.Target.Order G W) (η : ℝ) (R₀ : ℕ) (he : 0 ≤ η)
include hG hD hD' hn he

lemma pressings : ∃ e : ℝ→ℝ, Rate G L (-(1/2)) e ∧ ∀ᶠ s in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L s S T →
      ∀ (R : Rep G f) (Q : ConnectedActivityE6.Target G P) (μ α:ℝ) (H:Cash W s μ L Q o α T R) (B:BudgetPoint),
        B.B=radiusB s→ B.power=p→ Plays C D' B R.p P T s → Q.halo+5 ≤ R₀ → ∀ C' : ℝ, Release.accepts R₀ R.p.supportExponent η L → Release.Quotation C p R₀ R.p.supportExponent η C' →
        Lute.Plented C D' B R.p L R₀ s (gStep R.beta)→ ∀ (j:ℕ), n≤ j → ∀ (A b d t Y B₀ r v q : ℝ) (k : ℕ), Captain H j Y d v t A b r B₀ q k χ → ∀ q ε, Houses H D' q κ χ ε B η (C'/L.val*incomingE G L s) (|e s| *incomingE G L s) := by
  obtain ⟨E,hE,hq⟩:= royaltyB G P L D hD n p C D' hn W o χ κ hD'
  let e x:= |E x| * expatriate L η R₀ /L.val
  refine ⟨e,(by unfold e; simp_rw [div_eq_mul_inv]; exact ((absolut hE).mul_right _).mul_right _),?_⟩
  filter_upwards [hq] with s hh c f S T hS hs R Q μ α H B ht hb hV hv C' hA hC hB j hJ A b d t Y B₀ r v q k N q' ε
  have hf:=H.laws.intake; let K := S.patch.L; have hE:S.patch.L=L:= H.laws.data.funds.length_eq
  have h₀ : 0<gStep R.beta:= inv_pos.mpr (Real.sqrt_pos.mpr hf.positive); let σ:=scroll H D' κ hv
  obtain ⟨p₀,h,hP⟩:= Release.chorus (q:=q') (d:=ε) (labels:=plate H) σ (fun _=>rfl) hG (hb.symm ▸ hC) hV (hE.symm ▸ hA) ht h₀.le
    (hE.symm ▸ hB) (fun i=> show (σ i).Played n (gStep R.beta) (D'.ε*R.p.threshold) from ⟨fun t=> guard_silent κ h₀ (mul_pos D'.guards R.p.threshold_pos)⟩) hf.cap.labels.regular hf.cap.labels.boundE
  have he i : announced H D' q' κ ε i= _ := arithmetic H D' q' κ ε hv i
  have h₁ i := h i
  have h₂ i : B.Regular (plate H i).support (announced H D' q' κ ε i) ∧ B.supBounds (plate H i).site (plate H i).support (announced H D' q' κ ε i) (p₀ i) := (he i).symm ▸ h₁ i -- edit
  obtain ⟨τ,hτ,hT⟩:= hf.cap.labels.boundE
  refine ⟨⟨p₀,h₂,by rwa [hE] at hP⟩, ⟨fun i=> τ i*|E s|, ?_,?_⟩⟩
  · rw [abs_of_nonneg (show 0≤e s by unfold e expatriate; positivity)]
    exact landing H hv B hV ht (by assumption) hA (fun i=> (hτ i).1) _ (by rw [hE] at hT; exact hT) |E s| (abs_nonneg _)
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

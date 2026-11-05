import YM.RG12.Spins.Warp
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Spins
open Next.Foundations
open Function Filter Set Lattice Wilson Pressure RG Push.SectorMeasure
open Multi Multi.Vacuum.Jets Multi.Puff WardBin.Lies
open PhysicalNext.JointLoad.Heir PhysicalNext Next Next.SectorChange Next.SectorChange.Rows Wisps Next.Fluctuations AnalyticBridge.SectorAffine.Offset AnalyticBridge.LocalGaussian.Moments
open Finset Planned.AtomRegular Foliage MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{t:ℝ}{I:Type}[Fintype I][DecidableEq I]{p n r:ℕ}{P B:BudgetPoint}{c f:Side}{o: Site f}{A K C γ u d x:ℝ}
variable {S:StepData c f}{T:Tube G S}{Pt:Teller G}{L:Tree.Forest S.ratio}{b:S.Choices}{q χ:Chi}{X:Support f}{Y:Support c}{A₀: Stores S}
   (m:Museum L x A₀ X Y I)(U:Config G f){C':Libretto G p}{D:Record}
   (hb:Plays C' D P B Pt T x)
   {J: Config G f→ℝ}(hf:B.Regular X J)(ho:o∈X)(hs:PhysicalNext.JointLoad.Heir.Short S B X)
variable {F:Deck G c f→ℂ}
set_option quotPrecheck false
local notation "ψs" => S.ratio.parent o
local notation "c_0" => reach x
local notation "ψd" => Cube.fee C'.Z
local notation "R₁" => loom P (c_0) (ψd)
local notation "σ₀" z => m.extra (1:Site c→G.El) u z
local notation "ωΩ" z => ((0,σ₀ z):Deck G c f)
local notation "ΩF" z => (fun W=> ((J (m.received b T q d u W U z)):ℂ))
local notation "ρ" => PhysicalNext.JointLoad.Heir.crop (ψs) (c_0) (1:Site c→G.El)
local notation "wallX" => pivotRay G F P.threshold (ψs) (c_0)
include hb hf ho hs
protected noncomputable def reserve (A K:ℝ):ℝ:=1+A*Planned.AtomRegular.patterns 2*K^2
local notation "Ξ" => m.twilight b T
local notation "Y0"=> (1:Config G c)
local notation "Γ" => PhysicalNext.JointLoad.Heir.guard χ G I u (D.ε*B.threshold)
/-- Sharp (post-block) Hessian price for the ISOLATED concert. Required unscaled deck bound
 (next obtain from Heir.Plays on aligned d4 chart). require also Carillon bought on unscaled
 price; the displayed Crest d0 & df0 for deterministic frame follow from d4 chart and standard chain. u is physical, no transport between letters. -/
lemma design (hu:0<u)(hn:4≤p) (hY:Walled S X Y x r)(hF:∀ a, ‖a‖≤ (R₁) → Through 4 F a A)(hEq:∀ a:Deck G c f, F a = P.threshold^2 • ((J (increment 1 (display T L x b true a)):ℝ):ℂ))
    (hC0:Crest 2 (wallX 0) 1)(hZ:pivotRay G F P.threshold (ψs) (c_0) 0 1=0) (h1: ∀ j,P.dirBound (ψs) j → leftDerivs (wallX 0) [j] 1=0) (M:ℝ)(n:ℕ)(hM:0 ≤ M)(hB:∀ z, Band 2 (P.dirBound (ψs)) Y0 (P.threshold*M*powers z^n) 1 (fun W:Config G c=>(PhysicalNext.JointLoad.Heir.Carillon.vary Y0 (Ξ) z W:ℂ))) (a c':Directions G c)(ha:P.dirBound (ψs) a)(hv:P.dirBound (ψs) c'):
     let J':= Complex.ofRealCLM ∘ m.hymn T u q d b J Γ U
     ‖leftDerivs J' [a,c'] 1 - leftDerivs (wallX 0) [a,c'] 1‖ ≤
         ‖leftDerivs (wallX 0) [a,c'] 1‖ * (2 * Noise.fade (D.ε*B.threshold) u D.K * (Fintype.card I:ℝ) * 2 ^ Fintype.card G.ColorIndex) +
         (M+1)^2*(u * Spins.reserve A (ψd * ((1+((reach x:ℕ):ℝ))^(P.power*p))))^2 * AnalyticBridge.LocalGaussian.Moments.meter (Fintype.card (I × G.ColorIndex)) 0 D.K (2+2*n) :=by
    intro J'
    have hl:=D.guards; have hi:=B.threshold_pos; have hκ:=P.threshold_pos
    let γ:=PhysicalNext.JointLoad.Heir.guard χ G I u (D.ε*B.threshold)
    let σ:=wallX 0; let K:= ψd * ((1+((reach x:ℕ):ℝ))^(P.power*p)); have hp:1 ≤ K:=by exact one_le_mul_of_one_le_of_one_le (Cube.fee_one ..) (one_le_pow₀ (by exact le_add_of_nonneg_right (Nat.cast_nonneg _)))
    let J0:=m.hymn T u q d b J γ U; let C:= m.twilight b T; let R(z:Prices G I)(W:Config G c):ℂ:=↑(PhysicalNext.JointLoad.Heir.Carillon.vary 1 C z W)
    let μ:= Gaussian.cloud (C 1)
    have hP := hb.cantos (k:=b) m (one_healthy (G:=G) Y _ hκ.le) hY ho
    have hS:= guard_silent χ (G:=G) (I:=I) hu (n:=p) (mul_pos hl hi)
    obtain ⟨hW,hI,hD⟩:=Repeat.Peak.opaqueE q d b m U hb hf ho hY hu.le hS (one_healthy _ _ hκ.le) [a,c'] (by simpa using (show 2≤p by omega))
    -- apply consumer
    apply Noise.quota (χ:=χ) σ J' J (fun z W=>m.received b T q d u W U z) C a c' ha hv hP.pos (zero_lt_one.trans_le D.peak) (mul_pos hl hi) hu hκ hP.peak M 1 (Spins.reserve A K) n 2 hM zero_le_one ?_ hI hC0 hZ h1 hB
    swap; · unfold J'; rw [Push.Local.left_linear Complex.ofRealCLM [a,c'] (k:=p) (show Push.Local.Chart p J0 (1:Config G c) from hW.germ) (by simpa using (show 2≤p by omega))]; exact hD
    intro z hz
    have he:= warped (q:=q) (d:=d) m U hb hf ho hs hu hn hF hEq z hz
    refine ⟨he.1,ProofPorts.CommonComplexProduction.band_rise he.2 (c':= ((u*Spins.reserve A K)^2)*(powers z^2)/P.threshold^2) ?_ (by simp)⟩
    let N:=A*Planned.AtomRegular.patterns 2*K^2
    have hu0:= (Cube.fee_one C'.Z); have hp':=P.threshold_pos
    have hN:0≤N:=by unfold N; have ha:= (hF (0:Deck G c f) (by rw [norm_zero]; unfold loom; positivity)).nonneg; positivity [Planned.AtomRegular.patterns_nonneg 2]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _); change N*(powers z*u)^2 ≤ (u*(1+N))^2*powers z^2; have hx:=mul_le_mul_of_nonneg_right (show N≤ (1+N)^2 from by nlinarith) (sq_nonneg (powers z*u)); nlinarith only [hx]
end YM.RG12.Spins

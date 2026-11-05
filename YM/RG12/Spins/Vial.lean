import YM.RG12.Spins.Stencils
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
open Planned.PrimaryIntegral295 Place Labels Source Source.Drops
section reset
lemma sturdy {A:Deck G c f→ℂ}{t:ℝ}(o:Site c) (n:ℕ)(a:Canvas P o n (1:Config G c) 1 p K) (hA:Through 4 A 0 u)(hA':A 0=0)(hd:fderiv ℝ A 0 = 0) :
    Crest 2 (pivotRay G A t o n 0) 1 ∧ (pivotRay G A t o n 0) 1=0∧∀ v: Directions G c,leftDerivs (pivotRay G A t o n 0) [v] 1=0:=by
   let σ:=pivotRay G A t o n 0; let T:=PhysicalNext.JointLoad.Heir.crop o n (1:Site c→G.El); let H(y:Directions G c): Deck G c f:= (T (increment 1 y),0)
   have h0:H 0=0:=by simp [H,T,Repeat.Cub.blankBirth]
   have hH:ContDiffAt ℝ 2 H 0:=(a.germ.of_le le_top).prodMk contDiffAt_const
   have he:ContDiffAt ℝ 2 A (H 0):=h0.symm ▸ hA.smooth.of_le (by norm_num)
   have hi:σ ∘ increment (1:Config G c)= (t^2)⁻¹ • (A∘H):= by ext1 y; unfold σ pivotRay; rw [Function.comp_apply,add_zero]; rfl
   refine ⟨into _ _ (by change ContDiffAt ℝ 2 (σ ∘ increment (1:Config G c)) 0; rw [hi]; exact (he.comp _ hH).const_smul ((t^2)⁻¹:ℝ)), (by simp [pivotRay,Repeat.Cub.blankBirth,show A ((0,0):Deck G c f) = (0:ℂ) from hA']),fun v=>?_⟩
   have ht : HasFDerivAt (𝕜:=ℝ) (σ ∘ increment 1) 0 (0:Directions G c):=by
       rw [hi]; have ha: HasFDerivAt (𝕜:=ℝ) A 0 (H 0):= by have hh:= (he.differentiableAt (by norm_num)).hasFDerivAt; rw [h0,hd] at hh; rwa [h0]
       convert (ha.comp 0 (hH.differentiableAt (by norm_num)).hasFDerivAt|>.const_smul ((t^2)⁻¹:ℝ)) using 1<;> first|rfl|(ext v; simp)
   exact ((ht.comp_hasDerivAt_of_eq (0:ℝ) ((hasDerivAt_id' _).smul_const v) (by simp)).deriv).trans (by simp)
end reset

section angels
variable {e:ℕ}{U0:Labels.Frame G e}(N:SectionData U0)(α:U0.Index)(w:ℂ →L[ℝ]ℝ)
local notation "φT"=>PhysicalNext.JointLoad.Heir.Carillon.vary (1:Config G c) (m.twilight b T)
local notation "Ft" ξ => Spins.converter (T:=T) (b:=b) (x:=x) (L:=L) N o α w ξ
local notation "JK" => (w ∘ Push.Local.presented N o B.threshold (Place.copy U0 α))
include hb ho hs
lemma primary (h:Bid.pop N)(hz:(U0.grades α).2=2)(hw:‖w‖≤1)(hr:P.threshold≤2*B.threshold)(hg:B.Regular X (JK))(hY:Walled S X Y x r)(hu:0<u)(hn:4≤p)
     (M:ℝ)(n:ℕ)(hM:0≤M)(hB:∀ z,Band 2 (P.dirBound (ψs)) (1:Config G c) (P.threshold*M*(powers z^n)) 1 (fun W=>(φT z W:ℂ))):
       ∀ a c':Directions G c,P.dirBound (ψs) a → P.dirBound (ψs) c' → 
       let J':=Complex.ofRealCLM ∘ m.hymn T u q d b (JK) (PhysicalNext.JointLoad.Heir.guard χ G I u (D.ε*B.threshold)) U
       let η:=pivotRay G (Ft (P.threshold/B.threshold)) P.threshold (ψs) (reach x) 0
       ‖leftDerivs J' [a,c'] 1-leftDerivs η [a,c'] 1‖≤ ‖leftDerivs η [a,c'] 1‖*(2*Noise.fade (D.ε*B.threshold) u D.K*(Fintype.card I:ℝ)*2^Fintype.card G.ColorIndex)+(M+1)^2*(u*Spins.reserve (Spins.ceiling N α h hz D.majorant) (ψd*((1+((reach x:ℕ):ℝ))^(P.power*p))))^2*AnalyticBridge.LocalGaussian.Moments.meter (Fintype.card (I×G.ColorIndex)) 0 D.K (2+2*n):=by
    obtain ⟨hm,H⟩:=Classical.choose_spec (angels N α h hz D.majorant)
    have hf:0≤R₁:=by unfold loom; positivity [P.threshold_pos,Cube.fee_one C'.Z]
    have he: Tour T L x b p (R₁) D.Q:= (hb.acts L b).toTour.weaker hb.rehearsed.tensions.allows.le le_rfl
    obtain ⟨hY',h0,hJ⟩:= H o P.threshold_pos hr hw hf he (hb.rehearsed.tensions.small.trans (min_le_right ..)) hn
    obtain h' := Repeat.Cub.posed C'.Z hb.rehearsed.wire (o:=ψs)
    obtain ⟨he0,hk,Hj⟩:=sturdy (t:=P.threshold) (ψs) _ h' (hY' 0 (by simpa)) h0 hJ
    exact fun a c' ha hc=>design m U hb hg ho hs hu hn hY hY' (pin N o α w hz) he0 hk (fun j _=> Hj j) _ _ hM hB a c' ha hc
end angels
end YM.RG12.Spins

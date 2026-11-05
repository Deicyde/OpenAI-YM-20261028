import YM.RG12.Spins.Ring
import YM.RG12.Spins.Vial
/-! connect sharp unscaled Hessian port to marginal rep & literate hQ.
 Used with Beet release on same k. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir.Payed
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Vacuum.Jets Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score
    SelectedOrderedKernels SelectedOrderedKernels.Sector FreeResolvent Next.SectorChange.Rows Wisps Push.SectorMeasure
open Planned.AtomRegular Foliage Next.Foundations AnalyticBridge.NonflatCovarianceLocality.Placement YM.RG12 Labels Source Source.Drops Planned.PrimaryIntegral295 Place
open AnalyticBridge.LocalGaussianLaws (gap_positive gapped_iff)
open AnalyticBridge.LocalGaussian (Peak)
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{t:ℝ}{I:Type}[Fintype I][DecidableEq I]{p n r:ℕ}{P B:BudgetPoint}{c f:Side}{o: Site f}{α β δ η d x u N C M R Y' L' X':ℝ}
variable {S:StepData c f}{T:Tube G S}{Pt:Teller G}{L:Tree.Forest S.ratio}{b:S.Choices}{q χ:Chi}{X:Support f}{Y:Support c}{A₀: Stores S}
   (m:Museum L x A₀ X Y I)(U:Config G f){C':Libretto G p}{D:Record}
   (hb:Plays C' D P B Pt T x) (ho:o∈X)(hs:PhysicalNext.JointLoad.Heir.Short S B X)
variable {e:ℕ}{U0:Labels.Frame G e}(N:SectionData U0)(a:U0.Index)(w:ℂ→L[ℝ]ℝ)
set_option quotPrecheck false
local notation "JK" => (w ∘ Push.Local.presented N o B.threshold (Place.copy U0 a))
local notation "Z!"=> amended x A₀ (1:Config G c)
local notation "Wh"=> YM.PhysicalNext.JointLoad.Heir.scope B X r x
local notation "A!"=> 1+peal G 2 P.power α δ M R Y' β L'
local notation "χ₀"=> Cube.fee C'.Z
include hb ho hs
lemma payment (h:Bid.pop N)(hSlots:(U0.grades a).2=2)(hw:‖w‖ ≤1)(hr:P.threshold ≤2*B.threshold) (hF:B.Regular X JK)(hY:Walled S X Y x r)(hu:0<u)(hn:4≤p)
     (H':MarginalInputs T x (Z!) L b (1:Config G c) 2 α M δ R Y' β L')(hβ:0<β):
     let K:= canopy (A!) (Wh) P.power 2
     let feeZ:= (2:ℝ)*2*(1+(Fintype.card (I × G.ColorIndex):ℝ)^2*(K+1)*K)
     ∀ v v':Directions G c,P.dirBound (S.ratio.parent o) v → P.dirBound (S.ratio.parent o) v' →
       let φ':=Complex.ofRealCLM ∘ m.hymn T u q d b (JK) (PhysicalNext.JointLoad.Heir.guard χ G I u (D.ε*B.threshold)) U
       let ξ:=Spins.pivotRay G (Spins.converter (T:=T) (L:=L) (x:=x) (b:=b) N o a w (P.threshold/B.threshold)) P.threshold (S.ratio.parent o) (reach x) 0
       ‖leftDerivs φ' [v,v'] 1-leftDerivs ξ [v,v'] 1‖ ≤ ‖leftDerivs ξ [v,v'] 1‖*(2*Noise.fade (D.ε*B.threshold) u D.K*(Fintype.card I:ℝ)*2^Fintype.card G.ColorIndex)+(feeZ+1)^2*(u*Spins.reserve (Spins.ceiling N a h hSlots D.majorant) (χ₀*((1+((reach x:ℕ):ℝ))^(P.power*p))))^2*AnalyticBridge.LocalGaussian.Moments.meter (Fintype.card (I×G.ColorIndex)) 0 D.K 6:=by
    intro K D₀
    have hW:1 ≤ (A!):=le_add_of_nonneg_right (by unfold peal; positivity) -- add
    have h':1 ≤K:=canopy_one hW ..
    have hD:0≤D₀:=by unfold D₀; positivity
    apply Spins.primary (T:=T) (q:=q) (χ:=χ) (d:=d) m U hb ho hs N a w h hSlots hw hr hF hY hu hn D₀ 2 hD
    have ht : Healthy (temp x) Y (1:Config G c) := one_healthy (G:=G) _ _ (hb.rehearsed.temp_eq ▸ P.threshold_pos.le)
    suffices he: Carillon (m.twilight b T) (1:Config G c) 2 (Payed.fresh P) (S.ratio.parent o) (peakCost G 2 M R Y') (A!) 1 (Wh) from fun z=> price he hW z
    rw [m.twilight_price hb.bulletin ht]
    apply Payed.ringing H' hβ (P:=Payed.fresh P) rfl ((m.forwarded 1 ht).prodMap (Embedding.refl G.ColorIndex))
    intro j; exact scope_inside hY _ ho _ (m.stores j.1 (halo_subset _ _ (Finset.mem_singleton_self _)))
end YM.PhysicalNext.JointLoad.Heir.Payed

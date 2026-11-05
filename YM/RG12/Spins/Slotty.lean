import YM.RG12.Spins.Beet
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
open AnalyticBridge.SectorAffine.Offset AnalyticBridge.LocalGaussianLaws Extra.Iteration Extra.Iteration.Scales
lemma purchase (J:Patch)(hJ:J.Branches Pt.bind G)(g:G.Simple)(p':ℕ)(hn:4≤p)(t:ℝ) (ht:0≤t)(hη:0<η)(h:Bid.pop N)(r:ℕ):∀ᶠ x in atTop,∀ β:ℝ, betaF G x J.L/2 ≤ β→
  ∀ {c f:Side}(S:StepData c f)(T:Tube G S),S.patch=J → Lift.Booth Pt S T→100*(1+radiusB x) ≤ c.val →
    ∀{I:Type}[Fintype I][DecidableEq I]{r':Forest S.ratio}{A:Stores S}{X:Support f}{Y:Support c}(a:Museum r' x A X Y I)(U:Config G f){P B:BudgetPoint},
     P.power=p' → P.threshold ≤ 2* B.threshold → B.threshold=fiery G x J.L→ B.B ≤ 2*radiusB x→
     Plays C' D P B Pt T x →∀{o:Site f},o ∈ X → Short S B X → Walled S X Y x r→coverNumber B.B X ≤ 1 →
      ∀ (k:S.Choices)(χ q:Chi)(d:ℝ)(i:U0.Index)(w:ℂ→L[ℝ]ℝ),‖w‖ ≤1→(U0.grades i).2=2 →let f':= w ∘ Push.Local.presented N o B.threshold (Place.copy U0 i); let σ:= Repeat.Cub.deem o x T f'
      let Ξ:=a.hymn T (coupling β) q d k f' (PhysicalNext.JointLoad.Heir.guard χ G I (coupling β) (D.ε*B.threshold)) U
      B.Regular X f' → B.supBounds o X f' t → ∀ v v':Directions G c,P.dirBound (S.ratio.parent o) v → P.dirBound (S.ratio.parent o) v' →
      ‖leftDerivs Ξ [v,v'] 1-leftDerivs σ [v,v'] 1‖ ≤ x^η/x:=by
    obtain ⟨r₀,g₀,z,M,Y,V,L',hr,hg,hZ,hV,hM,hY,hL,H⟩:= haar_operators G J Pt hJ 2
    let Z':=1+peal G 2 p' z V M r₀ Y g₀ L'
    have hZ':0≤Z':= by unfold Z' peal; positivity
    have h₀:0≤Repeat.Cub.reachBill C' t:=by have h:=patterns_nonneg p; have hT:=C'.rights.large; have ht':=C'.matins; unfold Repeat.Cub.reachBill Repeat.Cub.wealth; positivity -- locate
    choose K hK hk using fun i:U0.Index=> Spins.uniform N i (n:=4)
    let F:= fun i:U0.Index=> if H:(U0.grades i).2=2 then Spins.ceiling N i h H D.majorant else 1
    have hf(i):0≤ F i:= by
       unfold F; split; next H=> exact zero_le_one.trans (Spins.roof N i h H D.majorant)
       exact zero_le_one
    have hr':= Cube.fee_one C'.Z
    have he(i):= concertG (G:=G) (D:=D) r p' p J.L hZ' (hK i) (zero_le_one.trans hr') h₀ (hf i) hη
    filter_upwards [H,(eventually_all.mpr he),evening J hJ 1,eventually_ge_atTop (1:ℝ)] with x hB he hE hx β hb c f S T h'T hT hc I _ _ r' A X Y a U P B hP hh hW hR hV o ho hS hY hX k χ q d i w hw hA f' σ Ξ hK' hU v v' hv hv'
    obtain ⟨hu,ha⟩:=he i β hb
    have hB':=hB S T h'T hc hT.1 (amended x A (1:Config G c)) r' k 1 rfl
    have hz:(x^1)⁻¹ ≤ 1:=by simp [inv_le_one_of_one_le₀ hx]
    have h:=leaseP (q:=q) (χ:=χ) (d:=d) a U hV ho hS N i w g h hA hw hh hK' hU hX hR hY hu hn (hk i _ o _ (norm_zero.le.trans zero_le_one)) (hE S T h'T hT hc r' k) hz hB' hg v v' hv hv'
    have hσ:=Repeat.Cub.deem_focus (o:=o) hV hK'
    obtain ⟨hΞ,-,-⟩:=Repeat.Peak.opaqueE q d k a U hV hK' ho hY hu.le (PhysicalNext.JointLoad.Heir.guard_silent χ hu (mul_pos D.guards B.threshold_pos)) (one_healthy Y _ P.threshold_pos.le) [v,v'] (by simp; omega)
    change ‖((leftDerivs Ξ [v,v'] 1)-(leftDerivs σ [v,v'] 1):ℝ)‖ ≤ _
    refine le_trans ?_ ha
    dsimp only at h -- reduce lets
    have hL: [v,v'].length ≤ p:=by simp; omega
    rw [Push.Local.left_linear Complex.ofRealCLM [v,v'] hΞ.germ hL,Push.Local.left_linear Complex.ofRealCLM [v,v'] hσ.germ hL,← Complex.ofRealCLM.map_sub] at h
    change ‖(((_-_:ℝ):ℝ):ℂ)‖ ≤ _ at h; rw [Complex.norm_real] at h
    unfold F; simp only [hA,dite_true]; convert h using 1 <;> first|rfl |rw [hW,h'T,hP]
end YM.PhysicalNext.JointLoad.Heir.Payed

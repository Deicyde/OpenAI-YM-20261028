import YM.RG12.Spins.Cache
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
open AnalyticBridge.SectorAffine.Offset AnalyticBridge.LocalGaussianLaws
local notation "GΣ" => Fintype.card G.ColorIndex
include ho
include m
omit [DecidableEq I] in
lemma ate (he:Nonempty G.ColorIndex)(h: Walled S X Y x r)(ht:B.B ≤ 2*radiusB x)(hX:coverNumber B.B X≤ 1){Q:ℝ}(hd:1≤Q) :
     let _F:= Lute.bulk 1 r x; let Z:= Payed.arcM G r S.patch.L x; let _V:= Payed.plumeM r P.power Q x; let y:= Fintype.card (I×G.ColorIndex); let U:=canopy Q (Wh) P.power 2
     (Fintype.card I:ℝ) ≤ Z ∧ (y:ℝ) ≤ Z ∧ 2*2*(1+(y:ℝ)^2*(U+1)*U) ≤ Payed.foeM G r P.power S.patch.L Q x ∧ AnalyticBridge.LocalGaussian.Moments.meter y 0 D.K 6 ≤ Payed.growM 6 D.K Z := by
     intro F Z V y U
     have hm:(y:ℝ) ≤ Z:=by
        have hx :=m.viewed h B ho G
        apply (Nat.cast_le.mpr hx).trans; apply le_trans (le_add_of_nonneg_left zero_le_one)
        have he:= Lute.overcrowded (X:=X) (L:=S.patch.L) (r:=r) (G:=G) ht; apply he.trans; have hh :=Lute.season_nn G S.patch.L
        have hu:Lute.bulk (coverNumber B.B X) r x ≤ Lute.bulk 1 r x:= by unfold Lute.bulk; gcongr
        have hv:0≤Lute.bulk (coverNumber B.B X) r x:=zero_le_one.trans (Lute.bulk_one ..)
        unfold Z Payed.arcM; gcongr
     have hJ:0≤Z:=(Nat.cast_nonneg _).trans hm
     have hh0:=canopy_one hd (Wh) P.power 2
     have hb : U ≤ V:= by
        unfold U V canopy Payed.plumeM; gcongr; exact (Lute.covers ht).2.2.trans (by unfold Lute.bulk; gcongr)
     have hi :0≤ AnalyticBridge.LocalGaussian.Moments.inflate 6 (D.K⁻¹/8):=by have hK:=D.peak; unfold AnalyticBridge.LocalGaussian.Moments.inflate; positivity
     have hx1:1≤ V:= hh0.trans hb
     refine ⟨le_trans ?_ hm,hm,?_,?_⟩
     · exact Nat.cast_le.mpr (Nat.le_of_lt_succ (by unfold y; rw [Fintype.card_prod]; have hY:= (@Fintype.card_pos G.ColorIndex _ he); exact Nat.lt_succ_of_le (Nat.le_mul_of_pos_right _ hY)))
     · unfold Payed.foeM; change _ ≤ 2*2*(1+Z^2*(V+1)*V); gcongr
     · unfold AnalyticBridge.LocalGaussian.Moments.meter Payed.growM; rw [pow_one]; gcongr
omit ho m
include hb
include L
lemma stampZ (hg:B.Regular X JK)(hτ:B.supBounds (o) X (JK) t)(hn:4≤p)(v v':Directions G c)(hl:P.dirBound (S.ratio.parent o) v)(hv:P.dirBound (S.ratio.parent o) v'):
       ‖leftDerivs (Complex.ofRealCLM ∘ Repeat.Cub.deem o x T (JK)) [v,v'] 1‖ ≤ Repeat.Cub.reachBill C' t:=by
     let f:=Repeat.Cub.deem o x T (JK); let D':= (![v,v']:Slab G c 2)
     have hf':=Repeat.Cub.deem_focus (o:=o) hb hg
     rw [Push.Local.left_linear Complex.ofRealCLM [v,v'] hf'.germ (by simp; omega)]
     change ‖(Complex.ofReal (leftDerivs f _ _))‖ ≤ _; rw [Complex.norm_real]
     have h:=Repeat.Cub.interpreted (D':=D') L hb hg hτ (by omega) (fun i=>by fin_cases i; exact hl; exact hv) 2 (by omega) (@cart 2) (by intro i; exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun j => by simp only [cart,Pi.single_apply]; split <;> simp))
     have he:=Germ.ordered D' (f:=f) (show Germ _ _ _ from hf'.germ.of_le (Nat.cast_le.mpr (by omega : 2≤p))); rw [show [v,v']= List.ofFn D' by simp [List.ofFn_succ,D'],he]; exact h
include m hb ho hs
lemma leaseP (g:G.Simple)(h:Bid.pop N)(hSlots:(U0.grades a).2=2)(hw:‖w‖ ≤1)(hr:P.threshold ≤2*B.threshold)(hg:B.Regular X JK)(hτ:B.supBounds o X JK t)(hX:coverNumber B.B X≤1) (ht:B.B ≤2*radiusB x)(hY:Walled S X Y x r)(hu:0<u)(hn:4≤p)
     (hV:Through 4 (Spins.drawing N o a) 0 C) (hsH:‖fderiv ℝ (display T L x b true) 0-mainStroke T L true‖ ≤ η)(hη:η ≤ 1)(H':MarginalInputs T x (Z!) L b (1:Config G c) 2 α M δ R Y' β L')(hβ:0<β)(v v':Directions G c)(hl:P.dirBound (S.ratio.parent o) v)(hv:P.dirBound (S.ratio.parent o) v'):
     let s:=S.patch.L; let H:=Payed.wax (Cube.fee C'.Z) P.power p x
     let K:= Payed.arcM G r s x; let F:= Payed.foeM G r P.power s (A!) x
     let Y:=8*C*(D.Q+1)*H^2
     let Q:= Spins.ceiling N a h hSlots D.majorant
     let φ':=Complex.ofRealCLM ∘ m.hymn T u q d b (JK) (PhysicalNext.JointLoad.Heir.guard χ G I u (D.ε*B.threshold)) U
     let κ:=Complex.ofRealCLM ∘ Repeat.Cub.deem o x T (JK)
     ‖leftDerivs φ' [v,v'] 1-leftDerivs κ [v,v'] 1‖ ≤ (Repeat.Cub.reachBill C' t+Y)*(2*Noise.fade (D.ε*B.threshold) u D.K*K*2^(GΣ))+(F+1)^2*(u*Spins.reserve Q H)^2*Payed.growM 6 D.K K + Y*η:=by
     intro s V K F Y Q φ κ
     letI : Nontrivial G.Color:= g.nontrivial_color
     have hd : Nonempty G.ColorIndex:=by
        by_contra! H; letI:=H; haveI:Subsingleton G.Color:=inferInstance; exact not_nontrivial G.Color inferInstance
     have hA:1≤(A!):=le_add_of_nonneg_right (by unfold peal; positivity)
     obtain ⟨hz,h₀,h₁,h₂⟩:= ate (P:=P) (D:=D) m ho hd hY ht hX hA
     have h:=merit hb N a w h hSlots hw hr hn hV hsH hη v v' hl hv
     have he':= payment (q:=q) (χ:=χ) (d:=d) m U hb ho hs N a w ‹_› hSlots hw hr hg hY hu hn H' hβ v v' hl hv
     let z:=Spins.pivotRay G (Spins.converter (T:=T) (L:=L) (x:=x) (b:=b) N o a w (P.threshold/B.threshold)) P.threshold (S.ratio.parent o) (reach x) 0
     let J(F:Config G c→ℂ):= leftDerivs F [v,v'] (1:Config G c); change ‖J φ-J κ‖ ≤ _
     have hy:0 ≤ Y:=by unfold Y; have hv:=hV.nonneg; have hK:=D.majorant; positivity
     have hh:‖J z-J κ‖ ≤ Y*η:=h
     apply (norm_sub_le_norm_sub_add_norm_sub (J φ) (J z) (J κ)).trans (add_le_add (he'.trans ?_) hh)
     have hm: ‖J z‖ ≤ Repeat.Cub.reachBill C' t + Y:= ((by simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub (J z) (J κ) 0): _ ≤ ‖J z-J κ‖+‖J κ‖)|>.trans (by have hT:=stampZ (T:=T) (L:=L) hb N a w hg hτ hn v v' hl hv; change ‖J κ‖ ≤ _ at hT; exact (add_le_add (h.trans (mul_le_of_le_one_right hy hη)) hT).trans_eq (add_comm _ _))
     have hK:=D.peak; have hg : 0≤Noise.fade (D.ε*B.threshold) u D.K:=le_of_lt (Real.exp_pos _)
     have hZ:0 ≤ AnalyticBridge.LocalGaussian.Moments.meter (Fintype.card (I×G.ColorIndex)) 0 D.K 6:=by unfold AnalyticBridge.LocalGaussian.Moments.meter AnalyticBridge.LocalGaussian.Moments.inflate; positivity
     have hv: 1≤ canopy (A!) (Wh) P.power 2:=canopy_one hA ..
     have hy: 0≤(Repeat.Cub.reachBill C' t + Y):=(norm_nonneg _).trans hm
     apply add_le_add (mul_le_mul hm ?_ (by positivity) hy)
     · apply mul_le_mul (mul_le_mul_of_nonneg_right ?_ (sq_nonneg (u*Spins.reserve Q V))) h₂ hZ (by positivity)
       gcongr ?_^2
       exact add_le_add_left h₁ 1
     gcongr ?_*_; gcongr
end YM.PhysicalNext.JointLoad.Heir.Payed

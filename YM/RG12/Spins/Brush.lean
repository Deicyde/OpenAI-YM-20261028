import YM.RG12.Spins.Vial
import YM.RG12.Spins.Cane
import YM.RG12.Spins.Meteor
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
/-! exact formula D2 & price on deterministic. no new calibration. -/
protected noncomputable def flash (A:Deck G c f→ℂ)(t:ℝ)(o:Site c)(n:ℕ):Config G c→ℂ:=pivotRay G A t o n 0
private lemma rates (D: Directions G f→ℂ)(_ht:t>0)(h:ContDiffAt ℝ 2 D 0)(hz:fderiv ℝ D 0=0)
   (F:Deck G c f→Directions G f)(hF:ContDiffAt ℝ 2 F 0)(hf:F 0=0)(o:Site c)(n p)(hr:Canvas P o n (1:Config G c) 1 p K)(hp:2 ≤ p)(x y:Directions G c):
    let v:Slab G c 2:= ![x,y]
    let L:=fderiv ℝ (instill G c f o n 2 v) 0
    leftDerivs (Spins.flash (D ∘ F) t o n) [x,y] 1=
        (t^2)⁻¹ • iteratedFDeriv ℝ 2 D 0 ![fderiv ℝ F 0 (L (cart 0)), fderiv ℝ F 0 (L (cart 1))]:=by
    intro v L
    let y':=F ∘ instill G c f o n 2 v
    have hv: ContDiffAt ℝ 2 (instill G c f o n 2 v) 0 := by
       apply ContDiffAt.prodMk ((hr.ready v).of_le (by exact_mod_cast hp)) contDiffAt_const
    have hk(p:ℕ)(X:Config G c→ℂ)(hh:Crest p X 1)(hu:2 ≤ p): leftDerivs X [x,y] 1=iteratedFDeriv ℝ 2 (X ∘ journey 1 2 v) 0 cart:=by
       have hb:=Germ.ordered v (f:=X) (show Germ _ _ _ from hh.germ.of_le (Nat.cast_le.mpr hu)); simpa [v,List.ofFn_succ] using! hb
    let z:=Spins.flash (D ∘ F) t o n
    have h0:instill G c f o n 2 v 0=0:=by unfold instill; rw [launch_zero, Repeat.Cub.blankBirth]; rfl
    let X(w:Directions G c):Deck G c f:= (PhysicalNext.JointLoad.Heir.crop o n 1 (increment 1 w),0)
    have hX:X 0=0:=by simp [X, Repeat.Cub.blankBirth]
    have hK: ContDiffAt ℝ 2 X 0:= (hr.germ.of_le le_top).prodMk contDiffAt_const
    have hC:Crest 2 z 1:=by
       apply into
       rw [show z ∘ increment (1:Config G c)= (t^2)⁻¹ • (D ∘ (F ∘ X)) from ?_]; swap; · funext w; unfold z X Spins.flash pivotRay; rw [Function.comp_apply,add_zero]; rfl
       have hx: ContDiffAt ℝ 2 F (X 0):=by rwa [hX];
       have he0: ContDiffAt ℝ 2 D ((F ∘ X) 0):=by simpa only [comp_apply,hX,hf] using h;
       exact (he0.comp _ (hx.comp _ hK)).const_smul ((t^2)⁻¹:ℝ)
    have he:y' 0=0:=by unfold y'; simp [h0,hf]
    have hy : ContDiffAt ℝ 2 y' 0:=(show ContDiffAt ℝ 2 F (instill G c f o n 2 v 0) from by rwa [h0]).comp _ hv
    have ha :ContDiffAt ℝ 2 (D ∘ y') 0:=(show ContDiffAt ℝ 2 D (y' 0) from by rwa [he]).comp _ hy
    change leftDerivs z _ _=_; rw [hk _ z hC le_rfl,show z∘journey 1 2 v=(t^2)⁻¹ • (D ∘ y') from ?_,iteratedFDeriv_const_smul_apply ha,_root_.smul_apply]
    swap; · funext w; unfold z y' Spins.flash pivotRay; rw [Function.comp_apply,add_zero]; rfl
    have ht:(cart : Fin 2→ Panels 2)=![cart 0,cart 1]:=by funext i; fin_cases i <;>rfl
    have hh:fderiv ℝ y' 0=(fderiv ℝ F 0).comp L:=by
        unfold y'; rw [fderiv_comp 0 _ (hv.differentiableAt (by norm_num)),h0]
        · rw [h0]; exact hF.differentiableAt (by norm_num)
    conv_lhs=>rw [ht,pair_price D y' h hz hy he .., hh]
    rfl

-- all dimensions fixed at two-slot d4 charges. op Hessian mass error.
lemma prompt (D:Directions G f→ℂ)(ht:t=P.threshold)(h:ContDiffAt ℝ 2 D 0)(h0:fderiv ℝ D 0=0)(hX:‖iteratedFDeriv ℝ 2 D 0‖ ≤ C)
   (H:Tour T L x b p u K)(hr:0 ≤ u)(hv:1 ≤ K)(hp:2 ≤ p)
   (hε:‖fderiv ℝ (display T L x b true) 0 - mainStroke T L true‖ ≤ A)(he:A≤1)
   (Y:Canvas P (S.ratio.parent o) (reach x) (1:Config G c) 1 p γ)(hK:1 ≤ γ)(a e:Directions G c)(ha:P.dirBound (S.ratio.parent o) a)(hk:P.dirBound (S.ratio.parent o) e):
    let G':= γ*(1+((reach x:ℕ):ℝ))^(P.power*p)
    let f':= fun (y:Deck G c f→ Directions G f)=>leftDerivs (Spins.flash (D∘y) t (S.ratio.parent o) (reach x)) [a,e] 1
    ‖f' (display T L x b true) - f' (mainStroke T L true)‖ ≤ 2*C*(K+1)*G'^2*A :=by
     subst t; intro G' f'
     have ht:=P.threshold_pos; have hγ:0 ≤ G':=by unfold G'; positivity
     let H':=display T L x b true; let W:=mainStroke T L true
     let v:Slab G c 2:= ![a,e]; let T':= fderiv ℝ (instill G c f (S.ratio.parent o) (reach x) 2 v) 0
     let J:= fderiv ℝ H' 0
     have ho:= (H.costs true).uniform 0 (norm_zero.le.trans hr)
     have hw: ‖J‖ ≤ K:= price_one ho (by omega)
     have hA:0 ≤ A:= (norm_nonneg _).trans hε
     have hh: ‖W‖ ≤ K+1 := ((by simpa only [sub_zero,norm_sub_rev W J] using norm_sub_le_norm_sub_add_norm_sub W J 0) : ‖W‖ ≤ ‖J-W‖+‖J‖)|>.trans ((add_le_add (hε.trans he) hw).trans_eq (add_comm ..))
     have hT:‖T'‖ ≤ G'*P.threshold:=by
       rw [← norm_iteratedFDeriv_one]; simpa only [pow_one,G',T'] using (floor_rate (f:=f) Y hK v (by intro i; fin_cases i; exact ha; exact hk) hp).2.2 1 le_rfl (by norm_num)
     have he0 (i:Fin 2):‖T' (cart i)‖ ≤ G'*P.threshold:= (T'.le_opNorm _).trans (le_trans (b:= _ * 1) (mul_le_mul hT ((pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j=> by simp only [cart,Pi.single_apply]; split <;> simp) (norm_nonneg _) (by positivity)) (by rw [mul_one]))
     unfold f'; rw [rates D ht h h0 H' (ho.smooth.of_le (Nat.cast_le.mpr hp)) (H.costs _).home _ _ _ Y hp, rates D ht h h0 (fun p=> W p) W.contDiff.contDiffAt W.map_zero _ _ _ Y hp,W.fderiv]
     let K':=(K+1)* (G'* P.threshold); let A':= A* (G'*P.threshold)
     have hP(i:Fin 2):‖J (T' (cart i))-W (T' (cart i))‖ ≤ A':=(show ‖(J-W) _‖ ≤ _ from ((J-W).le_opNorm _).trans (mul_le_mul hε (he0 i) (norm_nonneg _) hA))
     have hc:= (norm_nonneg _).trans hX
     rw [← smul_sub,norm_smul,Real.norm_of_nonneg (by positivity)]
     apply (mul_le_mul_of_nonneg_left (torque D (J (T' (cart 0))) (J (T' (cart 1))) (W (T' (cart 0))) (W (T' (cart 1))) C K' A' hX ((J.le_opNorm _).trans (mul_le_mul (hw.trans (le_add_of_nonneg_right zero_le_one)) (he0 0) (norm_nonneg _) (by positivity))) ((W.le_opNorm _).trans (mul_le_mul hh (he0 1) (norm_nonneg _) (by positivity))) (hP 0) (hP 1)) (by positivity)).trans_eq
     unfold K' A'; field_simp
end YM.RG12.Spins

import YM.RG12.Shadows.Stamp
/-! Retain order per temperature on bona fide projections on Hot platform -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sanction
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism Brim Lotus Peak
open WardBin.Lies Push.PriceCompiler Foramen Gate Planned.AtomRegular.Foliage
open YM.RG12.Shadows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{V:Loom G}
namespace Barque
variable (B:Barque V)(M:Leaf B.A)(d:ℝ)(κ:Chi)
def twin (y:Panels 2) (z:Prices G B.I):= Mercury.both B.X B.chip B.A B.a B.q κ B.b V.D M d V.o.a B.tour y z
def honor (x:Panels 2) (z:Prices G B.I):= coin B.X B.chip B.A B.a d B.A.beta V.o.a (B.tour x) z=1 ∧ veil B.X B.a B.q κ B.b V.D B.A.p d B.A.beta z (B.tour x)=1
lemma extracts {_z:Prices G B.I} {y:Panels 2}(h:B.honor d κ y _z): B.twin M d κ y _z=(B.pole6 d _z y-B.pole9 d _z y)*(B.cube M _z):=by
   unfold twin Mercury.both Mercury.T6 Mercury.T9 Mercury.box6 Mercury.box9
   change B.pole6 _ _ _* (_*B.cube _ _) - B.pole9 _ _ _ * (_*B.cube _ _) = _
   rw [h.1,h.2,one_mul,sub_mul]
end Barque
variable {S : Shows V}
namespace Bazaar
variable (H:Bazaar V S)
local notation "η*" => H.winter
local notation "x₀"=>fun _ : ℕ=> Unit
local notation "y₀"=>fun _ : ℕ=> Panels 2
local notation "B!" i:max =>S i
def pave (M:∀ i, Leaf (S i).A)(d:ℝ)(κ:Chi) (z:Water S): Drift x₀ y₀:=fun i _ y=> (S i).twin (M i) d κ y (z i)
variable (M:∀ i,Leaf (S i).A){d a:ℝ}(κ:Chi){z:Water S}(h0:Canary G d a)(hZ:RG12.Shadows.Charges H.winter 0 (H.Flood z)){D:ℕ→ℝ}(hd: RG12.Shadows.Charges H.winter 0 D)(F:∀ᶠ i in atTop,Nonempty ((S i).Horn (M i) (D i)))(hc:∀ᶠ i in atTop,(S i).OpenKey (z i)∧ (S i).OpenKey (-z i))
include h0 hZ F hd hc
theorem plume_spun (hP:∀ᶠ i in atTop,∀ᶠ x in 𝓝 (0:Panels 2),(S i).honor d κ x (z i)∧(S i).honor d κ x (-z i)) (he:Charges η* 0 (fun i=>(M i).weight)):
    Touch η* 2 1 false (pave M d κ z) (rend (pave M d κ (-z))):=by
   let f (z:Water S)(i:ℕ):= (S i).cube (M i) (z i); let u (z:Water S):Drift x₀ y₀ := fun i _ _=> f z i
   have h (z):Charges η* 0 (f z):= he.move (Eventually.of_forall fun i=> (M i).earn _)
   have hz :Touch η* 2 0 true (u z) (rend (u (-z))):= ⟨Call.up (h z),by simpa only [zero_add,RG12.Shadows.aura,one_smul] using! Call.up (I:=x₀) (E:=y₀) (H.golf_price M hd F z hZ hc)⟩
   have Ht:= (H.taxUp h0 hZ).shade; rw [zero_add] at Ht
   have ht := ((Ht.negates.times hz)); rw [add_zero] at ht
   have hv (z:Water S)(hl:∀ᶠ i:ℕ in atTop,∀ᶠ x in 𝓝 (0:Panels 2),(S i).honor d κ x (z i)):
       ∀ᶠ i:ℕ in atTop,∀ j:Unit,pave M d κ z i j =ᶠ[𝓝 0] ((track z d - slice z d)*u z) i j:= by
     filter_upwards [hl] with i hi j; filter_upwards [hi] with x hi using (S i).extracts _ _ _ hi
   have hX:= hv z (hP.mono fun i hi=> hi.mono fun j hj=> hj.1)
   have hY':= hv (-z) (hP.mono fun i hi=> hi.mono fun j hj=>hj.2)
   have hY:∀ᶠ i:ℕ in atTop,∀ j:Unit,rend (pave M d κ (-z)) i j =ᶠ[𝓝 0] ((rend (track (-z) d)-rend (slice (-z) d))*rend (u (-z))) i j := by
     filter_upwards [hY'] with i hi j; refine EventuallyEq.comp_tendsto (hi j) ?_; simpa only [neg_zero] using continuous_neg.tendsto (0:Panels 2)
   refine ⟨?_,?_⟩
   · simpa only [neg_sub] using! ht.origin.fakes (g:=pave M d κ z) (by simpa only [neg_sub] using! hX)
   refine ht.listens.fakes ?_
   simp only [fit,Bool.not_false,Bool.not_true,RG12.Shadows.aura,neg_sub]
   exact Filter.Eventually.mono (hX.and hY) (fun i hi j=>((hi.1 j).and (hi.2 j)).mono (fun x hx=>by change _- (-1:ℝ)*_= _- (-1:ℝ)*_; rw [hx.1,hx.2]))
include h0 hZ in
lemma mirror_price (hP:∀ᶠ i in atTop,∀ᶠ x in 𝓝 (0:Panels 2),(S i).honor d κ x (z i)∧(S i).honor d κ x (-z i)) (he:Charges η* 0 (fun i=>(M i).weight)):
   Charges η* 2 (fun i=> normJ 2 (pave M d κ z i ()+pave M d κ (-z) i ()) 0):=by
  have hh:= H.plume_spun _ κ h0 hZ hd F hc hP he
  have hv:= hh.listens; simp only [RG12.Shadows.aura,neg_smul,one_smul,sub_neg_eq_add,show (1:ℝ)+1=2 by norm_num] at hv
  have hb:= (click hv).second
  have hk:= Keeps.pays hb (fun i=> ()); change Charges η* 2 (fun i=> normJ 2 ((pave M d κ z+rend (pave M d κ (-z))) i ()) 0) at hk
  apply hk.equates
  obtain ⟨w,hv,hS⟩:=hh.origin; obtain ⟨w',he,H'⟩:=hh.remote
  filter_upwards [hS,H'] with i ha hb; let F:=pave M d κ z i (); let G':=pave M d κ (-z) i ()
  let v (x:Panels 2):=-x
  have hF: ContDiffAt ℝ (↑(2:ℕ)) F 0:= (ha ()).smooth; have he : ContDiffAt ℝ (↑(2:ℕ)) (G'∘v) 0:= (hb ()).smooth
  have hG:ContDiffAt ℝ (↑(2:ℕ)) G' 0:=by
      have hv:= (show ContDiffAt ℝ (↑(2:ℕ)) (G'∘v) (v 0) from by simp only [show v 0=0 from neg_zero]; exact he).comp  (0:Panels 2) (f:=v) (show ContDiffAt ℝ (↑(2:ℕ)) v 0 from contDiff_neg.contDiffAt) -- 0 neg
      simpa [v, Function.comp_def] using hv
  change normJ 2 (F+G'∘v) 0 = normJ 2 (F+G') 0
  rw [normJ,normJ,iteratedFDeriv_add_apply hF he,iteratedFDeriv_add_apply hF hG]; unfold v Function.comp; rw [iter_neg G' hG]; norm_num
end Bazaar
end YM.PhysicalNext.Repeat.Sanction

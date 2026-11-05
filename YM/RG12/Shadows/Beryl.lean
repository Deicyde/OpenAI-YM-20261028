import YM.RG12.Shadows.Clutch
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
variable (B:Barque V)
def gas (z:Prices G B.I)(i:B.I) : G.Color:= Baffle.anchor B.X B.a z B.A.beta i
def jetA (i:B.I)(y:Panels 2):= G.mat (Silica.action B.X (B.tour y) (B.a.address i))
abbrev luster (i:B.I)(d:ℝ)(z:Prices G B.I)(y:Panels 2):= Eider.plume G V.chi d (B.jetA i y) (B.gas z i)
def film (d:ℝ) (z:Prices G B.I)(y:Panels 2):= Baffle.pulse B.X (B.tour y) B.a z d B.A.beta
lemma jets0 (i:B.I):B.jetA i 0=1:=by unfold jetA; rw [Silica.action,B.j1,mul_inv_cancel,G.mat_one]
lemma gaseous(z:Prices G B.I)(i:B.I):B.gas z i=B.fuel • tape z i:=by unfold gas Baffle.anchor peanuts; rw [← B.j1]; change B.W6 i 0+B.fuel • tape z i= _; rw [B.zeroW,zero_add]
lemma gas_neg(z:Prices G B.I)(i:B.I):B.gas (-z) i= -B.gas z i:=by rw [gaseous,gaseous]; change B.fuel • colors (-z) i = -(B.fuel • colors z i); rw [map_neg,Pi.neg_apply, smul_neg]
lemma movie (z: Prices G B.I)(d:ℝ) : B.film d z= fun y=> ∏ i:B.I,palm G V.chi d (B.jetA i y) (B.gas z i):=by unfold film Baffle.pulse press jetA gas; rw [B.chi]
end Barque
abbrev Water {V:Loom G}(S:Shows V):= (i:ℕ)→Prices G (S i).I -- Neg etc
-- small thickness. Elaborate health-looking only after.Slurry & .Cone.
namespace Bazaar
variable {S:Shows V}(H:Bazaar V S)
local notation "η*"=> H.winter
local notation "B!" i:max => S i
abbrev Flood (_H:Bazaar V S)(z:Water S)(i:ℕ):ℝ:=‖z i‖ -- NOTE unscaled
lemma Flood_neg (z:Water S): H.Flood (-z)=H.Flood z:=by ext k; rw [Flood,Pi.neg_apply, norm_neg]
include H
lemma grand (z:Water S)(hz:Charges η* 0 (H.Flood z)) :Keeps η* 1 _ (fun i k=> ‖(S i).gas (z i) k‖)∧Keeps η* 0 (fun i=> (S i).Q₀) z := by
  let c:ℝ:= Fintype.card G.ColorIndex
  refine ⟨⟨_,RG12.Shadows.Charges.holdRight H.vapour.1 (hz.left c),Eventually.of_forall fun i k=>?_⟩,⟨_,hz,Eventually.of_forall fun i k=> (norm_le_pi_norm (z i) k)⟩⟩
  let B:=S i; rw [abs_of_nonneg (norm_nonneg _),B.gaseous,norm_smul,Real.norm_of_nonneg B.hot.le]; refine mul_le_mul_of_nonneg_left ?_ B.hot.le
  -- Euclidean norm ≤ L1.Sum
  have he:= (EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr (tape (z i) k)
  rw [← he]; apply (norm_sum_le ..).trans; calc
    _ ≤ ∑ j:G.ColorIndex, ‖z i‖:= Finset.sum_le_sum fun j _=> ?_
    _ = c*‖z i‖:= by simp [c]
  rw [norm_smul,OrthonormalBasis.norm_eq_one,mul_one]; simpa only [EuclideanSpace.basisFun_repr] using! norm_le_pi_norm (z i) (k,j)
lemma beams:∃ w:ℕ→ℝ,Charges η* 1 w ∧ (∀ i,0 ≤ w i) ∧∀ᶠ i:ℕ in atTop,let B:=S i; ∀ j:B.I,Brush 2 (royalty G) (w i) (B.jetA j) 0:=by
  obtain ⟨M,C,t,r,h,q,hM,hB,hC,ht,hr,hh,HQ⟩:= H.prices; refine ⟨M,hM,hB,HQ.mono fun i hi j=>?_⟩ -- let introduces? j=B if binder after let? tactic
  let B:= S i
  have hg:= Silica.chargeMode (X:=B.X) (M i) hi.sunny (B.a.address j)
  change Brush V.n _ _ (fun y=>G.mat (Silica.action B.X (journey B.X.V _ B.U y) (B.a.address j))) _ at hg; rw [B.center] at hg
  exact hg.smaller V.depth
variable {d a:ℝ} (h: Canary G d a){z:Water S}(he:RG12.Shadows.Charges H.winter 0 (H.Flood z))
structure Pulse (i:ℕ)(d Q M A:ℝ)(z:Water S):Prop where
   loom k: Brush 2 Q M ((S i).luster k d (z i)) 0
   piston k: normJ 1 (fun y=>(S i).luster k d (z i) y -(S i).luster k d (-z i) y) 0 ≤ A
   ample (k): Brush 2 Q M (fun y=> palm G V.chi d ((S i).jetA k y) ((S i).gas (z i) k)) 0
include h he
lemma storm : ∃ (Q:ℝ)(M D:ℕ→ℝ),0≤Q∧Charges η* 1 M ∧ (∀ i,0 ≤ M i) ∧Charges η* 2 D ∧∀ᶠ i:ℕ in atTop,Pulse i d Q (M i) (D i) z:=by
   obtain ⟨w,hw,ha,Hw⟩:=H.beams; obtain ⟨v,hv,he₁⟩:=(H.grand z he).1
   obtain ⟨Q,hQ,hp⟩:=optics9 (K:=royalty G) V.chi h
   have hf:= (hv.left Q).mul hw; rw [show (1:ℝ)+1=2 by norm_num] at hf
   refine ⟨Q,_,_,hQ,hw.left Q,fun i=>mul_nonneg hQ (ha i),hf,?_⟩
   filter_upwards [he₁,(hv.tend0 zero_lt_one).eventually (ge_mem_nhds zero_lt_one),Hw] with i hF hg Hw
   let B:= S i; have hB (k:B.I):‖B.gas (z i) k‖ ≤ v i:= (le_abs_self _).trans (hF k)
   have hc k:=hp (Panels 2) (B.jetA k) (w i) (B.jets0 k) (Hw k) (B.gas (z i) k) ((hB k).trans hg)
   exact ⟨fun k=> (hc k).1,fun k=>by unfold Barque.luster; rw [B.gas_neg]; exact (hc k).2.2.trans (by gcongr; exacts [ha i,hB _]),fun k=> (hc k).2.1⟩
lemma flowPulse : Sleeve η* 0 1 2 (fun (i:ℕ) (_:Unit)=> (S i).film d (z i)):=by
   obtain ⟨Q,M,D,hQ,hM,hm,hD,Hp⟩:= H.storm h he
   refine carries (RG12.Shadows.Charges.frozen 1 _) (RG12.Shadows.Charges.holdMul (hM.left (1+Q)) H.horizon0) ?_
   filter_upwards [Hp] with i Hp k; let B:=S i
   rw [B.movie]
   have hh := Brush.all_prod Finset.univ (fun (j:B.I) y=> palm G V.chi d (B.jetA j y) (B.gas (z i) j)) (fun _=>1) (fun _=>(1+Q)*M i) (fun j _=> (Hp.ample j).exalt (by rw [B.jets0,leaves h,norm_one]))
   rwa [Finset.prod_const_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
lemma flowL :Sleeve η* 1 1 2 (fun (i:ℕ) k=>(S i).luster k d (z i))∧Flares η* 1 2 (fun (i:ℕ) k y=>(S i).luster k d (z i) y- (S i).luster k d (-z i) y):=by
  obtain ⟨Q,M,D,hQ,hM,hm,hD,Hp⟩:= H.storm h he
  let f (i:ℕ)(k:(S i).I)(y:Panels 2):=(S i).luster k d (z i) y
  have he : Sleeve η* 0 1 2 f := carries (RG12.Shadows.Charges.frozen Q _) hM (Hp.mono fun _ hi j=> hi.loom j)
  exact ⟨⟨he.smooth,Flares.mk (RG12.Shadows.Charges.idle _ _) (Eventually.of_forall fun i k=>by simp only [normJ,norm_iteratedFDeriv_zero,Barque.luster,Barque.jets0,nothing h,norm_zero,le_refl]),he.first,he.second⟩, Flares.mk hD (Hp.mono fun i hi k=>hi.piston k)⟩
end Bazaar
end YM.PhysicalNext.Repeat.Sanction

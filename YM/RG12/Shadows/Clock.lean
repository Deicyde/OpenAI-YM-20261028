import YM.RG12.Shadows.Price
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
variable {S:Shows V}
namespace Bazaar
variable (H:Bazaar V S)
local notation "B!" i:max=> S i
set_option quotPrecheck false
local notation "η*" => H.winter
local notation "y₀" => fun i:ℕ=> (B! i).Q₀
local notation "x₀" => fun _ :ℕ=>Panels 2
variable {d a:ℝ}(h:Canary G d a){z:Water S}(hg:RG12.Shadows.Charges H.winter 0 (H.Flood z))
abbrev swift (d:ℝ)(z : Water S) : RG12.Shadows.Trail y₀ x₀ :=fun i=> (S i).swift d (z i)
abbrev speed (d:ℝ)(z : Water S) : RG12.Shadows.Trail y₀ x₀ :=fun i=> (S i).speed d (z i)
local notation "t!" => RG12.Shadows.tip
include H h hg
abbrev panel (S:Shows V)(B:Counter (fun i=> (S i).I) x₀ (fun _=>G.Color)): Drift (fun i:ℕ=> (S i).Q₀) x₀:=fun i j y=> B i j.1 y j.2
omit H h hg in
lemma volley {S:Shows V}{R:Haze}{t r p:ℝ}{f: Counter (fun i=>(S i).I) x₀ (fun _=>G.Color)}(H:Sleeve R t r p f) : Sleeve R t r p (panel S f):=by
  let L (i:ℕ)(j:(S i).Q₀):G.Color→L[ℝ] ℝ := EuclideanSpace.proj (𝕜:=ℝ) j.2
  have hl (i:ℕ)(j:(S i).Q₀): ‖L i j‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=> by rw [one_mul]; exact PiLp.norm_apply_le v _
  exact H.reports (Q:=fun _=>ℝ) (fun i j=>j.1) L hl
local notation "globe" => fun i:ℕ=> (B! i).W6
local notation "lobe" => (panel S (globe))
local notation "suit" z => fun i k=> (B! i).luster k d (z i)
set_option maxHeartbeats 440000 in
lemma pigment : Sleeve η* 0 0 1 (t! (swift d z))∧ Flares η* 1 1 ((t! (swift d z))-(t! (swift d (-z)))):=by
   have hz:RG12.Shadows.Charges H.winter 0 (H.Flood (-z)):= by rwa [H.Flood_neg]
   have ha:= H.flowL h hg; have hb:=H.flowL h hz; let K:Drift y₀ x₀:=lobe; have hf:= H.cadence.1
   let J (z:Water S):= panel S (suit z)
   let f(i:ℕ):ℝ:=((S i).fuel)⁻¹
   have hZ := H.vapour.2
   let T (z:Water S):Drift y₀ x₀:=fun i j _=>z i j
   have hp: Sleeve η* 1 1 2 K:=by have hK:=volley hf; exact ⟨hK.smooth,Flares.mk (RG12.Shadows.Charges.idle _ η*) (Eventually.of_forall fun i j=> by simp only [normJ,K,panel,norm_iteratedFDeriv_zero,Barque.zeroW]; exact (norm_zero: ‖(0:ℝ)‖=0).le),hK.first,hK.second⟩
   have hK :Sleeve η* 0 0 1 (fun i=>f i • (J z-K) i):=by
      have he:= ((volley ha.1).sub hp).scales hZ; rw [show (2:ℝ)+(-1)=1 by norm_num,add_neg_cancel] at he; exact he
   have hT := click (Call.flat (n:=2) (E:=x₀) (H.grand z hg|>.2)); change Sleeve η* 0 0 0 (T z) at hT
   have ht: Sleeve η* 0 0 1 (T z):= ⟨hT.smooth,hT.zero,hT.first,Flares.mk (RG12.Shadows.Charges.idle _ _) (Eventually.of_forall fun i j=> by unfold T; rw [normJ,iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero])⟩
   refine ⟨(ht.add hK).eq (fun i j x=>(Barque.scone (S i) d (z i) x j).symm),?_⟩
   -- luster difference
   have hh : Flares η* 1 2 (J z-J (-z)):=by
      let r:=fun (i:ℕ)(j:(S i).Q₀)=>j.1
      let C i (j:(S i).Q₀):G.Color→L[ℝ]ℝ:= EuclideanSpace.proj (𝕜:=ℝ) j.2
      have hl i j: ‖C i j‖ ≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=> by rw [one_mul]; exact PiLp.norm_apply_le v _
      exact Flares.reports ha.2 ((ha.1.sub hb.1).smooth.mono (by decide)) r (Q:=fun _=>ℝ) C hl
   have hs: Smooths 1 (J z-J (-z)) := ((volley ha.1).sub (volley hb.1)).smooth.mono (by decide)
   let v :Drift y₀ x₀ := T z-T (-z)
   have hv : Flares η* 1 1 v:= Flares.mk (RG12.Shadows.Charges.idle _ _) (Eventually.of_forall fun i j=> by change normJ 1 (fun _:Panels 2=> z i j- (-z i j)) _ ≤0; rw [normJ,iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero])
   have hx':=hh.scales hZ hs; rw [show (2:ℝ)+(-1)=1 from by norm_num] at hx'
   refine (hv.adds hx' (Eventually.of_forall fun i j=> show ContDiffAt ℝ (↑(1:ℕ)) (fun _:Panels 2=> z i j- -z i j) 0 from contDiffAt_const) (Filter.Eventually.mono hs fun i hi j=> (hi j).const_smul ((S i).fuel)⁻¹)).sameZero (Eventually.of_forall fun i j=> Eventually.of_forall fun x=>?_)
   change Barque.swift (S i) _ _ x j-Barque.swift (S i) _ _ x j=(z i j-(-z i j))+ f i*_
   unfold f; rw [Barque.scone,Barque.scone]; change _-( (-z i j)+_)= _+_*(J z i j x-J (-z) i j x); unfold J panel; ring
lemma touching : Touch η* 2 0 false (t! (swift d z)) (rend (t! (swift d (-z)))):= by
  obtain ⟨hp,hh⟩:= H.pigment h hg; have he:RG12.Shadows.Charges H.winter 0 (H.Flood (-z)):= by rwa [H.Flood_neg]
  exact cusp (by simpa only [zero_add] using! hp) (by simpa only [zero_add] using! (H.pigment h he).1) (Eventually.of_forall fun i j=> by unfold tip swift; rw [Barque.swift_zero _ _ h,Barque.swift_zero _ _ h]; simp) (by simpa only [zero_add] using! hh)
set_option maxHeartbeats 560000 in
omit H h hg in
private lemma alters (z:Water S)(d:ℝ)(i:ℕ)(j:(S i).Q₀)(x:Panels 2):
     (t! (speed d z)- t! (swift d z)) i j x=
       -(S i).fuel⁻¹*((S i).W9 j.1 x-(S i).W6 j.1 x) j.2:=by
     let B:=S i; change B.speed _ _ x j - B.swift _ _ x j= _
     rw [Barque.fit9];
     -- skip normalization of inputs
     have h (a b v:ℝ):a-b*v-a=(-b)*v:=by ring
     exact h (B.swift d (z i) x j) B.fuel⁻¹ ((B.W9 j.1 x - B.W6 j.1 x) j.2)

omit H h hg in
private lemma common {R:Haze}{I E:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)]{l:Drift I E}(hL:Sleeve R 1 2 1 l):Touch R 2 1 true l (rend l):=by
  have hx:=hL.flips; have hz:=hL.sub hx
  have hv:Sleeve R 2 2 2 (l-rend l):=by
    refine ⟨hz.smooth,Flares.mk (RG12.Shadows.Charges.idle _ _) (Eventually.of_forall (fun i j=>by simp [rend,normJ])),hz.first,Flares.mk (RG12.Shadows.Charges.idle _ _) ?_⟩
    filter_upwards [hL.smooth,hx.smooth] with i hs ht j
    change ‖iteratedFDeriv ℝ 2 (l i j-fun y=>l i j (-y)) 0‖≤0
    rw [iteratedFDeriv_sub_apply (f:=l i j) (g:=fun y=> l i j (-y)) (hs j) (ht j),iter_neg _ (hs j)]; norm_num
  exact ⟨hL.call le_rfl one_le_two le_rfl,by rw [show (1:ℝ)+1=2 from by norm_num,RG12.Shadows.aura,one_smul]; exact hv.call le_rfl le_rfl le_rfl⟩
lemma centeredG : Tilts η* 2 0 false (t! (swift d z)) (rend (t! (swift d (-z)))) (t! (speed d z)) (rend (t! (speed d (-z)))) := by
  refine ⟨H.touching h hg,?_⟩
  let D (i:ℕ)(b:(S i).I) := (S i).W9 b - (S i).W6 b; let f:=panel S D
  obtain ⟨hA,hD,hf,hi⟩:= H.cadence; change Flares η* 1 3 f at hf
  let q (z:Water S):= t! (speed d z)- t! (swift d z)
  have he:= volley (f:=D) hD; have ht:Sleeve η* 2 3 2 f:= by
     refine ⟨he.smooth,Flares.mk (RG12.Shadows.Charges.idle _ _) ?_,hf,he.second⟩
     filter_upwards [hi] with i hi j; rw [normJ,norm_iteratedFDeriv_zero]; change ‖(((S i).W9 j.1 0-(S i).W6 _ 0) j.2:ℝ)‖ ≤0; rw [hi,Barque.zeroW,sub_zero]; exact (norm_zero: ‖(0:ℝ)‖=0).le
  let D'(i:ℕ):= -((S i).fuel)⁻¹
  have hs:RG12.Shadows.Charges H.winter (-1) D':= H.vapour.2.transfer (Eventually.of_forall fun i=> by unfold D'; rw [norm_neg])
  let l:= fun i=> D' i • f i
  have hL:Sleeve η* 1 2 1 l:=by have hx:=ht.scales hs; rw [show (2:ℝ)+(-1)=1 from by norm_num,show (3:ℝ)+(-1)=2 from by norm_num] at hx; exact hx
  have hk:= common hL
  have hF (z:Water S)(i:ℕ)(j:(S i).Q₀)(x:Panels 2): q z i j x=l i j x:= alters z d i j x
  rw [zero_add]; exact hk.same (fun i j x=>hF z i j x) (fun i j x=>hF (-z) i j (-x))
end Bazaar
end YM.PhysicalNext.Repeat.Sanction

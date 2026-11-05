import YM.RG12.Shadows.Small
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
structure Horn (M : Leaf B.A)(C:ℝ) where
  turn : M.turn=.logKey B.chip
  g :Config G B.f→ℝ
  issue : B.A.p.Regular (B.A.activities.reg B.chip).support g
  hs:M.ingredient = masked B.A.p.threshold (B.A.activities.reg B.chip).support g
  ink: Directions G B.f→ℝ
  analytic :∀ x, ‖x‖≤1 →Offset.Through 3 ink x C
  affine:fderiv ℝ ink 0=0
  status (x):g (increment 1 x)=(B.A.p.threshold^2)⁻¹ * ink x
variable (M:Leaf B.A)(z:Prices G B.I)
abbrev cube := Mercury.golf B.X B.chip B.A B.a M z
def jet(z:Prices G B.I)(i: Bond B.f):G.Color:= if i∈B.F.trunks then 0 else isotope B.X B.a (B.gas z) i
set_option quotPrecheck false
local notation "E'"=> (B.A.activities.reg B.chip).support
lemma trapeze (z:Prices G B.I):Agrees (inspected (E')) (strip6 B.X B.a B.X.V (anchor B.X B.a z B.A.beta)) (increment 1 (B.jet z)):=by
  intro i hi hj
  by_cases he:i∈B.F.trunks
  · change B.F.drape _ i= _; rw [show B.F.drape _ i=(1:G.El) from B.F.on_tree _ ⟨i,he⟩,increment,jet,if_pos he]; simp
  obtain ⟨k,hk⟩:= falls B.X B.a ⟨i,he⟩ hi hj; change B.a.address k=i at hk; subst i
  rw [strip6,Coat.viewing (vary B.X B.X.V) _ _ (show (vary B.X B.X.V).Hot _ from borne B.X B.a B.curtains k)]
  unfold increment jet; rw [if_neg he]; change _*replica B.S.ratio B.X.V _ = _*_; rw [B.center,Malachite.replica_flat]; rfl
lemma jet_minus : B.jet (-z)= -B.jet z:=by
  funext i; rw [Pi.neg_apply,jet,jet]; split <;> rename_i he
  · rw [neg_zero]
  unfold isotope; by_cases hx : i∈Set.range B.a.address
  · obtain ⟨k,rfl⟩:=hx; rw [B.a.address_inj.extend_apply,B.a.address_inj.extend_apply]; exact B.gas_neg z k
  rw [Function.extend_apply' _ _ _ hx,Function.extend_apply' _ _ _ hx]; rw [Pi.zero_apply,neg_zero]
lemma jet_norm {v:ℝ}(hv:0≤v)(h:∀ i,‖B.gas z i‖≤v): ‖B.jet z‖≤v:=by
   refine (pi_norm_le_iff_of_nonneg hv).mpr fun i=>?_ ; unfold jet isotope; split
   · simpa only [norm_zero]
   by_cases he:i∈Set.range B.a.address
   · obtain ⟨k,rfl⟩:=he; rw [Function.Injective.extend_apply B.a.address_inj]; exact h _
   rw [Function.extend_apply' _ _ _ he,Pi.zero_apply,norm_zero]; exact hv
abbrev OpenKey:=(Healthy B.A.p.threshold (E') (strip6 B.X B.a B.X.V (anchor B.X B.a z B.A.beta)))
theorem hot_price {D:ℝ}(F:B.Horn M D)(h: B.OpenKey z): B.cube M z=(B.A.p.threshold^2)⁻¹ * F.ink (B.jet z):=by
  unfold cube Mercury.golf; rw [F.hs,masked_eq _ _ _ _ h]; exact (F.issue.sites _ _ (agrees_mono (B.trapeze z) (show (E')⊆inspected (E') from Finset.subset_union_left))).trans (F.status _)
end Barque
variable {S : Shows V}
namespace Bazaar
variable (H:Bazaar V S)
local notation "η*" => H.winter
local notation "B!" i:max => S i
theorem golf_price (M:∀ i,Leaf (S i).A){D:ℕ→ℝ}(hd:RG12.Shadows.Charges H.winter 0 D) (F:∀ᶠ i in atTop,Nonempty ((S i).Horn (M i) (D i))) (z:Water S)(h:Charges η* 0 (H.Flood z)) (hp:∀ᶠ i in atTop,(S i).OpenKey (z i)∧(S i).OpenKey (-z i)):
   Charges η* 1 (fun i=>(B! i).cube (M i) (z i)-(B! i).cube (M i) (-z i)):=by
  obtain ⟨v,hv,hG⟩:=(H.grand z h).1
  have hz :Charges η* 1 (fun i=> |v i|):=hv.absolute
  have ht:= H.colors0.2
  have he:= (ht.power 2).mul ((hd.left 2).mul (hz.power 3)); rw [show ((2:ℕ):ℝ)*(-1)+(0+((3:ℕ):ℝ)*1)=1 from by norm_num] at he
  refine he.move ?_
  filter_upwards [F,hG,hp,(hz.tend0 zero_lt_one).eventually (ge_mem_nhds zero_lt_one)] with i ⟨F⟩ hf ⟨hp,hp'⟩ hA; let B:=S i
  have hg := (F.analytic _ (show ‖(0:Directions G B.f)‖ ≤ 1 by simp)).nonneg
  have hx:B.cube (M i) (z i)-B.cube (M i) (-z i)=(B.A.p.threshold^2)⁻¹*(F.ink (B.jet (z i))- F.ink (-B.jet (z i))) := by rw [B.hot_price _ _ F hp',B.hot_price _ _ F hp, B.jet_minus]; ring
  change |B.cube _ _ - B.cube _ _|≤_; rw [hx,abs_mul,abs_of_nonneg (by positivity:(0:ℝ)≤ (B.A.p.threshold^2)⁻¹)]
  have hJ: ‖B.jet (z i)‖ ≤ |v i|:= B.jet_norm _ (abs_nonneg _) (fun k=> (le_abs_self _).trans ((hf k).trans (le_abs_self _)))
  rw [← inv_pow]; apply (mul_le_mul_of_nonneg_left (parity_desk _ (hJ.trans hA) _ F.analytic F.affine) (by positivity)).trans
  change _ ≤ B.A.p.threshold⁻¹^2*_; gcongr
end Bazaar
end YM.PhysicalNext.Repeat.Sanction

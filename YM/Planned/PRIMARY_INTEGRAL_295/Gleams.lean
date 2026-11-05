import YM.Planned.PRIMARY_INTEGRAL_295.Lumos
import YM.Planned.PRIMARY_INTEGRAL_295.Piers
import YM.Planned.PRIMARY_INTEGRAL_295.Solves
/-!
# Smooth earning of one canonical LXE output cut strength

Construct true torch heat equation extension near seam. Uses gauge transport
as proved on both sides in PSD poses; Uses genuine receipts. Not asserting
whole E.Sector law! Needed later X numerical payment & exact Stamp.
Doesn't alter Local.Paid support spline.Y.Check proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Gleams
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks Night Barges Novas Novas.Torch Mansions Decks Castles Ritual Solves Piers
open Icebergs Tropics Kelps Nimbuses Streets Dawning Cabins Cedar Next.Fluctuations Racks Dials WardBin WardBin.Lies
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G:Gauge} {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k r n d χ:ℕ} {c f:Side} {t θ ξ C M s : ℝ}
variable {F:Labels.Frame G d} {S:StepData c f} {Q:Teller G} (P:Torch G S)

-- before Temp primitive. Source UPDATE uses λ etc multiplied Lebl.Cash.L^d. At proof
-- halos Book general.JmeGase alternatives.Det independent of labels.X0.
def tint (T:SectionData F)(r:ℕ)(θ t ξ:ℝ)(i:F.Index) := Set.indicator (Zone c G r θ) (fun V:Config G c=> P.quest V t ξ T i)

variable {T:SectionData F}{H:Hol G} (i:F.Index)(h:Relic P Q T r k χ C t M s) (hg:ξ∈Set.Ioc 0 1) (ht:T.Sound H)
include h hg ht

-- core TRUE prices. LHC forcing Step. enough for every probe supplied at installed
-- height Budget; contour.S spark full.
lemma rolls [FiniteDimensional ℝ E] (X:E→Config G c) (g:Site c → G.El) (b:E→Dir G c)
    (hp:ContinuousAt X 0) (hm:X 0 ∈ Zone c G r θ) (hc:‖b 0‖≤M) (hf:ContDiffAt ℝ k b 0)
    (he:∀ᶠ y in 𝓝 0, AgreeNear id 0 r (Lattice.gauge g (X y)) (represent (t • b y))) :
    (∀ᶠ y in 𝓝 0,(P.staged (X y)).PosSemidef ∧ tint P T r θ t ξ i (X y) =baron P b t ξ T i y) ∧
      ContDiffAt ℝ k (tint P T r θ t ξ i ∘ X) 0:=by
   obtain ⟨hB,hA⟩:= salubrious P h b hc hf hg i
   have hv:= (punch P h hc).2; have hh: S.patch.Branches S.kernel G:= h.sizing.1
   have hx : ∀ᶠ y in 𝓝 0, ‖t • b y‖ ≤ trust S.patch S.kernel G :=
      (hf.continuousAt.const_smul t).norm.eventually (ge_mem_nhds hv)
   suffices H : ∀ᶠ y in 𝓝 0,(P.staged (X y)).PosSemidef ∧ tint P T r θ t ξ i (X y) =baron P b t ξ T i y from
      ⟨H,hA.congr_of_eventuallyEq (H.mono (fun _ hy=> hy.2))⟩
   filter_upwards [hB,hx,hp.eventually (zone_space.mem_nhds hm),he] with x hH hy hX he
   let A:=Lattice.gauge g (X x); let V:= represent (t • b x)
   have hp:= (board P t h.deck hh he).1
   have ho:(P.staged A).PosSemidef:= ((hp.trans (chair_of_sand P b t hy).1).symm ▸ hH) -- binder transport
   constructor
   · exact (Lumos.blaze P g (X x) hh ho).2
   unfold tint; rw [Set.indicator_of_mem (show X x∈Zone c G r θ from hX)]
   exact ((Lumos.treasure P g (X x) hh T ht i t ξ ho).symm.trans (Decks.require P t ξ h.deck hh he i)).trans (truth P b t T i ξ hy).symm

variable {U : Config G c} {K:Knurls G k} (hs: Spark K c r θ t M)
include hs
lemma roots (hm:U∈Zone c G r θ) :(P.staged U).PosSemidef ∧ Germ k (tint P T r θ t ξ i) U:=by
   let o:Lattice.Order:=1; let g := cardAt o U; let X:= increment U; let b:= Cabins.patched t g r X
   have he:X 0=U:=Work.G07.at_zero_increment _
   have hp:ContinuousAt X 0:= by unfold X increment; apply Continuous.continuousAt; fun_prop
   obtain ⟨hc,hx⟩:= shines o K U hm hs X he hp
   obtain ⟨hv,hH⟩:= rolls P i h hg ht X g b hp (he.symm ▸ hm) hc (traveled o K U hm hs) hx
   exact ⟨he ▸ (mem_of_mem_nhds hv).1,hH⟩
lemma current (hm:U∈Zone c G r θ) : ContinuousAt (tint P T r θ t ξ i) U:=by
   let f:=tint P T r θ t ξ i
   have he : ContinuousAt (fun y => f (increment U y)) 0 := (show ContDiffAt ℝ k (fun y => f (increment U y)) 0 from (roots P i h hg ht hs hm).2).continuousAt
   let L (t : Config G c) (e : Edge (Site c)) := G.plog (G.mat (t e*(U e)⁻¹))
   obtain ⟨(hx : L U=0),(hh:ContinuousAt L U),hv⟩ := WardBin.exp_local U id U rfl
     (fun i => (continuous_apply i).continuousAt)
   apply ContinuousAt.congr_of_eventuallyEq (f:=fun y => f (increment U (L y)))
     ((hx.symm ▸ he).comp hh)
   exact hv.mono fun y hy => congr_arg f hy.symm

-- meas argument. no continuity claim away strict.Y.


end YM.Planned.PrimaryIntegral295.Gleams

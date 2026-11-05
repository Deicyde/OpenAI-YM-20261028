import YM.UVExtension.Wick.View

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {z : E} {j n l m : ℕ} {U:E→Config G c}
namespace Festa
variable {X} (K:Festa Q L H V b B) (hx:X.x=x) (hX:X.width=o.K) (hm:X.manifest)
    (hU:Mode U z j v) (hY: V=V) (hq: U z=X.V)
    (p: Molecule S)
    {ρ:ℝ} (hd : Canary G D ρ) (hv: 8*o.a*Pressure.fiery G x L≤D/2)
local notation "Σ" => parade (ι:=ι) (betaF G x L) B
local notation "plane" => grounds (ι:=ι) (betaF G x L) b
local notation "Λ" => grown (ι:=ι) (betaF G x L) b
set_option quotPrecheck false
local notation "P₁" => edgesM S (H.unionP p) (radiusB x)
local notation "Kp" => lensS P₁ G
local notation "Φ" => cockpit X D o.a W p R Q.table Q.halo V
local notation "Jm" => (circuit Kp X.relating)
local notation "A" => (F.order G).prod X.dice
include H
lemma chaperone (C : Config G c) (I : Finset (Bond f)) (y:F.Slice G × Air f G) : Bumps Σ (fun t=> Φ t I C y) := by
  let Z:= X.wrapY y.1; intro S' f hZ hm hf
  let X(u : ℂ):= f u none; have he:DifferentiableOn ℂ X S':= (ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _:Option ι=>ℂ) none).differentiable.comp_differentiableOn hf
  apply (((he.sub_const _).mul_const (rosined Z D I C y.2:ℂ)).cexp.const_mul (Flux.scalp I Z C 1 D y.2:ℂ)).mul
  exact DifferentiableOn.fun_finsetProd fun i _=> amp_hol _ V Q.table i _ (altitude (H:=H)) _ _ _ _ _ _ _ S' f hZ hm hf -- .. edit

include K hx hX hm hd hv hq hU
-- V moving vs U comparison
lemma hovers {v: Vines ι} (hp:v∈Σ) (I : Finset (Bond f)) (y:F.Slice G × Air f G) :
    (fun t=> held X D o.a W p R Q.table Q.halo V v I (U t) y) =ᶠ[𝓝 z] fun t=> Φ v I (U t) y := by
  rcases y with ⟨c,w⟩
  let Z:= X.wrapY c; let d:=loom Z w
  have he:8*o.a*X.t≤D/2:=by unfold Coat.t; rw [hx,H.laws.data.funds.length_eq]; exact hv
  have hB:0< o.a*Z.t:=mul_pos o.large (H.laws.data.localP F Z hx hX hm).sails.room.fiery
  filter_upwards [Silica.nearby Z hd hq hU] with t ht
  unfold held cockpit; dsimp only; apply congr_arg; apply prod_congr rfl; intro i hi
  let T':= vary Z (U t)
  let p':= steer Z D d (U t); let C:= sailplane Z D w (U t)
  apply equals_hoist (amp_hol T' V Q.table i _ (altitude (H:=H)) _ _ _ B C p' (Z.input d))
    (amp_hol T' V Q.table i _ (altitude (H:=H)) _ _ _ B C p' (T'.input p'))
    (altitude (H:=H)) K.margin K.bound _ hp
  intro q h; let A':= (K.mixture q h).some; let R':=chunk R (blend V (q ∘ some)) (q none)
  have hu:0<q none := A'.laws.intake.positive
  change amberP T' R _ W _ _ _ _ (q none) ((fun i=>((q ∘ some) i:ℂ))) C _ (Z.input d) i = amberP T' R _ W _ _ _ _ (q none) (fun i=>((q ∘ some) i:ℂ)) C _ _ i
  rw [originalP _ V (q ∘ some) Q.table_exists hu, originalP _ V (q ∘ some) Q.table_exists hu]; apply congr_arg
  have hθ := conquered Z hd (U t) d ht hB he
  exact ((plastic hθ hB).reeled (show Room _ S T T'.x from hx.symm ▸ H.laws.data.room) W Q.table _ _ (show Intake _ _ T'.x R' from hx.symm ▸ A'.laws.intake) i _).symm
omit hm hX hd hv hq hU in
lemma confinement {v:Vines ι} (hp:v∈Σ) (C : Config G c) (x:F.Slice G) (y w:Air f G) (ht:Pond.swim Kp y=Pond.swim Kp w) :
    Φ v P₁ C (x,y)=Φ v P₁ C (x,w) := by
  refine equals_hoist (chaperone (H:=H) p _ P₁ _) (chaperone (H:=H) p _ P₁ _) (altitude (H:=H)) K.margin K.bound ?_ hp
  intro z hz; let J:= (K.mixture z hz).some
  have he : 0 < z none := J.laws.intake.positive
  let h(q):= jetcoin X D V x C (z none) R W Q.table Q.table_exists q z o.a p P₁ rfl he Q.halo

  rw [← h y,← h w]; apply congr_arg
  unfold Flux.rhythm Flux.recoil
  have hz' := projection Kp y w ht (z none)
  dsimp only; rw [Flux.slab P₁ (X.wrapY x) C _ _ hz']
  apply congr_arg
  let c':= H.unionP p
  let S':= X.wrapY x; let W':= vary S' C
  have hh:= H.laws.data; let Γ:= chunk R (blend V (z∘some)) (z none)
  have hm : ground Γ T Q.halo W'.B p⊆ c':=by unfold Coat.B; rw [show W'.x=_ from hx]; exact Finset.Subset.refl _
  have hv:= congr_arg (pitch P₁ S' D (z none) C) hz'; rw [pitch_alt,pitch_alt] at hv
  apply Borough.flops (X:=W') (Z:=c') ?_ (show Room _ S T W'.x from hx.symm ▸ hh.room) Q.buys (show Intake _ _ W'.x Γ from hx.symm ▸ J.laws.intake) _ _ _ hm
  have he : Kp = podium S G c' W'.B := by unfold Coat.B; rw [show W'.x=_ from hx]; exact chargedU ..
  exact ⟨Village.refl ..,fun i hi=> (Pond.observe Kp).1 hv i (he.symm ▸ hi), fun i _=>Iff.rfl⟩
end Festa
end YM.UVExtension.Wick

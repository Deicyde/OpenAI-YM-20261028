import YM.UVExtension.Wick.Party

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
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} (V : ι → Juice G f)

lemma fire_ray (p : Head S) (k : Finset ℕ) (h : 0<v) (D : ℝ) (Ñ : ChartRatio G) (w : Air f G) (l : ℕ):
    Bumps (parade v D) (fun y: Vines ι=> fireball X R Ñ s a k l V (y none) (y ∘ some) w p):= by
  intro Z f hZ hm hf
  let r (t:ℂ):=f t none
  have ht : DifferentiableOn ℂ r Z:= ((ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _:Option ι=>ℂ) none).differentiable.comp_differentiableOn hf)
  have hp i:DifferentiableOn ℂ (fun t=>(f t) (some i)) Z:= ((ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _:Option ι=>ℂ) (some i)).differentiable.comp_differentiableOn hf)
  unfold fireball; rcases p with p|p|p|p; all_goals dsimp only [Sum.elim]
  · exact (warmth_diff X ht (fun t hz=> breath h ((marching _).1 (hm hz)).1) 1 p _).mul_const _
  · exact DifferentiableOn.fun_sum fun i _ => (hp i).mul_const _
  · unfold logRay; split
    next hh=> exact (DifferentiableOn.fun_sum fun i _=> (hp i).mul_const _).cexp.sub_const _
    split
    next ht'=> exact (ht.mul_const _).cexp.sub_const _
    apply differentiableOn_const
  apply differentiableOn_const

def gush (X : Coat T F) (R : Rep G f) (W a : ℝ) (Ñ : ChartRatio G) (l : ℕ) (V : ι→ Juice G f) (p : Molecule S) (y : Vines ι) (x:F.Slice G × Air f G):ℂ:=
    ∏ i∈p, fireball (X.wrapY x.1) R Ñ W a (Matter.own p) l V (y none) (y ∘ some) x.2 i

namespace Festa
variable {V} (K : Festa Q L H V b B) (hx:X.x=x) (hX : X.width=o.K) (hm:X.manifest)
    (p : Molecule S)
local notation "Σ" => parade (ι:=ι) (betaF G x L) B
local notation "φ" => gush X R W o.a Q.table Q.halo V p
local notation "Kp" => podium S G (H.unionP p) X.B
local notation "plane" => grounds (ι:=ι) (betaF G x L) b
local notation "Λ" => grown (ι:=ι) (betaF G x L) b
include H
lemma altitude : 0<betaF G x L := by
  have ht:=H.laws.intake.height; rw [H.laws.data.funds.length_eq] at ht; linarith
lemma gush_hol (x' : F.Slice G × Air f G) : Bumps Σ (fun y=> φ y x') := by
  intro Z f hZ hf ht; apply DifferentiableOn.fun_finsetProd; exact fun i _=> fire_ray (X.wrapY x'.1) V i _ (altitude (H:=H)) _ _ _ _ Z f hZ hf ht
lemma real_val (X' : Drums ι) (hv : Λ X') (i : F.Slice G) (y : Air f G) :
    φ (hoist X') (i,y)=
      (X.body (chunk R (blend V (X' ∘ some)) (X' none)) Q.table W o.a (Matter.own p) Q.halo p (i,scaled (X' none) y):ℂ):= by
  unfold gush Coat.body Coat.term; rw [Complex.ofReal_prod]; apply prod_congr rfl; intro j hj
  apply Wick.original (X.wrapY i) V (X' ∘ some) Q.table_exists (show 0 < X' none from breath (altitude (H:=H)) (show ((X' none):ℂ)∈ _ from hv none)) j
omit H in
lemma spilling (d : ℝ) (I : Finset (Tubular f G)) (u : Poll.Body (↥I)) : spill I (d • u)=d • spill I u:= by
  ext i; change (if h:i∈I then (d • u) ⟨i,h⟩ else 0)=d*(spill I u) i; by_cases h : i∈I <;> simp [h,spill]
omit H in
lemma projection (I : Finset (Tubular f G)) (u v : Air f G) (h : Pond.swim I u=Pond.swim I v) (z:ℝ) :
    swim I (scaled z u) = swim I (scaled z v):= congr_arg (fun u:Body (↥I)=> (gStep z)⁻¹ • u) h
include hx hX hm K
omit hm in
lemma splash (t:Vines ι) (ht:t∈ Σ): StronglyMeasurable (φ t) := by
  refine propagates Husk.strong (fun i=> gush_hol (H:=H) X p i) (altitude (H:=H)) K.margin K.bound ?_ t ht
  intro Z hZ
  let Y:= K.mixture Z hZ|>.some; let fZ:= X.body (chunk R (blend V (Z∘some)) (Z none)) Q.table W o.a (Matter.own p) Q.halo p
  have hv : Intake _ _ X.x _ := hx.symm ▸ Y.laws.intake
  have hb : Measurable fZ:= X.body_b Q.table_exists hv (by rw [hx,hX]; exact H.laws.data.access) _ _ _ _
  have hh : (φ (hoist Z))=fun i=> ((fZ (i.1, (scaled (Z none) i.2))):ℂ):= by funext ⟨i,j⟩; exact real_val (H:=H) X p Z hZ i j
  have hhP : Measurable fun i:F.Slice G × Air f G=> Prod.mk i.1 (scaled (Z none) i.2):= by unfold scaled; fun_prop
  rw [hh]; exact (Complex.measurable_ofReal.comp (hb.comp hhP)).stronglyMeasurable
omit hX hm in
lemma cradle (t:Vines ι) (ht:t∈ Σ) (i:F.Slice G) (p' q': Air f G) (he:Pond.swim Kp p'=Pond.swim Kp q') : φ t (i,p')=φ t (i,q'):= by
  refine propagates (Husk.audit (i,p') (i,q')) (gush_hol X (H:=H) (V:=V) p) (altitude (H:=H)) K.margin K.bound ?_ t ht
  intro z hz; let A:= (K.mixture z hz).some
  rw [real_val (H:=H) X p z hz,real_val (H:=H) X p z hz]; apply congr_arg Complex.ofReal
  refine A.concord p (X.wrapY i) (X.wrapY i) (?_) hx (Finset.Subset.refl _)
  exact ⟨Village.refl ..,(observe Kp).1 (projection _ _ _ he _), fun _ _=>Iff.rfl⟩
end Festa
end YM.UVExtension.Wick

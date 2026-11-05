import YM.UVExtension.Copse.Berry
import YM.UVExtension.Wick.Kilt
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Pane
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Willow
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
open Animals Reserves Wick Festa PhysicalNext.Repeat.Lotus
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι → Juice G f}
open PhysicalNext.Repeat
-- require real legal leaves along compared real twists. no zero-V cov assumptions needed elsewhere
structure Lines (R:Rep G f)(V:ι→ Juice G f)(b d:ℝ)(M:Lotus.Leaf R) where
    leaf : ∀ (u:Drums ι), grown d b u→ Lotus.Leaf (chunk R (blend V (u∘ some)) (u none))
    turn u (h: grown d b u) : (leaf u h).turn=M.turn
    grain u (h: grown d b u): (leaf u h).ingredient=M.ingredient

-- value
def grains (X : Coat T F) (R : Rep G f) (W a : ℝ) (Ñ : ChartRatio G) (l : ℕ) (V : ι→ Juice G f) (M:Lotus.Leaf R) (p:Molecule S) (y : Vines ι) (x:F.Slice G × Air f G):ℂ:=
    let Z:= X.wrapY x.1; let m:= M.turn.badge S
    if m∈p then (M.paidU Z a (Z.μ+Z.atmos x.2):ℂ)* (∏ i∈p.erase m, fireball Z R Ñ W a (Matter.own p) l V (y none) (y ∘ some) x.2 i) else 0
variable (K : Festa Q L H V b B) (hx:X.x=x) (hX : X.width=o.K) (hm:X.manifest)
    (p : Molecule S) (M:Lotus.Leaf R) (hl:Lines R V b (betaF G x L) M) -- using PhysicalNext.Repeat to open
local notation "Σ" => parade (ι:=ι) (betaF G x L) B
local notation "φ" => grains X R W o.a Q.table Q.halo V M p
local notation "Kp" => podium S G (H.unionP p) X.B
local notation "Λ" => grown (ι:=ι) (betaF G x L) b
set_option quotPrecheck false
include H
lemma dips (i:F.Slice G × Air f G) : Bumps Σ (fun y=> φ y i):=by
   unfold grains; dsimp only; split; swap; · exact Lamppost.bumps _ _ (differentiableOn_const _)
   intro Z f hZ hm hf; exact (DifferentiableOn.fun_finsetProd (fun t _=> fire_ray (X.wrapY i.1) V t _ (altitude (H:=H)) _ _ _ _ Z f hZ hm hf)).const_mul _
lemma trains (d:Drums ι)(h:Λ d) (i:F.Slice G)(y: Air f G): φ (hoist d) (i,y)= ↑((hl.leaf d h).into X W o.a Q.table (Matter.own p) Q.halo p (i,scaled (d none) y)):= by
    let u:= d none; have hU:0<u:= breath (altitude (H:=H)) (show (u:ℂ)∈_ from h none)
    unfold grains Leaf.into Leaf.premium; dsimp only; rw [hl.turn]; split; swap; · rw [Complex.ofReal_zero]
    rw [Complex.ofReal_mul]; let S':= X.wrapY i; let g:= S'.μ+S'.atmos y; have hf:S'.liftA u (scaled u y)=g:=Wick.gust S' y hU
    apply congr_arg₂ (·*·)
    · unfold Leaf.paidU Leaf.fond; rw [hl.turn, hl.grain,show (X.wrapY i).liftA (chunk R (blend V (d ∘ some)) (d none)|>.beta) (Wick.scaled (d none) y)=g from hf]; rfl
    unfold Coat.term; rw [Complex.ofReal_prod]; exact prod_congr rfl (fun j _=> Wick.original _ V (d ∘ some) Q.table_exists hU _)
include hx hl K hX
lemma crew (t:Vines ι)(ht:t∈ Σ): StronglyMeasurable (φ t):=by
   refine propagates Husk.strong (dips (H:=H) X p M) (altitude (H:=H)) K.margin K.bound ?_ t ht
   intro z hz; let Y:= K.mixture z hz|>.some; let R':= chunk R (blend V (z ∘ some)) (z none); let fZ:= (hl.leaf z hz).into X W o.a Q.table (Matter.own p) Q.halo p
   have hv : Intake _ _ X.x R' := hx.symm ▸ Y.laws.intake
   have he: Measurable fZ:= (hl.leaf z hz).crystall X _ hv (by rw [hx,hX]; exact H.laws.data.access) Q.table_exists ..
   rw [show φ (hoist z)= (fun p=>(fZ (p.1,Wick.scaled (z none) p.2):ℂ)) from funext (fun ⟨i,j⟩=>trains (H:=H) X p M hl z hz i j)]; exact (Complex.measurable_ofReal.comp (he.comp (show Measurable (fun i:F.Slice G × Air f G=> (i.1, Wick.scaled (z none) i.2)) from (by unfold Wick.scaled; fun_prop)))).stronglyMeasurable
omit hX in
lemma caps (t:Vines ι)(ht:t∈ Σ)(i:F.Slice G)(p' q':Air f G) (he:Pond.swim Kp p'=Pond.swim Kp q'): φ t (i,p')=φ t (i,q'):=by
   refine propagates (Husk.audit (i,p') (i,q')) (dips (H:=H) X p M) (altitude (H:=H)) K.margin K.bound ?_ t ht
   intro z hz; let A:= (K.mixture z hz).some; rw [trains (H:=H) X p M hl z hz,trains (H:=H) X p M hl z hz]; apply congr_arg Complex.ofReal
   refine (hl.leaf z hz).concur (X.wrapY i) _ (X.wrapY i) (Z:= H.unionP p) ⟨Village.refl ..,(observe Kp).1 (projection _ _ _ he _),fun _ _=>Iff.rfl⟩ (show Room _ S T (X.wrapY i).x from hx.symm ▸ A.laws.data.room) Q.buys (?_) (show Intake _ _ (X.wrapY i).x _ from hx.symm ▸ A.laws.intake)
   rw [show ground (chunk R (blend V (z ∘ some)) (z none)) T Q.halo (X.wrapY i).B p = ground R T Q.halo (radiusB X.x) p from rfl,hx]; exact Finset.Subset.refl _
end YM.UVExtension.Willow

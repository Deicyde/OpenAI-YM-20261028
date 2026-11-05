import YM.FullVolume.E6.Axes
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
lemma aimed {ι:Type} [Fintype ι]{K H:ℕ→ E→ EuclideanSpace ℝ ι}(h:∀ i:ι,Frill φ j p (fun n y=> K n y i) (fun n y=> H n y i)):Frill φ j p K H:=by
    let L:=PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι=>ℝ)
    exact (Frill.stocks h).via (Q:=L.symm) L.symm.contDiff
lemma pointed {ι:Type} [Fintype ι]{K H:ℕ→ E→ EuclideanSpace ℝ ι}(h:Frill φ j p K H)(i):Frill φ j p (fun n y=> K n y i) (fun n y=> H n y i):= h.via (Q:= EuclideanSpace.proj (𝕜:=ℝ) i) (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff
variable [FiniteDimensional ℝ E]
lemma glance {D:Type}[NormedAddCommGroup D][NormedSpace ℝ D][FiniteDimensional ℝ D]{F:ℕ→ E→D}(h:∀ᶠ i in (J:Filter ℕ),Brush j v a (F i) p): Frill J j p F F := Frill.reserve (h.mono fun i hi=> hi.smooth) (fun i=> v*a^i) fun k hk=> h.mono fun i hi=> hi.order k hk
lemma scaleG (h:∀ᶠ i in (J: Filter ℕ),Mode (U i) p j a) : Quincy J j p U U:=fun i=> glance (h.mono fun k hk=> hk.atLink i)
-- extra post-L v.strong estimate needed only on Noble.Buy. applies V all. Supply independent N.Y
structure Promo (Q:ConnectedActivityE6.Target G P)(o:Target.Order G W) (j:ℕ)(x v ℓ a:ℝ)(χ:Chi)(T:Tube G S):Prop where
    star : ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](V:E→ Config G c)(p:E)(k:S.Choices)(i:Rod c f), Mode V p j v→ Clean (V p) x (focus S i) (radiusB x)→ Brush j ℓ 1 (fun y=> Scroll.freely T x (V y) k i) p
    buffs : ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](F:Forest S.ratio)(V:E→ Config G c)(p:E)(X:Coat T F), Mode V p j v→ X.x=x→ X.χ=χ → X.width=o.K → ∀ i:Bond f, Brush j a 1 (fun y=> (vary X (V y)).saved i) p
namespace Draft
variable (H₀:∀ n,Cash W x μ L Q o C₀ (K n).tubes (K n).kin)(hQ: ∀ n,Promo Q o j x v ℓ a Z.χ (K n).tubes)
   (hz:Z.Paid Q o x) (h:Finish J K H)(he:∀ᶠ i in (J:Filter ℕ), Mode (U i) p j v)(ht:∀ᶠ i in (J: Filter ℕ), Z.Viable (U i p))
include hz hQ he
set_option quotPrecheck false
local notation "D" => fun n y=> (Z.paints (K n) (U n y))
local notation "D'" => fun n y=> (Z.paints (H n) (U n y))
lemma absorb (i:Bond f):Frill J j p (fun n y=> (D n y).saved i) (fun n y=> (D' n y).saved i):=by
    exact glance (he.mono fun n hn=> (hQ n).buffs E F (U n) p (D n p) hn hz.1 rfl hz.2 i) -- D' redu
include h
variable {g f':ℕ→ E→ Directions G f}
include ht
lemma vision (u:Mention c f) (hc:(D 0 p).selected u.1 (spot S u.2)): Frill J j p
    (fun n y=> Scroll.freely (K n).tubes Z.x (pull u.1 0 (U n y)) (Oriented.choice u.1 Z.k) u.2)
    (fun n y=> Scroll.freely (H n).tubes Z.x (pull u.1 0 (U n y)) (Oriented.choice u.1 Z.k) u.2):=by
   have hu: Quincy J j p (fun n y=> pull u.1 0 (U n y)) (fun n y=> pull u.1 0 (U n y)):= (scaleG he).turn u.1; let k:=Pressure.Stores.till Z.x
   let V(n:ℕ)(y:E):= pull u.1 0 (U n y); let Y:=choice u.1 Z.k
   have hX:= h.highV hu k u.2
   simp_rw [Scroll.freely]; apply Frill.sub _ hX
   rcases u with ⟨s,i|i⟩
   · exact h.overF (hu.books S) i k
   let g(n:ℕ)(y:E):= Scroll.freely (K n).tubes Z.x (V n y) Y (.inr i)
   have hA:Frill J j p g g:=by
       refine glance (a:=1) (v:=ℓ) ?_
       filter_upwards [he,ht] with n hn hx
       have he:= safe_hull (D n p) (s:=s) (i:=.inr i) hx hc
       unfold g; rw [hz.1]; refine (hQ n).star _ (V n) p Y (.inr i) ?_ ?_; exact Blaze.turn (hn) s; change Clean (V n p) x _ _; rw [← hz.1]; exact he
   let f(n:ℕ)(y:E):= Scroll.visual (K n).tubes k (V n y) (.inr i)
   have hh:Frill J j p f f:=⟨hX.seer,hX.seer,fun i hi=>⟨_,(hX.feel i hi).choose_spec.1,(hX.feel i hi).choose_spec.1⟩⟩
   refine (hA.add hh).alter (Eventually.of_forall fun i=>Eventually.of_forall fun y=> sub_add_cancel ..) ?_
   exact Eventually.of_forall fun n=> Eventually.of_forall fun y=> sub_add_cancel (baseStroke (K n).tubes Z.x Y (V n y) (.inr i)) (f n y)
lemma ponds (u:Mention c f)(hc:(D 0 p).selected u.1 (spot S u.2))(hh:Frill J j p g f'): Frill J j p (fun n y=> strain (D n y) u.1 u.2 (g n y)) (fun n y=> strain (D' n y) u.1 u.2 (f' n y)):=by
   refine (vision hQ hz h he ht u hc).add (h.frameZ (scaleG he) (u:=fun n y=> (D n y).signal (g n y)) (v:=fun n y=> (D' n y).signal (f' n y)) (Frill.stocks fun i=> ?_) (Pressure.Stores.till Z.x) u.1 u.2); apply (absorb hQ hz he i).add
   by_cases hf:(D 0 p).Hot i
   · refine (hh.cross i).alter (Eventually.of_forall fun n=>Eventually.of_forall fun y=> (show (D n y).lens (g n y) i=_ from if_pos hf).symm) (Eventually.of_forall fun n=> Eventually.of_forall fun y=> (show (D' n y).lens (f' n y) i=_ from if_pos hf).symm)
   refine (Frill.still (0:G.Color)).alter (Eventually.of_forall fun n=> Eventually.of_forall fun y=> (if_neg (show ¬(D n y).Hot i from hf)).symm) (Eventually.of_forall fun n=> Eventually.of_forall fun y=> (if_neg (show ¬(D' n y).Hot i from hf)).symm)
end Draft
end YM.ConnectedActivityE6.Lim

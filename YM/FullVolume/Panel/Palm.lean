import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Pint
import YM.MergeProof.Tuna
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {M:Leaf R}(X:Coat T F)(H:Cash W x μ L Q o C T R)
    {q A B b e a χ' v d:ℝ}{j n:ℕ}{χ:Chi}
open Itinerary Animals
open Stained March
variable {Ξ:Utopia H j v d r q χ}(he : Herd H Ξ A B n)
    (Θ:Oboe H j v B n A b Ξ) (hx:X.x=x) (hF:X.χ=χ) (hk:X.width=o.K) (ht:Healthy (Pressure.temp x) (H.unionP p) X.V)(hm: (roster p).flags=∅)
section
variable {ι:Type}[Fintype ι]{T':ι→ Lotus.Leaf R}{s:ι→ℝ}(hM: Merge.Grouped M s T')
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E][FiniteDimensional ℝ E]{U:E→ Config G c} {y:E} (h: Mode U y j v)(hs:U y=X.V)
include hM
lemma paintL (z:F.Slice G×Air f G) (I:Finset (Bond f)) (V: Config G c)(K a d:ℝ) : M.carat I X V d Ñ p K a m z=∑ j,s j * (T' j).carat I X V d Ñ p K a m z:=by
   unfold Leaf.carat Leaf.chimes Leaf.floret; simp_rw [hM.turn]; split; swap;· simp
   next =>
     unfold Leaf.paidU Leaf.fond; simp_rw [hM.turn]
     have hf(U): M.ingredient U= ∑ i, s i * (T' i).ingredient U:= ((hasSum_fintype (fun i=> s i*(T' i).ingredient U)).unique (hM.earn U)).symm
     simp_rw [hf]; rw [sum_mul,sum_mul,mul_sum]; apply sum_congr rfl; intro i _; ring
omit hM in
lemma spice {I:Type}[Fintype I] {Z:I→ℝ}{p:ι→I→ℝ}{a:ι→ℝ}(hp:∀ i, Z i=∑ j,a j*p j i): likely Z=∑ i,a i* likely (p i):=by unfold likely; simp_rw [hp]; rw [sum_comm,Finset.mul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [← mul_sum,mul_left_comm]
include Θ hx hF hk ht hm h hs
lemma pacer : ∀ᶠ z in 𝓝 y,M.picture (vary X (U z)) p W o.a Q.table Q.halo= ∑ i,s i * (T' i).picture (vary X (U z)) p W o.a Q.table Q.halo:=by
   let V(b : Leaf R) z:= b.grove (vary X (U z)) p W o.a Q.table Q.halo
   have hh : ∀ᶠ z in 𝓝 y,V M z=∑ i,s i* V (T' i) z:=by
      unfold V Leaf.grove; simp_rw [show ∀ z:E,(vary X (U z)).B=radiusB x from fun z=> congr_arg radiusB hx]; split_ifs
      swap; · simp
      let K i:=(planted X p).taggedL i; let T₀:= H.unionP p; let I':= edgesM S T₀ (radiusB x); let I:=podium S G T₀ (radiusB x)
      let f (M:Lotus.Leaf R)(i:S.Choices)(z:E):= M.cinema ((preps (vary X (U z)) (roster p)).taggedL i) p W o.a Q.table Q.halo I
      have hf i: ∀ᶠ z in 𝓝 y,f M i z=∑ j,s j*f (T' j) i z:=by
         let Z:= K i; have hv:Z.manifest:=planted_valid X p; have hz:X.B=radiusB x:=congr_arg radiusB hx
         let m:=(F.order G).prod Z.dice; have H': Cash W Z.x μ L Q o C T R:= (show x=Z.x from hx.symm) ▸ H
         have hR:= H.laws.data
         have hh:= Θ.flow F Z hx hF hk hv E U y hs h
         have hℓ:8*o.a*Pressure.fiery G Z.x S.patch.L≤A/2:=by rw [show Z.x=x from hx,hR.funds.length_eq]; exact Θ.mode
         let b(M:Lotus.Leaf R)(t:E):= M.carat I' Z (U t) A Q.table p W o.a Q.halo
         have hC (M:Leaf R): ∀ᶠ z in 𝓝 y,f M i z= (∫ t, b M z t ∂m) ∧ Integrable (b M z) m:=by
             have hK : edgesM S (H'.unionP p) Z.B=I':=by unfold I';change edgesM S (ground _ T Q.halo X.B p) X.B= _; rw [hz]; rfl
             filter_upwards [M.chutes Z p H' hk hv hh Θ.conduit hℓ, (M.boosts Z p H' hk hv I' hh Θ.conduit hℓ).2] with z ht' hs
             refine ⟨?_,hs⟩; unfold f; rw [← M.casin X p H hx hm ht i (U z) (U z) (fun _ _ _=> rfl),show podium S G (H.unionP p) (radiusB x)=podium S G (H'.unionP p) Z.B from ?_]; rw [hK] at ht'; exact ht'
             change _=podium S G (ground _ T Q.halo X.B p) X.B; rw [hz];rfl
         filter_upwards [hC M, eventually_all.mpr (fun j=> hC (T' j))] with z hz hi
         rw [hz.1];simp_rw [fun j=> (hi j).1]; rw [show b M z= (fun t=>∑ j,s j * b (T' j) z t) from funext fun z=> paintL Z hM z I' _ W _ A, integral_finsetSum _ (fun i _=> ((hi i).2).const_mul (s i))]; simp_rw [integral_const_mul]
      filter_upwards [eventually_all.mpr hf] with t ht; exact spice ht
   filter_upwards [hh,M.arc X p H Θ hx hk hF hm ht h hs,eventually_all.mpr (fun i=> (T' i).arc X p H Θ hx hk hF hm ht h hs)] with z hz h' hs'
   rw [h']; simp_rw [hs']; exact hz
end
end YM.PhysicalNext.Repeat.Daisy

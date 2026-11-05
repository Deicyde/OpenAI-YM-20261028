import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Levan
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Par
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Luminesce

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Leaf
variable (M : Leaf R) (X : Coat T F) (k:Finset ℕ)
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Shield Eider  Hues Rotation
open Packets Art Silica Poll Pond
variable {X':Coat T F} {H: Support c} {I : Finset (Tubular f G)} {Z : Support c} {k k' : Finset ℕ} {l : ℕ}
    {u v : Air f G} (p:Molecule S)
-- common stencil and Hood.Flops
abbrev floret (W a : ℝ) (Ñ : ChartRatio G) (l : Finset ℕ) (n: ℕ) (w : Air f G) := if M.turn.badge S∈p then
    M.paidU X a (worldZ X R.beta w)* Polar.floating X a R W Ñ w l n (p.erase (M.turn.badge S)) else 0
lemma census (hX : Intake P T X.x R) (hp:Room P S T X.x) (hl:500≤l) (ht:Borough X X' Z u v k k' R) (he:ground R T l X.B p⊆ Z): M.floret X p W a Ñ k l u=M.floret X' p W a Ñ k' l v:=by
  unfold floret; split
  next ha=>
    have hh := ht.rooms hp R.beta
    let i:= M.turn.badge S; have hG : ground R T l X.B {i}⊆ Z:=by unfold ground; rw [singleton_biUnion]; exact (subset_biUnion_of_mem _ ha).trans he
    have hc:= M.concur X k X' (W:=W) (a:=a) (Ñ:=Ñ) hh hp hl hG hX
    unfold premium at hc; rw [if_pos (show i∈({i}:Finset _) from Finset.mem_singleton_self _), if_pos (show i∈({i}:Finset _) from Finset.mem_singleton_self _), X.oldysis hX.positive,X'.oldysis hX.positive] at hc
    have hI : M.paidU X a (worldZ X R.beta u)=M.paidU X' a (worldZ X' R.beta v):=by simpa only [i,erase_singleton,Coat.term, prod_empty,mul_one] using hc
    rw [hI]; exact congr_arg _ (ht.flops hp hl hX _ W Ñ ((show ground R T l X.B (p.erase (M.turn.badge S))⊆ ground R T l X.B p from Finset.biUnion_subset.mpr (fun i hi=>subset_biUnion_of_mem _ (mem_of_mem_erase hi))).trans he))
  rfl

lemma drift_b {A : Type*} [MeasurableSpace A] (Y : A→ F.Slice G) (V : A→ Config G c) (w : A→ Air f G) (hg:ShellAccess S G X.x W X.width C) (ht:Intake P T X.x R)(he:LocalRatio Ñ)(hV:Measurable V)(hY:Measurable Y)(h:Measurable w): Measurable fun t=> M.floret (Art.drive X (V t) (Y t)) p W a Ñ k l (w t):=by
  unfold floret; split_ifs
  swap; · exact measurable_const
  let r t:=drive X (V t) (Y t); let b t:=worldZ (r t) R.beta (w t)
  have hp:Measurable b:=(compassBro ht.ready hV X hY hg R.beta).2.2 _ h
  exact ((M.borel.comp (Art.entering _ hV hY hp)).mul ((X.enforce_b (2*a) (X.plaza (areas R T 0 X.B (M.turn.badge S)))).comp hp)).mul (Shield.collectionB X hg ht he hV hY h ..)

def cinema (W a:ℝ) (Ñ:ChartRatio G) (l:ℕ) (I : Finset (Tubular f G)):=
    ∫ Y, (∫ z, Shield.lens₀ (Pond.circuit I X.relating) z * M.floret (X.wrapY Y) p W a Ñ (own p) l (Pond.spill I z)) ∂F.order G

lemma page (h: Intake P T X.x R) (hp:ShellAccess S G X.x W X.width C)(hx:LocalRatio Ñ): Measurable fun V=> M.cinema (vary X V) p W a Ñ l I:=by
  let E':= (Config G c × F.Slice G) × Body (↥ I)
  let V (t:E'):= t.1.1; let Y (t:E'):= t.1.2
  let f' (i:E') := lens₀ (Pond.circuit I (vary X (V i)).relating) i.2* M.floret (drive X (V i) (Y i)) p W a Ñ (own p) l (Pond.spill I i.2)
  have hv : Measurable V := measurable_fst.comp measurable_fst
  have hh := c_measured X.shutter (A:=fun i=> (vary X (V i)).plate) (fun i j=> (Art.borel_plate X h.ready i j).comp hv)
  have hz : Measurable f' := (bulbB (fun i j=> hh.1 i.val j.val : Borel fun i=> Pond.circuit I (vary X (V i)).relating) measurable_snd).mul
    (M.drift_b X p Y V _ hp h hx hv (measurable_snd.comp measurable_fst) ((Pond.spill_m I).comp measurable_snd))
  exact ((hz.stronglyMeasurable.integral_prod_right' (ν:=MeasureTheory.volume)).integral_prod_right' (ν:=F.order G)).measurable
lemma synchronizeLK (h:Intake P T X.x R) (hp : ground R T l X.B p ⊆ H) (hr : Room P S T X.x) (hV : Village X X' H)(hl : 500 ≤ l):
    M.cinema X p W a Ñ l (podium S G H X.B)=M.cinema X' p W a Ñ l (podium S G H X.B):=by
  let I:=podium S G H X.B
  have he : Pond.circuit I X.relating=Pond.circuit I X'.relating := by ext i j; exact hV.same_cov hr j.val j.property i.val
  unfold cinema; rw [he]; apply integral_congr_ae; filter_upwards with q; apply integral_congr_ae; filter_upwards with y
  apply congr_arg₂ (·*·) rfl; let v:=Pond.spill I y
  exact M.census (X.wrapY q) p h hr hl (show Borough (X.wrapY q) (X'.wrapY q) H v v (own p) (own p) R from ⟨hV.wrap q q (fun _ _=> rfl),fun _ _=> rfl,fun _ _=>Iff.rfl⟩) hp

lemma selfish (U : Cash W X.x μ L Q o C T R) (hX:X.width=o.K) (hm:X.manifest)(H: Support c)(hP:Healthy (Pressure.temp X.x) (U.unionP p) X.V)(he: U.unionP p⊆ H): M.cinema X p W o.a Q.table Q.halo (podium S G H X.B)=M.tithe X (own p) W o.a Q.table Q.halo p:=by
  let B:=podium S G H X.B
  have ht : X.relating.PosDef := (U.laws.data.localP _ X rfl hX hm).sails.fullC
  have hv : (circuit B X.relating).PosDef:= ht.submatrix Subtype.val_injective
  have hh := M.tip X (own p) U hX hm p
  unfold cinema tithe; rw [integral_prod _ hh.2.1]; apply integral_congr_ae; filter_upwards with y
  let g (z : Air f G):= M.into X W o.a Q.table (own p) Q.halo p (y,z)
  have hp : Measurable g:= hh.1.meas.comp (measurable_const.prodMk measurable_id)
  let Y:= X.wrapY y; have hz z: M.floret Y p W o.a Q.table (own p) Q.halo z=g z:=by
    unfold g into premium floret; split
    next=>
      have hW:= U.laws.data.room; rw [show worldZ Y R.beta z=Y.liftA R.beta z from (shine Y hW hm _ _).symm]
      exact congr_arg (_*·) (Polar.afterborn Y o.a R W Q.table z (own p) hW hm Q.buys _ (Finset.disjoint_of_subset_left (Finset.biUnion_subset.mpr (fun i hi=> subset_biUnion_of_mem _ (mem_of_mem_erase hi))) hP)).symm
    next=> rfl
  symm; change (∫ i, g i ∂ _)=_; refine Eq.trans ((Pond.gathered (Pond.spill B) (Pond.spill_m B) (Pond.orbit ht.posSemidef B) (Pond.settled _) (f:=g) ?_ hp).trans (Shield.recommends _ hv (fun z=>g (spill B z)))) ?_
  swap; · exact integral_congr_ae (Eventually.of_forall fun z=>congr_arg (_*·) (hz _).symm)
  intro u v h
  exact M.concur Y _ _ ⟨Village.refl Y H, (Pond.observe B).1 h,fun _ _=>Iff.rfl⟩ U.laws.data.room Q.buys he U.laws.intake
end Leaf
end YM.PhysicalNext.Repeat.Lotus

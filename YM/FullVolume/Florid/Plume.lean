import YM.FullVolume.Sym.Stage
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Charm
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire.Imago
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray Daisy Lotus
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R}
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
open Lyre Jams
set_option quotPrecheck false
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
-- ONE independent leaf with arbitrary location. Pole (β optimism, E etc) remains real.
structure Mill (U:Tune H v δ) where
   pole: Leaf R
   flies : (t:sun)→Leaf (U.notes t)
   kind t:(flies t).turn=pole.turn
   reps t:(flies t).ingredient=pole.ingredient
   prices t:(flies t).weight=pole.weight
namespace Mill
variable (V:Mill U)
local notation "Λ"=> U.pole
local notation "Rv"=> V.pole
lemma crests(t:sun): (V.flies t).crest=V.pole.crest:=by
    unfold Leaf.crest;rw [V.kind]; cases V.pole.turn <;> simp only [Wing.support,←(U.seats t (U.lay t.property)).reg,←(U.seats t (U.lay t.property)).forced]
-- currency: allocated on W reserve regardless heights.X.Pay.
def dust (j:ℕ) (o:Target.Order G W) (χ:Chi)(L:Side) (x a u:ℝ) :=
   0≤u∧∀ (c f:Side)(S:StepData c f)(T:Tube G S)(F : Forest S.ratio)(X:Coat T F), X.x=x→ X.χ=χ→ S.patch.L=L→0< (2*o.a)*X.t→∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (z:Air f G) (a' β:ℝ) (y:E) (U:E→ Config G c)(f':E→ Directions G f)(w:E→Air f G), Clutch X z a' β a y j U f' w → ∀ Y M,Y ⊆ M → Brush j 1 (u*coverNumber X.B M) (fun y=> X.enforce (2*o.a) (f' y) (X.plaza Y)) y
lemma morph (j:ℕ)(o:Target.Order G W)(χ:Chi)(L:Side) (v:ℝ→ℝ)(he:Rate G L (-(1/2)) v):∃ d:ℝ→ℝ,Rate G L 0 d∧∀ᶠ x in atTop,dust j o χ L x (v x) (d x):=by obtain ⟨A,hA,hx,hV⟩:= Clutch.central G L χ j he (2*o.a); exact ⟨A,hA,hV.mono fun i h=>⟨hx i,h⟩⟩
variable (D: dust j o χ L x₀ d f')
variable (X : Coat T F)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U₀:E→ Config G c} {s:E} (hx:X.x=x₀)(he:X.width=o.K)(hv:X.χ=χ)(hm:X.manifest)(hy:U₀ s=X.V)(hU:Mode U₀ s j u)
variable (z:Air f G)
local notation "τ" => (Rv).turn.badge S
local notation "β"=> R.beta
local notation "w₀"=> radiusB x₀
local notation "I₀" => X.input (worldZ X β z)
local notation "f₀" => fun i=> steer X A (worldZ X β z) (U₀ i)
local notation "z₀" => fun i=> course X A β z (U₀ i)
local notation "Yd"=> fun i=> vary X (U₀ i)
section prices
include H in
lemma blooms {A:ℝ} {ρ:E→ Directions G f}{q:E→Air f G}{Ra:Leaf R} (h:dust j o χ L x₀ d A) (K: Clutch X z o.a β d s j U₀ ρ q) (he:X.x=x₀) (hv:X.χ=χ): Brush j Ra.weight (A*spanW T R w₀ Q.halo (Ra.turn.badge S)) (fun i=>Ra.fond (vary X (U₀ i)) o.a (ρ i) I₀) s:=by
   let M':=areas R T Q.halo X.B (Ra.turn.badge S);have hA': areas R T 0 X.B (Ra.turn.badge S) ⊆ M':= by unfold M'; simp_rw [Ra.turn.badge_area]; exact Lattice.Corona.halo_mono (by simp) (Subset.refl _)
   have hp:= h.2 c _ S T F X he hv H.laws.data.funds.length_eq (by rw [mul_assoc]; exact mul_pos zero_lt_two K.pulse) E _ _ _ _ _ _ _ K _ _ hA'
   have hh := (Brush.certified (d:=0) (x:=s) (k:=j) (le_refl 0) (Ra.ingredient I₀)|>.climb (Ra.earn _) (le_refl _)).paints hp
   rw [mul_one,zero_add] at hh; apply hh.climb le_rfl
   apply mul_le_mul_of_nonneg_left _ h.1; rw [← sparkPath]
   have hP : X.B=w₀:= by rw [Coat.B,he]
   unfold M'; rw [hP, ← sparkPath]; change (coverNumber w₀ (footprints T R _ w₀ _):ℝ) ≤ 1+ (_ + _); exact (le_add_of_nonneg_right (Nat.cast_nonneg (α:=ℝ) _)).trans (le_add_of_nonneg_left zero_le_one)
end prices
include M hx he hv hm hy hU
-- align ingredient to fixed arguments
lemma flume (l:Finset ℕ) (p:Molecule S)(hp: τ ∈ p)(t:sun):
    let s1:= V.flies t
    (fun y=> s1.floret (vary X (U₀ y)) p W o.a Q.table l Q.halo (Lyre.pulseJ (U:=U) (A:=A) (U₀:=U₀) X z y t)) =ᶠ[𝓝 s]
    fun y=> V.pole.fond (vary X (U₀ y)) o.a (steer X A (worldZ X R.beta z) (U₀ y)) I₀ *∏ i∈p.erase ((V.pole).turn.badge S), M.vertex X U₀ z l i t y:=by
    intro s1
    have h0:= U.lay t.property; let K:= M.plot t h0; let Y:=U.beams t h0; let D:=U.notes t; let z':= U.pole.flow t • z
    have hr := (K.rays F X hx he hv hm E U₀ s hy hU).2 z'|>.1
    have hf:worldZ X D.beta z'=worldZ X R.beta z:=by unfold z'; rw [← U.pitch t h0]; exact moving (U.seats t h0) ..
    let f y:= pulseJ (U:=U) (A:=A) (U₀:=U₀) X z y t
    have ht y:f y= U.pole.flow t • course X A R.beta z (U₀ y) := by unfold f pulseJ;rw [← U.pitch t h0]; exact coursing (U.seats _ h0) ..
    have hV:s1.turn.badge S=(V.pole).turn.badge S:= congr_arg (fun i=>Wing.badge i S) (V.kind t)
    filter_upwards [hr.patch] with y hy'
    unfold Leaf.floret; rw [hV,if_pos hp]; apply congr_arg₂ (·*·)
    · let T':=vary X (U₀ y); let q:=(steer X A (worldZ X D.beta z') (U₀ y));have hk : worldZ T' D.beta (f y)=q:=hr.moving y
      change s1.paidU T' o.a _= _; rw [hk]; unfold Leaf.paidU; rw [s1.canv T' _ _ _ (plastic hy' hr.pulse)] -- syntax
      have hx:areas D T 0 T'.B (s1.turn.badge S)=areas R T 0 T'.B (V.pole.turn.badge S):=by simp_rw [Wing.badge_area];rw [show s1.turn.support D= V.pole.crest from V.crests t]
      unfold Leaf.fond; rw [← show worldZ X D.beta z'=worldZ X R.beta z from hf]; -- aim
      change s1.ingredient _ * T'.enforce _ q _= _; rw [show s1.ingredient= V.pole.ingredient from V.reps t,hx]
    unfold Polar.floating; rw [hr.moving]; apply prod_congr rfl; intro j _
    let Y':=vary X (U₀ y)
    have hr': Room P S T Y'.x := hx.symm ▸ H.laws.data.room
    have hp': Intake P T Y'.x D:= hx.symm ▸ Y.laws.intake
    refine ((plastic hy' hr.pulse).reeled hr' W Q.table l Q.halo hp' j _).trans ?_
    unfold Lyre.vertex; change Polar.ember Y' o.a _ _ _ (steer X A (worldZ X D.beta z') (U₀ y)) _ (f y) l Q.halo j= _
    rw [ht y,hf]
variable {p:Signal j} {ν:ℝ}
local notation "x₀'" => M.meadow ν p
local notation "X'" p:max y:max t:max => (V.flies t).floret (vary X (U₀ y)) p W o.a Q.table (own p) Q.halo (pulseJ (U:=U) (A:=A) (U₀:=U₀) X z y (t:sun))
variable (hC:Clear Q L μ ν x₀ v p)(hR:Clarity H j A' δ ν)
include hC hR D
-- bodies at contiguous weights.
lemma plume (i:Molecule S)(hT:τ∈i)(hp:troupe T R Q.halo w₀ i)(hZ : Healthy (Pressure.temp X.x) (H.unionP i) X.V) :
    let H':= X.catastrophe (o.ξ/2) R.beta (blaze i); let f(p:sun)(y:E):= X' i y p
    Weigh j s v (H'.indicator (fun _=> (V.pole).weight *∏ k∈i.erase ((V.pole).turn.badge S), x₀' k) z) ((r+f')*(2*H.shapeW i)) (Jams.phraseS f) := by
  intro H' f
  have hy' := (M.pole.rays F X hx he hv hm E U₀ s hy hU).2 z|>.1; let K y:=V.pole.fond (vary X (U₀ y)) o.a (steer X A (worldZ X β z) (U₀ y)) I₀
  have ht' := Weigh.still (blooms (H:=H) X z D hy' hx hv (Ra:=Rv)) U.normed
  let q:= i.erase τ
  let A(k):= r*spanW T R w₀ Q.halo k; let W(u):= M.vertex X U₀ z (own i) u
  have ht(k)(hk:k∈q): Weigh j s v (x₀' k) (A k) (W k):= M.tided X hx he hv hm hy hU z hC hR _ _ (Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem H.supportP (mem_of_mem_erase hk)) hZ)
  have hA := ht'.dual (FullVolume.Ray.Weigh.prod q W (x₀') A U.normed ht)
  have hp':= M.pole.stencil.active
  have hf:r*(spanW T R w₀ Q.halo τ) ≥0:= (M.tided X hx he hv hm hy hU z hC hR (own i) τ (Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP hT) hZ)).slope
  have hD : f'* (spanW T R w₀ Q.halo τ)+ (∑ k∈q, A k) ≤ (r+f')*(2* H.shapeW i) := by
      let U k:=spanW T R w₀ Q.halo k; have hx(k)(he:k∈i):0 ≤ U k:= nonneg_of_mul_nonneg_right ((M.tided X ‹_› ‹_› ‹_› ‹_› hy hU z hC hR (own i) k (Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem H.supportP he) hZ)).slope) (zero_lt_one.trans_le hp')
      apply le_trans (add_le_add (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (zero_le_one.trans hp')) (hx τ hT)) (Finset.sum_le_sum (g:=fun k=>(r+f') * U k) (fun i hi=> mul_le_mul_of_nonneg_right (le_add_of_nonneg_right D.1) (hx i (mem_of_mem_erase hi)))))
      rw [← Finset.mul_sum,← mul_add, show spanW T R w₀ Q.halo τ + ∑ k∈q, U k=_ from Finset.add_sum_erase _ U hT]; exact mul_le_mul_of_nonneg_left (Utopia.worthy i hp) (add_nonneg (zero_le_one.trans hp') D.1)
  have hf':Weigh j s v _ ((r+f')*(2*H.shapeW i)) (Jams.phraseS f):= (hA.loses le_rfl hD).cong (by
      intro t ht; let s₁:sun:=⟨t,ht⟩
      rw [show phraseS f t=f s₁ from phrased f s₁]; exact flume M V X hx he hv hm hy hU z _ _ hT s₁)
  by_cases hg:z∈ H'; rw [Set.indicator_of_mem hg]; exact hf'
  rw [Set.indicator_of_notMem hg]; refine ⟨hf'.slope,hf'.smooth,fun y hy' n hn=> ((FullVolume.Ray.Scout.still U.normed (0:ℝ)).enlarged (by simp)).replace (fun t h => ?_)⟩
  let t':sun:=⟨t,h⟩; have he' := U.lay h; let z':=U.pole.flow t • z; let K:= M.plot t he'; let Y:=U.beams t he'; have hb:z' ∉ X.catastrophe (o.ξ/2) (U.notes t).beta (blaze i):= fun H=> hg ((bells X he' i z _).1 H)
  let l:=V.flies t'; have hz:= (K.rays F X hx he hv hm E U₀ s hy hU).2 z'|>.1
  have hH : Healthy (Pressure.temp X.x) (Y.unionP i) X.V := by rw [show Y.unionP i= _ from congr_fun (U.stage _ he').symm _]; exact hZ
  -- remove reserve (arity exactly one), no mask burn outside
  have hD : dust j o χ L x₀ d f':= D
  have hx':= acreage (f':=fun y=> steer X _ _ (U₀ y)) l X Y K.stencil ((U.troupe_hold t he' i).mp hp) (show l.turn.badge S∈i from (V.kind t').symm ▸ hT) (own i) hx he hv hm hH hU hz hD.1 ?hk
  case hk=>
    have he₀:=blooms (H:=Y) X _ hD hz hx hv (Ra:=l); rw [show X.B=w₀ from congr_arg _ hx]; exact he₀
  rw [Set.indicator_of_notMem hb] at hx'
  rw [show phraseS f t=f t' from phrased f t']; exact (norm_le_zero_iff.mp ((point_norm hx' hn (v:=y) hy').trans_eq (zero_mul _))).symm
end Mill
end YM.ConnectedActivityE6.Empire.Imago

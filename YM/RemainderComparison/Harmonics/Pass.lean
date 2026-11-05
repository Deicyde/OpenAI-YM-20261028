import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Vista
import YM.MergeProof.TeamTrees
import YM.RemainderComparison.Sleet.Density

/-!
# Folding the unmasked syntactic sector. Mark fields synchronized at their honest fine payloads.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Harmonics
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Stellar hC he K p X X') {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p
-- port lemma enough; don't require Rights equal budgets
variable (hC he)
lemma mold (T:Tube G (stepped Q h)) (T':Tube G (stepped Q H))
    (i i':Wing) (hs : i.support R=(i'.support R').image (L).high.cut) (ht:f.val>4) (l B':ℕ) : areas R T l B' (i.badge S)=(areas R' T' l B' (i'.badge Y)).image (L).low.cut:=by
  let b:= L
  rw [Wing.badge_area,Wing.badge_area, hs,show RG.inspected ((i'.support R').image (L).high.cut) = (RG.inspected (i'.support R')).image (L).high.cut from voyages (fineP h H hC) ht (i'.support R')]
  let J:= RG.inspected (i'.support R')
  have hb : (J.image (L).high.cut).image (S).ratio.parent=(J.image (Y).ratio.parent).image (L).low.cut:=by
     rw [image_image,image_image]; exact image_congr fun k _=> b.position _
  unfold enlargement; rw [hb]; exact ringed hC _ _
lemma stokes (i i':ℕ) (hs : (R.activities.reg i).support=((R'.activities.reg i').support).image (Lace.project (h:=h) (H:=H) hC he).high.cut)
    (ht:f.val>4) (hu:R.p.threshold= R'.p.threshold) (hE :∀ Ye:Config G f,Healthy R.p.threshold (R.activities.reg i).support Ye→ R'.activities.E i' ((L).high.links Ye)= R.activities.E i Ye) (Ye:Config G f): R'.activities.regularOccurrence R'.p i' ((Lace.project (h:=h) (H:=H) hC he).high.links Ye) =R.activities.regularOccurrence R.p i Ye:=by
    let l:= L
    have hp: Healthy R'.p.threshold (R'.activities.reg i').support (l.high.links Ye)↔Healthy R.p.threshold (R.activities.reg i).support Ye:=by
       rw [hu,hs]; exact vigor (fineP (by assumption) H hC) Ye ht _ _
    unfold Activities.regularOccurrence
    by_cases hq : Healthy R.p.threshold (R.activities.reg i).support Ye
    · rw [masked_eq _ _ _ _ (hp.2 hq),masked_eq _ _ _ _ hq]; exact hE _ hq
    rw [masked_ne _ _ _ _ (hp.not.mpr hq),masked_ne _ _ _ _ hq]
variable {hC he}
namespace Stellar
include A
lemma pills (i:Wing) (i':Wing)(hs : i.support R=(i'.support R').image (L).high.cut) (a:ℝ)(u:Directions G f) (n l:ℕ)(O:Site C)
    (hv:areas R' T' l B (i'.badge Y) ⊆ neighbors n O) (hk:2*(n+3)<c.val):
       X'.enforce a (Deck.light (L).high.cut u) (X'.plaza (areas R' T' 0 X'.B (i'.badge Y)))= X.enforce a u (X.plaza (areas R T 0 X.B (i.badge S))):=by
    have hh : c.val≤f.val:= h ▸ Nat.le_mul_of_pos_right _ P.L.property
    have hp:= A.old.buys
    rw [A.D.1,A.D.2,mold hC he T T' i i' hs (by omega)]
    apply A.porter _ n hk O ?_
    apply Finset.Subset.trans ?_ hv; rw [Wing.badge_area,Wing.badge_area]; exact Lattice.Corona.halo_mono (by simp) (Finset.Subset.refl _) -- ambiguity halo
lemma buysE (a:ℝ)(w:Air f G) (i i':ℕ)(hs : (R.activities.reg i).support=((R'.activities.reg i').support).image (L).high.cut)
    (hu:R.p.threshold= R'.p.threshold) (hb:R.beta=R'.beta) (hX :∀ Ya:Config G f,Healthy R.p.threshold (R.activities.reg i).support Ya→ R'.activities.E i' ((L).high.links Ya)= R.activities.E i Ya) (n:ℕ)(O:Site C) (k k':Finset ℕ) (W:ℝ)(l:ℕ)(J:ChartRatio G)
    (hv:areas R' T' l B (Opacity.key Y i')⊆ neighbors n O)(hk:2*(n+3)<c.val):
       X'.vertex R' J W a k l (blow (L) w) (Opacity.key Y i')= X.vertex R J W a k' l w (Opacity.key S i):=by
   apply congr_arg (fun v:ℝ=>Real.exp v-1)
     (show X'.inhale R' a (X'.liftA R'.beta _) (.inl i')= X.inhale R a (X.liftA R.beta w) (.inl i) from ?_)
   rw [A.rolls _ w,hb]; let v:= X.liftA R'.beta w
   have hs₁:=Stellar.pills A (Wing.logKey i) (Wing.logKey i') (R:=R) (R':=R') hs (2*a) v n l O hv hk
   refine congr_arg₂ (·*·) ((show -(_ : ℝ)= -_ from neg_inj.mpr ?_)) hs₁ -- infer missing inputs, alternative
   change R'.activities.regularOccurrence R'.p i' (X'.input (Deck.light (L).high.cut v))= _
   have hh:c.val≤f.val:= h ▸ Nat.le_mul_of_pos_right _ P.L.property
   rw [(A.glassU v).2.2]; exact stokes hC he _ _ hs (by omega) hu hX _
lemma buysM (a:ℝ)(w:Air f G)(Mv:Leaf R)(M':Leaf R')(hs:Mv.crest=M'.crest.image (L).high.cut)(hb : R.beta=R'.beta)
    (hX: ∀ V':Config G f,M'.ingredient ((L).high.links V')=Mv.ingredient V')(n l:ℕ)(O:Site C)
    (hv : areas R' T' l B (M'.turn.badge Y)⊆neighbors n O)(hk :2*(n+3)<c.val):
    M'.paidU X' a (X'.liftA R'.beta (blow (L) w))= Mv.paidU X a (X.liftA R.beta w):=by
   rw [A.rolls _ w,hb]; let v:= X.liftA R'.beta w
   exact congr_arg₂ (·*·) ((congr_arg M'.ingredient (A.glassU v).2.2).trans (hX _)) (pills A Mv.turn M'.turn (R:=R) (R':=R') hs (2*a) v n l O hv hk)
end Stellar
end YM.RemainderComparison.Harmonics

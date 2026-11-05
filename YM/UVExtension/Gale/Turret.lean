import YM.UVExtension.Cloud.Tail
import YM.UVExtension.Rafter.Pebble
import YM.UVExtension.Rafter.Late
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Gale
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard Metric Lamppost Motion Work.G08
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Push Push.AbsoluteSums Rafter Local Attach
variable {G:Gauge}{E Y:Type}{n:Side}{B:BudgetPoint}{F:Config G n→ℂ}
private def glaze (A : Activities G n) : Activities G n := { A with
  forced := fun i => {A.forced i with extraTest:=fun _ => True} }
def plate (R : Rep G n) : Rep G n := {R with activities:=glaze R.activities}
variable (X:Support n)(R:Rep G n)(H: Shelf (plate R).activities) (q:ℕ)
local notation "W"=> Pack R.activities X
local notation "A"=> R.activities
private lemma variant (X:Support n) (s: Finset ℕ): Packs R.activities X s ↔ (s.Nonempty ∧ coherent (plate R) s ∧ ∀ i∈s, ¬ Disjoint (Attach.X (plate R) i) X):=by constructor; rintro ⟨h,hp,hA⟩; exact ⟨h,hp,fun i hi=> (fun h=>hA i hi h.symm)⟩; rintro ⟨h,hp,hA⟩; exact ⟨h,hp,fun i hi=> (fun h=>hA i hi h.symm)⟩
private def convertC : Pack R.activities X ≃ Attach.Cluster (plate R) X:= Equiv.subtypeEquiv (Equiv.refl _) (fun i=> variant R X i)
lemma tellerBit (F:Config G n→ ℂ) (i:Box n) (U:Config G n): profile A (Attach.line (plate R) X H q F) i U=∑' s:Pack (A) X, if fusionBox R.activities X s.val=i ∧ i.1∩flags R.p.threshold U=i.2 then F U * ∏ j∈s.val,((A).K j U:ℂ) else 0 :=by
    unfold profile; rw [expand_eq]; let f(j):= if barcode A j=i then Attach.line (plate R) X H q F j U else 0
    let h:= stamp (plate R) X H q; let k:= convertC X R; have ht : (Function.support f) ⊆ range (h ∘ k):=by
       intro j hj; by_contra he; apply hj; unfold f; split; swap; · rfl
       rw [line_empty _ _ _ _ _ (by rintro ⟨s,rfl⟩; exact he ⟨k.symm s, by simp [h]⟩)];rfl
    change ∑' i,f i= _; rw [← (h.injective.comp k.injective).tsum_eq ht]; refine tsum_congr fun j=>?_ ; unfold f
    have he : barcode R.activities (h (k j))= fusionBox R.activities X j.val:= Prod.ext (stamp_x (plate R) X H q _) (stamp_i (plate R) X H q (k j))
    change (if barcode R.activities (h (k j))=i then _ else _)=_; rw [he]; split
    next hp=>
      simp_rw [hp,true_and]; dsimp only [Function.comp_apply]; rw [show Attach.line (plate R) X H q F (h (k j))= _ from line_stamp ..]; unfold chunk
      have h1:i.1 = span (plate R) X (k j) := congr_arg Prod.fst hp.symm
      have h2:i.2=debts (plate R) X (k j):=congr_arg Prod.snd hp.symm; rw [h1,h2]; rfl
    next hp=> rw [if_neg (fun hx=> hp hx.1)]

-- no volume toll
variable {w t u:ℝ} {D Z:Type} [NormedAddCommGroup Z][NormedSpace ℂ Z]{T:Opening D Z} (V:D→Rep G n)
   (hs:∀ i,(V i).activities.forced=(R).activities.forced)(hq:∀ i,(V i).p=B)
local notation "Y"=> Config G n
include hs
private def joinW (i:D): Pack (V i).activities X≃ Pack R.activities X:= Equiv.subtypeEquiv (Equiv.refl _) (fun p=>by
    suffices hp:∀ (A' B':Activities G n),A'.forced=B'.forced→ (Packs A' X p↔Packs B' X p) from hp _ _ (hs i)
    rintro ⟨a,b,c,d⟩ ⟨e,f,h,t⟩ hb; change b=f at hb; subst b; exact ⟨fun ⟨h1,h2,h3⟩=> ⟨h1,h2,h3⟩,fun ⟨h1,h2,h3⟩=> ⟨h1,h2,h3⟩⟩)
include hs hq
lemma telly (H':∀ i,Shelf (plate (V i)).activities) (F:Config G n→ℂ)(x:D)(i:Box n) (U:Config G n): profile (V x).activities (Attach.line (plate (V x)) X (H' x) q F) i U=∑' s:Pack A X, if fusionBox A X s.val=i ∧ i.1∩flags B.threshold U=i.2 then F U * ∏ j∈s.val,(((V x).activities.K j U):ℂ) else 0:=by
    rw [tellerBit,← (joinW X R V hs x).tsum_eq]; refine tsum_congr fun j=>?_ ; have he(s:Finset ℕ): fusionBox (V x).activities X s=fusionBox R.activities X s:=by unfold fusionBox Local.patch flagsFor; simp_rw [hs]
    change _ = if fusionBox R.activities X _=_ ∧ _ then _ else _; rw [he,hq]; rfl
include hs hq
lemma attachment (H':∀ i,Shelf (plate (V i)).activities)(f:Config G n→ℂ)(ht:∀ U,‖f U‖ ≤ t)(hP:Stalk (Concert.bell (A).forced B.B B.supportExponent) T (fun i j U=> ↑((V i).activities.K j U)) w)(hw:0≤w): Stalk (boxGoal G n B) T (fun i=> profile (V i).activities (Attach.line (plate (V i)) X (H' i) q f)) (mergePrice B w X t):=by
   have ht': 0≤ t:= (norm_nonneg _).trans (ht 1); let q':= mergePrice B w X t; have hQ:= mergePrice_nonneg B X hw ht'; let e(i:Pack A X):=fusionBox A X i.val; let y(i:Box n):= Real.exp (B.supportExponent* coverNumber B.B i.1); have hy i :1≤y i:= Real.one_le_exp (mul_nonneg B.exponent_pos.le (Nat.cast_nonneg _)); let L:= Rafter.shelf (Config G n) (y∘e) (fun x=>zero_lt_one.trans_le (hy (e x)))
   obtain ⟨p,hp,hF,h⟩:= hP.rises; let g(z:Z) (i:Pack (A) X) (U:Config G n) := if (e i).1∩flags B.threshold U=(e i).2 then f U * ∏ j∈i.val,p z j U else 0
   have hg: Stalk L T (g ∘ T.call) q':=by
       refine ⟨g,fun i U=> ?_,fun _=>rfl,fun z hz=>?_⟩
       · unfold g; split; · exact fun s F hs hh he=>DifferentiableOn.const_mul (DifferentiableOn.fun_finsetProd (fun i _=> hp i U s F hs hh he)) _
         exact bumps _ _ (differentiableOn_const _)
       obtain ⟨v,hv,hV⟩:= (h z hz).afloat; have hv'(i):0≤v i:= hv i|>.1; let c(i:Pack R.activities X):= t * ∏ j∈i.val,v j; have hc i:0≤ c i:=mul_nonneg ht' (Finset.prod_nonneg fun j _=>hv' _)
       have hW i: SumBudget (fun j=> if i∈Local.patch R.activities j then B.mass (Local.patch R.activities j) (v j) else 0) w:=by simpa only [Concert.bell,BudgetPoint.mass,ite_mul,zero_mul,Local.patch] using! hV i
       refine ⟨c,fun i=>⟨hc i,fun U=>?_⟩,fun _=> packBudget X («A»:=A) (B:=B) ht' hv' hW⟩
       unfold g; split; swap; · rw [norm_zero]; exact hc _
       rw [norm_mul,norm_prod]; exact mul_le_mul (ht _) (Finset.prod_le_prod (fun _ _=>norm_nonneg _) fun i _=> (hv _).2 U) (Finset.prod_nonneg fun _ _=> norm_nonneg _) ht'
   have hz: (fun d=>profile (V d).activities (Attach.line (plate (V d)) X (H' d) q f))=(fun d (i:Box n)(x:Config G n)=> cram e (fun a=> g (T.call d) a x) i):=by
       funext d i x; rw [expand_eq,telly X R q V hs hq]; apply tsum_congr; intro s; unfold g; rw [hF]; split_ifs with h hp ht he hx hA hB <;> first|rfl| (exfalso; unfold e at *; grind)
   exact hz.symm ▸ (show Stalk (boxGoal G n B) T (fun d (i:Box n)(x:Config G n)=> cram e (fun a=> g (T.call d) a x) i) q' from loop e y hy (g ∘ T.call) hQ hg)
-- sleeve economic input. numeric external coefficient only. identify plate.P rho. defeq through fixed B proof.
omit hs hq
private lemma donation (R V:Rep G n) (he:R.p=V.p){d:ℕ}{F:Frame G d}(u:F.Coeff)(S:SectionData F): supplement S (plate R) 0 u=supplement S (plate V) 0 u:=by
   obtain ⟨a,b,c,p,t,i⟩:=R; obtain ⟨a',b',c',p',t',i'⟩:=V; dsimp only at he; subst p; rfl
include hs hq
lemma enlist {d:ℕ}{F:Frame G d}(i0:D) (h:R=V i0)(S:SectionData F)(H:∀ i,Shelf (plate (V i)).activities)(x:F.Coeff)(C:ℝ)(hx:∀ i, ‖supplement S (plate R) 0 x i‖≤Extra.Histories.fullCost F B C * F.coeffSize (F.core x))(hw:0≤w)(k:ℝ)(he:Extra.Histories.fee F B (S.footprint (0:Site n)) C w ≤ k)(hp:Stalk (Concert.bell (V i0).activities.forced B.B B.supportExponent) T (fun i j U=> ↑((V i).activities.K j U)) w): Stalk (boxGoal G n B) T (fun i=>profile (V i).activities (Extra.Histories.born S (plate (V i)) 0 (H i) q x).forced) (k*F.coeffSize (F.core x)):=by
    let f:= S.footprint (0:Site n)
    let t:= attachment f R q V hs hq H _ hx (h ▸ hp) hw -- h.symm? rewrite
    let y:=supplement S (plate R) 0 x
    have hs': (fun i=>profile (V i).activities (born S (plate (V i)) 0 (H i) q x).forced) = (fun i=>profile (V i).activities (Attach.line (plate (V i)) f (H i) q y)):=by
        funext i; unfold y; rw [donation R (V i) (by rw [h,hq,hq])]; rfl
    exact hs'.symm ▸ t.eases (by refine le_trans ?_ (mul_le_mul_of_nonneg_right he (size_nonneg ..)); unfold Push.Local.mergePrice Extra.Histories.fee BudgetPoint.mass f; apply le_of_eq; ring)
end YM.UVExtension.Gale

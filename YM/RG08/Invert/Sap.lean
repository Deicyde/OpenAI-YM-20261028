import YM.RG08.Invert.Ring
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Locations
/-!
 # At inversion paint. Rank-zero constants not from inverted phases. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Invert
open Function Filter Lattice Wilson Exterior Precision Laurent Next.Free Next.Free.Flight RG RG.Supply Bloch Input Matrix
open Planned.PrimaryIntegral295 Carrier
open Stationary Analysis FreeResolvent Tree UVExt.Paths Reflect Push.SectorMeasure.Oriented AnalyticBridge.GaussianFieldAlignment.Locations
open scoped BigOperators Topology Real Classical Matrix ContDiff
variable {G:Gauge}{i j k t r:ℕ}{L c f:Side}{S:StepData c f}

abbrev grove (S:StepData c f) := (Repeated.axisRule S.patch.L S.patch.odd_side).forest S.ratio
lemma tinder (hp:Odd L.val)(x:Site L)(hx:x≠0): Repeated.orderStep (-x) = (Repeated.orderStep x).rotate sigma:=by
   have ht:= Repeated.candidates_ne hx; let i:= (Repeated.candidates x).min' ht
   have he: lift x i≠0:= (Finset.mem_filter.mp ((Repeated.candidates x).min'_mem ht)).2
   have H:Repeated.candidates (-x)=Repeated.candidates x:= by ext; simp [Repeated.candidates,lift_negate x hp]
   unfold Repeated.orderStep; simp_rw [H]; rw [dif_pos ht,dif_pos ht]; change (if lift (-x) i < 0 then _ else _)=Step.rotate (if lift x i< 0 then _ else _) _; rw [lift_negate x hp, Pi.neg_apply]; split_ifs <;> first|omega|rfl
lemma trunks_rev (x:Edge (Site f)): x ∈ (grove S).trunks ↔ sendEdge sigma 0 x ∈ (grove S).trunks:= by
   let A:= grove S; let B:=forest sigma 0 A
   have hv: B.trunks=A.trunks := by
      ext w; rw [Forest.trunk_mem_iff,Forest.trunk_mem_iff]; apply exists_congr; intro j
      refine and_congr_right (fun hx=>?_ )
      have he:S.ratio.residue j ≠ 0:= mt (S.ratio.root_id j).2 hx
      have hg : affine sigma (S.ratio.embed 0) j= -j:= by rw [show S.ratio.embed 0=0 from map_zero S.ratio.root,affine,sig_act,add_zero]
      have hh : S.ratio.residue (-j)= -S.ratio.residue j:= by
         obtain ⟨z,rfl⟩: ∃ z,wrap f z=j := ⟨lift j,wrap_lift _⟩
         rw [← map_neg,Streets.residue,Streets.residue,map_neg]
      have hp:B.up j=A.up j:= by
         change ((grove S).up (affine _ (S.ratio.embed _) j)).rotate _= _
         rw [hg]; change (Repeated.orderStep (L:=S.ratio.count) (S.ratio.residue (-j))).rotate _=Repeated.orderStep (L:=S.ratio.count) _; rw [hh,tinder (L:=S.ratio.count) S.patch.odd_side _ he,Step.rotate_mul]; simp
      rw [hp]
   rw [← hv]; -- RHS also. rewrite right only
   rw [show sendEdge sigma 0 x ∈ B.trunks ↔ sendEdge sigma 0 x ∈ (grove S).trunks from ?_]; · simpa only [show S.ratio.embed 0=0 from map_zero S.ratio.root] using trunk_map sigma 0 A x
   rw [hv]
def barrel (S:StepData c f): Equiv.Perm (grove S).Free := Equiv.subtypeEquiv (StepData.sendBonds sigma (0:Site f)) (fun i=> not_congr (trunks_rev i))
abbrev walnut (G:Gauge)(S:StepData c f): Equiv.Perm (Active G (grove S)):= Equiv.prodCongr (barrel S) (Equiv.refl G.ColorIndex)
lemma barrel_pin (x:Active G (grove S)): plant (grove S) (walnut G S x)=toneP G f 1 (plant (grove S) x):= by
   obtain ⟨⟨⟨x,i⟩,hx⟩,y⟩:=x; simp only [plant,tone_on,mate_one]
   congr -- defeq
   change -x+0-step i= _; rw [add_zero]
lemma forestOn (S:StepData c f):HeatV (toneP G f 1) (walnut G S) (sprig S (grove S) G):= by
   constructor; intro x y; change (if plant (grove S) y=x then _ else _)=(if plant (grove S) (walnut G S y)=toneP G f 1 x then _ else _); rw [barrel_pin]; simp only [(toneP G f 1).injective.eq_iff]
lemma treeOn (h: S.patch.Branches S.kernel G) (p:G.ColorIndex) (X:Train S.patch.J) :
    let K:= pink S.kernel.penalty X; let T:= grove S; let F:= walnut G S; let U:= toneP G f 1
    HeatV U U (FreeResolvent.fullMatrix G S K) ∧ HeatV F F (treeMatrix G S T K) ∧ HeatV U U (FreeResolvent.covariance G S T K) := by
    intro K' T F U
    have he: HeatV U U (patron G (Precision.K (K'.acts f))) := by rw [tensor_same]; exact pigmentT (shadow_v X S.kernel.penalty S.kernel.penalty_pos S.patch.order_cut)
    have ht: HeatV U U (fullMatrix G S K'):= by
       unfold fullMatrix baseMatrix; rw [← tensor_same,patron_add,patron_scale,patron_mul,patron_star]; let w:=tone_probe h p; exact he.plus ((w.flipped.chain w).pay _)
    have hv: HeatV U F (sprig S T G):= forestOn S
    have hs: HeatV F F (treeMatrix G S T K'):= by unfold treeMatrix; rw [← insertion.compress]; exact (hv.flipped.chain ht).chain hv
    refine ⟨ht,hs,?_⟩; unfold covariance treeInverse resolve; rw [zero_smul,add_zero]; exact (hv.chain hs.refund).chain hv.flipped
lemma flow_tree (h:S.patch.Branches S.kernel G)(p:G.ColorIndex)(X:Train S.patch.J)(V: Row (TypeFace 2) (TypeFace 2)){A: Matrix (Body 1 f) (Body 1 c) ℝ}(he: Inputs S A ((pink S.kernel.penalty X).acts f) (V.acts c)): HeatV (toneP G f 1) (toneP G c 1) (riseM S G (grove S) A):= by
    unfold riseM; rw [← linear_mean S _ _ he]; swap; · exact (forest_precision G S.kernel X c f S.sizes h (grove S)).isUnit
    exact (((treeOn h p X).2.2).chain (tone_probe h p|>.flipped)).pay _
-- factor Holds extension to Steps
lemma prediction_spin (x:Chain)(h:x.Wake G)(q:G.ColorIndex) (m k:ℕ)(hp:m<k)(hx:f.val=c.val*(x.S.block m).val): let g:= (x.pair m c f hx).ratio
    HeatV (toneP G f 1) (toneP G c 1) (installed g (Chain.predict G x k m)):= by intro g; rw [show installed g _=_ from Chain.predict_truth G h k m hp c f hx]; exact flow_tree (S:=x.pair m c f hx) (h _) q (x.history k (m+1)) (x.metric k m) (x.canonical _ _ hp hx)
end YM.RG08.Invert

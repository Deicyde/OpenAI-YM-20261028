import YM.MultipleContact.Pair.Request
import YM.MultipleContact.Total

/-! Unconditional activation of exact-order extension estimates on the pair. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.MultipleContact.Two
open Function Set Filter MeasureTheory Metric Table Power Direct Extraction Spec
open scoped Topology BigOperators ContDiff Filter Classical
variable {G:Gauge}{C:Family G}{L:Register G}{T:Table L}{S:Table C.book}{F:Order}{P:DiffPlan S} {n k:ℕ}
variable (H:Data C F S P)(A B:S.Tag)

/-- The kernel reads the product with the other positions relative to the designated center. -/
def measurePair (t:Target C.book) (y:E4):ℂ:=kernelPair A B t.1 t.2 y (relative t.2)

private lemma visit_path {W:Type*}[TopologicalSpace W]{E:Type*}[TopologicalSpace E]{z:W}{g:E4→E}{y:E4}{f:E4× W× E→ℂ}(hf:ContinuousAt f ((0:E4),z,g y))(he:ContinuousAt g y):ContinuousAt (fun a:E4×W=>f (0,a.2,g a.1)) (y,z):=by
   exact hf.comp_of_eq (continuousAt_const.prodMk (continuousAt_snd.prodMk (he.comp continuousAt_fst)) : ContinuousAt (fun a:E4 × W=> ((0:E4),a.2,g a.1)) (y,z)) rfl

lemma eval_continuous {S:Table L}(H:S.Smooth)(q:Fin n→L.Token){k:ℕ}{y:E4}{z:Points n}{g:E4 → S.Field k}(he:ContinuousAt g y)(hz:Safe 0 z):ContinuousAt (fun a:E4× Points n=> siteValue S q k (g a.1) 0 a.2) (y,z) := by
   let f(p:E4 × Points n × S.Field k):=siteValue S q k p.2.2 p.1 p.2.1
   have hf:=site_continuous H q k 0 z hz (g y)
   have h : ContinuousAt (fun a:E4×Points n=>f (0,a.2,g a.1)) (y,z) := visit_path (z:=z) (f:=f) (y:=y) (g:=g) hf he
   exact h

include H in
lemma estimate_targets (D:∀k,Detector S k) (Q:Splitting P){ι:Type*}[Fintype ι](u:ι→Profile C.book)(Hmax:ℕ)(e:Eligible u)(hh:∀k, k ≤ Hmax→∀x:(D k).probes,⟨S,x.val⟩∈targets S u):
       ∃r:ℝ, Estimates P D (massDeg A B) Hmax r (measurePair A B) (targets S u):=by
   let U:=targets S u
   let Y:=measurePair A B
   obtain ⟨R,hr,hR⟩:=Eligible.pick e
   let r:=min 1 (R/2)
   have hR':∀y∈closedBall (0:E4) (2*r),∀i,∀z∈(u i).support,y≠0 → away y z∈conf _:=fun y hy=> hR _ ((closedBall_subset_closedBall (by unfold r; linarith only [min_le_right (1:ℝ) (R/2)])) hy)
   let W:=closedBall (0:E4) (2*r) \ ({0}:Set E4)
   let Gv := kernelPair A B S
   have hg(i)(y:E4)(hy:y∈W)(z)(hz:z∈(u i).support):ContinuousAt (fun p:E4 × Points _=>Gv (u i).e p.1 p.2) (y,z):= continuous_value S H.seed.kernel.smooth A B _ (hR' y hy.1 i z hz (fun e=> hy.2 (Set.mem_singleton_iff.mpr e)))
   have he(t:Target C.book)(ht:t∈U):∃(i:ι)(z:Points (u i).e.n)(hz:z∈(u i).support), Y t=(fun y=>Gv (u i).e y z) ∧ ∀k:ℕ,∀v:S.Field k,response t.1 k t.2 v=siteValue S (u i).e.letter k v 0 z:=by
       obtain ⟨i,z,hz,h,x⟩:=(show ∃i, (u i).covers t.2 from ht.2)
       refine ⟨i,z,hz,?_,?_⟩
       · change measurePair A B t=_
         unfold measurePair; rw [ht.1,← x,paint_self];rfl
       intro k v; rw [ht.1,← x,← site_orig S (H.seed.kernel.translations) _ _ _ H.seed.kernel.laws.toSymmetric (fun _=>le_rfl)]
       erw [paint_self]; rfl
   -- observations at core probes always among these readings
   have hcont(i) : ContinuousOn (fun p:E4 × Points _=>Gv (u i).e p.1 p.2) (W×ˢ (u i).support):= continuousOn_of_forall_continuousAt (fun p hp=>hg _ p.1 hp.1 p.2 hp.2)
   have hcG(k:ℕ)(hk:k≤Hmax)(y)(hy:y∈W) : ContinuousAt (pull k (D k) Gv) y:=by
       apply (D k).decode.continuous_of_finiteDimensional.continuousAt.comp_of_eq (continuousAt_pi.mpr fun x=>?_) rfl
       let t:Target C.book:=⟨S,x⟩; obtain ⟨i,z,hz,eq,hz'⟩:=he t (hh _ hk _)
       change ContinuousAt (Y t) y
       have hu':ContinuousAt (fun v:E4=>(v,z)) y:= (continuous_id.prodMk continuous_const).continuousAt
       have ht:= (hg i _ hy _ hz).comp_of_eq hu' (by rfl)
       exact (congr_arg (ContinuousAt · y) eq.symm).mp ht
   have hcontMiss (k:ℕ)(hk:k≤Hmax)(i):ContinuousOn (fun p:E4×Points (u i).e.n=>missAt k (D k) Gv (u i).e p.2 p.1) (W×ˢ (u i).support):=by
       refine continuousOn_of_forall_continuousAt (fun p hp=>(hg i p.1 hp.1 _ hp.2).sub ?_)
       exact eval_continuous H.seed.kernel.smooth (u i).e.letter (hcG k hk p.1 hp.1) (e.room i p.2 hp.2)
   -- hh maps all active probes. Responses bound on relative catalogs.
   refine ⟨r,lt_min zero_lt_one (half_pos hr),min_le_left ..,H.seed.kernel.laws.toSymmetric,H.inclusion,(fun t ht=>filtered t (ht.1.symm ▸ H.seed.kernel.laws.toSymmetric) (by rw [ht.1]; exact fun _=>le_rfl) (ht.1.symm ▸ H.inclusion)),hh,?_,?_,?_⟩
   · intro k hk
     choose b hb hw using fun i=>site_bound H.seed.kernel.smooth (u i).e.letter k _ (e.compact i) (e.room i)
     obtain ⟨c₀,Hc⟩:=Finite.bddAbove_range b
     refine ⟨max 1 c₀,lt_of_lt_of_le zero_lt_one (le_max_left ..),fun t ht v=>?_⟩
     obtain ⟨i,z,hz,h₁,h₂⟩:=he t ht; rw [h₂ k _]; exact (hw _ z hz _).trans (mul_le_mul_of_nonneg_right ((Hc (Set.mem_range_self _)).trans (le_max_right ..)) (norm_nonneg _))
   · intro ε hz
     obtain ⟨c₁,hp⟩:=quota e (lt_min zero_lt_one (half_pos hr)) hR' (pair_price H A B ε hz) hcont
     exact ⟨c₁,fun t ht=>by obtain ⟨i,z,hz,h₁,h₂⟩:=he t ht;  rw [show measurePair A B t=_ from h₁]; exact hp _ _ hz⟩ -- `` invalid
   intro k hk
   -- center miss corresponds
   obtain ⟨a,ha⟩:=quota e (lt_min zero_lt_one (half_pos hr)) hR' (center_miss H A B k Q D) (hcontMiss k hk)
   refine ⟨a,gain,gain_pos,fun t ht=>?_⟩
   obtain ⟨i,z,hz,h₁,h₂⟩:=he t ht
   have ex(y):readField D (measurePair A B) k y = pull k (D k) Gv y:=rfl
   have ht : miss D k (measurePair A B) t = (fun y=>missAt k (D k) Gv (u i).e z y):=by
      funext y
      change Y t y-response t.1 k t.2 (readField D _ k y) = _
      rw [h₁,h₂,ex]; rfl
   rw [ht]; exact ha _ _ hz

include H in
lemma estimate_batch (D:∀k,Detector S k)(Q:Splitting P) {ι:Type*}[Fintype ι](u:ι→Profile C.book)(Hmax:ℕ)(e:Eligible u):∃r:ℝ, Estimates P D (massDeg A B) Hmax r (measurePair A B) (targets S (includeIndexes D Hmax u)):=by
   let U:= includeIndexes D Hmax u
   exact estimate_targets H A B D Q U Hmax (eligible_total D Hmax e) (fun _=>active_total D Hmax)
end YM.MultipleContact.Two

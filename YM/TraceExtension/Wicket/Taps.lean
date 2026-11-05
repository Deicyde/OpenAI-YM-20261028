import YM.TraceExtension.Wicket.Lotus
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Wicket
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels
open Cask Outer.Nodes
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}(R:Rep G n){U:Config G n} {x:ℝ}{P:Support n}{e:Lines G n 1}
-- compare.Core.Thick.
lemma velvet_exp (f:Badge n→ Mellow G n)(H:Mellow G n)(U:Config G n)(v:G.Color)(S:Vest n): ∑ i∈ S.powerset,velvet R.p f H i U v= H U v* Real.exp (∑ j∈ S,f j U v):=by unfold velvet; rw [← mul_sum, ← prod_one_add]; apply congr_arg (H U v*·); rw[Real.exp_sum]; apply prod_congr rfl; intro i hi; ring
abbrev closeT(R:Rep G n)(x:ℝ)(e:Lines G n 1)(L:Vest n)(m:ℕ):= flavor R (stageZ R m L) (rim x) (beaconR e)
abbrev tempQ(x:ℝ):Support n:=tower (high x+1)
def twigZ (R:Rep G n)(Y:Gal G n)(F:Peat G n)(s:ℝ)(e:Lines G n 1):Vest n→Mellow G n:= velvet R.p (zest R (beaconR e) s) (rasp (beaconR e) Y F s)
variable {v:Gal G n}
lemma tubers (Q:Finset GreenA)(L' D:Finset ℕ)(m r:ℕ)(s K:ℝ)(hx: e.1∈ Bay n x)(hP:Clouded v (Bay n x)){σ A Λ δ w:ℝ}(hp:R.Lawful σ A Λ δ w)(hz:WilsonStartup.Decent R.clip R.p)(hB:2 ≤ R.p.B)(hK:64*K≤ R.p.threshold)(hV:∀ u:G.Color, ‖u‖≤1→G.chord (G.lieExp (s • u))≤K)(hD : StemCut R m (rim x))(he:ringsZ R (beaconR e) m r)(hr: Bay n x ⊆ tower r)(hr': tempQ x (n:=n)⊆tower r)(hU:Healthy (R.p.threshold/16) (tower r) U)
   (ht: ∀ j∈(closeT R x e (shelves n Q L' D) m).powerset, Cohort R.p (brick (tempQ x) (boothC R) j) (beaconR e) (twigZ R v (ochre R x Q L') s e j)) :
   let L:=shelves n Q L' D; let F:=ochre R x Q L'; let o:=beaconR e; let H:=closeT R x e L m
   lute R e s v (cabinet R m L) U = (∫ w:G.El,(orbC v F U o (tuna e w) s-clamor o v (tuna e w) U) ∂G.probHaar) +∑ i∈ H.powerset.erase ∅, warp (twigZ R v F s e i) e U :=by
   intro L F o H; let A:= cabinet R m L
   let W(i:Vest n)(w:G.El):= twigZ R v F s e i U (tuna e w); let V(w:G.El):= clamor o v (tuna e w) U; let B:= H.powerset; let Z:=B.erase ∅; have hO:o.1∈ Bay n x:= hx; have hQ := R.p.threshold_pos
   have he'(w:G.El): whisk R e s v (cabinet R m L) U w=(W ∅ w-V w)+∑ i∈ Z,W i w:=by
       let b:= tuna e w; have hb: ‖b‖≤1:=by unfold b; rw[litChrom];
       have hz':= office R o m (rim x) r (Bay n x) hO Q L' D hD K s b U hp hz hB hK (hV b hb) he (hr hO) hU
       have hy := velvet_exp R (zest R o s) (rasp o v F s) U b H; rw [←add_sum_erase _ _ (show ∅∈ H.powerset from mem_powerset.mpr (empty_subset H))] at hy
       have hl: {o.1} ⊆ tower r:= singleton_subset_iff.mpr (hr hO); have hs:Healthy (R.p.threshold/8) {o.1} U:= healthyLift _ _ _ hl (by linarith only[hQ]) hU
       change windowH R e v (Tint o b s U) w*_ - _=_; rw [show W ∅ w-V w+∑ i∈Z,W i w=(W ∅ w+∑ i∈Z,W i w)-V w from by ring]; rw [show W ∅ w+∑ i∈Z,W i w= _ from hy]; unfold windowH; rw [if_pos (Tint.focus (i:=o) (hV _ hb) hK hs),if_pos (healthyLift (R.p.threshold/4) _ _ (Finset.Subset.refl _) (by linarith only[hQ]) hs)];
       apply congr_arg₂ (· - ·) ?_ rfl; rw [show cabinet R m L (Tint o b s U)-cabinet R m L U= _ from hz',Real.exp_add]; unfold rasp orbC; rw [mul_assoc]; rfl
   have ho : (∅:Vest n)∈B:=mem_powerset.mpr (empty_subset H)
   have ht(i:Vest n)(hi:i∈B): Integrable (W i) G.probHaar:=by
       apply (ht i hi).real U
       refine healthyLift _ _ _ (union_subset hr' ?_) (by linarith only[hQ]) hU
       intro q hx; obtain ⟨j,hj,hx⟩:=mem_biUnion.mp hx; obtain ⟨hx',hm,_⟩:=(show Below R o (rim x) m H from flair R L m (rim x) o) j (mem_powerset.mp hi hj); exact he _ hx' hm hx
   have hv: Integrable V G.probHaar:= (((calls_c hP (o:=o)).comp (f:=fun i:G.El=>(U,tuna e i)) (continuous_const.prodMk (tuneH e))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
   unfold lute; simp_rw [he']; rw [integral_add (f:=fun i=> W ∅ i-V i) ((ht _ ho).sub hv) (integrable_finsetSum Z fun i hi=> ht i (mem_of_mem_erase hi)),integral_finsetSum Z fun i hi=> ht i (mem_of_mem_erase hi)]; apply congr_arg₂ _ ?_ rfl; unfold W twigZ V; simp [velvet,rasp,o]
end YM.Trace.Wicket

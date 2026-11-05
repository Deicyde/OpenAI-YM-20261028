import YM.TraceExtension.Wicket.Taps
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Wicket
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels
open Cask Outer.Nodes
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}(R:Rep G n){U:Config G n}{x:ℝ}{P:Support n}
variable {v:Gal G n}
abbrev Lip (n:Side)(G:Gauge):= Lines G n 1 × ℕ
def allotZ(P:Support n)(m:ℕ):Finset (Lip n G):=(P ×ˢ (univ:Finset (Loc G 1))) ×ˢ range m
def callX(R:Rep G n)(F:Peat G n)(v:Gal G n)(h:ℝ)(m:ℕ)(Q:Support n):Peat G n:=fun U=> ∑ i∈ allotZ Q m, wage m i.2 * lute R i.1 (loc i.2*h) v F U
def roseM(e:Lip n G)(v:Gal G n)(h:ℝ)(F:Peat G n)(m:ℕ)(U:Config G n):ℝ:= wage m e.2 * ∫ w:G.El,(orbC v F U (beaconR e.1) (tuna e.1 w) (loc e.2*h)-clamor (beaconR e.1) v (tuna e.1 w) U) ∂G.probHaar
lemma rose_s_sum (v:Gal G n)(h:ℝ)(F:Peat G n)(m:ℕ){Q Q':Support n}(hx:Clouded v Q)(he:Drift _ F)(ht:Q⊆Q') : ∀ U,tDust m v F Q' h U =∑ i∈allotZ Q m,roseM i v h F m U:=by
    intro U; unfold tDust atune allotZ; let L:=Loc G 1; let Z:= Q ×ˢ (univ:Finset (Loc G 1)); let Y:= Q' ×ˢ (univ:Finset (Loc G 1)); have hQ:Z⊆Y:= Finset.product_subset_product ht (fun _ h=>h); let T (i:Lines G n 1)(x:G.El)(s:ℝ):= orbC v F U (beaconR i) (tuna i x) s
    have hB(i: Lines G n 1)(t:ℝ) : Integrable (fun x=>T i x t) G.probHaar:=by
        refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _); let f(u:G.Color):= orbC v F U (beaconR i) u t; have hp:Continuous f:= continuous_iff_continuousAt.mpr fun i=> ((thunder he hx.wakes (fun _=>U) id (fun _=>t) i (Army.park U i) contDiffAt_id contDiffAt_const _).continuousAt); exact hp.comp (tuneH i)
    change ∑ i∈Y,(∫ w,duel m h (T i w) ∂G.probHaar)=_; rw [← sum_subset hQ]; swap
    · intro i hi h; have hz:i.1∉Q:= fun hv=> h (mem_product.mpr ⟨hv,mem_univ _⟩); simp[T,orbC,toeW v hx _ _ _ (show (beaconR i).1∉Q from hz),duel]
    conv_rhs=> rw[sum_product]
    apply sum_congr rfl; intro i hi
    unfold T; change (∫ w,duel m h _ ∂ G.probHaar) = _; simp_rw[merem]; rw [integral_finsetSum]; rotate_left
    · intro j _; refine Integrable.const_mul (c:=wage m j) ((hB i (loc j*h)).sub ?_); have ht:= hB i 0; simpa [T,orbC,science,rung] using ht
    exact sum_congr rfl (fun j _=> integral_const_mul ..)
structure ToolF (m q r:ℕ) (x h:ℝ) (R:Rep G n) : Prop where
   stem : StemCut R q (rim x)
   sharp : 4 ≤ R.p.supportExponent
   paid : 2≤ R.p.B
   decent : WilsonStartup.Decent R.clip R.p
   lent i : i∈ allotZ (G:=G) (Bay n x) m → ∃ D:ℝ,64*D≤ R.p.threshold∧∀ v:G.Color,‖v‖≤1→ G.chord (G.lieExp ((loc i.2*h) • v)) ≤ D
   array i : i∈allotZ (G:=G) (Bay n x) m → ringsZ R (beaconR i.1) q r
   tree : tempQ (n:=n) x ⊆ tower r
lemma dec_b(n:Side)(x:ℝ):Bay n x⊆ ExtS n x∧ ExtS n x ⊆ tempQ x:=⟨sprout_mono 0 (by unfold high; omega),sprout_mono 0 (by omega)⟩
abbrev Tides(n:Side)(G:Gauge):=Lip n G × Vest n
abbrev stemsM(R:Rep G n)(J:Vest n)(x:ℝ)(L q:ℕ):Finset (Tides n G):= ((allotZ (Bay n x) L).biUnion (fun i=> ({i}:Finset (Lip n G)) ×ˢ ((closeT R x i.1 J q).powerset.erase ∅)))
abbrev radarT(R:Rep G n)(v:Gal G n)(F:Peat G n)(h:ℝ) (p:Tides n G):Peat G n:= warp (twigZ R v F (loc p.1.2*h) p.1.1 p.2) p.1.1
abbrev teas(i:Tides n G)(m:ℕ):ℝ:= wage m i.1.2
lemma sting (R:Rep G n)(J:Vest n)(x:ℝ)(L q:ℕ)(i:Tides n G) : i∈ stemsM R J x L q ↔ i.1∈allotZ (Bay n x) L ∧ i.2∈ (closeT R x i.1.1 J q).powerset.erase ∅:=by
     simp only[stemsM,mem_biUnion, Finset.mem_product,mem_singleton,exists_prop]; simp
lemma partedP (R:Rep G n)(J:Vest n)(x:ℝ)(L q:ℕ)(f:Tides n G→ℝ): ∑ i∈stemsM R J x L q,f i=∑ i ∈allotZ (Bay n x) L,∑ j∈(closeT R x i.1 J q).powerset.erase ∅, f (i,j):=by
    unfold stemsM; rw[sum_biUnion]; simp_rw [sum_product]; simp; intro i hi k hk h; exact Finset.disjoint_left.mpr fun _ h1 h2=>h ((mem_singleton.mp (mem_product.mp h1).1).symm.trans (mem_singleton.mp (mem_product.mp h2).1))
lemma calls_sum (Q:Finset GreenA)(L Z:Finset ℕ)(R:Rep G n)(m k r :ℕ)(h:ℝ)(hY: Clouded v (Bay n x)){σ A Λ δ w:ℝ}(hp:R.Lawful σ A Λ δ w)(ht:ToolF m k r x h R) (hg: Drift _ (ochre R x Q L)) (hx : ∀ i∈ allotZ (G:=G) (Bay n x) m,∀ j∈ (closeT R x i.1 (shelves n Q L Z) k).powerset,Cohort R.p (brick (tempQ x) (boothC R) j) (beaconR i.1) (twigZ R v (ochre R x Q L) (loc i.2*h) i.1 j)) (he:Healthy (R.p.threshold/16) (tower r) U):
     let F:=ochre R x Q L; let J:= shelves n Q L Z; callX R (cabinet R k J) v h m (Bay n x) U=tDust m v F (ExtS n x) h U + ∑ i∈stemsM R J x m k, teas i m*radarT R v F h i U:=by
   intro F J; unfold callX; rw [rose_s_sum _ _ _ _ hY hg (dec_b ..|>.1),partedP, ← Finset.sum_add_distrib]
   apply Finset.sum_congr rfl; intro i hi; obtain ⟨D,hD,hP⟩:= ht.lent i hi; have hz:=mem_product.mp ((mem_product.mp hi).1); let W:=Bay n x
   have hQ: W⊆ tower r := (dec_b ..|>.1).trans ((dec_b ..|>.2).trans ht.tree)
   rw [tubers R Q L Z k r (loc i.2*h) D (show _ from hz.1) hY hp ht.decent ht.paid hD hP ht.stem (ht.array i hi) hQ ht.tree he (hx i hi),mul_add,mul_sum]; rfl
-- stage.Few.Power.uniform
lemma recallH (m h₁:ℕ) (h:ℝ)(ε:ℝ){H: Clouded v P}{σ A Λ δ w:ℝ}(hh:0< ε)(hp:R.Lawful σ A Λ δ w)(hv:Geo.Width R.p R.clip σ)(he:WilsonStartup.Decent R.clip R.p)(hV:4 ≤ R.p.supportExponent) :∀ᶠ T:Vest n in atTop,∀ U:Config G n, |callX R (Shepherd.field R m) v h h₁ P U-callX R (cabinet R m T) v h h₁ P U| ≤ ε:=by
    let T:= allotZ (G:=G) P h₁; let D:ℝ:=∑ i∈T,|wage h₁ i.2|; have ht:0 ≤D:=sum_nonneg fun i _=>abs_nonneg _; let ξ:= ε/(1+D); have hξ:0<ξ:=by positivity
    filter_upwards [T.eventually_all.mpr (fun i _=> closer R i.1 (loc i.2*h) v P H m ξ hξ hp hv he hV)] with J hJ U
    unfold callX; rw[← Finset.sum_sub_distrib,← Real.norm_eq_abs]; apply le_trans (norm_sum_le ..); refine le_trans ?_ (show D*ξ ≤_ from ?_)
    · unfold D; rw [Finset.sum_mul]; refine sum_le_sum fun i hi=>?_ ; rw [← mul_sub,norm_mul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hJ i hi U) (abs_nonneg _)
    exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hξ.le).trans_eq (by unfold ξ; field_simp)
end YM.Trace.Wicket

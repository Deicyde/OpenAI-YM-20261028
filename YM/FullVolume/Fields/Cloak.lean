import YM.FullVolume.Fields.Sever
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Bourse
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Sever
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Metric
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi MergeProof MergeProof.Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V:Type}[DecidableEq V][Fintype V] {B:Census V} {G:Gauge}{n:Side}
lemma smeasure (q:B.Mode): Continuous (fun x:ℂ=>Poly.send q x):= (show Continuous (fun x:ℂ=>(Poly.send q x).part) from by apply continuous_pi; intro i; simp_rw [Poly.part_send]; split<;>fun_prop)
lemma pmeas {X:Type}[MeasurableSpace X](f:X→ Poly B)(hp:∀ i,Measurable (fun x=> (f x).part i)): Measurable f:=by
     rw [show f=(fun x=> ∑ i, Poly.send i ((f x).part i)) from funext fun i=>(Poly.studs _).symm];
     exact Finset.measurable_fun_sum _ (fun i _=> (smeasure i).measurable.comp (hp i))
variable {R: Rep G n}{σ C Λ c u:ℝ}
section
variable (F:V→ Config G n→ℂ)(g:V→ Box n→ Config G n→ℂ) {H: Support n→ Config G n→Poly B}{K:Box n→ Config G n→Poly B}
variable (hp:∀ i, Measurable (F i))(he:∀ i j,Measurable (g i j)) (hR:R.Lawful σ C Λ c u){o:V→Site n}{v:V→ℝ}
include hp he hR
lemma meas (hc:Carton o H K R.p.threshold):Measurable (restore R F g H K):=by
    let t:=R.p.threshold; let Gf U:= Mach B (fun i=> F i U)+∑ i,H i U
    let P U p:= bar R.activities B U p+Mach B (fun i=>g i p U)+K p U
    have hm (M:V→ Config G n→ℂ)(he:∀ i,Measurable (M i)):Measurable (fun U=> Mach B (fun i=> M i U)):= Finset.measurable_fun_sum _ fun i _=> (smeasure _).measurable.comp (he i)
    have hg: Measurable Gf:= (hm F hp).add (Finset.measurable_fun_sum _ fun i _=> pmeas _ (hc.exp i).1.me)
    have hz (p): Measurable (fun U=>P U p):= ((pmeas _ (granular R.activities R.p B (o:=o) hR.labels p|>.me)).add (hm _ (fun i=>he i p))).add (pmeas _ (hc.flag p|>.1.me))
    have ht (p:Finset (Box n)): MeasurableSet {U: Config G n| Pattern (flags t U) p}:=by
        let Q:=p.biUnion fun i=> i.2; by_cases h: (p:Set (Box n)).PairwiseDisjoint (fun i=> i.1); simp only [Pattern,h,true_and]; simp_rw [eq_comm]; exact flags_measurable_eq ..
        simp [Pattern,h]
    have hf:Measurable (fun U=> Accent.field (P U) (flags t U)):= Finset.measurable_fun_sum _ (fun i _=> Measurable.ite (ht i) (Finset.measurable_fun_prod _ (fun i _=> hz i)) measurable_const)
    exact (Complex.continuous_ofReal.measurable.comp (Real.continuous_exp.measurable.comp (R.exponentEnv hR).meas)).smul ((Poly.pass_cont.measurable.comp hg).mul hf)
omit hp he hR
namespace Lamps
abbrev lights (f:ℂ→ Poly B):Prop:=∀ i, Differentiable ℂ fun z:ℂ=> (f z).part i
open Poly
private lemma lamp (X:Poly B): lights fun _=> X:= fun i=> differentiable_const (X.part i) -- probably const value
lemma lam (f g:ℂ→ Poly B)(h:lights f)(hp:lights g): lights (fun i=> f i+g i):=fun i=> (h i).add (hp i)
lemma coda (f g:ℂ → Poly B)(h:lights f)(hp:lights g): lights (fun i=> f i*g i):=by
    intro i; simp_rw [part_mul]; apply Differentiable.fun_sum -- name
    intro j _; apply Differentiable.fun_sum; intro k _; split; exact (h _).mul (hp _); exact differentiable_const _
lemma cscale (f:ℂ→ℂ)(hf:Differentiable ℂ f) (g:ℂ→ Poly B)(hg:lights g): lights (fun i=> f i • g i):=by intro i; simp_rw [Poly.part_smul]; exact hf.mul (hg i)
lemma lots {ι:Type}(f:ι→ℂ→Poly B)(hp:∀ i,lights (f i))(t:Finset ι):lights (fun i=> ∑ j∈t, f j i):=by
    intro i; simp_rw [part_sum]; apply Differentiable.fun_sum; exact fun j _=> hp j i
lemma caves {ι:Type}(f:ι→ℂ→ Poly B)(hp:∀ i,lights (f i))(t:Finset ι):lights (fun i=>∏ j∈t, f j i):=by
    induction t using Finset.induction_on with
    | empty=> simpa using! lamp (1:Poly B)
    | insert i t hi ih=> simp_rw [Finset.prod_insert hi]; exact coda _ _ (hp i) ih
lemma czone {f:ℂ→ Poly B}(hp:lights f)(n:ℕ): lights fun i=>f i^n:=by induction n with | zero=>simp_rw [pow_zero]; exact lamp _ | succ n ih=>simp_rw [pow_succ]; exact coda _ _ ih hp
lemma cpass {f:ℂ→ Poly B}(hp:lights f): lights (fun i=>Poly.pass (f i)):=lots (fun j i=>(j.factorial:ℂ)⁻¹ • (f i)^j) (fun j=> cscale (fun _=>_) (differentiable_const _) _ (czone hp j)) _
lemma zoom (R: Rep G n)(U:Config G n)(H:Support n→ Config G n→ Poly B)(K:Box n→ Config G n→Poly B):lights (fun z:ℂ=> restore R F g (z • H) (z • K) U):=by
    let A:= bar R.activities B U
    let f (z:ℂ):= Mach B (fun i=>F i U)+∑ i,z • H i U; let g' (z:ℂ) p:=Accent.grid (fun i=> A i+ Mach B (fun j=>g j i U)+ z • K i U) (flags R.p.threshold U) p
    have ht: lights f:= lam _ _ (lamp _) (lots (fun i z=> z • H i U) (fun i=> cscale id differentiable_id _ (lamp _)) _)
    have hx p: lights fun z:ℂ=> g' (z:ℂ) p:=by
       unfold g' grid; split; next=> exact caves (fun i z=> A i+ Mach B (fun j=>g j i U)+ z • K i U) (fun i=> lam _ _ (lamp _) (cscale id differentiable_id _ (lamp _))) _
       next=> exact lamp _
    exact cscale (fun _=> _) (differentiable_const _) (fun z=>Poly.pass (f z)*∑ i,g' z i) (coda _ _ (cpass ht) (lots (fun i z=>g' z i) hx _))
end Lamps
-- end.Analyticity of numerator on disk via arbol norm. utilize retire support.Any integrated h.T stop.Ve
variable {x y t b:ℝ}{F g} (hx:8≤R.p.B)(hX:Drake B R.p.B o)(hg:Carton o H K R.p.threshold)(hw: Towed v id H R.p.B t b)(hy:Towed v Prod.fst K R.p.B t b)(hv: Vault v F g x y)(hE:∀ i,0<v i)
local notation "A'"=> fun z:ℂ=> restore R F g (z • H) (z • K)
variable (hc:0≤ R.beta)(hd:0≤t-2)
include hx hX hg hw hy hv hE hc hR hd
lemma radii :∃ Y:ℝ, ∀ z:ℂ,z∈ Metric.ball 0 (brisk R.p.B) → ∀ U, ‖A' z U‖≤Y:=by
    obtain ⟨c₀,hp,hf⟩:= Poly.equivalent_norm (R:=B) hE; let t':= Fintype.card V
    refine ⟨Real.exp (R.scalar+Overlay.Bands.fine t' R x y (2*b) 1 C Λ c u)*c₀,fun z hz U=>?_⟩ -- shadow c
    have hn : ‖z‖ ≤ brisk R.p.B:= (by simpa using hz : ‖z‖< _).le; exact (hf (A' z U)).trans (mul_le_mul_of_nonneg_right (hove hE (garnish R F g hx hg hw hy hE hX z hn) hR hc hv hd U) hp)
include hp he
lemma paidB (i:B.Mode): (∀ z:ℂ,z∈ Metric.ball 0 (brisk R.p.B) → Integrable (A' z) (prior G n)) ∧ DifferentiableOn ℂ (fun z:ℂ=> ∫ U,(A' z U).part i∂prior G n) (Metric.ball 0 (brisk R.p.B)):=by
    obtain ⟨Y,hY⟩:= radii hR hx hX hg hw hy hv hE hc hd -- order
    have hM z:Measurable (A' z):= Sever.meas _ _ hp he hR (lit hg z)
    let f (z:ℂ) U:= (A' z U).part i; refine ⟨fun z hz=> Integrable.of_bound ((hM z).aestronglyMeasurable) _ (Eventually.of_forall (hY z hz)),?_⟩
    have hp:= AnalyticNext.ConnectedActivity.Plotter.chapel (prior G n) f (integrable_const Y) _ (fun z=> (Poly.part_cont _).measurable.comp (hM z)) (fun U=> Lamps.zoom F g R U H K i) (fun z (hz:z∈Metric.ball 0 (brisk R.p.B)) U=> (norm_le_pi_norm (A' z U).part i).trans (hY z hz U))
    exact hp.2.1
end
end YM.FullVolume.Sever
#print axioms YM.FullVolume.Sever.paidB

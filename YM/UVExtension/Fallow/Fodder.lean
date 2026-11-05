import YM.UVExtension.Fallow.Fantail
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Fallow
open Finset Filter Function MeasureTheory Set Lattice Wilson RG Cells Extraction Push GridApprox Hearth Metric
open Lease Dash Bid MergeProof RelayDifference Opening Local Next.Foundations Source
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}(hG:G.Simple)(H:Vintage.YM.Family.Makes C)(B:Stock.Tabs C.path.levels) {d N p:ℕ}
open Extra.Histories Motion Next.Extract Harvest

include H
variable (K:Extraction.Wcmain C)
include K
lemma sustained (z:Shot C.book)(u:C.label d)(ht:suitable C.S p z.f) : Spar fun i:ℕ=> z.scan d i p u:=by
   let A:= tsupport z.f; let f i:= plant (z.left i) p; let v:= angle z (thor (fun _=>u) p); have hv i: Crude C (v i):=by
      by_cases h:i=z.i; · subst i; unfold v angle; rw [Function.update_self]; exact thorC H K p (Spar.rating u)
      unfold v angle; rw [Function.update_of_ne h]; exact thorC H K p (Spar.rating _)
   obtain ⟨r,hr,hR⟩:= stalk H v A z.f.hasCompactSupport (readable _ _ _ ht) hv; obtain ⟨c,hc,hL⟩:= Order.testSup z.f
   refine ⟨(Extraction.length C.S p)^(4*z.n)*(c*r),?_⟩; filter_upwards [hR] with i hi
   rw [← show smear z (thor (d:=d) (fun _=>u) p) i=_ from scanning ..]; apply Work.D03.period_cost
   intro x; rcases eq_or_ne (z.f (Order.cells C i p x)) 0 with h|h
   · rw [h,zero_mul,norm_zero]; exact mul_nonneg hc hr
   have ht:=hi (lift ∘ x) (show tag (C.S.a i) (lift ∘ x)∈A from subset_closure h); unfold Fallow.patch at ht; rw [wrapR] at ht; rw [norm_mul]; exact mul_le_mul (hL _) ht (norm_nonneg _) hc
omit H K
lemma subsequence {A:Type*}[NormedAddCommGroup A][ProperSpace A]{x:ℕ→A}(h:Spar x) : ∃ (f:Extraction.Sequence)(z:A), Tendsto (fun i=> x (f i)) atTop (𝓝 z):=by
    obtain ⟨r,hR⟩:=h
    let F (i:Unit)(j:ℕ):= x j; obtain ⟨t,K,hK⟩:= Extraction.simultaneous F (K:=fun _=> Metric.closedBall (0:A) r) (fun _=> isCompact_closedBall ..) (fun i=>hR.mono fun j hj=>by rw [Metric.mem_closedBall,dist_zero_right]; exact hj)
    exact ⟨t,K (), (hK ()).2⟩
lemma near_null {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (p q : V →L[ℂ] V) (hq : ∀ v, q (q v) = q v) (H : ‖p - q‖ < 1) :
    Module.finrank ℂ (LinearMap.ker p.toLinearMap) ≤ Module.finrank ℂ (LinearMap.ker q.toLinearMap) := by
  let s := LinearMap.ker p.toLinearMap
  let t := LinearMap.ker q.toLinearMap
  let W : s →ₗ[ℂ] V := (LinearMap.id-q.toLinearMap).comp s.subtype
  let B : s →ₗ[ℂ] t := W.codRestrict _ fun v => by
    apply LinearMap.mem_ker.mpr; change q ((v:V)-q v)=0; rw [map_sub,hq,sub_self]
  have ht v : B v = 0 → v = 0 := fun h => by
    have hp : (v:V)-q v=0 := congr_arg Subtype.val h
    apply Subtype.ext; change (v:V)=0
    by_contra hc
    have hh : p v = 0 := LinearMap.mem_ker.mp v.property
    have hw := (p-q).le_opNorm (v:V); rw [sub_apply,hh,← sub_eq_zero.mp hp,zero_sub,norm_neg] at hw
    have hl := mul_lt_mul_of_pos_right H (norm_pos_iff.mpr hc); rw [one_mul] at hl; exact hl.not_ge hw
  apply LinearMap.finrank_le_finrank_of_injective (f := B)
  intro x y hxy; exact sub_eq_zero.mp (ht (x-y) (by rw [map_sub,hxy,sub_self]))
lemma rank_home {T : Cuts C d}(Y:Yards C d p T){X: ℕ→ℕ} {Q:CoordMap C d}(h: Tendsto (fun n=> T (X n)) atTop (𝓝 Q)) : Module.finrank ℂ (LinearMap.ker Q.toLinearMap)=Harvest.charge G d:=by
    obtain ⟨i,hi⟩:=(Metric.tendsto_nhds.mp h 1 one_pos).exists; have hv:= projected_limit _ _ (fun i=> Y.changes (X i)) h; rw [dist_eq_norm] at hi
    exact (le_antisymm (near_null Q (T (X i)) (Y.changes (X i)) (by rw [norm_sub_rev]; exact hi)) (near_null _ _ hv hi)).trans (Y.slots _)
lemma cover_maps {V:Type*} {J:Type*}[Fintype J][NormedAddCommGroup V][NormedSpace ℂ V][FiniteDimensional ℂ V](A:ℕ→J→ V →L[ℂ] ℂ) (h:∀ j x, Spar fun i :ℕ=> A i j x) : ∃ g : Extraction.Sequence, ∃ Z:J→ V →L[ℂ] ℂ, ∀ j,Tendsto (fun i=> A (g i) j) atTop (𝓝 (Z j)):=by
    let B:=Module.finBasis ℂ V; let f (j': J× Fin (Module.finrank ℂ V)) i:= A i j'.1 (B j'.2)
    choose s hs using fun i:J×Fin (Module.finrank ℂ V)=> h i.1 (B i.2)
    obtain ⟨t,X,hX⟩:= Extraction.simultaneous f (K:=fun i=> Metric.closedBall 0 (s i)) (fun _=> isCompact_closedBall ..) (fun i=> (hs i).mono fun j hj=> Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hj))
    let M j:= B.constr ℂ (fun i=> X (j,i)); refine ⟨t,fun j=> LinearMap.toContinuousLinearMap (M j),fun j=> ?_⟩
    apply Dash.fit_plane (fun i=> (A (t i) j).toLinearMap) (M j); intro x
    have ht (S: V→ₗ[ℂ] ℂ) : ∑ i,B.repr x i • S (B i)=S x:=by simp_rw [← map_smul,←map_sum,B.sum_repr]
    have hk i:Tendsto (fun k=> (A (t k) j).toLinearMap (B i)) atTop (𝓝 (M j (B i))):=by rw [show M j (B i)=X (j,i) from Module.Basis.constr_basis ..]; exact (hX (j,i)).2
    rw [← ht (M j)]; exact (tendsto_finsetSum Finset.univ fun i _=> (tendsto_const_nhds (x:=B.repr x i)).smul (hk i)).congr (fun i=> ht ((A _ j).toLinearMap))
-- avoids rank semicont proof via injective complement count
lemma cleft {V : Type*}[NormedAddCommGroup V][NormedSpace ℂ V] [FiniteDimensional ℂ V]{I:Type*} [Fintype I]
     (T:V →L[ℂ] V)(U:Submodule ℂ V)(A:I → V→L[ℂ] ℂ)(h:Module.finrank ℂ (LinearMap.ker T.toLinearMap)+Module.finrank ℂ U=Module.finrank ℂ V)
     (hp:∀ i x,T x=0→ A i x=0)(hv:∀ x∈U,(∀ i,A i x=0)→ x=0) : ∀ x:V, (∀ i,A i x=0) → T x=0:=by
   let S:=LinearMap.pi fun i=> (A i).toLinearMap
   have he : Injective (S.comp U.subtype):= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x e=> Subtype.ext (hv x x.2 (fun i=> congr_fun e i)))
   have hz : Module.finrank ℂ U ≤ Module.finrank ℂ (LinearMap.range S):= LinearMap.finrank_le_finrank_of_injective (f:=S.rangeRestrict.comp U.subtype) (fun x y hh=> he (congr_arg Subtype.val hh))
   have hA : LinearMap.ker T.toLinearMap ≤ LinearMap.ker S:=fun x hx=> LinearMap.mem_ker.mpr (funext fun i=> hp i x hx)
   have hF : LinearMap.ker T.toLinearMap = LinearMap.ker S:= Submodule.eq_of_le_of_finrank_le hA (by have hh:= S.finrank_range_add_finrank_ker; omega)
   exact fun x he=> LinearMap.mem_ker.mp (hF.symm ▸ (LinearMap.mem_ker.mpr (show S x=0 from funext he))) -- subst syntax
end YM.UVExtension.Fallow

import YM.TraceExtension.Terrace.Delta
import YM.UVNext.FREE_STRESS_CERTIFICATE.Certificate
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux Maxwell
open Further.PhysicalPeriodLimitF933 UVNext.FreeStress
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
private lemma hear_matrix {E H:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup H][NormedSpace ℝ H][FiniteDimensional ℝ H](F:E→ₗ[ℝ] H)(h:Injective F)(W:ℕ→ E→L[ℝ] H)(hW:Tendsto W atTop (𝓝 (LinearMap.toContinuousLinearMap F)))(v:ℕ→ E)(hv:Tendsto (fun i=> W i (v i)) atTop (𝓝 0)): Tendsto v atTop (𝓝 0):=by
    obtain ⟨s,hS⟩:= F.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr h)
    let y i:= s.toContinuousLinearMap.comp (W i); let F':= LinearMap.toContinuousLinearMap F
    have hx:Tendsto (fun i=> y i (v i)) atTop (𝓝 0):=by simpa only[Function.comp_def,ContinuousLinearMap.comp_apply,map_zero] using! s.continuous_of_finiteDimensional.continuousAt.tendsto.comp hv
    have he:Tendsto y atTop (𝓝 (1:E→L[ℝ] E)):=by have hu: (LinearMap.toContinuousLinearMap s).comp F'= 1:=ContinuousLinearMap.ext (fun x=> LinearMap.congr_fun hS x); rw[← hu]; exact ((show Continuous (fun a:E→L[ℝ] H=>s.toContinuousLinearMap.comp a) from continuous_const.clm_comp continuous_id)).continuousAt.tendsto.comp hW
    have ht:∀ᶠ i in atTop, ‖v i‖ ≤ 2*‖y i (v i)‖:=by
        filter_upwards [Metric.tendsto_nhds.mp he (1/2) (by norm_num)] with i hi
        rw [dist_eq_norm] at hi
        have hu := ((y i-1).le_opNorm (v i)).trans (mul_le_mul_of_nonneg_right hi.le (norm_nonneg _)); change ‖y i (v i)-v i‖ ≤ _ at hu; rw [norm_sub_rev] at hu; linarith only [hu,norm_sub_norm_le (v i) (y i (v i))]
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) ht ?_); simpa using hx.norm.const_mul 2

private lemma sewn {E H:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup H][NormedSpace ℝ H][FiniteDimensional ℝ H](F:E→ₗ[ℝ] H)(U:ℕ→ E→ₗ[ℝ] H) (v:ℕ→ E)(hf:Injective F)(he:∀ x,Tendsto (fun i=>U i x) atTop (𝓝 (F x)))(hv:Tendsto (fun i=>U i (v i)) atTop (𝓝 0)) : Tendsto v atTop (𝓝 0):=by
   exact hear_matrix F hf (fun i=>LinearMap.toContinuousLinearMap (U i)) (fitV _ _ he) v hv

private theorem finite_faithful_R {ι E:Type*} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (f : ι → E →ₗ[ℝ] ℂ) (hf : Injective (LinearMap.pi f)) :
    ∃ s : Finset ι, Injective (LinearMap.pi (fun i : s => f i)) := by
  classical
  let K (s : Finset ι) := LinearMap.ker (LinearMap.pi (fun i : s => f i))
  obtain ⟨_, ⟨s, rfl⟩, h⟩ := wellFounded_lt.has_min
    (Set.range (fun s : Finset ι => Module.finrank ℝ (K s))) (Set.range_nonempty _)
  refine ⟨s, LinearMap.ker_eq_bot.mp ?_⟩
  refine bot_unique (fun v (hv : v ∈ K s) => ?_)
  rw [← LinearMap.ker_eq_bot.mpr hf]
  apply LinearMap.mem_ker.mpr
  funext i
  have he : K (insert i s) = K s := by
    refine Submodule.eq_of_le_of_finrank_le ?_ (not_lt.mp (h _ (Set.mem_range_self (insert i s))))
    intro x hx
    apply funext
    exact fun j => congr_fun (show (LinearMap.pi _) x = 0 from hx)
      ⟨j.val, Finset.mem_insert_of_mem j.property⟩
  rw [← he] at hv
  exact congr_fun (show (LinearMap.pi _) v = 0 from hv) ⟨i, Finset.mem_insert_self ..⟩


variable {G:Gauge}{C:Family G} {F: Extraction.Order} {𝓛: Ultrafilter (ℕ×ℕ)}
set_option quotPrecheck false
local notation "T!"=> Cells.standard C
variable {S:Table C.book} {X:Scaling S} (h:S.Hierarchy){a:(Cells.standard C).Hierarchy} (hs:StarPath F a X h 𝓛)

/-- To locate the co-kernel sufficient to do paired listening on angular cameras.
Take near them generic cells on all axes to use the actual point limits. -/
lemma ears_det {V:DiffPlan (Cells.standard C)} (H:V.Derivatives (Cells.standard C))(hV:V.Orientation a.spin)(hG:G.Simple) (v: TableOne a.spin) (ht:∀ g:(Cells.standard C).Field 4,
    (T!).useAt T! (camera 0) ![⟨5,v.val 0⟩,⟨4,g⟩]=0) : v=0:=by
   have hW : v.val∈ Vectors a.spin:= (one a.spin v.val).mp v.property
   let W:Vectors a.spin:=⟨v.val,hW⟩
   have he(i j:Axis): switch C.labels a.spin i j W=0 := by
       let R:=UVNext.FreeStress.embed C.labels 4 (ff G 4 le_rfl i j i j); have hh : hearing C.labels (camera 0) i j i j 5 (W.val 0)=0:= (listens C.labels ..).trans (by
          have hz : Fin.cons (α:=fun _ => (T!).Tag) (⟨5,W.val 0⟩:(T!).Tag) (negs C.labels i j i j)=![⟨5,W.val 0⟩,⟨4,R⟩]:=by funext j; fin_cases j <;> rfl
          rw[hz]; exact ht R)
       unfold switch; change _;
       change ((loud G)⁻¹*hearing C.labels (camera 0) i j i j 5 (W.val 0)).re=0; rw[hh,mul_zero];rfl
   have hx: W=0:= (scope_exact C.labels a.spin hG V H hV).1 (by rw [map_zero]; exact Prod.ext (he ..) (he ..))
   exact Subtype.ext (show W.val = 0 from congr_arg (fun v: Vectors a.spin => v.val) hx)

variable {V:DiffPlan (Cells.standard C)} (hV:V.Derivatives (Cells.standard C)){W:DiffPlan S}(he: W.Derivatives S)
include hV he hs
/-- can let the calibrated sensor geometry approach the axial one while solving linear tests. -/
lemma spots (v : (Cells.standard C).Field 5) (w:(Cells.standard C).Field 4)(z:ℕ→ Points 2)(hz:Tendsto z atTop (𝓝 (camera 0))) :
     Tendsto (fun i=> S.useAt S (X.r i • z i) ![⟨5,X.U i 5 v⟩,⟨4,X.U i 4 w⟩]) atTop (𝓝 ((T!).useAt T! (camera 0) ![⟨5,v⟩,⟨4,w⟩])):=by
    let v':Fin 2→(T!).Tag:=![⟨5,v⟩,⟨4,w⟩]; let x:= disc v'
    let y(i:ℕ):= tested (X.r i) (isoPanel X i) v'
    have hi:camera 0∈conf 2:= shutter ..; have hx : Tendsto (fun i=>x (z i)) atTop (𝓝 (x (camera 0))) := (show ContinuousAt x (camera 0) from (smoothDisc a.smooth v').continuousOn.continuousAt ((conf_open _).mem_nhds hi)).tendsto.comp hz
    have heq(i:ℕ):panels (isoPanel X i) ∘ v'=![⟨5,X.U i 5 v⟩,⟨4,X.U i 4 w⟩]:=by funext j; fin_cases j<;> rfl
    have hU:Tendsto (fun i=> y i (z i)) atTop (𝓝 (x (camera 0))):=by
       obtain ⟨ε,hε,hp⟩:= Metric.mem_nhds_iff.mp ((conf_open _).mem_nhds hi);
       let Z:= Metric.closedBall (camera 0) (ε/2); have hB:Z ⊆ conf 2:=(Metric.closedBall_subset_ball (half_lt_self hε)).trans hp
       let u j:=(v' j).2
       have ht₀:= hz.eventually (Metric.closedBall_mem_nhds (camera 0) (show 0 < ε/2 from half_pos hε))
       refine Metric.tendsto_nhds.mpr fun δ hδ=> ?_
       filter_upwards [Metric.tendsto_nhds.mp hx (δ/2) (half_pos hδ),ht₀,travels_jet h he a hV X hs.approach (t:=fun j=> (v' j).1) (fun _ j=>u j) u (fun _=>tendsto_const_nhds) 0 Z (isCompact_closedBall ..) hB (δ/2) (half_pos hδ)] with i h₁ h₂ h₃
       apply lt_of_le_of_lt (dist_triangle (y i (z i)) (x (z i)) (x (camera 0))); have hQ : dist (y i (z i)) (x (z i)) ≤ δ/2:=by
           specialize h₃ (z i) h₂; change ‖iteratedFDeriv ℝ 0 (y i) (z i)-iteratedFDeriv ℝ 0 x (z i)‖≤ _ at h₃
           rw [show iteratedFDeriv ℝ 0 (y i) (z i)-iteratedFDeriv ℝ 0 x (z i)=iteratedFDeriv ℝ 0 (y i-x) (z i) from ?_,norm_iteratedFDeriv_zero] at h₃
           · rw[dist_eq_norm]; exact h₃
           ext; simp
       linarith only [h₁,hQ]
    exact hU.congr (fun i=>by unfold y tested; rw [heq]; rfl)

lemma listened_G(z:ℕ→ Points 2)(hz:Tendsto z atTop (𝓝 (camera 0)))(v:ℕ→ TableOne a.spin) (ho:V.Orientation a.spin)(hG:G.Simple)
    (hK:∀ w:(Cells.standard C).Field 4, Tendsto (fun i=> S.useAt S (X.r i • z i) ![⟨5,X.U i 5 ((v i).val 0)⟩,⟨4,X.U i 4 w⟩]) atTop (𝓝 0)): Tendsto v atTop (𝓝 0):=by
    let L:= (T!).Field 4
    let B(w:L): (T!).Field 5→ₗ[ℂ] ℂ:= Work.A01.frontRead (S:=T!) (n:=1) ![⟨4,w⟩] (camera 0) 5
    let t (w:L): TableOne a.spin→ₗ[ℝ] ℂ:= (B w).restrictScalars ℝ|>.comp ((LinearMap.proj (0:Axis)).comp (TableOne a.spin).subtype)
    have hx(w:L)(v:TableOne a.spin): t w v=(T!).useAt T! (camera 0) (![⟨5,v.val 0⟩,⟨4,w⟩]:Fin 2→ (T!).Tag):= Work.A01.front_eval (S:=Cells.standard C) (n:=1) ![⟨4,w⟩] (camera 0) 5 (v.val 0)
    have ht:Injective (LinearMap.pi t):=by
       apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.mpr; intro y hy; refine ears_det (a:=a) hV ho hG y fun i=>?_ ; rw [← hx]; exact congr_fun hy i
    obtain ⟨s,hS⟩:= finite_faithful_R (E:=↥(TableOne a.spin)) t ht
    let u(i:ℕ)(w:L):S.Field 5→ₗ[ℂ] ℂ:= Work.A01.frontRead (S:=S) (n:=1) ![⟨4,X.U i 4 w⟩] (X.r i • z i) 5; let T (i:ℕ):= (X.U i 5).toLinearMap
    let c(i:ℕ):TableOne a.spin→ₗ[ℝ] (s→ℂ):= LinearMap.pi fun w :s=> ( (u i w.val).comp (T i)|>.restrictScalars ℝ).comp ((LinearMap.proj (0:Axis)).comp (TableOne a.spin).subtype)
    have heq(i:ℕ)(v:TableOne a.spin)(w:s): c i v w=S.useAt S (X.r i • z i) ![⟨5,X.U i 5 (v.val 0)⟩,⟨4,X.U i 4 w.val⟩]:= Work.A01.front_eval (S:=S) (n:=1) ![⟨4,X.U i 4 w.val⟩] (X.r i • z i) 5 (X.U i 5 (v.val 0))
    let Y:= LinearMap.pi (fun i:s=> t i.val)
    have hW(x):Tendsto (fun i=> c i x) atTop (𝓝 (Y x)):=by refine tendsto_pi_nhds.mpr fun i=>?_ ; change Tendsto (fun j=>c j x i) atTop (𝓝 (t i.val x)); simp_rw [heq,hx]; exact spots h hs hV he _ _ z hz
    have hw:Tendsto (fun i=> c i (v i)) atTop (𝓝 0):=by refine tendsto_pi_nhds.mpr fun i=>?_ ; change Tendsto (fun j=>c j (v j) i) atTop (𝓝 0); simp_rw[heq]; exact hK i.val
    exact sewn (E:=↥(TableOne a.spin)) (H:=s→ℂ) Y c v hS hW hw
end YM.Trace.Terrace

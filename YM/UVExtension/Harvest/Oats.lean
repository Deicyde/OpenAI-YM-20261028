import YM.Next.EXTRACTION.Coordinates
import YM.MergeProof.Powder
import YM.UVExtension.Hearth.Spoon
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Harvest
open Finset Set Function Filter MeasureTheory Lattice RG Push Wilson Precision Labels
open Extra.Histories Source PhysicalNext.Repeat Mast Extraction Next.Extract Dash MergeProof
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {V ι ℱ : Type*}[NormedAddCommGroup V][NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {G:Gauge} {C:Family G}
lemma arriveShots {P:ℕ→ Table C.book}(H: Order.full.Meshes C P)(ht: Bound C Extraction.Order.full) (p:ℕ) (d)(z:Shot C.book)(hz:suitable C.S p z.f): Arrives fun i=> z.scan (C:=C) d i p:=by
   let M:= Module.finBasis ℂ (C.book.Ref d); let V i:= z.scan d i p (C:=C)
   have hp(x): Arrives fun i=> V i x:= ⟨_, (Order.full.intraperiod C ht H hz (z.record x)).2⟩
   choose l hl using hp
   let T: C.label d →ₗ[ℂ] ℂ := M.constr ℂ (fun i=> l (M i)); let q:=T.toContinuousLinearMap
   have hz(x): Tendsto (fun j=> V j x) atTop (𝓝 (T x)):=by
       let y (j) (i):= (M.repr x i) • V j (M i)
       have he i : Tendsto (fun j=> y j i) atTop (𝓝 (M.repr x i • T (M i))):=by rw [show T (M i)=l _ from Module.Basis.constr_basis ..]; exact (tendsto_const_nhds (x:=M.repr x i)).smul (hl _)
       have h (K:C.label d→ₗ[ℂ] ℂ) : ∑ i,M.repr x i • K (M i)=K x:=by simp_rw [←map_smul,← map_sum,M.sum_repr]
       rw [← h T]; exact (tendsto_finsetSum _ fun j _=> he j).congr (fun j=>h (V j).toLinearMap)
   exact ⟨q, Dash.fit_plane (V:=C.label d) (fun i=>(V i).toLinearMap) T hz⟩
lemma squeezeOp {γ:Type*}{p:Filter γ}(I:Finset ι)(a:ℝ)(h:0<a){T:ι→V→L[ℂ]ℂ}{U:Submodule ℂ V}(hp:∀ x∈U, a*‖x‖ ≤ ∑ i∈I,‖T i x‖)
     (K:γ→ι→ V→L[ℂ]ℂ)(hK:∀ i∈I, Tendsto (fun n=> K n i) p (𝓝 (T i))): ∀ᶠ i in p,∀ x∈U,a/2*‖x‖ ≤ ∑ j∈I,‖K i j x‖:=by
   have hh:Tendsto (fun n=>∑ i∈I,‖(T i)-(K n i)‖) p (𝓝 0):=by
       have ht (i)(hi:i∈I) : Tendsto (fun n=> ‖T i-K n i‖) p (𝓝 0):=by simpa only [sub_self,norm_zero] using ((tendsto_const_nhds (x:=T i)).sub (hK i hi)).norm
       simpa only [Finset.sum_const_zero] using! tendsto_finsetSum I (fun i hi=> ht i hi)
   filter_upwards [hh.eventually (ge_mem_nhds (half_pos h))] with n hn x hx -- ge?
   have hv := Finset.sum_le_sum (s:=I) fun i _=> (norm_le_norm_add_norm_sub' (T i x) (K n i x)).trans (add_le_add_right (show ‖T i x-K n i x‖ ≤ ‖T i-K n i‖*‖x‖ from (T i-K n i).le_opNorm _) _)
   rw [Finset.sum_add_distrib,←Finset.sum_mul] at hv; linarith only [hp x hx,hv, mul_le_mul_of_nonneg_right (show _ ≤ a/2 from hn) (norm_nonneg x)]

def charge (G:Gauge)(d:ℕ):= Module.finrank ℂ (Maxwell.equationIdeal G d)

def Slicing (C:Family G)(d p:ℕ): Prop:=∃ (I:Finset (Dash.Shot C.book)) (a:ℝ)(U:Submodule ℂ (C.label d)), 0<a ∧
    (∀ i ∈ I,suitable C.S p i.f) ∧ Module.finrank ℂ U + charge G d= Module.finrank ℂ (C.label d) ∧
    ∀ᶠ N in atTop, ∀ x∈U,a*‖x‖ ≤ ∑ i∈I,‖snapshots i d (N,p) x‖
lemma along_rank {S: Table C.book}{M:ℕ→Table C.book}{f:Extraction.Order}{T:Bin S}{P:Table C.book}{R:DiffPlan P}{V:Push.Mark.Weave G} {W Y U}(h:Next.Extract.Base C f S M T P R)(hx:Scotia C V W Y)(hr:Projected Y f T U)(d:ℕ) (hp:∀ (p:ℕ)(i:Shot C.book), suitable C.S p i.f → Arrives fun n=>snapshots i d (n,p)) : ∀ᶠ i in atTop,Slicing C d (f.per i):=by
   let X:= C.label d; let g:= (T d).trueP
   let e:= LinearMap.ker g.toLinearMap; let A:= LinearMap.range g.toLinearMap
   have he: Module.finrank ℂ A+ charge G d = Module.finrank ℂ (C.label d):=by
      obtain ⟨hV,ht⟩:= hr.ranks d
      obtain ⟨i,hi⟩:= ht.exists; obtain ⟨j,hj⟩:= (hV (f.per i)).exists
      let v:=(f.mesh j,f.per i); let z:= bindP C V d v.1 v.2 (W d v)
      have h': Module.finrank ℂ (LinearMap.ker (Y.step d v).toLinearMap)= Module.finrank ℂ e:= hj.trans hi
      have hk:Module.finrank ℂ (LinearMap.ker (Y.step d v).toLinearMap)=charge G d:=by rw [show LinearMap.ker _= _ from (hx.step d v.1 v.2).ker]; exact (LinearEquiv.finrank_eq (z.submoduleMap (Maxwell.equationIdeal G d))).symm
      rw [← hk,h']; exact LinearMap.finrank_range_add_finrank_ker _
   let K(i:Shot C.book):= i.core (d:=d) S h.arrives.born
   have hv: e=monitor S h.arrives.born d:= Bin.exactC T h.arrives.census.integral (h.pinned.p d) (h.pinned.q d) -- replace
   obtain ⟨I,c,hc,hI⟩:=finite_detectors g K (fun x hx hp=>hx.symm.trans (LinearMap.mem_ker.mp (show x ∈ e from hv.symm ▸ (Submodule.mem_iInf _).2 (fun i=> LinearMap.mem_ker.mpr (hp i)))))
   have hD(x)(hx:x∈A): c*‖x‖ ≤ ∑ i∈I,‖K i x‖:=by
      have hu:g x=x:= by obtain ⟨w,rfl⟩:=hx; exact (T d).final _
      simpa [hu] using hI x
   have hM:= squeezeOp I _ hc hD (fun n i=> snapshots i d n) (fun i _=> i.ready h.arrives.born h.arrives.census.integral d)
   rw [Order.fused] at hM; unfold Order.late at hM
   filter_upwards [hM,(eventually_all_finset I).mpr (fun i hi=> f.per.cofinal.eventually (Extraction.reading C.S i.f))] with p ht hP
   choose! L hL using (fun i hi=> hp (f.per p) i (hP i hi))
   refine ⟨I,_,A,half_pos (half_pos hc),hP,he,squeezeOp I _ (half_pos hc) (T:=L) (fun x hx=> ?_) (fun n i=> snapshots i d (n,f.per p)) hL⟩
   exact ge_of_tendsto (tendsto_finsetSum I fun i hi=> show Tendsto (fun k=> ‖snapshots i d (f.mesh k,f.per p) x‖) atTop (𝓝 ‖L i x‖) from ((Dash.arcing ((hL i hi).comp f.mesh.cofinal) (tendsto_const_nhds (x:=x)))).norm) (ht.mono fun n hn=> hn x hx)
lemma rootwards {V W Y}(hx:Scotia C V W Y)(d:ℕ)(hp:∀ (p:ℕ)(i:Shot C.book), suitable C.S p i.f → Arrives fun n=>snapshots i d (n,p))(h:∀ f:Extraction.Order, ∃ g T P R Z A I, Projected Y (f.refine g) R Z∧ Next.Extract.Base C (f.refine g) T P R A I) : ∀ᶠ p:ℕ in atTop,Slicing C d p:=by
    by_contra he; obtain ⟨t,ht,hT⟩:= extraction_of_frequently_atTop (show ∃ᶠ i:ℕ in atTop, ¬ Slicing C d i from by simpa [Filter.Frequently] using he); let f: Extraction.Order:= ⟨Sequence.full, ⟨t,ht⟩⟩
    obtain ⟨g,T,P,R,Z,A,I,hz,hB⟩:= h f; obtain ⟨i,hi⟩:= (along_rank hB hx hz d hp).exists; exact hT (g.per i) hi
end YM.UVExtension.Harvest

import YM.OPE.Orbits.Parameter

/-! Finite-horizon readouts on the actual scalar kernel, before averaging.
Separation collars eventually contain whole O(4) orbits. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Filter MeasureTheory Set Table Extraction Word
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{L:Register G}{S T:Table L} {I:Type}[Fintype I]{d:I→ℕ} {P0:DiffPlan S}
variable (P:Prescription P0) (n:ℕ)(i:Mode P0)

/-- Multilinearity over the tested input slots. Non-separated configurations again
extend to zero (test by test, separation guard independent of labels). -/
def checkRow (x:I→E4) (o:E4): MultilinearMap ℂ (fun i=> S.Field (d i)) ℂ:=
    ∑ e∈ (P.sheet i).support, (P.sheet i) e •
      let z:=beside (away x o) (bearing e)
      let f:= beside d fun j => (e.letter j).fst
      if Injective z then sectionLabels (d:=f) (fun j=>S.project _ (e.letter j).snd) (moment S (d:=f) z)
      else 0

lemma check_eq (hS:S.Hierarchy) (x:I→E4) (o:E4) (v:Labels S d): checkRow P i x o v=P.ope i x (names v) o:=by
   unfold checkRow Prescription.ope; rw [_root_.sum_apply]; refine Finset.sum_congr rfl (fun e he=>?_) -- double sum notation
   dsimp only; let f:= (if Injective (beside (away x o) (bearing e)) then sectionLabels (d:=beside d (fun j=>(e.letter j).fst)) (W:=ℂ) (fun j=> S.project _ (e.letter j).snd) (moment S (beside (away x o) (bearing e))) else 0)
   change ((P.sheet i) e • f) v = _
   have hv: ((P.sheet i) e • f) v=(P.sheet i) e • f v:=rfl
   rw [hv]; apply congr_arg (fun z:ℂ=> (P.sheet i) e * z)
   let z':= beside (away x o) (bearing e); let b:(Fin e.n→ℕ):= fun j=>(e.letter j).fst; let f':MultilinearMap ℂ (fun q=> S.Field (Sum.elim d b q)) ℂ := moment S z'; let ys:Labels S b:= fun j => S.project _ (e.letter j).snd
   have h0:f = if Injective z' then sectionLabels (d:=Sum.elim d b) ys f' else (0:MultilinearMap ℂ (fun q=> S.Field (d q)) ℂ):=rfl
   rw [h0]; change (ite (Injective z') (sectionLabels (d:=Sum.elim d b) ys f') (0:MultilinearMap ℂ (fun q=> S.Field (d q)) ℂ)) v = ite (Injective z') _ _; split_ifs with hx
   · rw [sectionLabels_apply]; change moment S (d:=Sum.elim d b) (beside (away x o) (bearing e)) (stages v (fun j => S.project _ (e.letter j).snd)) = _
     rw [observed]; let a:Labels S (beside d (fun j=>(e.letter j).fst)):=stages v (fun j=>S.project _ (e.letter j).snd); let p:=beside (names v) e.letter
     unfold observe worded; rw [S.readAt,S.readAt]
     let z:=points (beside (away x o) (bearing e) ∘ runNames (I⊕Fin e.n))
     change S.read z (names a ∘ runNames (I⊕Fin e.n))=S.read z (p ∘ runNames _)
     have hh: (fun h=> S.classTokens (names a h))= S.classTokens ∘ p:=by
        funext h; rcases h with h|h; · rfl
        simp only [a,stages,p,names,beside_right,Function.comp_apply]
        change (⟨(e.letter h).fst, _⟩:S.Tag)=_
        erw [S.rep]
     rw [← S.at_project S hS.laws.toSymmetric (fun _ => le_rfl) (runs_conf.mpr hx),← S.at_project S hS.laws.toSymmetric (fun _ => le_rfl) (runs_conf.mpr hx)]
     exact congr_arg _ (congr_arg (Function.comp · (runNames _)) hh)
   rfl

section Smooth
variable {Z:Type}[NormedAddCommGroup Z][NormedSpace ℝ Z]
lemma mixed_word {f : Z→ MultilinearMap ℂ (fun i=> S.Field (d i)) ℂ} {y:Z}
   (h:∀ a, ContDiffAt ℝ ∞ (fun k=>f k a) y) {v:Z→ Labels S d} (hv:ContDiffAt ℝ ∞ v y):
   ContDiffAt ℝ ∞ (fun k=> f k (v k)) y:=by
   let b i:= Module.finBasis ℂ (S.Field (d i));
   let v'(k)(i)(j):= ((b i).repr (v k i)) j
   let c(k)(i)(j):ℂ:=(LinearMap.toContinuousLinearMap ((b i).coord j)) (v k i)
   have hb(k):v k=fun i=>∑ j,(v' k i j) • b i j:=funext fun i=>(Module.Basis.sum_repr ..).symm
   have hf(k): f k (v k) =∑ r:(∀ i, Fin (Module.finrank ℂ (S.Field (d i)))), ((∏ j, c k j (r j)) • f k (fun i=> b i (r i))) :=by
       rw [hb,MultilinearMap.map_sum_finset]; have hu: Fintype.piFinset (fun i=> (Finset.univ:Finset (Fin (Module.finrank ℂ (S.Field (d i))))))=Finset.univ:= by ext; simp
       rw [hu]; apply Finset.sum_congr rfl fun r _=>?_; rw [MultilinearMap.map_smul_univ]; rfl
   simp_rw [hf]; apply ContDiffAt.sum; intro r _; refine ContDiffAt.smul (f:=fun k=>∏ (j:I), c k j (r j)) ?_ (h _)
   have h' (s:Finset I): ContDiffAt ℝ ∞ (fun k=>∏ j∈s,c k j (r j)) y:=by
       induction s using Finset.induction_on with
       | empty=> simp only [Finset.prod_empty]; exact contDiffAt_const
       | @insert i s hi ih=>
           simp_rw [Finset.prod_insert hi]; apply ContDiffAt.mul (f:=fun k=>c k i (r i)) ?_ ih
           apply ((LinearMap.toContinuousLinearMap ((b i).coord (r i))).restrictScalars ℝ).contDiff.contDiffAt.comp _ ((contDiffAt_pi).mp hv i)
   apply h' 

lemma check_smooth (hS:S.Hierarchy){x:I→E4}{o:E4}{v:Labels S d} (hx:∀ e∈ (P.sheet i).support, Injective (beside (away x o) (bearing e))) : ContDiffAt ℝ ∞ (fun z:((I→E4)×E4)×Labels S d=>checkRow P i z.1.1 z.1.2 z.2) ((x,o),v):= by
    refine mixed_word (fun a=>?_ ) contDiffAt_snd
    simp_rw [check_eq P i hS]; exact ContDiffAt.comp (f:=Prod.fst) _ (smooth_ope P hS (names a) i hx) contDiffAt_fst
end Smooth

attribute [local instance] YM.Work.A15.compact_ortho

def Dock (x:I→ E4) (o:E4): Prop :=∀ k:Ortho,∀ e∈ (P.sheet i).support,
    Injective (beside (away (Ortho.move k ∘ x) (Ortho.move k o)) (bearing e))
abbrev Lines:= Axis → Axis → ℝ
lemma smoothMotion : ContDiff ℝ ∞ (fun z:(E4×Lines) => M4.move z.2 z.1):=by
   apply (PiLp.contDiff_toLp (𝕜:=ℝ) (E:=fun _:Axis=>ℝ) (n:=∞) (p:=2)).comp (f:=fun z:E4×Lines=>fun j:Axis=>∑ i:Axis, z.2 j i * z.1 i)
   refine contDiff_pi.mpr fun j=> ContDiff.sum fun u _=> ?_
   let f:= fun t:E4×Lines=> (t.2:Axis→Axis→ℝ)
   have h : ContDiff ℝ ∞ f:=contDiff_snd
   exact ((contDiff_pi.mp ((contDiff_pi.mp h) j)) u).mul (show ContDiff ℝ ∞ (fun z:E4×Lines=> z.1 u) from by apply (EuclideanSpace.proj u:E4→L[ℝ]ℝ).contDiff.comp (f:=Prod.fst) contDiff_fst)
lemma orbCont : Continuous (fun z:E4×Ortho=> Ortho.move z.2 z.1):=by
    apply smoothMotion.continuous.comp ((continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
-- Tube around a whole compact orbit of one port.
omit [Fintype I] in
private lemma one_dock_cont {J:Type}(b:J→E4) : Continuous (fun g:((I→E4)×E4)×Ortho=> beside (away (Ortho.move g.2 ∘ g.1.1) (Ortho.move g.2 g.1.2)) b):=by
     refine continuous_pi fun q=> ?_
     rcases q with j|j; swap; exact continuous_const
     show Continuous fun z:((I→E4)× E4)×Ortho=>Ortho.move z.2 (z.1.1 j) - Ortho.move z.2 (z.1.2)
     have h1: Continuous (fun z:((I→ E4)× E4) × Ortho=> (z.1.1 j,z.2)):=by fun_prop
     have h2: Continuous (fun z:((I→ E4)× E4) × Ortho=> (z.1.2,z.2)):=by fun_prop
     exact (orbCont.comp h1).sub (orbCont.comp h2)
private lemma whole_tube {Z:Type*}[TopologicalSpace Z] {A:Set (Z×Ortho)}(h:IsOpen A):IsOpen {g:Z | ∀ k:Ortho,(g,k)∈A}:=by
     apply isOpen_iff_mem_nhds.mpr; intro g hg
     obtain ⟨B,C,hA,_,hB,hC,hF⟩:= generalized_tube_lemma isCompact_singleton (show IsCompact (univ:Set Ortho) from isCompact_univ) h (show {g} ×ˢ univ ⊆ A from fun z hz=>by change (z.1,z.2)∈ A; exact (mem_singleton_iff.mp hz.1).symm ▸ (show (g,z.2)∈A from hg _))
     exact mem_of_superset (hA.mem_nhds (hB (mem_singleton g))) (fun z hz k=> hF (mk_mem_prod hz (hC (mem_univ k))))
set_option maxHeartbeats 500000 in
private lemma one_dock {J:Type}[Fintype J] (b:J→E4) : IsOpen {g:(I→E4)×E4| ∀ k:Ortho,Injective (beside (away (Ortho.move k ∘ g.1) (Ortho.move k g.2)) b)} :=
     whole_tube ((one_dock_cont (I:=I) b).isOpen_preimage {g:I⊕J→E4| Injective g} (open_inj (I:=I⊕J)))
lemma compact_dock : IsOpen {g:(I→E4)×E4|Dock P i g.1 g.2}:=by
    apply isOpen_iff_mem_nhds.mpr; intro g hg; have h(e:Exterior L) (he:e∈ (P.sheet i).support) : ∀ᶠ z:(I→E4)×E4 in 𝓝 g, ∀ k:Ortho,Injective (beside (away (Ortho.move k ∘ z.1) (Ortho.move k z.2)) (bearing e)) := (one_dock (bearing e)).mem_nhds (fun k=>hg k e he)
    filter_upwards [(eventually_all_finset _).2 h] with z hz; exact fun k e he=> hz e he k
end YM.OPE.Orbits

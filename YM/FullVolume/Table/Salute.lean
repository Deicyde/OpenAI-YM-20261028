import YM.FullVolume.Rise.Lemon
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Module.Completion
/-!
# Ambient shelf budget
Full ℓ¹ support currencies at fixed p. No histories positions thrown away.On the same merged `drawer` always used by actual prescription. Moves subspace further.
 May complete it taking closure of these representatives. Does not price off E-germ coordinates (no role except honor fields; pseudometric intentional).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Urns
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration RG.Shoot
open Push.PriceCompiler Push.AbsoluteSums Progress.DirectedRecipe Time UVNext.CouplingReset Ovens Ovens.Pipes
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}{c:Side} {p:BudgetPoint}
def layout (G : Gauge)(c : Side)(p:BudgetPoint): Listing G c:= ⟨(drawer G c).reg,Ovens.Pipes.addr (folio G c) p⟩
-- pair functions. componentwise.
abbrev MatrixP (G:Gauge) (c:Side):= Code G c × Code G c
def issue (p:BudgetPoint)(A:MatrixP G c): Activities G c:= (layout G c p).read ⟨A.1,A.2⟩
def Cash (p:BudgetPoint)(A:MatrixP G c)(b k:ℝ):Prop:= (issue p A).RegularFamily p ∧ (issue p A).ForcedFamily p ∧ (issue p A).EBound p b ∧ (issue p A).KBound p k
variable {b k d l:ℝ}{R K:MatrixP G c}
local notation "P"=> layout G c p
lemma ticket0 (G:Gauge)(c:Side)(p:BudgetPoint): Cash (G:=G) (c:=c) p 0 0 0:=by
  let X:= (layout G c p); refine ⟨⟨fun i=> VerifiedReset.reg_const _,fun _=>rfl,fun i h s t _ _=>hessian_zero ..⟩, ?_, ⟨0,fun i=> ?_,?_⟩,⟨0,fun i=> ⟨le_rfl,fun U=>?_⟩,?_⟩⟩
  · -- extra tests shelf output; call H03 via trivial empty or unfolds.
    have h1 i j (U:Config G c) : (X.hard i).extraTest (Lattice.gauge j U) ↔ (X.hard i).extraTest U := by
      change condition _ _ _ _ ↔ condition _ _ _ _; unfold condition ForcedAddress.eligible; rw [gauge_flags]; rfl
    have h2 i: MeasurableSet {U | (X.hard i).extraTest U}:=by
      change MeasurableSet {U|condition _ _ _ U}
      unfold condition; rw [Set.setOf_forall]
      apply MeasurableSet.iInter; intro j
      by_cases hj : j ∈ lefts ((folio G c) i).val; · simp only [hj,true_imp_iff]; exact Work.H03.eligible_measurable _ _ MeasurableSet.univ
      simp [hj]
    have h3 i: UsesFinal p.threshold (X.hard i).support (X.hard i).extraTest:=by
      intro U V ha hf
      have hh j (hj:j∈lefts ((folio G c) i).val): ((drawer G c).kernel j).eligible p.threshold U = ((drawer G c).kernel j).eligible p.threshold V:= by
        have ht : ((drawer G c).kernel j).support ⊆ (X.hard i).support:= Finset.subset_biUnion_of_mem (drawer G c).patch (Finset.mem_toLeft.mp hj)
        exact Work.H03.reads_larger ht (Work.H03.eligible_reads _ _ (fun _ _ _ _=>rfl)) U V ha hf
      change condition .. = condition ..; exact propext ⟨fun h j hj=> (hh j hj).mp (h j hj),fun h j hj=>(hh j hj).mpr (h j hj)⟩
    exact ⟨fun _ _ _=>rfl,h1,fun _=>measurable_const,h2,fun _ _ _ _ _=>rfl,h3,fun _ _ h=>False.elim (h rfl)⟩
  · exact WilsonStartup.Start.zero_bound (b:=p)
  · intro x; simp [SumBudget, BudgetPoint.mass]
  · exact le_of_eq norm_zero
  intro x; simp [SumBudget, BudgetPoint.mass]
lemma movingS (t:ℝ) (h:Cash p R b k): Cash p (t • R) (|t| * b) (|t| * k) := by
  obtain ⟨hr,hf,⟨z,hz,hZ⟩,w,he,hh⟩ := h
  let P':= P
  refine ⟨⟨fun i=> CouplingShape.reg_scale _ (hr.smooth i),fun i=>?_, fun i hi u v hu hv=>?_⟩,⟨fun i y U=> congr_arg (fun a:ℝ=>t • a) (hf.sym i y U), hf.symtest, fun i=> (hf.meas i).const_smul t, hf.meas_test, fun i x y A B=> ?_,hf.reads_test,fun i U h=> hf.permit i U ?_⟩,⟨fun i=> |t| *z i,fun i=> CouplingShape.sup_scale t (hz i), anchored_scale (n:=c) (abs_nonneg t) hZ⟩,⟨fun i=>|t| *w i,fun i=> ⟨mul_nonneg (abs_nonneg _) (he i).1,fun U=>?_⟩,fun i=>?_⟩⟩
  · change t * (issue p R|>.E i 1)=0; rw [hr.at_flat,mul_zero]
  · change iteratedFDeriv ℝ 2 (t • (germ (issue p R|>.E i))) 0 _=_
    rw [iteratedFDeriv_const_smul_apply (germ_diff (hr.smooth i))]; change t • logHessian _ u v=_; rw [hr.vanish i hi _ _ hu hv,smul_zero]
  · exact congr_arg (fun v:ℝ=> t • v) (hf.reads i x y A B)
  · intro hv; apply h; change t • ((issue p R).K i U)=0; rw [hv,smul_zero]
  · change ‖t • ((issue p R).K i U)‖ ≤ |t| * w i; rw [norm_smul]; exact mul_le_mul_of_nonneg_left ((he i).2 _) (abs_nonneg _)
  convert budget_scale (abs_nonneg t) (hh i) using 2 with i; dsimp only [BudgetPoint.mass,issue,Listing.read]; split<;>ring
lemma moveP (h:Cash p R b k)(hk:Cash p K d l): Cash p (R-K) (b+d) (k+l):=by
  obtain ⟨h,hf,⟨k,hk',hA⟩,⟨w,hw,hW⟩⟩:= h; obtain ⟨hz,hK,⟨Y,hY,hL⟩,⟨r,hr,hR⟩⟩:=hk
  let f:= issue p (R-K); let X:= issue p R; let H:=issue p K
  refine ⟨⟨fun i=> VerifiedReset.reg_sub (h.smooth i) (hz.smooth i),fun i=>?_,fun i hi u v hu hv=>?_⟩,?_,?_,?_⟩
  · change (issue p R).E i 1-(issue p K).E i 1=_; rw [h.at_flat,hz.at_flat,sub_zero]
  · change logHessian ((issue p R).E i-(issue p K).E i) u v=0; rw [hessian_sub (h.smooth i) (hz.smooth i), h.vanish i hi u v hu hv,hz.vanish i hi u v hu hv, sub_zero]
  · refine ⟨fun i j k=> congr_arg₂ (·-·) (hf.sym i j k) (hK.sym i j k),hf.symtest, fun i => (hf.meas i).sub (hK.meas i), hf.meas_test, fun i x y a b=> congr_arg₂ (·-·) (hf.reads i x y a b) (hK.reads i x y a b), hf.reads_test, ?_⟩
    intro i U hp; contrapose! hp; change X.K i U - H.K i U=_; change ¬ ((X.forced i).eligible _ _) at hp; rw [show X.K i U=0 from not_not.mp ((mt (hf.permit i U)) hp), show H.K i U=0 from not_not.mp ((mt (hK.permit i U)) hp),sub_self]
  · refine ⟨k+Y,fun i=> sup_sub (h.smooth i) (hz.smooth i) (hk' i) (hY i),fun i=>?_⟩
    convert budget_plus (hA i) (hL i) using 2 with i; dsimp only [Pi.add_apply,BudgetPoint.mass, Listing.read,issue]; split <;> ring
  refine ⟨w+r,fun i=> ⟨add_nonneg (hw i).1 (hr i).1,fun U=> (norm_sub_le (X.K i U) (H.K i U)).trans (add_le_add ((hw i).2 _) ((hr i).2 _))⟩,fun i=>?_⟩
  convert budget_plus (hW i) (hR i) using 2 with i; dsimp only [Pi.add_apply,BudgetPoint.mass, Listing.read,issue]; split <;> ring
lemma addP (h:Cash p R b k)(hk:Cash p K d l): Cash p (R+K) (b+d) (k+l):=by
  have hf:= movingS (-1:ℝ) hk; rw [abs_neg,abs_one,one_mul,one_mul,neg_one_smul] at hf; rw [← sub_neg_eq_add]; exact moveP h hf -- rwa issue
structure Price (G:Gauge)(c:Side) where
  p:BudgetPoint
  b:ℝ
  k:ℝ
  b0 : 0<b
  k0 : 0<k
variable {S:Price G c}
-- no Norm prior
abbrev arena (S:Price G c) : Submodule ℝ (MatrixP G c) where
  carrier:= {X|∃ u v,Cash S.p X u v}
  zero_mem':= ⟨_,_,ticket0 G c S.p⟩
  add_mem' {x} {y} hx hy:= by obtain ⟨u,v,h⟩:=hx; obtain ⟨a,b,t⟩:=hy; exact ⟨_,_,addP h t⟩
  smul_mem' a x h:= by obtain ⟨b,u,v⟩:=h; exact ⟨_,_,movingS a v⟩
lemma more (hp:Cash p R b k)(he:b≤d)(hr:k≤l): Cash p R d l:= ⟨hp.1,hp.2.1,E_rises hp.2.2.1 he,K_rises hp.2.2.2 hr⟩
-- gains before norm.
end YM.FullVolume.Urns

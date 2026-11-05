import YM.FullVolume.Mark.Table
/-! Reseat helpers. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}{R E : Rep G n}{Y:Hol G} {κ a b t:ℝ}
variable (P:Coefficient F n)(K:Guard.Keeper R.p R.activities)
def tongue (S:ℕ→Support n):ℕ ↪ ℕ:=⟨fun i=> (code (Support n)).symm (S i,i),fun _ _ h=> Prod.mk.inj ((code (Support n)).symm.injective h)|>.2⟩
abbrev liveE (P:Coefficient F n):= extend (tongue P.support) P.regular 0
def capture (P:Coefficient F n)(K:Guard.Keeper R.p R.activities): File G n:= (liveE P,stowK K P)
-- measure support literal
lemma leased (h:P.Format 0 Y R)(i:ℕ): mapSeat (tongue P.support i)=P.support i:=by
   unfold tongue mapSeat; dsimp only [Embedding.coeFn_mk]; rw [Equiv.apply_symm_apply]; exact Finset.insert_eq_of_mem (h.origin i)
lemma invest (h:P.Format 0 Y R): (book P.x (capture P K)).Format 0 Y R:=by
   let Q:= book P.x (capture P K); have hh:= rack_format K P h
   suffices hb: ∀ i,RegFit R 0 d Y (mapSeat i) (liveE P i) from
      ⟨fun i=>(hb i).smooth, fun i=> spot n i,fun i=> (hb i).unit_null,fun i=> (hb i).proj, hh.forcing,hh.carried,hh.invariant,hh.supported,hh.borel⟩
   intro i; by_cases he:i∈range (tongue P.support)
   · obtain ⟨i,rfl⟩:= he; rw [liveE,(tongue P.support).injective.extend_apply, leased _ h]; exact ⟨h.smooth _,h.origin _,h.identity_null _,h.projects _⟩
   rw [liveE,extend_apply' _ _ _ he]; exact ⟨(regular0 R.p (mapSeat i) 0).1,spot n i,rfl,fun _=> vanishing0 d (0:Site n) Y⟩
lemma wages (h:P.Format 0 Y R)(hp:Tab P 0 R κ a b): Tab (book P.x (capture P K)) 0 R κ a b:=by
   let T:={P with regular:=0}; have hT:Tab T 0 R κ 0 b:= ⟨hp.divisor,le_rfl,hp.second,⟨fun i=>0,budget0 ..,fun i=> (regular0 ..).2⟩, hp.forced⟩
   obtain ⟨u,v,h₁,h₂⟩:=rem_tabs.mp (keeps K T (hT.bound (zero_add b).le)); have hk:v≤b:= (le_add_of_nonneg_left h₁.first).trans h₂
   obtain ⟨A,hA,hC⟩:=hp.regular; let f:=tongue P.support; let t:=extend f A 0
   have hz i:t (f i)=A i:=f.injective.extend_apply ..
   refine ⟨hp.divisor,hp.first,hp.second,⟨t,?_,fun i=>?_⟩,?_⟩
   · refine Local.sumBudget_pass f _ ?_ ?_
     · change SumBudget (fun i=> R.p.mass (mapSeat (n:=n) (f i)) (t (f i))) a
       have he i: mapSeat (f i)=P.support i:= leased _ h i
       simp_rw [he,hz]; exact hA
     · intro i hi; rw [show t i=0 from extend_apply' _ _ _ hi,BudgetPoint.mass,mul_zero]
   · change R.p.supBounds 0 (mapSeat i) (liveE P i) (t i)
     by_cases he:i∈ Set.range f
     · obtain ⟨i,rfl⟩:= he; rw [hz,show mapSeat (f i)=P.support i from leased P h i,show liveE P (f i)=P.regular i from f.injective.extend_apply ..]; exact hC i -- fill
     rw [liveE,extend_apply' _ _ _ he,show t i=0 from extend_apply' _ _ _ he]; exact (regular0 ..).2
   obtain ⟨f,hf,hg⟩:= h₁.forced; exact ⟨_,⟨hf.1,hf.2.1,hf.2.2.trans (mul_le_mul_of_nonneg_left hk h₁.divisor.le)⟩,hg⟩
lemma tariffs (h:P.Format 0 Y R)(hx:P.remBound 0 R κ t): (book P.x (capture P K)).remBound 0 R κ t:=by obtain ⟨u,v,hv,ht⟩:=rem_tabs.mp hx; exact (wages _ _ h hv).bound ht
lemma expo (B : SectionData F)(h:P.Format 0 Y R): (book P.x (capture P K)).exponentialEntry 0 B R=P.exponentialEntry 0 B R:=by
   funext U; let f:=tongue P.support; let x:=book P.x (capture P K)
   have hz i: x.maskedTerm R (f i)=P.maskedTerm R i:=by
      change masked _ (mapSeat ..) (liveE P (f i)) = _
      rw [show liveE P (f i)=P.regular i from f.injective.extend_apply ..,show mapSeat (f i)=P.support i from leased P h i];rfl
   have hp : ∑' i, x.maskedTerm R i U=∑' i, P.maskedTerm R i U:=by
      simp_rw [← hz]; exact (Function.Injective.tsum_eq f.injective (fun i hU=> by contrapose! hU; apply Function.notMem_support.mpr; have hh : x.regular i=0:= Function.extend_apply' _ _ _ hU;  rw [Coefficient.maskedTerm, hh]; exact congr_fun (map_zero (maskLinear _ _)) _)).symm -- API
   exact congr_arg (part B 0 R U P.x+ ·) hp
lemma profited : profile R.activities (capture P K).2= profile R.activities P.forced:= stows K P
lemma pays (B : SectionData F)(h:P.Format 0 Y R)(hx:P.remBound 0 R κ t){σ u v w q:ℝ}(hp:R.Lawful σ u v w q): (book P.x (capture P K)).density 0 B R=P.density 0 B R:=
   reentry (expo P K B h) hp (rem_dominated (tariffs P K h hx)) (rem_dominated hx) (profited P K)
section
variable {v:F.Coeff}
-- support & force same across stacks required. P.H.Labels
structure Along (R E: Rep G n):Prop where
  price : R.p=E.p
  force : R.activities.forced=E.activities.forced
lemma along_format (hs:Along R E)(hp:P.Format 0 Y R): P.Format 0 Y E:= ⟨fun i=> hs.price ▸ hp.smooth i,hp.origin,hp.identity_null,hp.projects,fun i U h=> by rw [← hs.force,←hs.price]; exact hp.forcing i U h,fun i h=>by rw [←hs.force]; exact hp.carried i h,hp.invariant,fun i=>by rw [←hs.price,←hs.force]; exact hp.supported i,hp.borel⟩
lemma along_bound (hs:Along R E)(hp: P.remBound 0 R κ t): P.remBound 0 E κ t:=by unfold Coefficient.remBound; rw [← hs.price,← hs.force];exact hp
lemma Along.sym {R E: Rep G n}(h: Along R E): Along E R:= ⟨h.price.symm,h.force.symm⟩
lemma Along.toll {R E:Rep G n}(h:Along R E): R.activities.K=E.activities.K → profile R.activities P.forced=profile E.activities P.forced := fun _=>by -- doesn't actually need K
    unfold profile barcode; rw [h.force]
end
end YM.MergeProof.Matric

import YM.MergeProof.Stow
/-! Hooks: the singleton part of flagged redistribution, AS HISTORY aggregates not at zero external probes. Unit tests included. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{ι:Type*}{d:ℕ}{F:Labels.Frame G d}{o:Site n}

def fusionBox (A:Activities G n)(p:Support n)(b:Finset ℕ): Box n:= (p∪b.biUnion (Push.Local.patch A), b.biUnion (flagsFor A))
variable (A:Activities G n)(t:ℝ)
abbrev Response (G:Gauge)(n:Side):= Support n→ Config G n→ℂ
-- concentrate

def grasp (p:Support n)(b:Finset ℕ)(u:Box n)(U:Config G n):ℂ:= if Packs A p b ∧ fusionBox A p b=u ∧ u.1 ∩ flags t U=u.2 then ∏ j∈b,(A.K j U:ℂ) else 0
def portion (p:Support n)(u : Box n)(U:Config G n):= ∑' i:Finset ℕ, grasp A t p i u U
def hook (f : Response G n)(u:Box n)(U : Config G n):= ∑ p:Support n, f p U*portion A t p u U

lemma grasp_pack {p:Support n}(q:Pack A p)(u : Box n)(U:Config G n) : grasp A t p q.val u U= if fusionBox A p q.val=u ∧ u.1∩flags t U=u.2 then ∏ i∈q.val,(A.K i U:ℂ) else 0:= by rw [grasp];simp [q.property]
-- add p var
lemma travel (p:Support n)(q:Box n)(U:Config G n): ∑' i:Pack A p,grasp A t p i.val q U= portion A t p q U:=
   tsum_subtype_eq_of_support_subset (s:={u|Packs A p u}) (f:=fun i=>grasp A t p i q U) (fun i hi=>by by_contra h; exact hi (by unfold grasp; dsimp only; rw [if_neg (fun H=> h H.1)]))
def clipSum (X:ι→ Support n)(f:ι→Config G n→ℂ):Response G n:= fun p U=> cram X (fun i=> f i U) p
variable {A t}{X:ι→Support n}{f:ι→Config G n→ℂ}{e:Letters A X ↪ ℕ}{k:ℕ→Config G n→ℂ}
lemma toll (he:∀ i,barcode A (e i)= fusionBox A (X i.1) i.2.val) (hv:∀ i U,k (e i) U=f i.1 U*grasp A t (X i.1) i.2.val (fusionBox A (X i.1) i.2.val) U) (h:∀ i,i∉Set.range e → k i=0)(hk:Dominated k):
   profile A k=hook A t (clipSum X f):=by
   funext u U
   let F (j:ℕ):= if barcode A j=u then k j U else 0
   have hs: Summable F:=by rw [show F=Set.indicator {i| barcode A i=u} (fun i=>k i U) by funext i; simp [F,Set.indicator]]; exact (hk.summable U).indicator _
   let c (x:Letters A X):= F (e x)
   have hx:Summable c:= hs.comp_injective e.injective
   have hec (x:Letters A X):c x= f x.1 U*grasp A t (X x.1) x.2.val u U:=by
      unfold c F; rw [he]; split;next h=> rw [hv,h]
      next h=> rw [grasp,if_neg (fun H=> h H.2.1),mul_zero]
   have hf: profile A k u U=∑' i,c i:=by
      unfold profile; rw [expand_eq]; change ∑' j,F j= _; refine (e.injective.tsum_eq ?_).symm; intro i hi; by_contra hp; exact hi (by unfold F; split; exact congr_fun (h i hp) U;rfl)
   have hh i: ∑' j,c ⟨i,j⟩= f i U*portion A t (X i) u U:=by
      simp_rw [hec];change ∑' j:Pack A (X i), f i U*grasp A t (X i) _ u U=_; rw [tsum_mul_left,travel]
   rw [hf,hx.tsum_sigma]; let a(i:ι):= ∑' j, c ⟨i,j⟩
   have hz:HasSum (cram X a) (∑' i,a i):= bulky X hx.sigma
   change ∑' i,a i= _; rw [← hz.tsum_eq,tsum_fintype]; refine Finset.sum_congr rfl fun i _=> ?_
   unfold cram a; simp_rw [hh]; unfold clipSum cram; rw [← tsum_mul_right]; exact tsum_congr fun j=> congr_arg (f j.val U*·) (congr_arg (fun i=> portion A t i u U) j.property)
end YM.MergeProof

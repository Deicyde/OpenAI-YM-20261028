import YM.MergeProof.BarCode
import YM.Planned.ATOM_GUARDED_LAYOUT.Guards

/-! The gas profile forgets aliases, but before returning always rebook into the same dictionary with eligibility. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{A:Activities G n}{ι I:Type*}{d:ℕ}{F:Labels.Frame G d}{o:Site n}{R:Rep G n}
    (K:Guard.Keeper R.p R.activities)
-- injective finite stocks
def cart : StockTag n ↪ ℕ where
   toFun p:= K.code (p,0)
   inj' _ _ h:= Prod.mk.inj (K.code.injective h)|>.1
lemma cardK (p:StockTag n) : barcode R.activities (cart K p)=p.val:= Prod.ext (K.support _) (K.inventory _)

-- record just profile
def profile (A:Activities G n)(f:ℕ→Config G n→ℂ) : Box n→Config G n→ℂ:=fun x U=> cram (barcode A) (fun i=> f i U) x
lemma reentry {P Q:Coefficient F n}{B:SectionData F} (h:P.exponentialEntry o B R=Q.exponentialEntry o B R)
    {σ u v w z:ℝ} (he:R.Lawful σ u v w z)(hx: Dominated P.forced)(hy:Dominated Q.forced)(hp:profile R.activities P.forced=profile R.activities Q.forced):
    P.density o B R=Q.density o B R:=by
   funext U; have hv : cram (barcode R.activities) (fun i=> P.forced i U)=cram (barcode R.activities) (fun i=> Q.forced i U):=funext fun x=> congr_fun (congr_fun hp x) U
   have hh:= chamber hv U ((dress_abs he hx).summable U) ((dress_abs he hy).summable U); unfold Coefficient.density; rw [h,dress_eq he hx,dress_eq he hy,hh]
variable (P:Coefficient F n)
def stowK : ℕ→Config G n→ℂ:=extend (cart K) (profile R.activities P.forced ∘ Subtype.val) 0
lemma stowed (p:StockTag n): stowK K P (cart K p)= profile R.activities P.forced p.val:=(cart K).injective.extend_apply ..
lemma pit {i:ℕ}(h:i∉ Set.range (cart K)): stowK K P i=0:= extend_apply' _ _ _ h

def sender (A:Activities G n)(i:ℕ):StockTag n:= ⟨barcode A i,(A.forced i).inventory_ne,(A.forced i).inventory_sup⟩
-- StockTag finite: proof in Tome if needed.
lemma stows : profile R.activities (stowK K P)=profile R.activities P.forced:=by
   funext p U
   by_cases h:p∈ Set.range (barcode R.activities)
   · obtain ⟨i,rfl⟩:=h; let u:=sender R.activities i; let f:=barcode R.activities; let c:= stowK K P
     change cram f (fun i=> c i U) u.val= _
     rw [expand_eq,tsum_eq_single (cart K u)]
     · rw [if_pos (cardK K u)]; exact congr_fun (stowed K P u) U
     intro j hz; split;swap;rfl
     rename_i e; apply congr_fun (pit K P ?_) U;rintro ⟨p,rfl⟩; exact hz (congr_arg (cart K) (Subtype.ext ((cardK K p).symm.trans e)))
   haveI : IsEmpty {i // barcode R.activities i=p}:= ⟨fun ⟨i,e⟩=> h ⟨_,e⟩⟩; unfold profile cram; rw [tsum_empty,tsum_empty]
def rack := { P with forced:=stowK K P }
lemma rack_format {H:Hol G}(h:P.Format o H R): (rack K P).Format o H R:=by
   let c:=stowK K P; suffices he : Local.ForceFormat R.p R.activities o c from
      ⟨h.smooth,h.origin,h.identity_null,h.projects,he.forcing,he.carried,he.invariant,he.supported,he.borel⟩
   constructor
   all_goals (intro i; by_cases ht:i∈ Set.range (cart K))
   all_goals first | obtain ⟨p,rfl⟩:=ht; rw [show c _= _ from stowed K P p] | rw [show c _= _ from pit K P ht]; try simp
   · intro U hu; suffices H : (R.activities.forced (K.code (p,0))).support ∩ flags R.p.threshold U=(R.activities.forced (K.code (p,0))).inventory from ⟨H,K.pass _ U H⟩ -- second input duplication? 
     by_contra hg
     apply hu;unfold profile cram; refine (tsum_congr ?_).trans tsum_zero
     intro j; by_contra he; have hp:= (h.forcing _ _ he).1; have h':barcode R.activities j.val= barcode R.activities (K.code (p,0)):= j.property.trans (cardK K p).symm -- typo
     exact hg (((congr_arg (·∩flags R.p.threshold U) (Prod.mk.inj h'|>.1)).symm.trans (hp.trans (Prod.mk.inj h'|>.2))))
   · intro hz; by_contra htY; apply hz; funext U; unfold profile cram; refine (tsum_congr ?_).trans tsum_zero; intro j; by_contra hj
     have hp:= h.carried j.val (fun ht=> hj (congr_fun ht U))
     have hY: barcode R.activities j.val= barcode R.activities (cart K p):= j.property.trans (cardK K p).symm
     exact htY ((show Local.patch _ _= Local.patch R.activities ((cart K) p) from Prod.mk.inj hY|>.1) ▸ hp)
   · intro g U; exact tsum_congr fun i=> h.invariant i.val g U
   · intro g U; rfl
   · intro U V huv htC; apply tsum_congr; intro i; have hx : barcode R.activities i.val = barcode R.activities (cart K p):= i.property.trans (cardK K p).symm; have he':=Prod.mk.inj hx|>.1; exact h.supported i.val U V (he'.symm ▸ huv) (he'.symm ▸ htC)
   · intro U V _ _; rfl
   · exact Measurable.tsum (fun i=> h.borel i.val)
   exact measurable_const
lemma keeps {u v:ℝ} (h:P.remBound o R u v): (rack K P).remBound o R u v:=by
   obtain ⟨a,b,h₁,h₂,hx,hv,hR,c,hc,hC⟩:= h
   let q:= barcode R.activities; let X(i:ℕ):= R.p.mass (q i).1 (c i); let d:=cram q c; have hz: Summable c:= hc.2.1.of_nonneg_of_le (fun i=> (hC i).1) (fun i=> R.p.loMass _ _ (hC i).1)
   let e : ℕ→ℝ:= extend (cart K) (d ∘ Subtype.val) 0; have he p:e (cart K p)=d p.val:= (cart K).injective.extend_apply ..; have hs i (h:i∉ Set.range (cart K)): e i=0:= extend_apply' _ _ _ h
   have hu p (j:{i // q i=p}): (R.activities.forced j.val).support=p.1:= Prod.mk.inj j.property|>.1
   have hCq(p): R.p.mass p.1 (d p)=cram q X p:=by -- cannot infer p?
     unfold BudgetPoint.mass d cram; rw [← tsum_mul_left]; apply tsum_congr; intro i; unfold X; change _=R.p.mass (R.activities.forced i.val).support _; rw [hu p i];rfl
   refine ⟨a,b,h₁,h₂,hx,hv,hR,e,Local.sumBudget_pass (cart K) _ ?_ (fun i h=> by rw [hs i h,BudgetPoint.mass,mul_zero]),fun i=>?_⟩
   · simp_rw [he, (fun i => show (R.activities.forced (cart K i)).support=i.val.1 from (cardK K i |> congr_arg Prod.fst)),hCq]; let p:=cram q X; have hz:=heavy q (f:=X) hc.2.1
     exact Local.sumBudget_subtype _ ⟨fun i=>tsum_nonneg (fun j=> hc.1 j.val),hz.summable,hz.tsum_eq.trans_le hc.2.2⟩
   by_cases hp:i∈ Set.range (cart K)
   · obtain ⟨p,rfl⟩:=hp; rw [he,show (rack K P).forced (cart K p)=_ from stowed K P p]; exact ⟨tsum_nonneg (fun i=> (hC i.val).1),fun U=> metric_cram q hz (fun i=> (hC i).2 U) p.val⟩
   rw [hs i hp, show (rack K P).forced i=0 from pit K P hp]; simp
end YM.MergeProof

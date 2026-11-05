import YM.MergeProof.Meringue
import YM.Push.LOCAL_SPLITTING.Raw
/-!
 Read any expression into universal palette addresses. This doesn't sum
 regular pieces on a support (could leave germs ambiguous around exact threshold).
 Keep forced profile, which suffices for reentry. Budget, measurements at equality
 preserved (angle measurements later).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Eyelet
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{d :ℕ} {F:Frame G d} {H: Hol G} {Z Q : Coefficient F n}
abbrev Region (n:Side):= {X:Support n // (0:Site n)∈X}
instance (n:Side): Nonempty (Region n):= ⟨⟨{0},Finset.mem_singleton_self _⟩⟩
abbrev Slot (n:Side) := Region n × ℕ
def key (n:Side) : ℕ ≃ Slot n:= code (Region n)
def area (n:Side)(i:ℕ) := (key n i).1.val
variable (P: Coefficient F n)

def graft (i : Eyelet.Slot n): Config G n→ℂ := if i.1.val= P.support i.2 then P.regular i.2 else 0
def bud (i:StockTag n){R: Rep G n} := profile R.activities P.forced i.val

def ageing {R:Rep G n}(K:Keeper R.p R.activities) : Coefficient F n:= ⟨P.x,area n,graft P ∘ key n,stowK K P⟩
def takes (h:∀ i:ℕ,(0:Site n)∈P.support i):ℕ↪ℕ := (⟨fun i=> (⟨P.support i,h i⟩,i),fun _ _ he=> Prod.mk.inj he|>.2⟩ : ℕ↪Eyelet.Slot n).trans (key n).symm.toEmbedding

variable {R:Rep G n} (K : Keeper R.p R.activities)
set_option quotPrecheck false
local notation "Pat"=> ageing P K
local notation "U!"=> R.activities
local notation "π"=> R.p
local notation "a!"=> (0:Site n)
lemma bunch (h:∀ i:ℕ,a!∈P.support i) (i): area n (takes P h i) = P.support i ∧ graft P (key n (takes P h i))=P.regular i:=by
   have he:key n (takes P h i)=(⟨P.support i,h i⟩,i):= (key n).apply_symm_apply _; exact ⟨congr_arg (fun x : Eyelet.Slot n=> x.1.val) he,by rw [he,graft]; simp⟩
lemma sleeps (h:∀ i:ℕ,a!∈P.support i) (i)(he:i∉Set.range (takes P h)): graft P (key n i)=0:=by
   refine if_neg (fun hx=> he ?_); let q := key n i; refine ⟨q.2,(key n).injective ?_⟩; erw [(key n).apply_symm_apply]; exact Prod.ext (Subtype.ext hx.symm) rfl
lemma hot (P:BudgetPoint)(X:Support n){o:Site n}: P.Regular X (0:Config G n→ℂ)∧ P.supBounds o X (0:Config G n→ℂ) 0:=by simpa using regular_bound_sum (P:=P) (o:=o) (s:=X) (∅:Finset Unit) (fun _=> 0) (fun _=>0) (by simp)
lemma dye (h:P.Format 0 H R): (ageing P K).Format 0 H R:=by
   have hp:= rack_format K P h; have he i:=((key n i).1.property)
   have hr(i):RegFit R 0 d H ((ageing P K).support i) ((ageing P K).regular i):=by
     by_cases hv:i∈ Set.range (takes P h.origin)
     · obtain ⟨j,rfl⟩:= hv; let i:= takes P h.origin j; obtain ⟨hA,hB⟩:= bunch P h.origin j; change RegFit _ _ _ _ (area n i) (graft P (key n i)); rw [show area n i= _ from hA,show graft P (key n i)= _ from hB]; exact ⟨h.smooth _,h.origin _,h.identity_null _,h.projects _⟩
     rw [show (Pat).regular i=0 from sleeps P h.origin i hv]; exact ⟨(hot (G:=G) (o:=a!) _ _).1,he i,rfl,fun _ _=>⟨contDiffAt_const,fun k _=> by change iteratedDeriv k (fun _=>(0:ℂ)) 0=0; simp⟩⟩
   exact ⟨fun i=>(hr i).smooth,he,fun i=>(hr i).unit_null,fun i=>(hr i).proj,hp.forcing,hp.carried,hp.invariant,hp.supported,hp.borel⟩
lemma priced {u t:ℝ}(h:∀ i:ℕ,a!∈P.support i)(hp:P.remBound 0 R u t): (Pat).remBound a! R u t:=by
   obtain ⟨a,b,hA,hB,h₁,h₂,⟨e,h₃,h₄⟩,E,hc,hC⟩:= keeps (o:=a!) K P hp
   let f:= extend (takes P h) e 0; have he i: f (takes P h i)=e i:= (takes P h).injective.extend_apply ..
   have hs i (hi:i∉range (takes P h)): f i=0:= extend_apply' _ _ _ hi
   refine ⟨a,b,hA,hB,h₁,h₂,⟨f,sumBudget_pass (takes P h) _ ?_ (fun i hi=>by rw [hs i hi,BudgetPoint.mass,mul_zero]),fun i=>?_⟩,E,hc,hC⟩
   · simp_rw [show ∀ i,(ageing P K).support (takes P h i)=P.support i from fun i=>(bunch P h i).1, he]; exact h₃
   by_cases hv:i∈Set.range (takes P h)
   · obtain ⟨j,rfl⟩:=hv; rw [show (ageing P K).regular _=P.regular j from (bunch P h j).2,show (ageing P K).support _=P.support j from (bunch P h j).1,he]; exact h₄ j
   rw [hs i hv, show (ageing P K).regular i=0 from sleeps P h i hv]; exact (hot ..).2
lemma respect (h:∀ i:ℕ,a!∈P.support i)(B:SectionData F): (Pat).exponentialEntry 0 B R=P.exponentialEntry 0 B R:=by
   let e:=takes P h; funext U; let z i:= (Pat).maskedTerm R i U
   have he:z∘ e=fun i=> P.maskedTerm R i U := funext fun i=>by change masked _ (area n _) (graft P (key n _)) U=_; rw [show area n (takes P h i)=P.support i from (bunch P h i).1, (bunch P h i).2]; rfl
   unfold Coefficient.exponentialEntry; rw [← he]; refine congr_arg (P.x 0+_ + ·) ((e.injective.tsum_eq (f:=z) ?_)|>.symm); intro i hi; by_contra hn; apply hi
   unfold z Coefficient.maskedTerm; rw [show (ageing P K).regular i=0 from sleeps P h i hn]; exact congr_fun (map_zero (Local.maskLinear _ _)) _
lemma mirrors {u v μ δ C a b :ℝ}(h:∀ i:ℕ,a!∈P.support i)(hp:P.remBound 0 R u v)(hr:R.Lawful μ δ C a b)(B:SectionData F): (Pat).density 0 B R=P.density 0 B R:= reentry (respect P K h _) hr (rem_dominated (priced P K h hp)) (rem_dominated hp) (stows K P)

end YM.UVExtension.Eyelet

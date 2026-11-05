import YM.OPE.Trees.Repairs
import YM.OPE.Trees.Audience
/-!
# Direct and nested products

`factorization` is the actual finite intermediate-channel sum, always using
this same basis frame. It also applies to a redacted tree with its current
input slots (set `live`) as leaves. Positions / labels of children are read
on this *same* organization of the tree by the product of the same `ope`
coefficients. Scales are not arguments to the channel convention, but to
pricing, so a successive replacement doesn't require changing earlier choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Finset Filter
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{L:Register G}{S:Table L} {H:DiffPlan S}
    (P:Prescription H)(A:Table L)
variable {I J K:Type}[Fintype I][Fintype J][Fintype K](s:Arboreal I)(a b:Finset I) (x:I→ E4)(p:I→ L.Token)(i j:I)(w:Mode H)(y:J→ E4)(q:J→L.Token)

def coalesce := P.ope w (crop x b) (crop p b) (x i)
-- arg order b x p i w

def whole := observe A (beside (crop x b) y) (beside (crop p b) q)
def pickOne := observe A (beside (sole (x i)) y) (beside (sole (P.letter w)) q)
def flux (n:ℕ) := whole A b x p y q - P.truncated A n (crop x b) (crop p b) (x i) y q
lemma flow_eq (n) : flux P A b x p i y q n = whole A b x p y q - ∑ w ∈ bands H n, coalesce P b x p i w * pickOne P A x i w y q:= rfl

/-- postcomposition supplies intermediate labels only in the active subtree;
no horizon at the root (whose output is `w`). Outside intermediate vertices f=w
as a placeholder, preserving a single sum and no multiplicities on absent edges. -/
def casting (s:Arboreal I)(a:Finset I)(d:I→ℕ)(w: Mode H) := Fintype.piFinset (fun i:I=> if i∈ s.middle a then bands H (d i) else {w})
lemma casts {D:I→ℕ}{f:I→Mode H} : f∈ s.casting a D w↔ ∀ i:I,(i∈ s.middle a→f i∈ bands H (D i)) ∧ (i∉ s.middle a→ f i=w):=by
    rw [casting,Fintype.mem_piFinset]; refine forall_congr' (fun i=> ?_); by_cases h:i∈ s.middle a <;> simp [h]
-- isolate compound calculations
variable (f:I→ Mode H)
def audition : I→ L.Token:= fun i=> if i∈ a then P.letter (f i) else p i
def eventAt := coalesce P (s.kids i) x (audition P a p f) i (f i)
def ensemble := ∏ i∈ a,eventAt P s a x p i f
def factorization (D:I→ℕ) := ∑ f∈ s.casting a D w, ensemble P s a x p f

lemma coalesce_labels {p':I→ L.Token}(he:∀ i∈ b,p i=p' i): coalesce P b x p i w=coalesce P b x p' i w:=by rw [coalesce,coalesce,show crop p b=crop p' b from funext (fun i=> he i.val i.property)]

namespace Nest
variable {s a b f i p}
lemma as_leaf (h:s.Border a i)(hi:i∈a) : eventAt P s a x p i f=coalesce P (s.inputs a i) x p i (f i):=by
    unfold eventAt; rw [next_leaves h hi]; exact coalesce_labels P _ _ _ i _ (fun i hi=> if_neg (show i∉a from fun hx=> useful hi (h i hx (Anc.child hi))))
lemma singleton_for (h:s.Active a)(he:s.middle a=∅)(hf:f s.root=w) : ensemble P s a x p f=coalesce P (s.live a) x p s.root w:= by
    have h' : s.Border a s.root:= by intro i hi h; rw [rootAlone (by assumption) he,mem_singleton] at hi; exact hi
    unfold ensemble; -- only cardinal one
    rw [prod_eq_single_of_mem _ h.main (by intro i hi hh; exact (hh (h' i hi (s.closure i))).elim), as_leaf P x h' h.main,s.top_roots,hf]
lemma staging (h:s.Active a)(hv:s.middle a=∅)(D:I→ℕ) : factorization P s a x p w D = coalesce P (s.live a) x p s.root w :=by
    let f (_:I):= w; unfold factorization; have he:s.casting a D w={f}:= by ext v; rw [s.casts,mem_singleton]; simp [hv,funext_iff,f]
    rw [he,sum_singleton]; exact singleton_for P x _ h hv rfl
end Nest
end YM.OPE.Arboreal

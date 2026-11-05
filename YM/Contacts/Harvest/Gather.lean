import YM.Contacts.Harvest.Formula
import Mathlib.Analysis.Normed.Ring.InfiniteSum
/-!
# Simultaneous shell choices in every open group

Requires no re-registration of the admissible fields. `beckon` with all output cuts and test
masks recombines into `windings` with this election preserved while visiting all shell indices.
Supplies arbitrary order *and absolutely summable integral norms* of the kernels appearing as these
joint annular terms in those disjoint groups. May appeal to L1 convergence, not pointwise products.
Doesn't assert Cartesian finite pieces don't need cancellation among alternative 'cumulant' routes
(inside the canonical proper-stratum formula); the arity recursion has kept sums and the original
subtractions throughout.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Harvest.Route
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Layers Ordered
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory
variable {E X W I : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup X][NormedSpace ℂ X]
variable {G: Gauge} {C: Family G}{F: Extraction.Order}{S : Table C.book} {Z: Final C F S}
variable {k : ℕ} {d : Fin k→ℕ}{g : Normal.Group k} {P : E→ₗᵢ[ℝ] Points k} {Q : Pieces g} {γ : ℝ}
local notation "GN" => Normal.Group k

-- bookkeeping for shells: output guaranteed permutation independent via the integral, order explicit in index tuple.
def slideTo (f : Menu k)(i : Normal.Group k) (n : ℕ) := Function.update f i ((f i).flip n)
@[simp] lemma slid (f : Menu k)(i : GN)(n : ℕ): slideTo f i n i= Ballot.adjust (f i).vote (some n):= Function.update_self ..
lemma unslipped (f : Menu k) {i j : GN} (h : i≠j)(n : ℕ): slideTo f j n i=f i:= Function.update_of_ne h ..
def Centered (Q : Pieces g) (f : Menu k)(L : List Q.parts) := L.Nodup ∧ ∀ i∈L, (f i.val).slice=none ∧ 1 < i.val.card
-- lowercase to avoid shadow centered.

def Overtures {X : Type} : List X → Type
| []=> Unit
| _::k=> ℕ × Overtures k
private def looseEq (j : Q.parts)(L : List Q.parts) : Overtures (j::L) ≃ (ℕ × Overtures L) := Equiv.refl _ -- reduction

def march (f : Menu k) : (L : List Q.parts)→ Overtures L→ Menu k
| [],_=> f
| j::k, a => march (slideTo f j.val (show ℕ × Overtures k from a).1) k (show ℕ × Overtures k from a).2

def concession {X : Type} (γ : ℝ) : (k : List X) → Overtures k→ℝ
| [],_ => 1
| _::k, a => (dyad (show ℕ × Overtures k from a).1)^γ * concession γ k (show ℕ × Overtures k from a).2

variable (f : Menu k) (L : List Q.parts)(i : Q.parts)
lemma knows (j : Q.parts) (h : j∈ L) (he : Centered Q f L) : 1< j.val.card:=(he.2 j h).2
lemma head_free (he : Centered Q f (i::L)): (f i.val).slice=none∧1< i.val.card:=he.2 i (List.mem_cons_self ..)
lemma slip_centered (he : Centered Q f (i::L))(n : ℕ) : Centered Q (slideTo f i.val n) L:= by
   refine ⟨(List.nodup_cons.mp he.1).2,fun j hj=>?_⟩; rw [unslipped f (Subtype.val_injective.ne (show j≠i from fun h=> (List.nodup_cons.mp he.1).1 (h ▸ hj)))]; exact he.2 j (List.mem_cons_of_mem _ hj)
lemma slip_fee (he : Centered Q f (i::L))(n : ℕ)(γ : ℝ): shadow Q (slideTo f i.val n) γ=shadow Q f γ * (dyad n)^γ:= by
   rw [from_behind i, from_behind i f,bare ((head_free f L i he).1),mul_one, kick,if_neg (not_le.mpr ((head_free f L i he).2)),slid]; congr 1; exact Finset.prod_congr rfl fun j hj=> by unfold kick; rw [unslipped f (Finset.mem_erase.mp hj|>.1)] -- ambiguous
lemma shadows_centered (he : Centered Q f L)(n : Overtures L) : shadow Q (march f L n) γ= shadow Q f γ * concession γ L n:=by
    induction L generalizing f with
    | nil=> rw [march,concession,mul_one]
    | cons i p ih=> rw [march,ih _ (slip_centered f p i he _),slip_fee f p i he,concession,mul_assoc]
lemma fees_overtures (he:0<γ) : Summable (concession γ L) := by
    induction L with
    | nil=> exact (hasSum_fintype (fun _:Unit=> (1:ℝ))).summable
    | cons i p ih=>
      change Summable (fun x : ℕ × Overtures p=> (dyad x.1)^γ * concession γ p x.2)
      exact summable_mul_of_summable_norm (geometric_dyadic he).norm ih.norm

variable (r : Route P Q I W) (M : Devices Z.sector.derivatives) (T : W→ Cells S d) (D : Reader E W X k Z.sector.derivatives)
-- equations before actually changing the election. No assumption that head vote is none.
lemma votes_same (n : ℕ) (w:W) : (r.components M T w).slate i.val (slideTo f i.val n i.val)=(r.components M T w).slate i.val (f i.val) := by rw [slid]; rfl
lemma background (b:Ballot) (v:Way d i.val) (w z) : r.select M T D i v (Function.update f i.val b) w z=r.select M T D i v f w z:= by
    unfold select System.absentee System.attend; rw [show System.back P _ _ (Function.update f i.val b) Q i=_ from (?_)] -- meta
    unfold System.back; apply Ordered.eq_product; intro j hj; simp_rw [System.present,Function.update_of_ne (Finset.mem_erase.mp hj).1]

lemma adjusts (h : 1 < i.val.card) (n : ℕ) w z x : r.windings M D T (slideTo f i.val n) w z x= ∑ v∈ (r.components M T w).slate i.val (f i.val), r.beckon M T D i (d:=d) v f w z n x:= by
   rw [r.decomposition M T D i h, votes_same, slid]; -- `Function.update` inside select occurs
   refine Finset.sum_congr rfl fun v hv=> ?_; unfold slideTo; rw [background (d:=d)]; rfl

variable [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure]
variable [CompleteSpace X][Fintype I]
variable {M r T D} {B : W→ℝ}(H : Loan Z M r B D)(hT : Given T)(hm : r.Authority M d) (A : Services C F S)
variable {z : SmoothTests E}{w : W}
include H hT hm A
lemma canopy (h : tsupport z.val ⊆ r.stage w)(he : Centered Q f L) :
    (∀ n:Overtures L, Integrable (r.windings M D T (march f L n) w z)) ∧
      Summable (fun n:Overtures L=>∫ x, ‖r.windings M D T (march f L n) w z x‖) := by
   obtain ⟨γ,hγ,he',_⟩:= desired_budget 1 one_pos Q; obtain ⟨C,hc,h'⟩:= achieved M r T D A H hm hT he'; obtain ⟨m,hp,hℱ⟩:=budget_for_test w z r h (stairs d Q)
   let t:= shadow Q f γ; let R:= C*m*r.bag d B w (generosity Q γ); let K(n:Overtures L):= R*(t*concession γ L n)
   have hX(n:Overtures L) : Dust (r.windings M D T (march f L n) w z) (K n):= by have hg:= h'.estimates (march f L n) w z h hℱ; rw [shadows_centered f L he] at hg; exact hg
   exact ⟨fun n=>(hX n).integrated,Dust.norm_paid hX (((fees_overtures L hγ).mul_left t).mul_left R)⟩
variable [NormedSpace ℝ X]
lemma dawn (hh : 1 < i.val.card)(h : tsupport z.val ⊆ r.stage w)(hp : (f i.val).slice=none):
     HasSum (fun n=>∫ x,r.windings M D T (slideTo f i.val n) w z x) (∫ x,r.windings M D T f w z x):= by
    let Y:=r.components M T w; let p:Finset (Way d i.val):= Y.slate i.val (f i.val); let t(v:Way d i.val):= r.beckon M T D i v f w z; let F(v:Way d i.val):= r.select M T D i v f w (r.net i v w z); have H'(v:Way d i.val):=emphatic i hh v f w z H hT hm A h; let U:= ∑ v∈p,∫ x,F v x
    have eL(n:ℕ):(∫ x,r.windings M D T (slideTo f i.val n) w z x)= ∑ v∈p,∫ x,t v n x:= by rw [funext (r.adjusts f i M T D hh n w z)]; exact integral_finsetSum p (fun v _=> (H' v).2.1 n)
    rw [funext eL, show r.windings M D T f w z=(fun x=>∑ v∈p,F v x) from funext (fun x=> by have hh:=r.decomposition M T D i hh f w z x; simp_rw [hp] at hh; exact hh),integral_finsetSum p (fun v _=> (H' v).1)]; exact hasSum_sum (fun v _ => (H' v).2.2.2.1) -- mathlib
lemma cartesian (h : tsupport z.val ⊆ r.stage w) (he : Centered Q f L) :
    HasSum (fun n:Overtures L=> ∫ x, r.windings M D T (march f L n) w z x) (∫ x,r.windings M D T f w z x):= by
   induction L generalizing f with
   | nil=> change HasSum (fun _:Unit=>∫ x,r.windings M D T f w z x) _; simpa only [Fintype.sum_unique] using! hasSum_fintype (fun _:Unit=>∫ x,r.windings M D T f w z x)
   | cons i p ih =>
      let V := march f (i::p); let t(v:Menu k):=∫ x,r.windings M D T v w z x; let F(x:Overtures (i::p)):= t (V x)
      have hm' : Summable F:= (canopy f (i::p) H hT hm A h he).2.of_norm_bounded (fun i=> norm_integral_le_integral_norm _)
      let U:= ∑' n,F n; let p'(t:ℕ × Overtures p):= F ((looseEq i p).symm t); have heL : HasSum p' U:= (looseEq i p).symm.hasSum_iff.2 hm'.hasSum
      have hs(n:ℕ) : HasSum (fun z:Overtures p=>p' (n,z)) (t (slideTo f i.val n)):= ih (slideTo f i.val n) (slip_centered f p i he n)
      have hU:= HasSum.prod_fiberwise heL hs; change HasSum F (t f); rw [show t f= U from (dawn f i H hT hm A (head_free f p i he).2 h (head_free f p i he).1).unique hU]; exact hm'.hasSum
end YM.Contacts.Harvest.Route

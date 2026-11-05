import YM.RG08.Isles.Fruit
import YM.RG08.Trickle.Fleet

/-! # Cofinal from the finite common denominator transfer. Covers rank zero
now (scalar appears WITH marker at fixed root), all contacts in formal periodization.
These lemmas to be applied after lifting link alphabet incl crossing; read every f
before projecting. Also BOUNDED polynomial positions, never a density estimate.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Hatch
open Jetty Skiff Lattice Isles Forms Pert.Bulk Function Finset Laurent Filter
open scoped Topology BigOperators ENNReal Classical
variable {I J:Type}{n m d b:ℕ}{σ C B:ℝ}{h:0<σ}

def stance (I:Type):Loom (Market I):=⟨Isles.abroad,abroad_nn⟩
def crest (P:Side)(I:Type):Loom (Cove P I):=⟨Isles.native,native_nn⟩
lemma spindled (I:Type):fits (stance I) (carpet I):=fun u v=> (show length v.1≤length u.1+sep u.1 v.1 from by
  have he:=sep_triangle v.1 u.1 0
  unfold sep at *;simp only [sub_zero,show u.1-v.1=-(v.1-u.1) from (neg_sub ..).symm,length_neg] at *; linarith only [he])
lemma crested (P:Side)(I:Type):fits (crest P I) (shore P I):=fun u v=> (Isles.region v u).trans_eq (by rw [(shore P I).left,add_comm,crest])
lemma decay (l:Loom I){F:Pack n I}(hv:Lyrics F)(hs:Sings l d h F C)(hc:0≤C)(f:Pearl)(x): |F x f| ≤ C*beam d h f*Real.exp (-σ*l.cage x):=by
 have he : ENNReal.ofReal (|F x f| *Real.exp (σ*l.cage x)) ≤ ENNReal.ofReal (C*beam d h f):=by
    rw [ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_mul hc];apply le_trans (mul_le_mul_left (purse_gives _ _ (hv x) _) _)
    rw [mul_comm (purse d h (F x)),mul_assoc]; change _* gems l d h F x ≤ _;rw [mul_comm (ENNReal.ofReal _)];exact mul_le_mul_left (hs.point x) _ -- rw ambiguity
 rw [neg_mul,Real.exp_neg,←div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]
 exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc (beam_nn ..))).mp he

abbrev Span (n:ℕ)(I:Type):=(m:ℕ)→Pack n (colony I m)
structure Reed (d:ℕ)(h:0<σ)(C:ℝ)(P:Pack n (Market I))(Q:Span n I):Prop where
 cost : 0≤C
 openP : Lyrics P
 openQ (i:ℕ): Lyrics (Q i)
 lead : Sings (stance I) d h P C
 back (i:ℕ): Sings (crest (chain i) I) d h (Q i) C
 front (f:Pearl)(z:Tape n (Market I)):Tendsto (fun i=>Q i (port (chain i) ∘ z) f) atTop (𝓝 (P z f))

variable {P:Pack n (Market I)}{Q:Span n I}
theorem Reed.mono {τ:ℝ}{ht:0<τ}(hs:Reed d h C P Q)(hc:τ≤σ)(H:d≤b)(he:C≤B):Reed b ht B P Q:=⟨hs.cost.trans he,hs.openP,hs.openQ,hs.lead.mono hc H (fun _=>le_rfl) he,fun i=>(hs.back i).mono hc H (fun _=>le_rfl) he,hs.front⟩
lemma Reed.solo (I:Type)(h:0<σ)(hC:0≤C):Reed d h C (0:Pack n (Market I)) 0:=⟨hC,hush,fun _=>hush,tin,fun _=>tin,fun _ _=>tendsto_const_nhds⟩
lemma Reed.scale (hs:Reed d h C P Q)(a:ℝ):Reed d h (|a| *C) (a • P) (fun i=>a • Q i):=⟨mul_nonneg (abs_nonneg _) hs.cost,hs.openP.smul _,fun i=>(hs.openQ i).smul _,hs.lead.smul _,fun i=>(hs.back i).smul _,fun f z=> (hs.front f z).const_mul _⟩
lemma Reed.add {P' Q'}(hs:Reed d h C P Q)(hh:Reed d h B P' Q'):Reed d h (C+B) (P+P') (fun i=>Q i+Q' i):=⟨add_nonneg hs.cost hh.cost,hs.openP.add hh.openP,fun i=>(hs.openQ i).add (hh.openQ i),hs.lead.add hh.lead hs.cost hh.cost,fun i=>(hs.back i).add (hh.back i) hs.cost hh.cost,fun f x=> (hs.front f x).add (hh.front f x)⟩
lemma Reed.collect (h:0<σ){C:J→ℝ}{P:J→Pack n (Market I)}{Q:J→Span n I}(S:Finset J)(H:∀ i∈S,Reed d h (C i) (P i) (Q i)) : Reed d h (S.sum C) (S.sum P) (fun i=>∑ j∈S,Q j i):=by
 induction S using Finset.induction_on with
 | empty=>simp only [sum_empty];exact Reed.solo I h le_rfl
 | insert _ _ hi ih=>simp_rw [sum_insert hi];exact (H _ (mem_insert_self ..)).add (ih (fun i he=> H _ (mem_insert_of_mem he)))
lemma Reed.accrue {P:J→Pack n (Market I)}{Q:J→Span n I}(S:Finset J)(he:∀ i∈S,∃ C,Reed d h C (P i) (Q i)):∃ C,Reed d h C (S.sum P) (fun i=>∑ j∈S,Q j i):=by
 choose C hC using he
 let B (i:J):ℝ:=if h:i∈S then C i h else 0
 exact ⟨_,show Reed d h (S.sum B) _ _ from Reed.collect h S (fun i hi=>by simpa [B,hi] using hC i hi)⟩
lemma Reed.symm (hs:Reed d h C P Q): Reed d h C (breeze P) (fun i=>breeze (Q i)):=by
 refine ⟨hs.cost,hs.openP.breeze,fun i=>(hs.openQ i).breeze,hs.lead.breeze hs.cost,fun i=>(hs.back i).breeze hs.cost,fun f z=>?_⟩
 simp only [breeze,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,pattern]; refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _=>?_); exact hs.front f (z ∘ i)
end YM.RG08.Hatch

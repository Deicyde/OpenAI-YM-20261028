import YM.RG08.Jetty.Chests
import YM.RG08.Forms.Weld

/-! # Whole-tape marked recipe billing

Use for connected cover operations, replacement of stencils, etc. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Skiff
open Jetty Forms Pert.Bulk Function Packets Finset
open scoped ENNReal Classical BigOperators Topology ContDiff
variable {I J T:Type}{l:Loom I}{n d:ℕ}{σ B C:ℝ}{h:0<σ}
abbrev Blue (n:ℕ)(I T:Type):= Tape n I→T→NoteX
variable {P:Blue n I T}
def Bare (P:Blue n I T):Prop:=∀ x t,Voice (P x t)
def fruit (l:Loom I)(d:ℕ)(h:0<σ)(P:Blue n I T)(x:Tape n I)(t:T):=purse d h (P x t)*weft l σ x
def CableCar (l:Loom I)(d:ℕ)(h:0<σ)(P:Blue n I T)(C:ℝ≥0∞):= (∑' x:Tape n I,∑' t,fruit l d h P x t)≤C
def decker (P:Blue n I T):Pack n I:=fun x f=> ∑' t,P x t f
lemma CableCar.sings (he:CableCar l d h P (ENNReal.ofReal C)):Sings l d h (decker P) C:=he.trans' (ENNReal.tsum_le_tsum fun x=>by
  rw [show (∑' t,fruit l d h P x t)=_ from ENNReal.tsum_mul_right];exact mul_le_mul_left (purse_sum d h (P x)) _)
lemma CableCar.basket (he:CableCar l d h P (ENNReal.ofReal C))(x:Tape n I): (∑' i:T,purse d h (P x i))≠⊤:=by
 apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
 apply LE.le.trans (b:= ∑' i, fruit l d h P x i) _ ((ENNReal.le_tsum x).trans he)
 exact ENNReal.tsum_le_tsum fun i=>le_mul_of_one_le_right (zero_le (a:=purse d h _)) (knits x h.le)
lemma CableCar.deep (he:CableCar l d h P (ENNReal.ofReal C))(hv:Bare P)(x:Tape n I)(f:Pearl):Summable (fun t=>‖P x t f‖):= audible d h _ (hv x) (he.basket x) f
lemma CableCar.lyric (he:CableCar l d h P (ENNReal.ofReal C))(hv:Bare P):Lyrics (decker P):=fun x=>choir d h (P x) (hv x) (he.basket x)

-- Transparency helpers
lemma wind (l:Loom I)(B:ℝ)(x:Tape n I){r:ℝ}(hs:B*l.cage x≤r): weft l B x≤ ENNReal.ofReal (Real.exp r):= ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hs)
lemma stamp (a B C:ℝ):ENNReal.ofReal |a| * ENNReal.ofReal (Real.exp (B+C))= bill a B * ENNReal.ofReal (Real.exp C):=by unfold bill;rw [Real.exp_add, ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_mul (Real.exp_pos _).le,mul_assoc]
lemma gifts {m:ℕ}{L:Loom J}(d:ℕ)(h:0<σ)(F:Pack m J)(x:Tape m J)(y:Tape n I)(a r:ℝ)(ha:σ*l.cage y ≤ σ*L.cage x+r):
 purse d h (a • F x) * weft l σ y ≤ bill a r * gems L d h F x:=by
 apply (mul_le_mul' (purse_smul ..) (wind _ _ _ ha)).trans_eq
 unfold gems weft; rw [add_comm (σ*L.cage x)]; unfold bill
 rw [Real.exp_add, ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_mul (Real.exp_pos _).le]; ac_rfl
end YM.RG08.Skiff

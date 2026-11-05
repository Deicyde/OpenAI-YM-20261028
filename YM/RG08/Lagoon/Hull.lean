import YM.RG08.Lagoon.Pen
import YM.RG08.Clef.Bravo

/-!
# Step normalization and coefficient data
The step uses the common denominator in the signed coefficient sums.
-/
noncomputable section
namespace YM.RG08.Lagoon
open Jetty Laurent Function Finset Lattice Pert.Bulk
open Weald Skiff Forms Gallery Clef Room Nacre
open RG Stationary Quarry Hatch
open Planned.PrimaryIntegral295.Place Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical PowerSeries ContDiff
set_option autoImplicit false
variable {s d n l:ℕ}{σ τ B:ℝ}{h:0<σ}{k:0<τ}{I J:Type}
variable (L:Side)(o:Site L)

def tilt (x:E4)(a:ℝ)(P:Pack n I):Pack n I:=fun i f=>P i (aisle a x f)
def dip :ℝ:= (L.val:ℝ)⁻¹
def ahead :E4:= dip L • seat (Lattice.lift o)
lemma dipping :0 < dip L ∧ dip L≤1:=⟨unitStep_pos L,unitStep_le ..⟩
lemma heading :‖ahead L o‖≤4:=by
 rw [ahead,norm_smul,Real.norm_eq_abs,abs_of_pos (dipping L).1]; refine (mul_le_mul_of_nonneg_left (shade_seat (lift o)) (dipping L).1.le).trans ?_;rw [mul_comm,dip,←div_eq_mul_inv];exact length_lift L o
def flow (P:GrainS I):GrainS I:=fun i n=> tilt (ahead L o) (dip L) (P i n)
lemma tilts (P:Pack n I)(ht:Lyrics P):Lyrics (Lagoon.tilt (ahead L o) (dip L) P):=fun i=>⟨fun x y=> by unfold Lagoon.tilt;rw [map_add,(ht i).plus],fun a x=>by unfold Lagoon.tilt;rw [map_smul,(ht i).hum]⟩
lemma sales (L:Side)(o:Site L){d:ℕ}{S:Jetty.Loom I}(P:Pack n I)(hp:Lyrics P)(hv:Sings S d h P B)(k:0<τ)(hk:τ≤σ):Sings S d k (Lagoon.tilt (ahead L o) (dip L) P) (Real.exp (4*τ)*B):=by
 calc
  _ ≤ ∑' x,ENNReal.ofReal (Real.exp (4*τ))*gems S d h P x:=ENNReal.tsum_le_tsum fun i=> ?_
  _ ≤ _ :=by rw [ENNReal.tsum_mul_left,ENNReal.ofReal_mul (Real.exp_pos _).le];gcongr;exact hv
 unfold gems;rw [←mul_assoc];apply mul_le_mul'
 · -- need transformed test with output hτ, evaluation input h: yes W f where output Test beam d k≤1. beam d h W ≤1...
   apply purse_le _ _
   intro f hf
   apply (purse_gives _ _ (hp i) (aisle (dip L) (ahead L o) f)).trans
   rw [mul_comm];gcongr
   have he:= spending (d:=d) (h:=h) k (ahead L o) (dip L) (show |dip L|≤1 from (abs_of_pos (dipping L).1).trans_le (dipping L).2) (show τ*|dip L|≤σ by rw [abs_of_pos (dipping L).1]; nlinarith only [hk,k,(dipping L).2]) f
   apply he.trans
   have hT:= heading L o
   apply (mul_le_of_le_one_left (Real.exp_pos _).le hf).trans (Real.exp_le_exp.mpr ?_)
   rw [mul_comm 4]; exact mul_le_mul_of_nonneg_left hT k.le
 unfold weft;gcongr;exact S.cage_nn i
lemma flowing [Fintype I](P:GrainS (Market I))(hP:Permit d l P):Permit d l (flow L o P):=by
 constructor
 · intro e n hi; exact hP.lit e n (fun H=>hi (by unfold flow Lagoon.tilt;rw [H];rfl))
 · intro f e n; exact hP.fine (aisle (dip L) (ahead L o) f) e n
 intro e n;obtain ⟨hV,σ,h,B,H,hY⟩:=hP.price e n; exact ⟨tilts L o (P e n) hV,σ,h,_,mul_nonneg (Real.exp_pos _).le H,sales L o _ hV hY h le_rfl⟩
lemma flagging {G:Gauge}(P:GrainS (Ed G Cover))(hp:Calls l P):Calls l (flow L o P):=fun x a b d=>hp (aisle (dip L) (ahead L o) x) a b d

variable {G:Gauge}(T:RG.Patch)(K:RG.KernelChoices)(A B:Precision.Bed)(C:Mount.Castle G)(Z:Precision.ChartRatio G)
-- name check

def bustle (H:T.Branches K G)(d l:ℕ)(P:GrainS (Ed G Cover)):GrainS (Ed G Cover):=(((T.L.val:ℝ)^d)/Fintype.card (Site T.L)) • ∑ i:Site T.L, carrier T K A C Z H l (flow T.L i P) i
-- use d maybe horizon h; normally stencil weight l attached. preserve order

theorem Lobby (H:T.Branches K G)(J:Foyer T K A B C Z)(g:ℕ)(P:GrainS (Ed G Cover))(he:Permit d l P)(hp:Calls l P)(w:ℕ→ℝ):
 let S:=bustle T K A C Z H g l P
 ; Permit d l (Clef.film w S) ∧ Calls l (Clef.film w S):=by
 intro S
 let F(i:Site T.L):GrainS (Ed G Cover):=carrier T K A C Z H l (flow T.L i P) i
 have hI (i):Permit d l (F i)∧Calls l (F i):=Weald.self T K A B C Z i H _ J (flowing T.L i P he) (flagging T.L i P hp)
 have hT {I:Type}(F : I→ GrainS (Ed G Cover))(u:Finset I)(hF:∀ i,Permit d l (F i)∧Calls l (F i)):Permit d l (∑ i∈u,F i)∧ Calls l (∑ i∈u,F i):=by
    induction u using Finset.induction_on with
    | empty=> rw [sum_empty];exact ⟨Permit_hush ..,Calls_hush⟩
    | @insert i u hh ih=> rw [sum_insert hh];exact ⟨Permit_add (hF i).1 ih.1, by simpa using (Calls_lin (hF i).2 ih.2 (1:ℝ))⟩
 obtain ⟨hA,hP⟩:=hT F univ hI
 have hS:Permit d l S:= Permit_smul hA _
 exact ⟨Permit_lend w hS,royalty w (Calls_smul hP _) hS.lit⟩
end YM.RG08.Lagoon

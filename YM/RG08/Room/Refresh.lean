import YM.RG08.Room.Saloon
import YM.RG08.Glyph.Balance

/-!
# Coarse formal invariance at finite regulator from centered germ identities, including
positive-degree frame changes on the coarse variables. Assume identities BEFORE gaussian and
preservation of flat quadratic/aperture, not same statement after step. This version keeps
all field-independent terms in the connected relation; only assert if density equivalence also
includes them. See panel version for Markov cancellation. Quadratic included here as Q (NEGATIVE
exponent) in Boil & transformation input diff; output external quadratic also negative.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Room
open Glyph Cloud Finset Function Steam Forms
open scoped PowerSeries BigOperators Topology Classical
variable {I J:Type}[Fintype I][Fintype J]
namespace Haze
variable {H:Haze I}{S:Haze J}

omit [Fintype I][Fintype J] in
lemma abroad_rise {f:Port I}(h:Abroad H.foam f)(hp:tiny f):Abroad H.foam (rise f):=by
 intro i hi;rw [show pin i (rise f)=_ from lift_rise _ hp,h i hi,mul_zero]
omit [Fintype I][Fintype J] in
lemma belt_tiny {f:Port I}(h:tiny f)(x:I→Port J):tiny (belt x f):=by unfold tiny at *;change tap 0 (belt _ _)=_;rw [rim];unfold tap;rw [h,map_zero]

-- Construct side ledgers, separate raw symbols from centered & padded. Include quadratic in
-- negative sign, powers of g absorbed, mod higher positive powers not used here.
structure Ledger (I R:Type)[Fintype R] where
 theater : Haze I
 K : Inn I -- exponent internal quadratic centered
 P : I→I→ℝ
 κ : Port I -- exponent external cost (typically quadratic coarse K including sign); doesn't
             -- depend on integrated vars; level identification may only require κ in sum.
 input : Grain R -- V, AFTER factoring entire integrated square before shift
 prices : Line R
 view : R→I→ℝ -- total shift linear; survivor & heat pull defined by it

namespace Ledger

variable {R T:Type}[Fintype R][Fintype T]

def schema (A:Ledger I R):Prop:= waxed A.input ∧ Eligible A.input ∧ ∀ i j,A.prices i j=A.prices j i

structure Sincere (A:Ledger I R):Prop where
 cards : waxed A.input ∧ Eligible A.input ∧ ∀ i j,A.prices i j=A.prices j i
 boil : A.theater.Boil A.P A.K
 deck : Relation A.theater A.prices A.view
 perimeter : Abroad A.theater.foam A.κ

def printed (A:Ledger I R):Port I:= belt (fun i=>liftInn (median A.view i)) (stock A.input)
def connected (A:Ledger I R):Port I:= pushed (Γ:=A.prices) (mView A.theater A.view) A.input

lemma cold (A:Ledger I R)(H:Sincere A):tiny (A.printed):=by
 apply belt_tiny
 unfold tiny stock;rw [PowerSeries.coeff_mk];simp [showV,H.cards.2.1.dark,parley_zero]
lemma bright (A:Ledger I R)(H:Sincere A): A.theater.brew (rise A.printed)=rise A.connected:=by
 have he:tiny (stock A.input):=by unfold tiny stock;rw [PowerSeries.coeff_mk];simp [showV,H.cards.2.1.dark,parley_zero]
 rw [printed,←belt_rose _ he,Haze.stood H.deck H.cards.2.2,connected,Glyph.housed _ H.cards.2.1 H.cards.1 H.cards.2.2]
lemma void (A:Ledger I R)(H:Sincere A):tiny (A.connected):=tiny_on _ H.cards.2.1

/- Same total law condition after map center2→center1 in two pieces: heat-preserving L on
integrated & arbitrary Y on external, FOLLOWED in pullback by near-id (identity on external) η.
Supply normalized Jacobian on whole map, i.e. that of near-id piece alone since constant
determinant factor cancels in the normalized flat measure. (`Covers` with divided det
canonically). Supply total quadratic matching for heat-preserving piece on centered variables
& κ: structural external difference tiny; centered part formally exactly (not just at g=0),
 natural since x packed on fine variables. fine integrated positive germs include Haar; hcorr
 law includes spin factors for both. All absolute constraints (if logarithms/vacuum modulo
constant, must supply matching factor separately OR use below through capture via panel).
-/
structure Covers (A:Ledger I R)(B:Ledger J T)(b:J→Port I)(η:I→Port I):Prop where
 analytic : ∃ L, Scout B.theater A.theater b L
 outside : Abroad A.theater.foam (belt b B.κ)
 first : belt b (liftInn B.K)=liftInn A.K
 scales : tiny (belt b B.κ-A.κ)
 gateFix : anchored A.theater.foam η
 echo : Near η
 law :
    rise (belt η (belt b (B.printed+liftInn B.K+B.κ)) - liftInn A.K - A.κ) * (gate η).det=rise A.printed

 omit [Fintype I] in
private lemma stay {W:Finset I}{η:I→Port I}(h:anchored W η){f:Port I}(hf:Abroad W f):belt η f=f:= by rw [abroad_belt hf (y:=rod) h,belt_id]

/-- FINITE cover transformation on centered algebra. Neither quadratic κ need have zero
constant coefficient in g; only their DIFFERENCE after transform. -/
theorem impress (A:Ledger I R)(B:Ledger J T)(h:Sincere A)(k:Sincere B)(b:J→Port I)(η:I→Port I)(ht:Covers A B b η):
     belt b (B.κ+B.connected)=A.κ+A.connected:=by
 obtain ⟨L,hL⟩:=ht.analytic
 let D:=belt b B.κ - A.κ
 have hd:tiny D:=ht.scales
 have he:Abroad A.theater.foam (rise D):=abroad_rise (H:=A.theater)
    (show Abroad A.theater.foam D from fun i hi=>by unfold D; rw [map_sub,ht.outside i hi,h.perimeter i hi,sub_zero]) hd
 have hv:=A.theater.absorbed ht.echo ht.gateFix h.boil (belt b B.printed) (belt_tiny (B.cold k) _)
 unfold evolve at hv
 let Z:=belt η (belt b B.printed)+belt η (liftInn A.K)-liftInn A.K
 have hh : tiny Z:=neartiny ht.echo (belt_tiny (B.cold k) _) _
 have hy := ht.law
 simp only [map_add,ht.first,stay ht.gateFix ht.outside] at hy
 rw [show (belt η (belt b B.printed)+belt η (liftInn A.K)+belt b B.κ-liftInn A.K-A.κ)=D+Z from by unfold D Z; abel,rise_together hd hh,mul_assoc] at hy
 apply_fun A.theater.brew at hy
 rw [Haze.brew_shunt _ he,show A.theater.brew (rise Z * (gate η).det)=_ from hv] at hy -- hv not a fn
 rw [←belt_rose _ (B.cold k),entrusted hL,B.bright k,A.bright h,belt_rose _ (B.void k),←rise_together hd (belt_tiny (B.void k) _)] at hy
 have ha:tiny (D+belt b (B.connected)):=by have H:=belt_tiny (B.void k) b;unfold tiny at *;rw [map_add,H,hd,add_zero]
 have hi:= truly ha (A.void h) hy
 rw [map_add,←hi];unfold D;abel

end Ledger
end Haze
end YM.RG08.Room

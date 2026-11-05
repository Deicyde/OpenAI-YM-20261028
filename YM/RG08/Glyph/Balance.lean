import YM.RG08.Glyph.Mean

/-!
# Normalize by the common formal denominator before taking the connected marked log.

Here one may take V the WHOLE combined bulk positive jet and W its unmarked version.
Repeated mixed tags at finite load/degree can be encoded in the ONE auxiliary counting
variable by mapping each tag to its own sufficiently large power (for parity ask degrees
even if the valence parity already matches e on its unmarked part; otherwise add e of the
required parity; for digits in finite use e.g. huge even increments), or polarize pure
insertions. The encoding/reconstruction of a physical alphabet is NOT asserted here;
this is a theorem for arbitrary input stencils with the indicated positive-order valence
and parity. It retains the WHOLE partition (so a conditional denominator depending on lower
fields is fully inverted at every coefficient). Works on any finite period tree with any
symmetric covariance and any mean (subst); does not assert stationarity on arbitrary chart
or identify analytic density derivatives.
-/
noncomputable section
namespace YM.RG08.Glyph
open Forms Steam Cloud Finset Function MvPolynomial
open scoped BigOperators Topology Classical
set_option autoImplicit false
variable {I J:Type} [Fintype I] [Fintype J]

/-- Pin the order of operations and factorials via the three series `rise` (powers divided
by factorial), `house` (pairings and unpaireds, then substitute; wick_occurrences), reciprocal
& `fall` (log1p with signs). A denominator inverse here is not a typeclass inverse (codomain
only a ring); specify as unique inverse of the actual formal Hankel series. -/
def counter {S:Type*}[CommRing S](z:S):S:=if h:IsUnit z then ↑(h.unit⁻¹ : Sˣ) else 0
lemma counter_pays {S:Type*}[CommRing S](z y:S)(h:z*y=1):counter z = y:=by
 have hz:IsUnit z:=⟨⟨z,y,h,by rw [mul_comm,h]⟩,rfl⟩
 rw [counter,dif_pos hz];apply hz.mul_right_inj.mp -- inspect
 conv_rhs=> rw [h]
 exact hz.unit.mul_inv

def panel (Γ:Line I)(μ:I→J→ℝ)(V W:Grain I):PowerSeries (Inn J):=fall (house Γ μ (rise (stock V)) * counter (house Γ μ (rise (stock W))))

theorem capture (Γ:Line I)(μ:I→J→ℝ)(V W:Grain I)
    (hV:Eligible V)(h:waxed V)(hW:Eligible W)(hw:waxed W)(hΓ:∀ i j,Γ i j=Γ j i) :
    panel Γ μ V W=pushed Γ μ V - pushed Γ μ W:=by
 have he:= tiny_on (Γ:=Γ) μ hW;have hf:= tiny_on (Γ:=Γ) μ hV
 have hh:=tiny_mirror he
 rw [panel,housed μ hV h hΓ,housed μ hW hw hΓ,counter_pays _ _ (rise_unit he),←rise_together hf hh]
 have hg:tiny (pushed Γ μ V + -pushed Γ μ W):=by unfold tiny; rw [map_add,hf,hh,add_zero]
 rw [ground hg, sub_eq_add_neg]
end YM.RG08.Glyph

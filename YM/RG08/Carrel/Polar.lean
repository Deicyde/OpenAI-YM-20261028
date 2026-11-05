import YM.RG08.Carrel.Works
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Effective coefficients of EACH definite field rank on the infinite cover identified by
       cofinal evaluations in symmetric literal tensor norm. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Carrel
open Lattice Laurent Forms Pert.Bulk Isles Packets Rudder Rudder.Symmetry Filter Finset Function RG Extra.Iteration
open Camera Cloud Room Glyph Exterior Wilson Precision Spar
open scoped BigOperators Topology Classical ENNReal PowerSeries Matrix
variable {I:Type}{k n:ℕ}{P:Side}
-- Sym rank detection including zero. Want fixed-rank and combinations across ranks via
-- loading cumulants later.
lemma pursuit [Fintype I]{F V:Flake n I}(h:Sym F)(hh:Sym V)(he:parley F=parley V): F=V:=by
 induction n with
 | zero=>
          ext x; have H:F x • (1:Inn I)=V x • (1:Inn I):=by
                    convert he using 1 <;> {unfold parley; rw [Fintype.sum_unique]; simp only [word,prod_of_isEmpty]; rw [Subsingleton.elim x default]}
          have H':MvPolynomial.C (σ:=I) (F x)=MvPolynomial.C (V x):=by convert H using 1 <;> {rw [Algebra.smul_def,mul_one];rfl}
          exact MvPolynomial.C_injective _ _ H'
 | succ n ih=>
    have hk(i:I): Sym (fun x:Tape n I=>F (Fin.cons i x)):=Glyph.sym_cons h i
    ext x
    let c:=x 0;let a:=Fin.tail x;have hx:x=Fin.cons c a:=(Fin.cons_self_tail x).symm
    rw [hx]
    have hv:=congr_arg (MvPolynomial.pderiv c) he
    rw [Glyph.first c n h,Glyph.first c n hh] at hv
    exact congrFun (ih (hk c) (Glyph.sym_cons hh c) (Cloud.untangle (by positivity) hv)) a

lemma pour_sym {I:Type}{F:Flake n (Mix I k)}(h: Cohort F)(hF:Sym F)(a:Fin n):Sym (pour (P:=P) F a):=fun η=>by rw [ordered _ _ _ h,hF]

lemma crystals [Fintype I]{F V:Flake n (Mix I k)}(a:Fin n){σ τ C D:ℝ}(hσ:0<σ)(hτ:0<τ)
     (hc:Cohort F)(hc':Cohort V)(h:Sym F)(hh:Sym V)(ht:Held (carpet _) σ C F)(ht':Held (carpet _) τ D V)
     (he:∀ P:Side,P.val≥1→∀ z:Cmix P I k→ℝ,reading (pour F a) z=reading (pour V a) z):F=V:=by
 have hP(j:ℕ):pour (P:=chain j) F a=pour V a:= pursuit (pour_sym hc h a) (pour_sym hc' hh a) (MvPolynomial.funext fun z=>by rw [←reading_parley,←reading_parley,he _ ((chain j).property)])
 ext x
 have ha:=pour_view ht hσ.le a x
 have hv:=pour_view ht' hτ.le a x
 simp_rw [hP] at ha;exact tendsto_nhds_unique ha hv

variable {G:Gauge}{F V:Rudder.Raw G.ColorIndex n}{σ p:ℝ}
lemma early_vanish (o:Fin n)(h: Cohort F)(ht:Held (carpet _) σ p F)(hp:0≤p)(hs:0<σ)(i:Fin k)(he:k<n):completed F o k=0:=by
 obtain ⟨C,hC,H⟩:=completed_held G k o hs
 obtain ⟨he',hf,hT⟩:=H F hp ht
 have hw:0<(σ/(n:ℝ)/32):=by have hj:0<(n:ℝ):=Nat.cast_pos.mpr o.pos; positivity
 apply crystals (σ:=(σ/(n:ℝ)/32)) (τ:=σ) (D:=0) i hw hs hT (fun _ _=>rfl) hf Forms.Sym.zero he' zero_held
 intro P _ z;rw [spared o h ht hs hp i he z];simp [reading,pour,Set.indicator]

private lemma photo_grade (o:Fin n)(h:Cohort F)(he:Held (carpet _) σ p F)(hp:0≤p)(ht:0<σ):
     ∃ C:ℝ, Cohort (picture G.ColorIndex n F) ∧ Held (carpet _) (σ/2) C (picture _ n F):=⟨_,(Spar.photograph (NextTo.unit ht hp h he o.pos)).cohort, Spar.encode o.pos ht hp h he⟩
end YM.RG08.Carrel

import YM.OPE.Exchange.Coherence
import YM.OPE.Rough.Supply
import YM.MergeProof.Summit
/-!
# All horizons, all phases: single scale subpower version

Construct first the same theory of all continuum weights and cutoffs as
`Spec.CLOSED`. Stronger Base supplies and estimates on that choice give the
explicit compatible prescription, dilation powers with an arbitrarily small
fixed loss parameter, compact shapes / exterior clearances. The projection basis
is a fixed complex one. We apply the construction of `xanadu`--`summit`
of `MergeProof.Acme`, retaining stronger receipts but *no* assumption for the
base. The log-improvement is NOT claimed in this file.

No choice of the prescription each time is necessary. Once a Final here is thus
selected, all `Prescription`s on its algebra satisfying `Coherent` can be used
(with their own bases); all have these estimates. Multilinear labels (weights
may be any presented stage in the filtering) represented by actual `book.Ref`
tokens. Filtration projection agrees as in `YM.OPE.Exchange.Coherence`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Lattice RG Next.Extract Dash Org Bid OS Ground Spec MergeProof
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}

/-- Services through the **same** actual Final. Stronger start-through choice;
UV-level comparisons can still use the `xanadu` witnesses here iff taken
accordingly (with `p` in this proof etc.). No uniqueness or claims about
all possible `Spec.Final` constructions. -/
lemma through_final (h:G.Simple){b:ℝ}(hb:0<b) (f:Extraction.Order) : ∃ (C:Family G), C.path.levels.clock.kernel.penalty=b ∧ ∃ (g:Extraction.Order)(A:Table C.book), Services C (f.refine g) A ∧ Nonempty (Final C (f.refine g) A):=by
    obtain ⟨C,hB,hC,hM,hW,hS,H,hQ,hF⟩:= YM.PhysicalNext.Repeat.Legato.noel_columns h hb
    obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF f
    obtain ⟨hs,hG⟩:= hQ (f.refine g) s.copies
    obtain ⟨M,I,hI,p⟩:=Acme.emanate (W:=E) H h hs hG s hA.clean.ready hA.clean.tilt
    exact ⟨C,hB,g,T,⟨hs,h,hS,A,L,R,E,hA⟩,Acme.glistens hC hA.clean.ready hA.clean.tilt p⟩

variable {C:Family G}{F:Extraction.Order}{S:Table C.book} (U:Final C F S)
structure SingleSubpower (P:Prescription U.sector.derivatives) : Prop where
    coherent: P.Coherent
    terms (I:Type)[Fintype I] (p:I→ C.book.Token) (η M ε:ℝ) :
        0 < η → 0 ≤ M → 0 < ε → ∀ i : Mode U.sector.derivatives,
          ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (x:I→ E4)(o:E4), WithinRoom r M η x o →
             (∀ u∈ (P.sheet i).support, Injective (beside (away x o) (bearing u))) ∧
                ‖P.ope i x p o‖ ≤ r^((i.fst:ℝ)-(sigma p:ℝ)-ε)
    horizons (I J:Type)[Fintype I][Fintype J] (p:I→ C.book.Token)(q:J→ C.book.Token) (η M c ε:ℝ):
        0 < η→ 0 ≤ M → 0 < c → 0 < ε → ∀ n : ℕ,
          ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (x:I→ E4) (o:E4)(y:J→ E4), WithinRoom r M η x o → ClearOf o y c →
             Injective (beside x y) ∧ Injective (beside (sole o) y) ∧
                Tested U P n x p o y q (r^((n:ℝ)+1-(sigma p:ℝ)-ε))

lemma one_radius {P:Prescription U.sector.derivatives} (hP:P.Coherent) (h:Services C F S) : SingleSubpower U P :=
    ⟨hP,fun _ _ p _ _ _ hη hM he=> small_coeff U hP h p hη hM he, fun _ _ _ _ p q _ _ _ _ hη hM hc he=> small_horizon U hP h p q hη hM hc he⟩ -- type syntax Prop inst lambda

/-- Joint existence extending CLOSED for these estimates. -/
theorem single (G:Gauge) (h:G.Simple) (f:Extraction.Order) : ∃ (C:Family G) (g:Extraction.Order)(A:Table C.book), Services C (f.refine g) A ∧ ∃ (U:Final C (f.refine g) A)(P:Prescription U.sector.derivatives), SingleSubpower U P:=by
    obtain ⟨C,-,g,A,hC,⟨U⟩⟩:= through_final h (b:=1) zero_lt_one f; obtain ⟨p,hp⟩:= Prescription.chosen U.room.kernel.laws.toSymmetric U.phase.transport.injection; exact ⟨_,g,A,hC,U,p,one_radius U hp hC⟩
end YM.OPE

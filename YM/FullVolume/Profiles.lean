import YM.FullVolume.Smears
import YM.FullVolume.Literal

/-!
# UV positional statement. Work with the periodic lift to real positions.
Test class from target is `_ : Test n` with `suitable`: any smooth compact
support as there (choose period large enough to fit those physical positions
away from the seams). The *local uniform* statement has no such seam guards:
compact subsets of `NoHit` may straddle period cells and include any ties.
All fixed finite families via all p after admitting ONE Run with
unbounded schedule budgets. Our strengthened input supports every fixed d
and every order at every admitted period; e.g. the bounds for first and one
higher derivative still hold at that same p. `N` threshold can depend on ALL
those quantities (and compact set/tests). No assertion for unbounded field
or test tapes without their own thresholds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Filter Set MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells Asymptotics Finset
open PhysicalNext.Repeat.Legato
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge} {C:Family G} (e:Extraction.Sequence) {n:ℕ}

def PositionsUV (C : Family G) (e : Extraction.Sequence) :=
  ∀ (p n : ℕ) (v : Fin n → C.book.Token),
   ∃ f : Points n → ℂ, ContDiffOn ℝ ∞ f (NoHit C.S p n) ∧
     (∀ t : Test n, suitable C.S p t → Tendsto (fun j => Order.smears C (e j) p v t) atTop (𝓝 (t.applyTo f))) ∧
     ∀ l : List (Reach n),
       let F N := squall (C.S.a N) l (lifted C N p v)
       let g := derive f (l.map Reach.where_)
       Cluster C e p n F g ∧
       Meets (NoHit C.S p n) (fun j => interpolated C.S (e j) (F (e j))) g ∧
       ∀ t : Test n, suitable C.S p t →
         Integrable (fun x : Points n => t x * g x) ∧
         Tendsto (fun j => sumOn F C.S p (e j) t) atTop (𝓝 (t.applyTo g))

lemma at_probe (p N:ℕ)(t:Test n)(v:Fin n→ C.book.Token) : sumOn (fun N=> lifted C N p v) C.S p N t= Order.smears C N p v t:=by
   unfold sumOn Order.smears
   refine congrArg _ (Finset.sum_congr rfl (fun j _=> ?_))
   unfold lifted; dsimp only; rw [show wrap (C.side N p) ∘ (Lattice.lift ∘ j)=j from funext (fun i=> wrap_lift (j i))]; rfl
theorem positioned (M:FixedBounds C) (h:Purchased C e) : PositionsUV C e:=by
   intro p n v
   obtain ⟨f,hf,h⟩:= reachable M e h p v
   refine ⟨f,hf,fun t ht=>?_,fun l=>⟨h l,held (h l),fun t ht=>pudding e (h l) t ht⟩⟩
   have hk : Cluster C e p n (fun N => lifted C N p v) f:= h []
   exact ((pudding e hk t ht).2).congr' (Eventually.of_forall fun i=>at_probe p (e i) t v)

/-- An actual extension of the achieved subsequential Seed. Along that
same order (no new extraction) at fixed p, uniform convergence of all
orders and through ties. Not full-sequence until Purchased on .full. -/
theorem printed (h:G.Simple)(R:Run G)(f : Extraction.Order){S:Table R.family.book} (hf:Nonempty (Spec.Final R.family f S)): PositionsUV R.family f.mesh:=by
   obtain ⟨T⟩:=hf; apply positioned _ (genuine R h); intro n p v x hx
   obtain ⟨P,H,hP⟩:= T.room.generic
   have hr:= Extraction.chosen (S:=R.family.S) x |>.comp f.mesh.cofinal
   have hv:= f.evaluated R.family H p n v x hx (fun i=> address (R.family.S.a (f.mesh i)) x) hr
   exact hv.cauchySeq
end YM.FullVolume

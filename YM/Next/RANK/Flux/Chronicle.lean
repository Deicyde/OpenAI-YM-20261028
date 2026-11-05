import YM.Next.RANK.Flux.Pure

/-!
# Vacuum expansion stamp. First-system coefficients on output site, before
*any* marked exclusions estimates. This statement needs actual RG Step partners.
- Vac involves a recovery stamp AT ZERO (receipt from the unmarked step,
  with validity to be tested together with the marked pressure against holes,
  can see a reduction via `Intervals` testing at any hole).
- R/Bin precursors still must prove first-system exact expansion with weights
  (absolute marker coefficient estimates, true flag coverage, using Lifted for
  every forced candidate at native output); `Matric` is this version AFTER substituting
  the vac hole identity. Can use first-system formula with that hole law directly to
  verify. Keep support charges *through all* first system steps; only tested here at
  last term. No radial data, updated H matrices, nor gauss spectral comparisons asked
  in this hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes Spindle Atlas Station Peak Cells Perch
open scoped BigOperators Classical

variable {V ι κ α β : Type} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side} {Q : Rep G n} {x y z d : ℝ} {ζ : V→Site n}

structure Vac (ζ : V→Site n) (Q : Rep G n) where
  D : Type
  [d : Fintype D]
  R : Type
  [r : Fintype R]
  K : Type
  [k : Fintype K]
  f : D→ Lifted G ζ Q.p.threshold
  holes : R → Inner G ζ
  pay : K → CoverReads G ζ Q.p.threshold
  debt i : (f i).fires=quiet V
  hole i : (holes i).fires=quiet V
  boundary : Boundary pay
  coat : Background Q (toRain (toRain f (fun i=> .inl (holes i))) (witness pay))

attribute [instance] Vac.d Vac.r Vac.k
variable (B : Vac ζ Q)
def measureH : B.R→Lining G ζ Q.p.threshold:= Sum.inl ∘ B.holes
-- precision in Norms asked separately. old K unchanged all proof; Mach crown L parity etc
structure Matric (T : Vac ζ Q) {ι : Type} [Fintype ι] (F : ι→Plug G ζ Q.p.threshold) (U : Config G n→veil V) : Prop where
  emboss : Nonempty (Embedded T.f F)
  passed a : U a=(Real.exp (Q.exponent a):ℂ) • infrared F (measureH T) T.pay a
-- factored by prior vac hole log formula (unmarked only).
section
variable [Fintype ι] (F : ι→Plug G ζ Q.p.threshold) (U : Config G n→veil V) (h : Matric B F U)

abbrev FLog := sunny (panel F (measureH B))
abbrev Top (R : ι→Prop) := { i // rawclean (Q:=Q.p) F (measureH B) R i }
abbrev Bottom (R : ι→Prop) := { i //¬ rawclean (Q:=Q.p) F (measureH B) R i }

def upstairs (R : ι→Prop) : Top B F R → SourceAt G ζ:= Bond (FLog B F) ∘ Subtype.val
def downstairs (R : ι→Prop) : Bottom B F R → SourceAt G ζ:= Bond (FLog B F) ∘ Subtype.val
include h in
lemma sunny_pass (R) : U=dust Q (Sum.elim (downstairs B F R) (upstairs B F R)) (after F (measureH B) B.pay) ∧ Background Q (after F (measureH B) B.pay):= by
  let A:= panel F (measureH B); let X:= FLog B F
  let E:= MergeLog X; let O:=Top B F R; let D:=Bottom B F R; let V:=Bond X
  constructor
  · ext1 u
    let t:= Q.p.threshold
    let Ω: D ⊕ O ≃ E:= (Equiv.sumComm ..).trans (Equiv.sumCompl (rawclean (Q:=Q.p) F (measureH B) R))
    let s:= Sum.elim (downstairs B F R) (upstairs B F R); let Y:=after F (measureH B) B.pay
    have hv:(∑ i, (s i).amount Q.p.threshold u)=∑ i, (V i).amount t u:= Fintype.sum_equiv Ω (fun w=> (Sum.elim (downstairs B F R) (upstairs B F R) w).amount t u) (fun i=>(V i).amount t u) (fun i=>by cases i <;>rfl)
    have he := placed F (measureH B) B.pay u B.boundary
    let a : ℂ:= Real.exp (Q.exponent u)
    calc
      _ = a • (Poly.pass (∑ i,(V i).amount t u) * RAIDage Y u) :=(h.passed u).trans (congr_arg (fun z=> a • z) he)
      _ = _ := by rw [← hv]; rfl
  obtain ⟨X⟩:=h.emboss
  obtain ⟨Y⟩:=rainy F (measureH B) B.pay X
  exact fun i U=> (emb_bg Y U i).trans (B.coat i U)
lemma sunlight (s : ι→Prop) (a : Config G n) : Poly.pass (∑ i : Top B F s,(upstairs B F s i).amount Q.p.threshold a) = pitch (Q:=Q.p) F s a:= by
  apply Eq.trans _ (clean_log (Q:=Q.p) F (measureH B) s a); apply congr_arg Poly.pass; let A:= FLog B F;let H:= rawclean (Q:=Q.p) F (measureH B) s
  exact (sum_subtype _ (show ∀ i,i∈ univ.filter H ↔ H i from fun _=>by simp) (fun i=>(Bond A i).amount Q.p.threshold a)).symm
lemma authenticity (s : ι→Prop) (r : V→ℝ) {M L e} (hr : ∀ i,0<r i) (hp : 1 ≤ M) (hl : 1≤ L) (he : 0≤ e) (ht : Tickets Q.p z)
    (h : ∃ f g, Authorship F (measureH B) B.pay f g s r e M L z y) :
    Shine (downstairs B F s) Q.p r e (y/L) ∧ Shine (upstairs B F s) Q.p r e y ∧ Stripes Q.p (after F (measureH B) B.pay) r (e+1) (1/M):= by
  obtain ⟨f,g,hA⟩:=h
  obtain ⟨ha,hb⟩:= heard F (measureH B) s hr hp hl ht he (fun i=>B.hole i) hA
  exact ⟨hb,ha,cloud F _ _ f g s hr hp hl ht he hA⟩
end
end YM.Next.Rank.Flux

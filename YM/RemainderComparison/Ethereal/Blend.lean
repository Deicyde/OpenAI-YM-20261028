import YM.RemainderComparison.Ethereal.Sun
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Ethereal
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration
open Push Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Lacuna Vowel PhysicalNext.Repeat Jolt Flues
variable {G: Gauge}{n:Side}{ι : Type} {α:Type*}
open MeasureTheory Marker Serif PhysicalNext.Repeat.Trio

variable (X Y : Scone ι α G n)(u:Set ι)(p:BudgetPoint)(roots:ι→Support n) {k:ℕ}{σ b t b' t' : ℝ}
open Function

def stem : ℕ ≃ ℕ⊕ℕ:= YM.Extra.Iteration.numbering _

def blend : Scone ι α G n:= ⟨fun i=> Sum.elim X.leg Y.leg (Ethereal.stem i),fun i=>by cases Ethereal.stem i with
                                                          | inl i=> exact X.rest _
                                                          | inr i=> exact Y.rest _, Sum.elim X.glyph Y.glyph ∘ stem,fun a=> Sum.elim (X.glow a) (Y.glow a) ∘ stem⟩
local notation "Sʼ"=> blend X Y
lemma vino (hx:X.Treasures u k p.B σ b t)(hy:Y.Treasures u k p.B σ b' t'): Scone.Treasures Sʼ u k p.B σ (b+b') (t+t') :=by
    obtain ⟨f,g,hf,hg,hV,hS,hX⟩:=hx.wages; obtain ⟨f',g',hf',hg',hV',hS',hX'⟩:=hy.wages
    let F:= Sum.elim f f'; let G:= Sum.elim g g'; refine ⟨F∘stem,G∘stem,fun i=>?_ ,fun i=>?_,fun i=> Cost.equiv stem (show SumBudget (fun j=> if i∈ Sum.elim X.leg Y.leg j then F j * Real.exp (σ*coverNumber p.B (Sum.elim X.leg Y.leg j)) else 0) _ from Cost.sum (hV i) (hV' i)),fun i=> ?_,fun i hi a V=>?_⟩
    · unfold Function.comp; cases stem i with
                          | inl i=> exact hf i
                          | inr i=> exact hf' i
    · unfold Function.comp; cases stem i with
                          | inl i=> exact hg i
                          | inr i=> exact hg' i
    · exact Cost.equiv stem (show SumBudget (fun j=> if i∈ Sum.elim X.leg Y.leg j then G j * Real.exp (σ*coverNumber p.B (Sum.elim X.leg Y.leg j)) else 0) _ from Cost.sum (hS i) (hS' i))
    unfold Ethereal.blend at hi ⊢; simp only [Function.comp_apply] at hi ⊢; cases he:stem i with
                          | inl i=> rw [he] at hi; exact hX i hi _ _
                          | inr i=> rw [he] at hi; exact hX' i hi _ _
lemma partied (hx:X.Rises p roots)(hy:Y.Rises p roots): (Sʼ).Rises p roots:=by
    have he (i j a): stem i= j →Tidy p ((Sʼ).leg i) ((Sʼ).glow a i) ∧ (∀ V, Healthy p.threshold ((Sʼ).leg i) V→ (Sʼ).glow a i V=0) ∧ apex roots ((Sʼ).leg i) ((Sʼ).glyph i) ((Sʼ).glow a i):=by
       intro h; unfold blend; simp only [Function.comp_apply,h]; rcases j with j|j; exact ⟨⟨hx.reads a _,hx.borel a _,hx.durable a _⟩,hx.leaked j a,hx.origin j a⟩
       exact ⟨⟨hy.reads a j,hy.borel a j,hy.durable a _⟩,hy.leaked j a,hy.origin j a⟩
    exact ⟨fun a i=>(he i _ a rfl).1.uses,fun a i=>(he i _ a rfl).1.borel,fun a i=>(he i _ a rfl).1.invariant,fun i a=> (he i _ a rfl).2.2, fun i a=> (he i _ a rfl).2.1⟩
lemma arias (hx:Jolt.Whirls X u)(hy:Jolt.Whirls Y u): Jolt.Whirls (blend X Y) u:=by
    constructor
    · intro i hi a b; unfold Jolt.dawn at hi; unfold Ethereal.blend at hi ⊢; dsimp only [Function.comp_apply] at *; cases he:stem i with
                                                | inl i=> rw [he] at hi; exact hx.quiet i hi ..
                                                | inr i=> rw [he] at hi; exact hy.quiet i hi ..
    intro s b; obtain ⟨e,h⟩:=hx.spins s b; obtain ⟨f,hf⟩:=hy.spins s b; let g:= Equiv.sumCongr e f
    let q:= (stem.trans g).trans stem.symm; refine ⟨q,fun i=>?_⟩; unfold Jolt.dawn blend; dsimp only [Function.comp_apply]; rw [show stem (q i)= _ from stem.apply_symm_apply (g (stem i))]; cases stem i with
                                                | inl i=> exact h i
                                                | inr i=> exact hf i
variable (V:Config G n) (a:α) {β:Type}[DecidableEq β]{J:Marker.Census β}(z:ι→Marker.Poly J){C C' :Marker.Poly J}
lemma tar (hf:HasSum (X.plume u z a V) C)(hg:HasSum (Y.plume u z a V) C'): HasSum (Scone.plume Sʼ u z a V) (C+C'):=by
    let F:= Sum.elim (X.plume u z a V) (Y.plume u z a V); refine (stem.hasSum_iff.mpr (HasSum.sum (f:=F) hf hg)).congr_fun ?_
    intro i; unfold Scone.plume blend; dsimp only [Function.comp_apply]; cases stem i <;> rfl
end YM.RemainderComparison.Ethereal

import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Layering
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Payout

/-! # Y purchase once on ANY call. Split colors, not layout! -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Docking
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid Precision Filter Station Thirst
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {x τ l k e z : ℝ} {L : Lantern G S} {A : Stores S} {P : Teller G} {W ι α ν ρ : Type} [Fintype W] [DecidableEq W]
    {θ : W→Site f} {u : W→ Site c} {r : W→ℝ}
    {R : Rep G f} {Q : Rep G c}
section
variable [Fintype ι] [Fintype α] (Y : ι→ Flake S G x L.park u Q.p.threshold) (Z : α → Flake S G x L.park u Q.p.threshold)
    (C : ι→Prop) (K : α→Prop)
lemma packed_both (x y v : ℝ) (hp : Spot Q Y C T l r e x) (ht : Spot Q Z K T l r e y) (hb : x+y≤v) : Spot Q (Sum.elim Y Z) (Sum.elim C K) T l r e v:= by
  obtain ⟨p,hp,h₁,h₂,h₃⟩:=hp.balance; obtain ⟨q,hq,h₄,h₅,h₆⟩:= ht.balance
  refine ⟨Sum.elim p q,fun i=>Sum.recOn i hp hq,?_,?_,fun i=>?_⟩
  · rintro (i|i); exacts [h₁ i,h₄ i]
  · rintro (i|i); exacts [h₂ i,h₅ i]
  rw [Flux.locus]; exact (add_le_add (h₃ i) (h₆ i)).trans hb
lemma joined [Fintype ν] [Fintype ρ] {H : ν→ SourceAt G θ} {G' : ρ → SourceAt G θ} (ht : audition R Q Y (T:=T) H) (hz : audition R Q Z (T:=T) G') : audition R Q (Sum.elim Y Z) (T:=T) (Sum.elim H G'):= by
  intro V A k z; rw [Fintype.sum_sum_type,Fintype.prod_sum_type]
  let U:=gazed T k.tag L.χ V x R.beta L.hood z
  have he(s : SourceAt G θ) : (s.amount R.p.threshold U).part (Glyph.quiet W)=0:= Flux.asleep _ s.chosen _
  rw [Exponential.pass_add _ _ (by rw [Poly.part_sum]; exact Finset.sum_eq_zero fun _ _=>he _) (by rw [Poly.part_sum]; exact Finset.sum_eq_zero fun _ _=>he _)]
  simp only [Sum.elim_inl,Sum.elim_inr,ht V A k z,hz V A k z]; rfl

end
end YM.PhysicalNext.InteractingRank.Display.Docking

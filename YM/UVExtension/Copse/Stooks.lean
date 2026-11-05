import YM.UVExtension.Copse.Thatch
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Copse
open Function Filter Set RG Wilson Lattice Precision Push Push.AbsoluteSums Animals Finset Progress.DirectedRecipe Payments
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Mallow Extra.Iteration MeasureTheory
open Lamppost Concert Ovens Ovens.Pipes
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {D Z:Type}{G:Gauge}{n:Side} {X:Pipes G n} [NormedAddCommGroup Z][NormedSpace ℂ Z]{T:Opening D Z}
variable (S:ℕ≃ X.Pellet)(q:BudgetPoint)
variable {p:BudgetPoint} (Y:D→ Ovens.Tap G n){b c g h r k:ℝ}(H:Atlas (bell X.kernel p.B (p.supportExponent+1)) T (fun i j u=> (Y i).forced j u) (fun _=>b))(J:Atlas (softer X p.B (p.supportExponent+1)) T (fun i j u=> (Y i).logarithm j u) (fun _=>c))
set_option quotPrecheck false
variable (F:D→ℝ→Ovens.Code G n) (d:ℕ) (M:Scent (downs X p d) T F (fun _=>g)) (hF:∀ i,F i 0=(Y i).forced)
open Progress.DirectedRecipe.Rack
noncomputable def stripe (i:D)(θ : ℝ):= (widen X (spice (Y i) (F i θ))).forced
include M
lemma lintel: Nonempty (Scent (downs (drawer G n) p d) T (stripe (X:=X) Y F) (fun _=>g)):=by
   let W:= downs (drawer G n) p d; let w(i):=breezeM W (stripe (X:=X) Y F) i
   have ht (i:D)(k:ℕ)(θ:ℝ): stripe (X:=X) Y F i θ (upK X k)=F i θ k:=stuffed ..; have hz i θ k(h:k∉ Set.range (upK X)): stripe (X:=X) Y F i θ k=0:= blank _ _ h
   have he:Nonempty (Atlas W T w (fun _=>g)):=by
     refine Lamppost.inserted _ _ _ (upK X) w (fun _ x=> x) ?_ ?_ ?_ M.toAtlas
     · intro i j k; exact congr_arg (fun f =>deriv f (0:ℝ)) (funext fun θ=> congr_fun (ht i j θ) k)
     · intro i hi j k; unfold w breezeM; simp_rw [hz _ _ i hi]; exact deriv_const _ _
     · intro x i; dsimp only [downs,W,nose,portal]; rw [hard_up]; rfl
   obtain ⟨P⟩:=he
   refine ⟨⟨P,fun i x k=>?_⟩⟩; by_cases he: x∈ Set.range (upK X); · obtain ⟨x,rfl⟩:=he; simp_rw [ht]; exact M.bright ..
   simp_rw [hz _ _ x he]; exact differentiableAt_const _

omit M
-- test uses μ; branch offset t.Actual chart counts.On Real.
lemma stripes (i:D)(t:ℝ) : (widen X (spice (Y i) (F i t)))= spice (widen X (Y i)) (stripe (X:=X) Y F i t):= rfl
variable (P:Payments.Rates p.B h b c k)
include hF M P H J
lemma grooms:Nonempty (Scent (nose (G:=G) (fun i=> (addr (folio G n) p i).support) d p.B p.supportExponent) T (fun i=>Mallow.final.frigid X (Y i) (F i) p) (fun _=> g)) := by
   obtain ⟨V⟩:= Yard.spansH Y H; obtain ⟨Z₀⟩:= Yard.spansS Y J; obtain ⟨N⟩:= lintel Y F d M
   have he (i: D): stripe (X:=X) Y F i 0= (widen X (Y i)).forced:=by unfold stripe; rw [hF]; rfl
   obtain ⟨N⟩:= petalsT (folio G n) p (fun i=>widen X (Y i)) V Z₀ (stripe (X:=X) Y F) d N he P
   exact ⟨N⟩
end YM.UVExtension.Copse

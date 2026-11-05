import YM.RG08.Spar.Terminal
import YM.RG08.Cell.ReleaseHeat

noncomputable section
namespace YM.RG08.Spar
open Forms Rudder Packets Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch Anchor Symmetry Isles Stationary RG Rows LinearMap Precision Tree RG08.Line
open scoped Topology BigOperators Classical ENNReal Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {c f:Side}{P:Patch}{k:KernelChoices}{G:Gauge}{b b':Bed}

lemma pigment {i j : ℕ}(A:Matrix (Body i c) (Body j f) ℝ):shaded c f G.ColorIndex A=patron G A:=by
 ext ⟨x,i,u⟩ ⟨y,j,v⟩
 by_cases huv : u = v <;>
   simpa [shaded, huv] using (Line.patron_cell G A (x,i) (y,j) u v).symm

lemma cozy {η B:ℝ}(h:Cell.Warm G k P b η B)(he:0≤η)(hs:η≤1):Tagged η (B*Cell.key G P k) (clover P.L (Cell.plotted P k G b)) (Cell.predictorFinite P k G b) := by
 convert Cell.predictor_price P k G b h he hs using 1; unfold clover Cell.plotted Cell.out; ext x y; rw [Equiv.symm_apply_apply]

lemma desk {η B δ π δ' π':ℝ}{H H':Clip}(hv:∀ n,Floor b H n δ π)(h:Cell.Warm G k P b η B)(_he:0≤η)(_hs:η≤1){A:Bed}(hz:f.val=c.val*P.L.val)(W:Towers P.L)
  (hi:Towers.Diagonal (StepData.mk P k hz) b A W)
  (ho:∀ n, Floor A H' n δ' π') -- change Clip allowed
  : let S:= (StepData.mk P k hz : StepData c f)
    -- the Ψ defined with unmodified metric. carrier notation from keys.
    let M:=Pert.Bulk.carrier S.ratio W b A
    shaded f f G.ColorIndex ((cobound 1).acts f)*Cell.RootField k G S b = shaded f c G.ColorIndex M * shaded c c G.ColorIndex ((cobound 1).acts c):=by
  intro S M
  have hvEq:f=c*P.L:=Subtype.ext hz;subst hvEq
  let U:=installed S.ratio W.A0
  have Hinv (x):Line.onTree (Line.green S) x → Line.NativeLine S G b *ᵥ (Line.linePrecision G S b *ᵥ x)=x:= (h.invert c).2.1 x
  have ht:Cell.RootField k G S b=patron G (Precision.extracted S (Line.green S) U):=Cell.tree_station _ G rfl _ _ Hinv hi.trial -- arg order check
  change shaded (c*P.L) (c*P.L) G.ColorIndex (d 1 (c*P.L))*_= _*shaded c c G.ColorIndex (d 1 c)
  rw [ht,pigment,pigment,pigment,← patron_mul,← patron_mul,Precision.extracted,Matrix.mul_add, ← Matrix.mul_assoc,d_d_vac,Matrix.zero_mul,add_zero]
  have hw:=inherited_precision b A hi (hv _) (ho _) -- type
  rw [show M*d 1 c= _ from hw]

end YM.RG08.Spar

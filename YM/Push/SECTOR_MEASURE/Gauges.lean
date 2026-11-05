import YM.Push.SECTOR_MEASURE.Profile

/-!
# Bind with forests and gauges

Use invariance to connect the *individual* booked/profile columns back
to terms even under the original Haar integral. . Does not
move an assessed/unassigned formula off its tree. Fixed k and F
throughout, also for a tree mixture (which doesn't replace any
conditioned marginal by a new tag law).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure

open Filter Function Lattice RG Wilson Pressure Pressure.Stores Tree MeasureTheory

open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {x W : ℝ}

lemma toll_gauge (g : Site f → G.El) (U : Config G f) (p : Cell f) : toll (gauge g U) p = toll U p := by
  simp [toll]

lemma choice_gauge (hm : S.patch.Branches S.kernel G) (U : Config G f) (k : S.Choices) (g : Site f → G.El) :
    S.likelihood (gauge g U) k = S.likelihood U k ∧
    S.prediction (gauge g U) k = gauge (g ∘ S.ratio.embed) (S.prediction U k) := by
  constructor
  · unfold StepData.likelihood; apply congr_arg₂
    · refine Finset.prod_congr rfl fun j _ => ?_; rw [expandAt_gauge]; exact (S.patch.frame_gauged hm ..).1
    refine Finset.prod_congr rfl fun j _ => ?_; rw [S.updateGauged hm]; exact (S.patch.bond_gauge (h:=hm) ..).1
  funext i
  unfold StepData.prediction
  rw [S.updateGauged hm,(S.patch.bond_gauge (h:=hm) ..).2]
  rfl

lemma wire_gauge (g : Site c → G.El) (Q V : Config G c) (b : Bond c) :
    wire (gauge g Q) (gauge g V) b = wire Q V b := by
  unfold wire Lattice.gauge
  rw [show g _*V b*_ * (g _*Q b*_)⁻¹ = g b.1*(V b*(Q b)⁻¹)*(g b.1)⁻¹ by group, G.chord_conj]



section symmetry
variable (D : Allocation G S x W)









end symmetry

section applications
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]



end applications

/-- For fixed S, even the type of stipulated Forests is finite. Thus can also do any
finite probability mixture (e.g., if supplied, a tree tag law).
Nonempty at actual L; nothing here buys invariance of a *scheme* from
independent tags. -/
lemma finite_forests : Finite (Forest S.ratio) := by
  haveI : Finite Step := Finite.of_injective (fun x : Step => (x.dir,x.neg)) (by rintro ⟨a,b⟩ ⟨c,d⟩ h; cases Prod.mk.inj h; congr)
  let g (F : Forest S.ratio) : (Site f → Step) × (Site f → Fin (4*S.patch.L.val+1)) :=
    ⟨F.up,fun i => ⟨F.height i,Nat.lt_succ_of_le (F.bound i)⟩⟩
  apply Finite.of_injective g
  rintro ⟨u,h,n,o,p⟩ ⟨u',h',n',o',p'⟩ he
  have ht : u = u' := congr_arg Prod.fst he
  have hx : h = h' := funext fun i => congr_arg Fin.val (congr_fun (congr_arg Prod.snd he) i)
  subst ht hx; rfl





end YM.Push.SectorMeasure

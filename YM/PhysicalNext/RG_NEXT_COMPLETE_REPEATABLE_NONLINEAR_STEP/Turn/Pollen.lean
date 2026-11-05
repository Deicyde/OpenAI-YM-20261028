import YM.PhysicalNext.ORDERED_AFFINE_2B.SymWhole
import YM.PhysicalNext.ORDERED_AFFINE_2B.Till
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Rods

/-!
# Preserve E6 symmetries: INCLUDING the window cut
This is the actual inverse+ordered data of the first regeneration, not
borrowing Cab estimates at altered panels. Even though we rely on the same
finite-dimensional warp APIs, `panelpad` uses **ANY** endpoints in radius B,
not the Semester window's ALL endpoints in B/20.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Turn
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory Matrix
open AnalyticBridge.GaussianFieldAlignment Locations Channels Orthogonal Tensor
open ConnectedActivityE6 Shell Coat SliceRows Pulse Itinerary Control
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (s : Signed) (b : Site c) (V : Config G c)

abbrev Rev (V : Config G c) (S : StepData c f) := Orthogonal.move (fiber s b V S) (diagram s b S)
abbrev Spray (V : Config G c) (S : StepData c f) := warp (fiber s b V S) (diagram s b S)
abbrev exhale (V : Config G c) (S : StepData c f) (z : Air f G) : Air f G := WithLp.toLp 2 (Rev s b V S z.ofLp)

lemma sumRev (z u : Tubular f G → ℝ) : Rev s b V S (z+u)=Rev s b V S z+Rev s b V S u := Matrix.mulVec_add ..
lemma smulRev (t : ℝ) (z : Tubular f G → ℝ) : Rev s b V S (t • z)=t • Rev s b V S z := Matrix.mulVec_smul ..
lemma tapeRev (v : Directions G f) : stand (wheels (S:=S) s b V v) = Rev s b V S (stand v) := by
  apply tape.injective; funext i; exact (move_tape (fiber s b V S) (diagram s b S) (ConnectedActivityE6.stand v) i).symm

namespace Parked
open OrderedAffine2B.SymWhole
variable {s b} {P : Teller G} {F : Forest S.ratio} {T : Tube G S} {X : Coat T F} {Y : Coat T (Locations.forest s b F)}
variable (h : Parked s b X Y) (hp : P.Funds S T)

include h hp
lemma forming (a : Tubular f G → ℝ) : Y.form *ᵥ Rev s b X.V S a = (X.form *ᵥ a) ∘ Orthogonal.addr (perChannel s b S) G.ColorIndex := by
  obtain ⟨_,_,hl,-⟩:= hp.feeds; let u:= erect G a
  have ht : a=stand u := rfl; have hb := tapeRev s b X.V u (S:=S)
  funext i; change Y.form.mulVec (Rev s b X.V S (stand u)) i= (X.form*ᵥ stand u) _
  rw [← hb,← Y.charged_for hl,← X.charged_for hl]; simp only [ConnectedActivityE6.stand,h.strands (funds_branch hp)]; rfl
lemma adjoint (a : Coat.Target c f G → ℝ) :
    Y.form.transpose *ᵥ (a ∘ Orthogonal.addr (perChannel s b S) G.ColorIndex) = Rev s b X.V S (X.form.transpose *ᵥ a) := by
  let i:=Orthogonal.addr (perChannel s b S) G.ColorIndex
  let R:=Rev s b X.V S
  have hk (v : Tubular f G→ℝ) : dotProduct v (Y.form.transpose *ᵥ (a ∘ i)) = dotProduct v (R (X.form.transpose *ᵥ a)) := by
    obtain ⟨v,rfl⟩ := move_surj (fiber s b X.V S) (diagram s b S) v
    change dotProduct (R v) _=dotProduct (R v) _
    rw [dotProduct_transpose_mulVec,h.forming hp,move_dot,dotProduct_transpose_mulVec]; exact i.sum_comp (fun j=> a j*(X.form *ᵥ v) j)
  funext j; simpa using hk (Pi.single j 1)
omit hp in
lemma weary (u : Tubular f G→ℝ) : Y.sleepy*ᵥ Rev s b X.V S u=Rev s b X.V S (X.sleepy*ᵥ u) := by
  apply tape.injective; funext i; unfold Rev; rw [move_tape]
  have he {t : Forest S.ratio} (g : Coat T t) (a : Tubular f G→ℝ) (i : Bond f) : tape (g.sleepy*ᵥ a) i=if g.Hot i then 0 else tape a i := by
    ext j; rw [tape_ap,g.sleepy_act]; split <;> rfl
  rw [he,he]; split
  next hp => rw [if_pos ((h.eligible i).1 hp),map_zero]
  next ht => rw [if_neg (mt (h.eligible i).2 ht),move_tape]
lemma coherent : Y.plate=Spray s b X.V S X.plate := by
  apply warp_of; intro x y
  change dotProduct (Rev s b X.V S x) (_ *ᵥ Rev s b X.V S y)= _
  unfold Coat.plate; rw [Matrix.add_mulVec,Matrix.add_mulVec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,h.forming hp,h.adjoint hp,h.weary,← sumRev,move_dot]

end Parked

-- Moment frames using literal end projection of this kernel.
abbrev anypane (S : StepData c f) (B : ℕ) (i : Bond f) := {j : Bond f|hop S B j i}

lemma facespan (i : Tubular f G) (B : ℕ) :
    ((frames G S B).take i : Set (Tubular f G))=Orthogonal.together _ (anypane S B) i := by
  ext j; exact in_frame _ _

lemma span_turn (s : Signed) (b : Site c) (B : ℕ) (i j : Bond f) : diagram s b S j∈ anypane S B (diagram s b S i) ↔ j∈ anypane S B i := by
  change hop S B _ _ ↔ hop S B _ _
  unfold hop; simp_rw [ends_full, Finset.exists_mem_image,walk_near]

lemma pointwise (A : Mat f G) (B : ℕ) : (frames G S B).pad A=Next.SectorChange.Schur.per (together _ (anypane S B)) A := by
  let W := frames G S B
  rw [show together G.ColorIndex (anypane S B)=(fun i => ((W.take i):Set _)) from funext fun i=> (facespan _ _).symm]
  ext i j
  by_cases he : i∈ W.take j
  · rw [Next.SectorChange.Schur.per_read (fun i => ((W.take i):Set (Tubular f G))) _ (W.here _) he]
    change W.pad _ i j=_
    rw [W.inside A j ⟨i,he⟩]; congr!
  rw [W.outside A _ _ he,Next.SectorChange.Schur.per_zero (fun i => ((W.take i):Set (Tubular f G))) _ he]

lemma panelpad (A : Mat f G) (B : ℕ) : (frames G S B).pad (Spray s b V S A)=Spray s b V S ((frames G S B).pad A) := by
  rw [pointwise,pointwise]; apply warp_per; intro i; ext j; exact span_turn ..

namespace Parked
variable {F : Forest S.ratio} {P : Teller G} {T : Tube G S} {s b} {X : Coat T F} {Y : Coat T (Locations.forest s b F)} (h : Parked s b X Y) (hp : P.Funds S T)
include h hp
open OrderedAffine2B.SymWhole
lemma flashy : Y.kernelA=Spray s b X.V S X.kernelA := by unfold kernelA shutter; rw [h.coherent hp,h.aligned.2.1,panelpad]
lemma shone : Y.relating=Spray s b X.V S X.relating := by
  change (1/2:ℝ) • (Y.kernelA+Y.kernelA.transpose)=Spray s b X.V S ((1/2:ℝ) • (X.kernelA+X.kernelA.transpose))
  rw [h.flashy hp]; unfold Spray; rw [weave_scale,weave_add,weave_trans]
lemma shuts : Y.shreds=Spray s b X.V S X.shreds := by
  change Y.plate*Y.relating-1=Spray s b X.V S (X.plate*X.relating-1); rw [h.shone hp,h.coherent hp]; unfold Spray; rw [weave_sub,weave_times,weave_one]
lemma preserving (he : X.relating.PosDef) : MeasurePreserving (exhale s b X.V S) X.dice Y.dice := by
  unfold dice Poll.sweep; rw [h.shone hp]
  have hf := Agreements.warp_cloud (fiber s b X.V S) (diagram s b S) X.relating he
  let e : Air f G ≃ᵐ (Tubular f G→ℝ) := -- synthesize
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Tubular f G => ℝ)).toHomeomorph.toMeasurableEquiv
  let C := Spray s b X.V S X.relating
  have he (C : Mat f G) : MeasurePreserving e (Poll.sweep C) (Next.SectorChange.Gaussian.cloud C) := ⟨e.measurable,rfl⟩
  exact (he C).symm.comp (hf.comp (he X.relating))
end Parked
namespace Tuned
variable {F : Forest S.ratio} {P : Teller G} {T : Tube G S} {s b} {X : Coat T F} {Y : Coat T (Locations.forest s b F)}
   (h : Tuned s b X Y) (hp : P.Funds S T) {W C : ℝ} (ht : ShellAccess S G X.x W X.width C)
include h hp ht
lemma tilling (a : Directions G f) (p : Mention c f) : Y.priced (wheels (S:=S) s b X.V a) p=X.priced a (perChannel s b S p) := by
  unfold Coat.priced; rw [if_congr (h.toParked.panel p) rfl rfl]; split
  · exact congr_arg _ (h.footing (funds_branch hp) ht p a)
  rfl
lemma line : Y.linearBill = Rev s b X.V S X.linearBill := by
  have he : ConnectedActivityE6.stand (Y.priced 0)=ConnectedActivityE6.stand (X.priced 0) ∘ Orthogonal.addr (perChannel s b S) G.ColorIndex := by
    funext i; have hu:=h.tilling hp ht 0 i.1; rw [map_zero] at hu; exact congr_fun (congr_arg WithLp.ofLp hu) i.2
  unfold linearBill; rw [he]; exact h.toParked.adjoint hp _
lemma means : Y.driftM=Rev s b X.V S X.driftM := by
  unfold driftM; rw [h.toParked.flashy hp,h.line hp ht]; unfold Rev Spray
  rw [← OrderedAffine2B.SymWhole.weave_trans, warp_mv]; exact (Matrix.mulVec_neg _ _).symm
lemma axle (β : ℝ) (z : Air f G) : Y.liftA β (exhale s b X.V S z)=wheels (S:=S) s b X.V (X.liftA β z) := by
  unfold liftA; rw [map_add,map_smul]
  have hc : Y.μ = wheels (S:=S) s b X.V X.μ := congr_arg (erect G) ((h.means hp ht).trans (tapeRev s b X.V X.μ).symm)
  exact congr_arg₂ (·+·) hc (congr_arg (gStep β • ·) (congr_arg (erect G) (tapeRev (S:=S) s b X.V (X.atmos z)).symm : Y.atmos (exhale s b X.V S z)=wheels (S:=S) s b X.V (X.atmos z)))
lemma ex (q : Signed) (i : Spot c f) (u : Directions G f) : Y.extracted (wheels (S:=S) s b X.V u) q i=X.extracted u (s*q) (wind s b S q i) := by
  apply bills (shiftSlot s b q S.ratio) _ _ (parents_go s b i q) _ _; intro j _
  unfold surcharge; have he : Y.selected q (spot S j) ↔ X.selected (s*q) (spot S ((shiftSlot s b q S.ratio) j)) := h.toParked.panel (q,j)
  rw [if_congr he rfl rfl]; split
  · rw [show Y.realPath q j (wheels (S:=S) s b X.V u) = X.realPath (s*q) ((shiftSlot s b q S.ratio) j) u from h.footing (funds_branch hp) ht (q,j) u]
  rfl
end Tuned
end YM.PhysicalNext.Repeat.Turn

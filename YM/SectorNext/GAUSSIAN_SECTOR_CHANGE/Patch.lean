import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Block


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Local patch at each active e

Bind the derivative prices with the sector's global output flag clause
only. No fine-search hypotheses and no flattening V globally.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.LocalJet
open Function Filter Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open YM.Push.SectorMeasure YM.Push YM.Bid YM.Next.Fluctuations YM.Next.SectorChange.Motion
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}

private lemma failed (A : Stores S) {V : Config G c} {x : ℝ} (h : A.flags=RG.flags (temp x) V)
    {o : Site c} (r : ℕ) (hr : o∉ A.dome r) : ∀ i : Site c, separation o i ≤ r → ∀ p : PlaqAxes, toll V (i,p) ≤ temp x := by
  intro i hi p
  by_contra! hx
  have he : i∈ A.flags := h.symm ▸ (flags_spec ..).2 ⟨(i,p), by exact YM.Work.E01.base_touched (i,p), hx⟩
  exact hr (halo_spec.mpr ⟨i, mem_union_right _ he, (separation_comm ..).trans_le hi⟩)

/-- Fine representative copy is small in a constant-block gauge, all
of whose choice may depend on o. Condition is only output seed
avoidance (for canonical channel; call on rotated output if needed).
Constants explicit for the caller. -/
theorem trim (R : ℕ) {x : ℝ} {A : Stores S} {V : Config G c} {o : Site c}
    {r : ℕ} (ho : o∉ A.dome r) (hr : R+1 ≤ r) (hp : 2*(R+1) < c.val) (h : A.flags=RG.flags (temp x) V) :
    let C := 16*(2*((R+1:ℕ):ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ)
    ∃ w : Site f → G.El, ∀ i : Bond f, separation o (S.ratio.parent i.1) ≤ R →
      G.chord (Lattice.gauge w (replica S.ratio V) i) ≤ C*temp x := by
  intro C
  obtain ⟨w,H⟩ := Work.E08.axial_patch o V R (R+1) (by omega) hp (temp x) (temp_nonneg x)
    (fun y hy => failed A h r ho y (hy.trans hr))
  refine ⟨constantGauge w S.ratio,fun i hi => ?_⟩
  rw [copied S.ratio S.patch.odd_side]
  unfold replica; split
  next h => rw [G.chord_one]; apply mul_nonneg _ (temp_nonneg _); unfold C; positivity
  next h => exact H _ hi

def allot (P : Patch) := 2*macroR P+P.L.val+predReach P+5

def permit (P : Patch) : ℝ := 16*(2*((allot P+1:ℕ):ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ)

private lemma attends (S : StepData c f) {o : Site c} {q : Cover} (hq : q ∈ box (macroR S.patch)) :
    separation o (S.ratio.parent (wrap f q + S.ratio.embed o))+1 ≤ allot S.patch := by
  let i := S.ratio.embed o
  let y := wrap f q + i
  have he : S.patch.L.val*separation o (S.ratio.parent y) ≤ separation i y + S.patch.L.val := by
    change S.ratio.count.val*_ ≤ _ + S.ratio.count.val
    simpa only [Ratio.embed_parent, i] using Corona.foreshorten S.ratio i y
  have hl : 1 ≤ S.patch.L.val := S.patch.L.property
  have hh : separation o (S.ratio.parent y) ≤ S.patch.L.val*separation o (S.ratio.parent y) := by nth_rw 1 [← Nat.one_mul (separation _ _)]; gcongr
  have hg : separation i y ≤ macroR S.patch := Work.E08.separation_box_add _ hq
  unfold allot; change _ ≤ _ at he
  change separation o (S.ratio.parent y) + _ ≤ _; omega

lemma swing_settle (a : Directions G f) (w : Site f → G.El) (x r) :
    settle S x r (swing w a)=settle S x r a := by unfold settle; simp only [swing_size]

/-- At an active e, choose ONE rotation of the a tangent over its
whole macro comparison. The RHS of link_bound can thus use separate
independent envelope for each p, b. -/
def Sponsored {x : ℝ} (A : Stores S) (F : Tree.Forest S.ratio) (k : S.Choices) (V : Config G c)
    (i : Active A x F) (ε : ℝ) :=
    ∃ w : Site f → G.El,
    let o := S.ratio.parent i.val.val.1
    let y (z : Cover) := wrap f z + S.ratio.embed o
    ∀ a : Directions G f,
      (∀ z ∈ box (macroR S.patch), ∀ p : PlaqAxes,
        ‖Work.F03.faceCurl (y z,p) (Flat.labels (swing w a))‖ ≤ ‖plaquetteJet S V 1 (y z,p) a‖ +
          ε * settle S (S.ratio.parent (y z)) 1 a) ∧
      (‖bills S (Flat.labels (swing w a)) (o,coord i.val.val.2)‖ ≤ ‖blockJet V k 1 (o,i.val.val.2) a‖ +
          ε * settle S o (predReach S.patch) a)

lemma sponsorship (P : Patch) (K : KernelChoices) (G : Gauge) (h : P.Branches K G) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {c f : Side} (S : StepData c f) (F : Tree.Forest S.ratio) (A : Stores S) (V : Config G c)
      (k : S.Choices) (x : ℝ), S.patch=P → S.kernel=K → allot P+1 ≤ 10*radiusB x → 2*(allot P+1) < c.val →
      A.flags=RG.flags (temp x) V → permit P*temp x ≤ δ → ∀ i : Active A x F, Sponsored A F k V i ε := by
  obtain ⟨B,d,hB,hd,he⟩ := Block.block_comparison G P K h hε
  obtain ⟨r,hr,hT⟩ := face_comparison G hε
  let y := min r d
  refine ⟨y,lt_min hr hd,?_⟩
  intro c f S F A V k x hP hK hl ht hF hp i
  obtain ⟨w,hw⟩ := trim (allot P) (remote i) hl ht hF
  let U := replica S.ratio V
  let u := Lattice.gauge w U
  let o := S.ratio.parent i.val.val.1
  have H0 (p : Bond f) (h : separation o (S.ratio.parent p.1) ≤ allot P) : G.chord (u p) ≤ y := (hw _ h).trans hp
  let z (q : Cover) := wrap f q+S.ratio.embed o
  have hS : S.patch.Branches S.kernel G := by rw [hP,hK]; exact h
  refine ⟨w, fun a => ⟨fun q hq p => ?_,?_⟩⟩
  · let b : Cell f := (z q,p)
    have H := hT S b u (fun e h => ?_) (swing w a)
    rotate_left
    · refine (H0 e ?_).trans (min_le_left ..)
      have he := separation_triangle o (S.ratio.parent b.1) (S.ratio.parent e.1)
      have hv := attends (o:=o) S hq
      rw [hP] at hv; change separation o (S.ratio.parent b.1)+_ ≤ _ at hv; omega
    have H' := (p_auth w U b (face_smooth u b).contDiffAt).2 a
    rw [swing_settle, H', ← canon_p V (S:=S), p_empty S] at H
    calc
      _ ≤ ‖G.adjoint (w b.1) (plaquetteJet S V 1 b a)‖ + ‖G.adjoint (w b.1) (plaquetteJet S V 1 b a) - Work.F03.faceCurl b (Flat.labels (swing w a))‖ := by
        set t := G.adjoint (w _) (plaquetteJet S V 1 b a)
        set y := Work.F03.faceCurl b (Flat.labels (swing w a))
        have hh := norm_sub_le t (t-y); rwa [sub_sub_cancel] at hh
      _ ≤ _ := add_le_add (G.norm_adjoint ..).le H
  let b : Bond c := (o,i.val.val.2)
  obtain ⟨-,ha,hN⟩ := he S hP hK k u b (fun e hh => (H0 e (hh.trans (by unfold allot; omega))).trans (min_le_right ..))
  have H := (hN (swing w a)).2
  rw [swing_settle, (b_auth hS w U b k ha).2, ← canon_b V _ _ hS,b_empty _ _ _ hS] at H
  set t := G.adjoint (w (S.ratio.embed b.1)) (blockJet V k 1 b a) with eq
  let y := bills S (Flat.labels (swing w a)) (pole b)
  refine (show ‖y‖ ≤ ‖t‖+‖t-y‖ from ?_).trans (add_le_add (by unfold t; rw [G.norm_adjoint]) ?_)
  · have hh := norm_sub_le t (t-y); rwa [sub_sub_cancel] at hh
  simpa only [eq,hP] using H
end YM.Next.SectorChange.LocalJet

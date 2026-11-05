import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Author
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gap


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Actual periodic D entry exponential price

Uses uncut exp-rate receipts at true path lengths. No restriction on
winding multiplicities or growth of the number of paths. Distances here
on initial sites (and after parent for fine keys/charges); use in Window.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Wisps
open Function Filter Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Tree
open YM.Push.SectorMeasure YM.Bid YM.Next.Fluctuations Matrix
open YM.Push.SectorMeasure.Oriented Motion LocalJet Rows Gaussian NormedSpace
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ} {σ : ℝ}

private lemma peak (A : Stores S) (F : Forest S.ratio) (j : Rows.In x A F (G:=G))
    (W : Stencils S) (e : Bond f) :
    ‖fresh x W A F (axisPrice j) e‖ ≤ if e=j.1.val.val then 1 else 0 := by
  split
  next h => rw [h,Gap.freshly_read,on_axis,Pi.single_eq_same,OrthonormalBasis.norm_eq_one]
  next h =>
    unfold fresh
    split
    · rename_i hi; split
      · rename_i hx
        have hl : (⟨⟨e,hi⟩,hx⟩:Active A x F) ≠ j.1 := fun he => h (congr_arg (fun a : Active A x F => a.val.val) he)
        rw [on_axis,Pi.single_eq_of_ne hl,norm_zero]
      · rw [norm_zero]
    · rw [norm_zero]

abbrev front (A : Stores S) (F : Forest S.ratio) (i : Rows.In x A F (G:=G)) : Site c := S.ratio.parent i.1.val.val.1
abbrev down (S : StepData c f) (i : Rows.Receipt G S) := i.1.1.act (roots S (i.1.2.elim (fun x => .inl x.1) Sum.inr))

def rate (σ : ℝ) (D : ℕ) := Real.exp (σ*D)
lemma rate_pos (σ : ℝ) (D : ℕ) : 0<rate σ D := Real.exp_pos _
lemma rate_add (σ : ℝ) (i j : ℕ) : rate σ (i+j) = rate σ i * rate σ j := by unfold rate; rw [Nat.cast_add,mul_add,Real.exp_add]
lemma rate_le (h : 0 ≤ σ) {i j : ℕ} (e : i ≤ j) : rate σ i ≤ rate σ j := by unfold rate; gcongr

private lemma summit (A : Stores S) (F : Forest S.ratio) (j : Rows.In x A F (G:=G))
    (W : Stencils S) (U : Config G f) (s : Signed) (o : Site c) (n : ℕ) {u : Site c} {k : ℕ}
    (hk : separation u (s.act o) ≤ k) (σ : ℝ) (hσ : 0 ≤ σ) :
    let z := fresh x W A F (axisPrice j)
    rate σ (separation u (front A F j)) * settle S o n (inChannel s U z) ≤ rate σ (k+n+1) := by
  intro z
  let v := fun i : Bond f => sendEdge s 0 i
  let M := members S o n
  let e := j.1.val.val
  have hu (i : Bond f) : ‖inChannel s U z i‖ ≤ if v i=e then 1 else 0 := by rw [in_size]; exact peak ..
  have hs : settle S o n (inChannel s U z) ≤ ∑ i ∈ M, if v i=e then (1:ℝ) else 0 := sum_le_sum fun i _ => hu i
  have hx : Injective v := sendEdge_injective s 0
  rw [← sum_image (f:=fun i => if i=e then (1:ℝ) else 0)] at hs
  · rw [sum_ite_eq'] at hs
    by_cases h : e∈M.image v
    · simp only [h,↓reduceIte] at hs
      obtain ⟨i,hi,he⟩ := mem_image.mp h
      have hw := (mem_filter.mp hi).2
      have hh := spin_separation (S:=S) i s o
      have hd : separation u (front A F j) ≤ k+n+1 := by
        have hc : S.ratio.parent e.1=front A F j := rfl
        unfold v at he; rw [he,hc] at hh; apply (separation_triangle u (s.act o) _).trans; omega
      apply le_trans (mul_le_of_le_one_right (rate_pos ..).le hs)
      exact rate_le hσ hd
    simp only [h,↓reduceIte] at hs
    apply le_trans _ (rate_pos ..).le
    exact mul_nonpos_of_nonneg_of_nonpos (rate_pos ..).le hs
  exact fun _ _ _ _ => @hx _ _

private def indexCost (σ : ℝ) (u : Site c) (A : Stores S) (F : Forest S.ratio) (j : Rows.In x A F (G:=G)) :=
  rate σ (separation u (front A F j))

private lemma scored (A : Stores S) (F : Forest S.ratio) (j : Rows.In x A F (G:=G)) (W : Stencils S)
    (s : Signed) (i : Cell f) (σ C : ℝ) (hc : 0 ≤ C) (hσ : 0 ≤ σ) (V : Config G c)
    (h : ∀ (S : StepData c f) (p : Cell f) (U : Config G f) (a : Directions G f),
      ‖fderiv ℝ (pTest U p) 0 a‖ ≤ C * settle S (S.ratio.parent p.1) 1 a)
    {k} {u : Site c} (hu : separation u (s.act (S.ratio.parent i.1)) ≤ k) :
    let a := fresh x W A F (axisPrice j)
    indexCost σ u A F j * ‖plaquetteJet S V s i a‖ ≤ C * rate σ (k+2) := by
  intro a
  rw [plaquetteJet,(plaquette_turn s V i (face_smooth _ _).contDiffAt).2]
  refine (mul_le_mul_of_nonneg_left (h S i _ _) (rate_pos ..).le).trans ?_
  rw [mul_left_comm]
  rw [show k+2=k+1+1 by omega]
  exact mul_le_mul_of_nonneg_left (summit A F j W _ s _ 1 hu σ hσ) hc

private lemma stacked {C E Λ : ℝ} (T : Tube G S) (hT : T.up.Bounds T.high σ E Λ) (A : Stores S) (F : Forest S.ratio)
    (j : Rows.In x A F (G:=G)) (W : Stencils S) (i : Twin f) (hi : i.2=true) (s : Signed) (V : Config G c) (hc : 0 ≤ C)
    (h : ∀ (S : StepData c f) (p : Cell f) (U : Config G f) (a : Directions G f),
      ‖fderiv ℝ (pTest U p) 0 a‖ ≤ C * settle S (S.ratio.parent p.1) 1 a) :
    indexCost σ (s.act (S.ratio.parent i.1.1)) A F j * ‖faceKick T x V (fresh x W A F (axisPrice j)) s i‖ ≤
      E*(C * rate σ 2) := by
  let R := Stores.till x; let U := facade S s V 0; let a := fresh x W A F (axisPrice j)
  let p (l : ℕ) := (T.up.row i.1.2 l).2
  let l (j : ℕ) := (T.up.row i.1.2 j).1
  let b (i : Cell f) := plaquetteJet S V s i a
  let H (j : ℕ) : G.Color := if (p j).length ≤ R then l j •
    G.adjoint (travel U i.1.1 (p j).walk) (b (Work.F03.slotFace (p j) i.1.1)) else 0
  have hs : Summable H := barrel_summed T.up R _ _ i.1 hT
  rcases hT.rows i.1.2 with ⟨hQ,he,hE⟩
  let u := s.act (S.ratio.parent i.1.1)
  let X := indexCost σ u A F j
  let D (i : ℕ) := |l i| * rate σ (p i).length
  have hd := rate_pos σ 2
  simp only [faceKick,hi,↓reduceIte]
  change X * ‖∑' j, H j‖ ≤ _
  calc
    _ ≤ X * ∑' j, ‖H j‖ := mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs.norm) (rate_pos ..).le
    _ = ∑' j, X*‖H j‖ := by rw [hs.norm.tsum_mul_left]
    _ ≤ ∑' j, (C*rate σ 2)*D j := by
      apply Summable.tsum_le_tsum (fun j₀ => ?_) (hs.norm.mul_left _) ((show Summable D from he).mul_left _)
      unfold H; split
      · rw [norm_smul, G.norm_adjoint, Real.norm_eq_abs, mul_left_comm]
        let z := Work.F03.slotFace (p j₀) i.1.1
        have ht := slot_distance (S:=S) (p j₀) i.1.1
        have hv : separation u (s.act (S.ratio.parent z.1)) ≤ (p j₀).length := by
          unfold u; rw [separation_signed]; unfold Slot.length; exact ht.trans (by omega)
        have hm := scored A F j W s z σ C hc hT.width.le V h hv
        refine (mul_le_mul_of_nonneg_left hm (abs_nonneg (l j₀))).trans_eq ?_
        unfold D; rw [rate_add]; ring
      · rw [norm_zero,mul_zero]; exact mul_nonneg (mul_nonneg hc hd.le) (hQ j₀)
    _ = (C*rate σ 2)*∑' j, D j := tsum_mul_left
    _ ≤ _ := (mul_le_mul_of_nonneg_left hE (mul_nonneg hc hd.le)).trans_eq (mul_comm ..)

def stems {S : StepData c f} (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ) (k : S.Choices) (V : Config G c) (σ C : ℝ) :=
    ∀ (i : Receipt G S) (j : Rows.In x A F (G:=G)), rate σ (separation (down S i) (front A F j)) *
      |move T x V k (shots S x) A F i j| ≤ C

lemma written (K : KernelChoices) (P : Patch) (G : Gauge) (Pt : Teller G) (hK : P.Branches K G) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → S.kernel=K →
      Pt.Funds S T → ∀ (A : Stores S) (V : Config G c) (F : Forest S.ratio) (x : ℝ),
      A.flags=RG.flags (temp x) V → span P x ≤ radiusB x/50 → allot P+1 ≤ 9*radiusB x → 2*(allot P+1)<c.val →
      permit P*temp x ≤ δ → ∀ k : S.Choices, stems A F T x k V Pt.top.width C := by
  obtain ⟨C,hC,H⟩ := face_global G
  obtain ⟨B,δ,hB,hδ,hE⟩ := earned P K G hK
  let σ := Pt.top.width
  let a := Real.sqrt Pt.top.clip.direct
  let b := max Pt.top.paths a
  let M := b*(C*rate σ 2)+Real.sqrt K.penalty*(B*rate σ (predReach P+1))
  have hl : 0 < b := lt_of_lt_of_le (Real.sqrt_pos.2 Pt.top.clip.quadratic_pos) (le_max_right ..)
  have hm : 0 < M := by unfold M; have := rate_pos σ 2; have := Real.sqrt_pos.2 K.penalty_pos; have := rate_pos σ (predReach P+1); positivity
  refine ⟨slip*M,δ,mul_nonneg slip_pos.le hm.le,hδ,?_⟩ -- order
  intro c f S T he hk hT A V F x hA hx hs hp hd k i j
  obtain ⟨t,u,hH,-⟩ := hT.feeds
  let o := down S i
  let r := rate σ (separation o (front A F j))
  let W := shots S x
  let kx := fresh x W A F (axisPrice j)
  have hw (u : LogArray G (Slots S)) : |tape.symm u i| ≤ ‖u i.1‖ := by
    change |u i.1 i.2| ≤ _
    rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ (u i.1) i.2]
    simpa using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i.2) (u i.1)
  change r * |tape.symm (Rows.restrict x W A F _) i| ≤ _
  refine (mul_le_mul_of_nonneg_left (hw _) (rate_pos ..).le).trans ?_
  unfold Rows.restrict; split
  · rename_i ha
    rw [norm_smul,Real.norm_of_nonneg slip_pos.le,mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ slip_pos.le
    rcases i with ⟨⟨s,t'|t'⟩,i⟩
    · change r * ‖faceKick T x V kx s t'‖ ≤ _
      have hz : b*(C*rate σ 2) ≤ M := by unfold M; apply le_add_of_nonneg_right; have := Real.sqrt_pos.2 K.penalty_pos; have := rate_pos σ (predReach P+1); positivity
      apply le_trans _ hz
      cases hh : t'.2
      · dsimp only [faceKick]; rw [hh]; simp only [Bool.false_eq_true, ↓reduceIte, norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_left_comm r]
        rw [hT.high]
        refine mul_le_mul (le_max_right Pt.top.paths a) ?_ (mul_nonneg (rate_pos ..).le (norm_nonneg _)) hl.le
        exact scored A F j W s t'.1 σ C hC.le Pt.top.width_pos.le V (fun S => H S) (k:=0) (le_of_eq (separation_self _))
      · rw [← hT.high] at hH
        refine (stacked T hH A F j W _ hh s V hC.le ?_).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (mul_nonneg hC.le (rate_pos ..).le))
        exact fun S => H S
    · change r * ‖noiseKick V k kx s t'‖ ≤ _
      unfold noiseKick; rw [norm_neg,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _), hk]
      -- pull the oriented base gauge but keep actual directions
      obtain ⟨hQ,hD,hG⟩ := (hE S he hk F A V x hA hx hs hp hd).noise s k t' ha
      rw [blockJet,(block_turn s V t' k hD).2]
      rw [mul_left_comm]
      refine le_trans (b:=Real.sqrt K.penalty*(B*rate σ (predReach P+1))) ?_ (le_add_of_nonneg_left (mul_nonneg hl.le (mul_nonneg hC.le (rate_pos ..).le)))
      refine mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (hG _) (rate_pos ..).le).trans ?_) (Real.sqrt_nonneg _)
      rw [mul_left_comm,← he]
      have ht := summit A F j W (replica S.ratio V) s t'.1 (predReach S.patch) (k:=0) (le_of_eq (separation_self _)) σ Pt.top.width_pos.le
      rw [zero_add] at ht; exact mul_le_mul_of_nonneg_left ht hB.le
  · rw [norm_zero,mul_zero]; exact mul_nonneg slip_pos.le hm.le
end YM.Next.SectorChange.Wisps

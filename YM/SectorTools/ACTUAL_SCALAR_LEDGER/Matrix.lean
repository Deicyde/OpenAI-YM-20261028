import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Agreements
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Local
import YM.Next.MAXWELL.Silt
import YM.Next.WARD_BIN.LabelEst
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Reconstruct
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.LOCAL_SPLITTING.Clocks
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Fiber
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free
import YM.UVNext.COUPLING_RESET.Reset
import YM.UVNext.FREE_STRESS_CERTIFICATE.ShellForce
import YM.UVNext.FREE_STRESS_CERTIFICATE.Triangle


set_option warningAsError false
set_option autoImplicit false
set_option synthInstance.maxSize 1024
/-!
# End-panel covariance, mean, and prices of the true completed precision

Use the real variable-space Gram on active links, padded by identity on frozen non-tree,
forming principal compressions of THAT precision. All statements at one tree/window policy;
no dropping rows meeting window boundaries or deleting zero Fourier modes. Uses the
symmetric whole-endpoint prescription of `SectorChange.panels`, NOT a theorem equating
it to E's midpoint prescription. Window size in coarse units; absolute scalar costs per
coordinate. No regular-germ assertion on any indicators. In particular `supported` is
only for pricing values in the all-fields Scanner, it reads the flag equality on the whole
configuration, do not infer local support of the resulting function.
-/
noncomputable section
namespace YM.SectorTools.ActualScalar
open Function Filter Set MeasureTheory Matrix RG Wilson Lattice Pressure Pressure.Stores Precision Tree Push.SectorMeasure
  Next.SectorChange Schur Further GaussianScalar AnalyticBridge.ResetIncome
  AnalyticBridge.GaussianFieldAlignment
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} (e : Plate G S) (h : Doors e) (A : Stores S)
    (k : S.Choices) (V : Config G c) (Y : GaussianScalar.Frozen (held e A) G)
    {s η M D : ℝ}

/-- Both decompositions in common positive convention on the tree slice. -/
def splitKey : Rows.In e.x A e.forest (G:=G) ⊕ Hold G (held e A) ≃ Key e.forest G :=
  ((moving e A).symm.sumCongr (Equiv.refl _)).trans (mergeBits ..)
lemma live_eq (i : Rows.In e.x A e.forest (G:=G)) : splitKey e A (.inl i)=live A e.forest e.x i := rfl
lemma fill_eq (C : Wall (Rows.In e.x A e.forest (G:=G))) :
    filled (held e A) (C.submatrix (moving e A) (moving e A))=fill (live A e.forest e.x) C := by
  let Q := filled (held e A) (C.submatrix (moving e A) (moving e A))
  let u := splitKey e A
  have hm : Q.submatrix u u = Completion.wide C 1 := by
    unfold Q filled u splitKey
    let t := (moving e A).symm.sumCongr (Equiv.refl (Hold G (held e A)))
    rw [Equiv.coe_trans, ← Matrix.submatrix_submatrix, sortBits]
    ext (i|i) (j|j) <;> simp [Completion.wide]
  ext i j; obtain ⟨i,rfl⟩ := u.surjective i; obtain ⟨j,rfl⟩ := u.surjective j
  exact congr_fun (congr_fun (hm.trans (fill_read _ _ u (live_eq e A)).symm) i) j
lemma sigma_fill : (page e h A k V).sigma Y = fill (live A e.forest e.x) (e.Gram A V k) := (sigma_eq ..).trans (fill_eq ..)
lemma complete_fill : (page e h A k V).complete Y = fill (live A e.forest e.x) (e.Cov A V k) := fill_eq ..

def distance (i : Key e.forest G) := S.ratio.parent i.1.val.1
abbrev rangeSize (x : ℝ) : ℝ := ((radiusB x / 60 : ℕ) : ℝ)

/-- Use the same whole-link endpoint window as SectorChange. -/
def frame (hb : 120 ≤ radiusB e.x) : Lens (Key e.forest G) where
  eye i := Finset.univ.filter (fun j => meeting S e.x i.1.val j.1.val)
  sees i := Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun y hy z hz =>
    (separation_triangle y (distance e i) z).trans (by
      have hi : separation y (distance e i) ≤ 1 := (separation_comm ..).trans_le (meetings i.1.val hy)
      have hj : separation (distance e i) z ≤ 1 := meetings i.1.val hz
      omega)⟩
lemma eye_test (hb) (i j : Key e.forest G) : i∈(frame e hb).eye j ↔ meeting S e.x j.1.val i.1.val := by simp [frame]
lemma away (hb) : (frame e hb).Outside (distance e) (rangeSize e.x) := by
  intro i j he
  contrapose! he
  apply (eye_test ..).mpr; intro p hp q hq
  have he' : separation (distance e j) (distance e i) < radiusB e.x / 60 := by rw [separation_comm]; exact_mod_cast he
  have hl : separation p (distance e j) ≤ 1 := (separation_comm ..).trans_le (meetings j.1.val hp)
  have hi : separation (distance e i) q ≤ 1 := meetings i.1.val hq
  exact ((separation_triangle p (distance e i) q).trans (Nat.add_le_add ((separation_triangle p (distance e j) (distance e i)).trans (Nat.add_le_add hl he'.le)) hi)).trans (by omega)
lemma panels_loc (hb) : let v := live (G:=G) A e.forest e.x; let Z := frame e hb
    (fun i => v ⁻¹' (Z.eye (v i) : Set (Key e.forest G))) = panels (G:=G) A e.forest := by
  ext i j; exact eye_test e hb _ _

private lemma lens_per {ι : Type} [Fintype ι] [DecidableEq ι] (Z : Lens ι) (C : Gaussian.Table ι) :
    Z.visit C 0 = per (fun i => ↑(Z.eye i)) C := by
  ext i j
  unfold Lens.visit Lens.plus
  rw [of_apply,zero_smul, add_zero]; split
  next hi =>
    rw [per_read (fun i => (Z.eye i : Set ι)) C (Z.sees j) hi]; congr! -- Fintype on subtype
  next hi => exact (per_zero (fun i => (Z.eye i : Set ι)) C hi).symm

lemma visit_per (hb) (hη : 0<η) (ht : Gapped (e.Gram A V k) η) :
    (frame e hb).visit ((page e h A k V).sigma Y) 0 = fill (live A e.forest e.x) (per (panels A e.forest) (e.Gram A V k)) := by
  rw [lens_per,sigma_fill, Completed.per_fill' _ (fun i => ↑((frame e hb).eye i)) ((frame e hb).sees) _ (sym_gram ..) hη ht,
    panels_loc]
lemma view_eq (hb) (hη : 0<η) (ht : Gapped (e.Gram A V k) η) :
    (page e h A k V).viewLens (frame e hb) Y = (page e h A k V).complete Y := by
  unfold Fiber.viewLens RawPrice.field
  rw [visit_per e h A k V Y hb hη ht,complete_fill,sym_fill (live A e.forest e.x) _ (splitKey e A) (live_eq e A)]; rfl
lemma C_eq (hb) (hη : 0<η) (ht : Gapped (e.Gram A V k) η) : let v := page e h A k V
    v.C Y = (v.screen (frame e hb)).C Y := by
  intro v; change v.C Y = blankOut _ (v.viewLens _ Y); unfold v
  rw [view_eq _ h _ _ _ _ hb hη ht]; exact (blank_meets ..).symm
lemma μ_eq (hb) (hη : 0<η) (ht : Gapped (e.Gram A V k) η) : let v := page e h A k V
    v.μ Y = (v.screen (frame e hb)).μ Y := by
  intro v
  change (chartMap e A).symm _ = viewBits (held e A) (RawPrice.meanAt _ (v.sigma Y) (spreadBits _ (linearCost (v.D Y) (v.b0 Y))))
  let H := held e A; let t := moving e A
  let P := per (panels A e.forest) (e.Gram A V k)
  let B := Rows.blame e.tube e.x V k (shots S e.x) A e.forest e.chip e.d (shellMap e A Y)
  unfold v RawPrice.meanAt; rw [visit_per _ h _ _ _ _ hb hη ht, ← fill_eq,linear_eq,chart_sym]
  let u := mergeBits H G
  have hs j : spreadBits H (B ∘ t) (u j) = Sum.elim (B ∘ t) (fun _ => 0) j := by unfold spreadBits u; rw [Equiv.symm_apply_apply]
  ext i
  change (-P.transpose *ᵥ B) (t i) = (- (filled H (P.submatrix t t)).transpose *ᵥ spreadBits H (B ∘ t)) (u (.inl i))
  rw [mulVec,dotProduct,mulVec,dotProduct, ← Equiv.sum_comp u]
  rw [← Equiv.sum_comp t,Fintype.sum_sum_type]
  simp only [hs,Sum.elim_inl,Sum.elim_inr,mul_zero,Finset.sum_const_zero,add_zero,Function.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_apply,neg_apply,transpose_apply,transpose_apply]
  exact congr_arg (fun x : ℝ => -x * B (t j)) (congr_fun (congr_fun (sortBits H (P.submatrix t t) 1) (.inl j)) (.inl i)).symm

/-- A second identification, including independence of the choice tag *on the same tree*
for the whole table, and equality to the genuine truncated `Affine.primary` used in
finite-history kernel estimates. No thermodynamic limit or off-flag substitution. -/
theorem canonical {P : Teller G} (hT : P.Funds S e.tube) (hL : Bid.Larger S (G:=G)) :
    let T := e.tube; let U := FreeResolvent.Affine.primary S e.forest k T.high T.up
    benchmark e h = e.Flat ∧ e.Flat = U (FreeResolvent.Affine.shorter (Stores.till e.x)) 0 ∧
      e.Flat = Native.kinetic e.tube e.forest k e.x := by
  intro T U
  have hv : e.Flat = Native.kinetic e.tube e.forest k e.x := by
    have hx (a : Directions G f) : Rows.bump T e.x 1 e.tag a = Rows.bump T e.x 1 k a := by
      funext i; obtain ⟨s,j|j⟩ := i
      · simp only [Rows.bump,Sum.elim_inl]
      unfold Rows.bump Rows.noiseKick; simp only [Sum.elim_inr, Flat.flat_probe _ _ _ _ hL.1]
    unfold Plate.Flat Native.kinetic Native.seed
    simp_rw [show e.tube=T by rfl,hx]
  refine ⟨flat_price_eq e h hL.1,?_,hv⟩
  rw [hv, ← Native.ground_gram _ _ _ _ hL.1, flat_exact _ _ _ _ _ hT hL (1:Config G c) rfl]; rfl

/-- Absolute location multiplicity PER coarse site including all real colors. -/
def count (L : Side) (G : Gauge) := Fintype.card (Site L) * (Fintype.card Axis * Fintype.card G.ColorIndex)
lemma count_bound : Push.Uniform.Multiplicity (distance e) (count S.patch.L G) := by
  intro x
  let J := Finset.univ.filter (fun i => distance e i=x)
  let t : J → Site S.patch.L × Axis × G.ColorIndex := fun i =>
    (S.ratio.residue i.val.1.val.1,i.val.1.val.2,i.val.2)
  have ht : Injective t := by
    intro i j he; obtain ⟨h1,h2⟩ := Prod.mk.inj he
    apply Subtype.ext; apply Prod.ext _ (Prod.mk.inj h2).2
    apply Subtype.ext; apply Prod.ext _ (Prod.mk.inj h2).1
    have hi := (Finset.mem_filter.mp i.property).2; have hj := (Finset.mem_filter.mp j.property).2
    unfold distance at hi hj
    rw [← S.ratio.unpack_at i.val.1.val.1,← S.ratio.unpack_at j.val.1.val.1,hi,hj,h1]
  change J.card ≤ _; simpa only [Fintype.card_coe,Fintype.card_prod,count] using Fintype.card_le_of_injective _ ht

/-- Explicit post-L Expense, using the SAME GaussianFieldAlignment.Ready parameters
on matched and pricing fallback sectors, and on the real canonical flat bill. -/
def expense (G : Gauge) (d : Side) (v : AnalyticBridge.GaussianFieldAlignment.Rates) : Expense where
  η := v.s
  low := min v.η 1
  high := v.C+1
  counts := count d G
  η_pos := v.width_pos
  low_pos := lt_min v.η_pos one_pos
  high_pos := by linarith [v.cost_pos]
lemma hi (G : Gauge) (d v) : (expense G d v).low ≤ (expense G d v).high := (min_le_right ..).trans (by change 1≤v.C+1; linarith [v.cost_pos])

lemma precision_price (v : AnalyticBridge.GaussianFieldAlignment.Rates)
    (hv : AnalyticBridge.GaussianFieldAlignment.Ready A e.forest e.x e.tube k V v.s v.η v.C v.D) :
    RawPrice (expense G S.patch.L v) (distance e) ((page e h A k V).sigma Y) := by
  have ht := (MatrixBounds.mk hv.ends.prec (sym_gram ..) hv.solvent).pad (p:=distance e) (e:=live A e.forest e.x)
  let C := fill (live A e.forest e.x) (e.Gram A V k)
  have hr := ht.pours
  have he := ht.lower
  rw [sigma_fill]; refine ⟨fun a => ?_,Matrix.isHermitian_iff_isSymm.mpr ht.symm,⟨fun i => hr.row i,fun i => ?_⟩,count_bound e⟩
  · rw [← sumSq_dot]; refine ⟨he a, (le_abs_self _).trans ((estimate (L:=C) (hr.weaker v.width_pos.le le_rfl) a a).trans ?_)⟩
    unfold expense; dsimp only; linarith
  have ht := hr.col i
  simp_rw [separation_comm _ (distance e i)] at ht
  exact ht

lemma screened_eq (hb) (hη : 0<η) (ht : Gapped (e.Gram A V k) η) :
    (page e h A k V).screen (frame e hb) = page e h A k V := by
  unfold Fiber.screen
  congr
  · exact funext (fun y => (C_eq _ h A k V y hb hη ht).symm)
  · exact funext (fun y => (μ_eq _ h A k V y hb hη ht).symm)

end YM.SectorTools.ActualScalar

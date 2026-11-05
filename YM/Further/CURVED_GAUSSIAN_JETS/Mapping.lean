import YM.Further.CURVED_GAUSSIAN_JETS.Actual
import YM.Further.CURVED_GAUSSIAN_JETS.Mirrors
import YM.Further.CURVED_GAUSSIAN_JETS.Stacks
import YM.Further.CURVED_GAUSSIAN_JETS.Truncated

/-!
# D producer (linear coefficients) for a particular sector mapping

Single-copy actual `Precision.tested` noise (positive common orientation,
same tag in every read), and path `shorten` cutoff and signed channels
for incoming `K` path/direct part! Not altering any `change` inputs to
assert this works as the genuine change on a `Rep`, nor constructing the
constant part (may depend on actual held Y, clamps, ...). Rows may stay on
all plaquette/bond keys: before doing this in a proposed mapping, ensure
that rows which would have been omitted have zero active a coefficient
(e.g. potential-a stencils miss the active set) AND set their constants
appropriately. `ell` is evaluated in the copy connection in that channel,
not itself differentiated in a here. No claim about a procedure using
extra Q evaluations in per-path orientation channels at nonzero V or
rotating the k term by the Q tangent orientation without checking it.
See Mapping.income; genuine uniform (if post L) A and B0 receipts in
source conventions after choosing avoidance budget. Doesn't identify
that cutoff Gram determinant with the cumulative Horizon uncut one even
on the trivial background. Identity on inactive F.Free coords as always;
at caller if also tree links identity-completed they must be expunged by
same block identities. No PNC on unused numerical probabilities.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
noncomputable section
namespace YM.Further.CurvedGaussianJets.Mapping
open Function Filter Matrix Gauge Lattice Wilson Tree RG Precision Pressure Exterior Bid SectorNext.Vacuum Progress.StationaryScenes Shape Pockets Stacks
open Green (wt wt_pos Both address link)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology
variable {G : Gauge} {f c : Side} {S : StepData c f} {F : Forest S.ratio} (H : Finset F.Free)
    (W : PathData G) (p : Clip) (N : ℕ) (V : Config G c) (k : S.Choices)

abbrev Domain (G : Gauge) (c f : Side) := (Signed × Shape.Page G f 2) ⊕ ((Signed × Shape.Page G f 2) ⊕ Shape.Page G c 1)

def table : Matrix (Domain G c f) (Bits H G) ℝ := let U:=replica S.ratio V
  tall (fun s => Real.sqrt p.direct • Shape.basic H U s)
    (fun s => Shape.ell W N (pull s 0 U)*Shape.basic H U s)
    (-(Real.sqrt S.kernel.penalty • Shape.fluid H U k))

def version (B : Table (Flat.OneForm f)) := Tint.row G.ColorIndex (B.submatrix (free S H) (free S H))

theorem trivial_eq (hb : S.patch.Branches S.kernel G) :
    gram (table H W p N 1 k) = (Actual.initial W p N F).submatrix (active H G) (active H G) := by
  let ver := version (G:=G) (S:=S) H
  unfold table; rw [tall_gram,replica_one]
  have ha (s : Signed) : gram (Real.sqrt p.direct • Shape.basic (G:=G) H 1 s) +
      gram (Shape.ell W N (pull s 0 1)*Shape.basic H 1 s) = ver (Rot.conjugate (Rot.map f s) (K (Cut.metric W p N f))) := by
    rw [show pull s 0 (1:Config G f)=1 by funext i; unfold pull Lattice.Step.read; split <;> simp,Shape.ell_flat, gram_scale,Real.sq_sqrt p.quadratic_pos.le,Shape.direct_flat]
    unfold hide; rw [← Tint.product,← same_cols, gram_row,gram_row,gram_cols,gram_cols,row_weight,← row_plus]
    change ver _ = ver _; congr 1
    unfold Rot.conjugate K Cut.metric gram
    simp only [transpose_mul, Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul, Matrix.mul_one,Matrix.mul_assoc]
  simp_rw [ha]; rw [Shape.noise_flat H k hb, ←neg_smul,gram_scale,neg_sq, Real.sq_sqrt S.kernel.penalty_pos.le]
  unfold hide ver version; rw [row_avg, col_avg, gram_row, gram_cols,row_weight,←row_plus]; rfl

lemma compulsory (h : ∀ b, DifferentiableAt ℝ (fun x=> G.mat (Shape.readBond H (replica S.ratio V) k b x)) 0) :
    Covers H V k (table H W p N V k) ((Fintype.card Signed:ℝ)/p.direct+S.kernel.penalty⁻¹) := by
  intro x U v
  let A (s : Signed) := Shape.basic H U s
  let E s := Shape.ell W N (pull s 0 U)*A s
  let B := Shape.fluid H U k
  let D := table H W p N V k
  have hg : ∀ i, (A 1 *ᵥ x) i = (Shape.direct H U 1 i.1 x).ofLp i.2 := fun _=>row_test ..
  have hh i : ‖Shape.direct H U 1 i x‖ = curlPrice U v i := by
    rw [← (Shape.direct_eq ..).deriv,curlPrice]; simp only [pull_id,Shape.restore_line]; rfl
  have hm : ∑ i, (((Real.sqrt p.direct • A 1) *ᵥ x) i)^2=p.direct*∑ i,(curlPrice U v i)^2 := by
    simp_rw [smul_mulVec, Pi.smul_apply,smul_eq_mul,mul_pow, Real.sq_sqrt p.quadratic_pos.le,← Finset.mul_sum, ←hh,hg]
    rw [Fintype.sum_prod_type]; simp only [EuclideanSpace.real_norm_sq_eq]
  have he : ∑ i, ((-(Real.sqrt S.kernel.penalty • B) *ᵥ x) i)^2 = S.kernel.penalty*∑ i,(noisePrice U v k i)^2 := by
    simp_rw [Matrix.neg_mulVec, Matrix.smul_mulVec, Pi.neg_apply,Pi.smul_apply, smul_eq_mul, neg_sq, mul_pow, Real.sq_sqrt S.kernel.penalty_pos.le,← Finset.mul_sum]; congr 1
    unfold B Shape.fluid; simp_rw [row_test,Fintype.sum_prod_type]
    have he i : noisePrice U v k i = ‖nozzle H U k ((FlatTree.wheel c).symm i) x‖ := by rw [nozzle_price H U _ (h _) x, show pole ((FlatTree.wheel c).symm i) = _ from (FlatTree.wheel c).apply_symm_apply i]
    simp_rw [he, EuclideanSpace.real_norm_sq_eq]
  have hd : dotProduct (D *ᵥ x) (D *ᵥ x) = ∑ i, ((D *ᵥ x) i)^2 := by simp [dotProduct,pow_two]
  let Y := dotProduct (D *ᵥ x) (D *ᵥ x); let m : ℝ := Fintype.card Signed
  have hr : Y=(∑ i, ((normalize (fun s => Real.sqrt p.direct • A s) *ᵥ x) i)^2) + ((∑ i, ((normalize E *ᵥ x) i)^2) + S.kernel.penalty*∑ i,(noisePrice U v k i)^2) := by unfold Y; rw [hd]; unfold D table; rw [tall,stack_energy,stack_energy,← he]
  rw [share_energy] at hr
  rw [add_mul]
  have hA (s : Signed) := show (0:ℝ) ≤ ∑ i, (((Real.sqrt p.direct • A s)*ᵥx) i)^2 from Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE : (0:ℝ) ≤ ∑ i, ((normalize E *ᵥ x) i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply add_le_add
  · rw [div_mul_eq_mul_div, le_div_iff₀ p.quadratic_pos, mul_comm _ p.direct, ←hm]
    apply (Finset.single_le_sum (f:=fun s=> ∑ i, (((Real.sqrt p.direct • A s)*ᵥx) i)^2) (fun s _=> hA s) (Finset.mem_univ 1)).trans
    change _ ≤ m*Y; rw [hr,mul_add, mul_inv_cancel_left₀ (show m≠0 from Rot.normal.ne')]; exact le_add_of_nonneg_right (mul_nonneg Rot.normal.le (add_nonneg hE (mul_nonneg S.kernel.penalty_pos.le (Finset.sum_nonneg fun _ _ => sq_nonneg _))))
  rw [inv_mul_eq_div,le_div_iff₀ S.kernel.penalty_pos]; change _ ≤ Y; rw [hr]; have := S.kernel.penalty_pos
  rw [mul_comm _ S.kernel.penalty]; exact (le_add_of_nonneg_left hE).trans (le_add_of_nonneg_left (mul_nonneg (inv_pos.mpr Rot.normal).le (Finset.sum_nonneg fun s _=>hA s)))

theorem invoice (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (σ C : ℝ) (hw : 0<σ) : ∃ L δ : ℝ, 0<L ∧ 0<δ ∧
    ∀ {f c : Side} (S : StepData c f), S.patch=P → S.kernel=K → Paid S G → ∀ (F : Forest S.ratio) (H : Finset F.Free) (V : Config G c) (t : ℝ),
      0≤t → t≤δ → Covered H t V → ∀ (W : PathData G) {Λ : ℝ}, W.Bounds p σ C Λ → ∀ k N,
      Covers H V k (table H W p N V k) ((Fintype.card Signed:ℝ)/p.direct+K.penalty⁻¹) ∧
      Rows.Bill (keySite H) (σ/2) (gram (table H W p N V k)) L := by
  let w := σ/2; have h₁ := half_pos hw
  obtain ⟨t,D,ht,hD,hE⟩ := noise_allows G P K h₁
  obtain ⟨M,hM,hA⟩ := basic_prices G h₁
  let A := |Real.sqrt p.direct| * M
  let B := max C 0 * (crowd G * Push.Uniform.countCost w) * M
  let U := |Real.sqrt K.penalty| * D
  let Y := A*A+B*B+U*U
  have hY : 0≤Y := by unfold Y; nlinarith only [sq_nonneg A,sq_nonneg B,sq_nonneg U]
  refine ⟨1+Y,t,by positivity,ht,fun {f c} S hp hk hS F H V r hr hT he W {Λ} hW k N=>?_⟩
  obtain ⟨hQ,hq⟩ := hE S hp hk hS k F H V r hr hT he
  constructor
  · rw [←hk]; exact Mapping.compulsory H W p N V k (fun b=>(hQ b).differentiableAt (by simp))
  apply Rows.bigger _ (show Y≤1+Y by linarith); unfold Y table
  have hb (s : Signed) := Shape.ell_price N hW (pull s 0 (replica S.ratio V)) s h₁ (show 2*(σ/2)≤σ by linarith)
  have hc := Cut.pos_cost hW; have hp := Push.Uniform.count_pos h₁
  have hz (s : Signed) := hA S F H (replica S.ratio V) s
  apply Stacks.tall_bill (w:=w) (a:=fineSite) (b:=fineSite) (l:=coarseSite S) (hC:=show 0≤A by unfold A; positivity) (hL:=show 0≤U by unfold U; positivity)
  · exact fun s=>⟨(hz s).1.pay _, (hz s).2.pay _⟩
  · intro s; unfold B; rw [max_eq_left hc]; exact ⟨(hb s).1.multiply h₁.le (hz s).1 hM.le, by rw [transpose_mul,mul_comm _ M]; exact (hz s).2.multiply h₁.le (hb s).2 (by unfold w; positivity)⟩
  · unfold U; rw [←hk,←neg_smul,←abs_neg (Real.sqrt S.kernel.penalty)]; exact ⟨hq.1.pay _,hq.2.pay _⟩
  · exact h₁.le
  unfold B; rw [max_eq_left hc]; unfold w; positivity

lemma initial_mount (S : StepData c f) (F : Forest S.ratio) (W : PathData G) (p : Clip) (N : ℕ) (hb : S.patch.Branches S.kernel G) (k : S.Choices) :
    mount (∅:Finset F.Free) (gram (table ∅ W p N 1 k)) = Actual.initial W p N F := by
  ext i j; obtain ⟨i,b⟩ := i; obtain ⟨j,c⟩ := j
  let e (i : Key F G) : Bits (∅:Finset F.Free) G := (⟨i.1,Finset.notMem_empty _⟩,i.2)
  have he (i : Key F G) : active (∅:Finset F.Free) G (e i)=i := rfl
  rw [← he (i,b), ← he (j,c)]; exact congr_fun (congr_fun ((active_read _ _).trans (trivial_eq (∅:Finset F.Free) W p N k hb)) (e (i,b))) (e (j,c))

/-- Entire paired pre-budget for THIS affine D scheme, independent of
both cut radii. Not requiring Sworn or Horizon. Even the numerical flat
price is at the true mapping with tree as its only inactive constraint
(use `initial_mount` and `Actual.initial_shared`). Derivative budgets
through a moving V still require variation estimates.
-/
theorem income (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (σ C : ℝ) (hw : 0<σ) : ∃ v : Prices, ∃ δ : ℝ, 0<δ ∧
    ∀ {f c : Side} (S : StepData c f), S.patch=P → S.kernel=K → Paid S G → ∀ (F : Forest S.ratio) (H : Finset F.Free) (V : Config G c) (t : ℝ),
      0≤t → t≤δ → Covered H t V → ∀ (W : PathData G) {Λ : ℝ}, W.Bounds p σ C Λ → ∀ k N,
        Fits (address F) v (Actual.initial W p N F) ∧ Fits (address F) v (mount H (gram (table H W p N V k))) := by
  let l : ℝ := (Fintype.card Signed:ℝ)/p.direct+K.penalty⁻¹
  have hl : 0<l := by unfold l; have := K.penalty_pos; have := p.quadratic_pos; positivity
  obtain ⟨L,δ,hL,hδ,h⟩ := invoice G P K p σ C hw
  let s : Prices := ⟨σ/2,1,1,Fintype.card Axis*Fintype.card G.ColorIndex,half_pos hw,zero_lt_one,zero_lt_one⟩
  obtain ⟨v,δ',hδ',H⟩ := issue.{0} G P K s (C:=l) (w:=σ/2) (L:=L) (half_pos hw) hl
  refine ⟨v,min δ δ',lt_min hδ hδ', fun {f c} S hp hk hS F H' V t ht he hv W {Λ} hW k N => ?_⟩
  have hf : Fits (address (G:=G) F) s (1:Table (Key F G)) := ⟨Matrix.isHermitian_one, Rows.one, CurvedGaussianJets.key_count,fun x=> by rw [one_mulVec]; exact (one_mul _).le⟩
  have heq (H' : Finset F.Free) (V : Config G c) (hv : Covered H' t V) := (H S hp hk hS F V k _ H' ht (he.trans (min_le_right ..)) (hv.clean H') (address F) _ hf
      (table H' W p N V k) ((h S hp hk hS F H' V t ht (he.trans (min_le_left ..)) hv W hW k N).1)
      ((h S hp hk hS F H' V t ht (he.trans (min_le_left ..)) hv W hW k N).2)).2
  rw [← initial_mount S F W p N hS.1.1 k]; exact ⟨heq ∅ 1 (fun j i hi => by obtain ⟨p,-,hx⟩ := (RG.flags_spec ..).1 hi; simp [faceValue,square,travel] at hx; linarith), heq H' V hv⟩
end YM.Further.CurvedGaussianJets.Mapping

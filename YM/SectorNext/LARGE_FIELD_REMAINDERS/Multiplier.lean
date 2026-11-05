import YM.Push.SECTOR_MEASURE.LabelSum



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Bringing the true RHS multiplier into a pre-change volume estimate

Real tori at any period. Strengthen the naive fixed-world bound by paying
*absolute* incoming K hit costs on just the defect sites (before dropping
defaults/likelihood). This is not cluster summability. For the cut mismatch
pay true path costs exponentially in LENGTH in PathData.Bounds conventions,
even on repeated and long walks. Apply Vac healthy prices on the remaining
atoms. Don't unwrap the masks just because a row is outside a seed; that
wouldn't work for all the paths! Includes statements for single occurrences
with the same address space.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Oriented Presented LabelSum
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure

variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {σ C Λ : ℝ} (h : R.Bounds c σ C Λ)

private lemma tail_ge {i : ℕ} {l d : ℕ} (hl : l<d*i) {ρ : ℝ} (hρ : 0≤ρ) (hd : 0<d) :
    1 ≤ Real.exp (ρ*(i:ℝ))*Real.exp (-ρ*(l:ℝ)/d) := by
  rw [← Real.exp_add]; refine Real.one_le_exp ?_
  have h : (l:ℝ) ≤ (d:ℝ)*i := by exact_mod_cast hl.le
  have hh := mul_le_mul_of_nonneg_left h hρ
  have hd : (0:ℝ)<d := by exact_mod_cast hd
  have hy : -(ρ*(l:ℝ)/d) = -ρ*(l:ℝ)/d := by ring
  have hk : ρ*(l:ℝ)/d ≤ ρ*i := by apply (div_le_iff₀ hd).mpr; linarith
  linarith

include h in
lemma fine_cut_pay (p : Cell n) (U : Config G n) (d l : ℕ) (hd : 0<d) :
    ‖R.ell U p‖ ≤ 2*C ∧ ‖shorten R l d U p‖ ≤ 2*C ∧
      ‖R.ell U p - shorten R l d U p‖ ≤ 2*C * Real.exp (-σ*l/d) := by
  let f i := |(R.row p.2 i).1| *Real.exp (σ*(R.row p.2 i).2.length)
  have hf : SumBudget f C := h.rows p.2
  have hh (i : ℕ) : ‖R.ellTerms p i U‖ ≤ f i*2 := by
    let j := (R.row p.2 i).2
    rw [PathData.ellTerms,norm_smul,Real.norm_eq_abs]
    apply le_trans (mul_le_mul_of_nonneg_left (show ‖j.atSite U p.1‖≤2 from Slot.eval_norm ..) (abs_nonneg _))
    gcongr; exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by have := h.width; positivity))
  have he (i : ℕ) : ‖shortenTerm R l d U p i‖ ≤ f i*2 := by
    unfold shortenTerm; split
    · exact hh _
    rw [norm_zero]; exact mul_nonneg (hf.1 _) (by norm_num)
  have H {F : ℕ → G.Color} {v : ℝ} (h : ∀ i, ‖F i‖ ≤ f i*v) (hv : 0 ≤ v) :
      Summable F ∧ ‖∑' i, F i‖ ≤ C*v := by
    have hp := hf.2.1.mul_right v
    have he := hp.of_nonneg_of_le (fun _ => norm_nonneg _) h
    exact ⟨he.of_norm,(norm_tsum_le_tsum_norm he).trans ((he.tsum_le_tsum h hp).trans (by
      rw [tsum_mul_right]; gcongr; exact hf.2.2))⟩
  obtain ⟨he1,h1⟩ := H hh (show (0:ℝ)≤2 by norm_num)
  obtain ⟨he2,h2⟩ := H he (show (0:ℝ)≤2 by norm_num)
  refine ⟨h1.trans_eq (mul_comm _ _),h2.trans_eq (mul_comm _ _),?_⟩
  let W := Real.exp (-σ*l/d)
  have ht (i : ℕ) : ‖R.ellTerms p i U-shortenTerm R l d U p i‖ ≤ f i*(2*W) := by
    unfold shortenTerm; split
    · rw [sub_self,norm_zero]; exact mul_nonneg (hf.1 _) (by unfold W; positivity)
    rename_i hl
    rw [sub_zero,PathData.ellTerms,norm_smul,Real.norm_eq_abs]
    have hg := tail_ge (i:=((R.row p.2 i).2.length)) (l:=l) (d:=d)
      (by simpa only [mul_comm] using (lt_of_not_ge hl)) h.width.le hd
    apply le_trans (mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (abs_nonneg _))
    unfold f W
    nlinarith [mul_le_mul_of_nonneg_right hg (abs_nonneg (R.row p.2 i).1)]
  unfold PathData.ell shorten
  rw [← he1.tsum_sub he2]; exact (H ht (by unfold W; positivity)).2.trans_eq (by unfold W; ring)

include h in
lemma cuff_pay (m : BudgetPoint) (p : Cell n) (U : Config G n) (d l : ℕ) (hd : 0<d) :
    |cuff R c m d l U p| ≤ 4*C^2*Real.exp (-σ*l/d) := by
  obtain ⟨h1,h2,h3⟩ := fine_cut_pay h p U d l hd
  unfold cuff crown trunk PathData.baseTerm; split
  · rw [add_comm (PathData.clipped ..),add_sub_add_right_eq_sub]
    rw [show ‖R.ell U p‖^2/2-‖shorten R l d U p‖^2/2=(‖R.ell U p‖-‖shorten R l d U p‖)*(‖R.ell U p‖+‖shorten R l d U p‖)/2 by ring]
    rw [abs_div,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), abs_of_nonneg (show (0:ℝ)≤2 by norm_num)]
    apply le_trans (div_le_div_of_nonneg_right (mul_le_mul ((abs_norm_sub_norm_le ..).trans h3)
      (add_le_add h1 h2) (add_nonneg (norm_nonneg _) (norm_nonneg _)) ((norm_nonneg _).trans h3)) (by norm_num))
    ring_nf; rfl
  rw [zero_add,add_zero,sub_self,abs_zero]; positivity

variable {q k : Side} {S : StepData q k} {x W w δ : ℝ} (A : Stores S) (F : Activities G k) (p : BudgetPoint)

/-- True projection to K hit-supports, not possible-support-in-box. -/
def hits := A.costs.biUnion touched
lemma hits_card : (hits A).card ≤ 4*A.shares := by
  calc
    _ ≤ ∑ i ∈ A.costs, (4:ℕ) := Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun i _ => Work.E01.touched_card _))
    _ = 4*A.costs.card := by simp [mul_comm]
    _ ≤ _ := by unfold shares; omega

/-- Majorants for the *occurrences* in this column. Can integrate each
still retaining gauge/history paths & sign before using the sums. `w`
regarded as a nonnegative cost; extract this at use. -/
lemma occurrence_budget (d : Allocation G S x W) (hw : 0 ≤ w)
    (hF : F.Valid p δ w) (he : p.threshold = fiery G x S.patch.L) :
    ∃ b : Finset ℕ → ℝ, SumBudget b (Real.exp (w*4*A.shares)) ∧
      ∀ (i : Finset ℕ) (U : Config G k) (V : Config G q) (t : S.Choices), d.bill A t U V ≠ 0 →
        ‖F.gasOccurrence p i U‖ ≤ b i := by
  obtain ⟨B,hb,h⟩ := hF.boundK
  let ζ (j : Site k) i := if j ∈ (F.forced i).support then p.mass (F.forced i).support (B i) else 0
  let η (i : ℕ) := ∑ j∈hits A, ζ j i
  have hz j : SumBudget (ζ j) w := h j
  have hη i : 0≤η i := Finset.sum_nonneg (fun _ _ => (hz _).1 i)
  have h1 : Summable η := summable_sum (fun i _ => (hz i).2.1)
  have h2 : ∑' i, η i ≤ w*(hits A).card := by
    unfold η; rw [Summable.tsum_finsetSum fun i _ => (hz i).2.1]
    apply (Finset.sum_le_sum fun i (_ : i ∈ hits A) => (hz i).2.2).trans_eq; simp [mul_comm]
  have hp i (hh : ∃ j ∈ (F.forced i).inventory, j ∈ hits A) : B i ≤ η i := by
    obtain ⟨j,hj,hA⟩ := hh
    apply le_trans (p.loMass (F.forced i).support _ (hb i).1)
    have hk : ζ j i=p.mass _ (B i) := if_pos ((F.forced i).inventory_sup hj)
    rw [← hk]; exact Finset.single_le_sum (fun j _ => (hz j).1 i) hA
  refine ⟨fun s => ∏ i∈s,η i,⟨fun s => Finset.prod_nonneg fun i _ => hη i, summable_finsetProd_of_summable_nonneg hη h1,?_⟩,?_⟩
  · apply Real.tsum_le_of_sum_le (fun s => Finset.prod_nonneg fun i _ => hη i)
    intro s
    calc
      _ ≤ ∑ x ∈ (s.biUnion id).powerset, ∏ i ∈ x, η i := Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => Finset.mem_powerset.mpr (Finset.subset_biUnion_of_mem id hx)) (fun x _ _ => Finset.prod_nonneg fun i _ => hη i)
      _ = ∏ x ∈ s.biUnion id, (1+η x) := (Finset.prod_one_add _).symm
      _ ≤ Real.exp (∑ i∈s.biUnion id, η i) := Real.prod_one_add_le_exp_sum _ hη
      _ ≤ _ := by
        apply Real.exp_monotone
        apply ((h1.sum_le_tsum _ fun i _ => hη i).trans h2).trans
        have hi := mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr (hits_card A)) hw
        push_cast at hi; linarith
  intro i U V t hD
  unfold Activities.gasOccurrence; split
  next hhi =>
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _); intro a ha
    obtain ⟨j,hj⟩ := (F.forced a).inventory_ne
    have ht : j∈RG.flags (fiery G x S.patch.L) U := by rw [← he, ← hhi.2]; exact Finset.mem_biUnion.mpr ⟨a,ha,hj⟩
    exact ((hb a).2 _).trans (hp a ⟨j,hj, Finset.mem_biUnion.mpr (d.flagged hD j ht)⟩)
  rw [norm_zero]; exact Finset.prod_nonneg fun j _ => hη j

/-- Honest *extensive* loss besides v. Even where these prices are much
smaller than 1 per site after delay, don't treat as an $L^\\infty$ envelope
uniform in volume. -/
def air (R : Rep G k) (x σ C Λ δ : ℝ) : ℝ :=
  δ+PathData.loopsPrice R.p R.beta C Λ +
    R.beta*(Fintype.card PlaqAxes:ℝ)*(4*C^2 * Real.exp (-σ*(till x)))

lemma tail_scalar {R : Rep G k} (hR : R.Lawful σ C Λ δ w) (hβ : 0 ≤ R.beta) (x : ℝ) (U : Config G k) :
    R.v * (Fintype.card (Site k):ℝ) - averaged (fun s => reduced R (till x) (pull s 0 U)) -
      R.activities.additive R.p U ≤ R.scalar + air R x σ C Λ δ * (Fintype.card (Site k):ℝ) := by
  let z := 4*C^2 * Real.exp (-σ*(till x))
  let u := (Fintype.card PlaqAxes:ℝ)
  let e := PathData.loopsPrice R.p R.beta C Λ
  let N := (Fintype.card (Site k):ℝ)
  have he s : -(e+R.beta*u*z)*N ≤ reduced R (till x) (pull s 0 U) := by
    let P := pull s (0:Site k) U
    have hh (i : Site k) : -(C*R.p.threshold^3+C*R.p.threshold^4) ≤
        PathData.atomSeries R.path.cubic R.p P i + PathData.atomSeries R.path.quartic R.p P i :=
      neg_le_of_abs_le ((abs_add_le ..).trans (add_le_add (atomVolume _ _ _ _ hR.paths.width hR.paths.three)
        (atomVolume _ _ _ _ hR.paths.width hR.paths.four)))
    have h (i : Cell k) : -z ≤ cuff R.path R.clip R.p 1 (till x) P i := by
      apply neg_le_of_abs_le
      simpa [z] using cuff_pay hR.paths R.p i P 1 (till x) (by norm_num)
    have hi (i : Site k) : -(Λ*R.p.threshold^2) ≤ PathData.atomSeries R.path.loop R.p P i :=
      neg_le_of_abs_le (atomVolume _ _ _ _ hR.paths.width hR.paths.two)
    apply le_trans ?_ (add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add (Finset.sum_le_sum fun i (_:i ∈ Finset.univ) => h i)
        (Finset.sum_le_sum fun i (_:i ∈ Finset.univ) => hh i)) hβ)
      (Finset.sum_le_sum fun i (_:i ∈ Finset.univ) => hi i))
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Cell,Face,Fintype.card_prod,Nat.cast_mul]
    unfold e N u PathData.loopsPrice Site; ring_nf; rfl
  have h := av_mono he; rw [av_const] at h
  have H := (abs_le.mp (volumeE R.activities hR.labels U)).1
  unfold air Rep.scalar; unfold N u z e at h; linarith only [h,H]

lemma exposed_absolute (d : Allocation G S x W) (R : Rep G k) {B : Finset ℕ → ℝ}
    (hw : 0 ≤ w) (hB : SumBudget B (Real.exp (w*4*A.shares)))
    (hb : ∀ (i : Finset ℕ) (U : Config G k) (V : Config G q) (t : S.Choices), d.bill A t U V ≠ 0 → ‖R.activities.gasOccurrence R.p i U‖ ≤ B i)
    (hR : R.Lawful σ C Λ δ w) (hβ : 0≤R.beta) (U : Config G k) (V : Config G q) (t : S.Choices) (hD : d.bill A t U V ≠0) :
    let K := Real.exp (R.scalar + air R x σ C Λ δ * (Fintype.card (Site k):ℝ))
    (∀ i : Finset ℕ, ‖separate R (till x) i U‖ ≤ K*B i) ∧
    ‖exposed R (till x) U‖ ≤ K*Real.exp (w*4*A.shares) := by
  intro K
  let g := fun i : Finset ℕ => separate R (till x) i U
  let f := R.v*(Fintype.card (Site k):ℝ)-averaged (fun s => reduced R (till x) (pull s 0 U))-R.activities.additive R.p U
  have h i : g i = Real.exp f*R.activities.gasOccurrence R.p i U := by
    have he := expel R (till x) U -- need before gas multiplication; gas could be zero; algebra
    let r := R.path
    have he : r.inChannels R.clip R.p R.beta U = averaged (fun s => reduced R (till x) (pull s 0 U)) + R.beta*cutR R (till x) U := by
      let q (s : Signed) := ∑ i, crown R.path R.clip (till x) 1 R.p.threshold (pull s 0 U) i
      have hk (s : Signed) : r.principal R.clip R.p R.beta (pull s 0 U) =
          reduced R (till x) (pull s 0 U) + R.beta * q s := by
        simp only [PathData.principal,q,reduced,cuff,Finset.sum_sub_distrib,mul_sub,mul_add,r]; abel
      have hx : r.inChannels R.clip R.p R.beta U = averaged fun s => reduced R (till x) (pull s 0 U) + R.beta * q s := by
        simp only [PathData.inChannels,hk,averaged]
      rw [hx, av_add]; unfold q cutR averaged; rw [← Finset.mul_sum]; ring
    unfold g separate f Rep.exponent
    unfold r at he; rw [he,← Real.exp_add]; ring_nf
  have H i : ‖g i‖ ≤ K*B i := by
    rw [h,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul (Real.exp_monotone (tail_scalar hR hβ _ _)) (hb i U V t hD) (norm_nonneg _) (Real.exp_pos _).le
  have he := hB.2.1.mul_left K
  refine ⟨H,?_⟩
  rw [← separate_sum]; have hh := he.of_nonneg_of_le (fun _ => norm_nonneg _) H
  refine (norm_tsum_le_tsum_norm hh).trans ((hh.tsum_le_tsum H he).trans ?_)
  rw [tsum_mul_left]; gcongr; exact hB.2.2

end YM.SectorNext.Remainder

import YM.Next.RANK.Gust
import YM.Next.RANK.SparkPart

/-!
# Rotated forced records for each real marker at k

Even crossing old or new seam (in applications specific placements fixed).
Coordinate record required relative to actual k-screen query.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source Labels
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {A : Activities G n} {Q : Rep G n} {V ι κ : Type} [DecidableEq V] [Fintype V]
variable {d : ℕ} {W : Frame G d} {ζ : V→Site n} {σ α δ η Λ e z : ℝ}
variable {F : Coefficient W n} {P : BudgetPoint} {H : Hol G}
variable (s : Signed) (x : Site n)

-- group movements by charge at canonical support
abbrev Rootage (n : Side) := { x : Neat n // 0∈x.val.1}

def foam (F : Coefficient W n) (Q : Rep G n) (P : Neat n) (U : Config G n) :=piece (identifier Q) (fun j=>F.forced j U) P

lemma foamed (h : F.Format 0 H Q) (x : Neat n) (U V) (hi : Agrees x.val.1 U V) (hp : x.val.1 ∩ flags Q.p.threshold U=x.val.1 ∩ flags Q.p.threshold V) :
    foam F Q x U=foam F Q x V:= by
  refine tsum_congr fun i=> ?_; split
  · rename_i he;have hW : (Q.activities.forced i).support=x.val.1:= congr_arg Prod.fst (congr_arg Subtype.val he)
    exact h.supported i U V (hW.symm ▸ hi) (hW.symm ▸ hp)
  rfl
lemma shore (h : F.Format 0 H Q) (x : Neat n) (k : Site n→ G.El) (U : Config G n) : foam F Q x (Lattice.gauge k U)= foam F Q x U:= by apply tsum_congr; intro i; dsimp only; rw [h.invariant i k U]
lemma foamy (h : F.Format 0 H Q) (x : Neat n) : Measurable (foam F Q x):= by
  apply Measurable.tsum; intro i; split; exact h.borel _; exact measurable_const
lemma foamp (h : F.Format 0 H Q) (x : Neat n) (U : Config G n) (he : foam F Q x U≠0) : x.val.1∩ flags Q.p.threshold U=x.val.2 := by
  apply Classical.byContradiction; intro hv; apply he; refine (tsum_congr (g:=fun _=>0) ?_).trans tsum_zero; intro i; split
  · rename_i hh; apply Classical.byContradiction; intro hg; apply hv; rw [← hh]; exact h.forcing i U hg|>.1
  rfl
lemma dusted (h : F.Format 0 H Q) (x : Neat n) (hp : 0∉x.val.1) (U : Config G n) : foam F Q x U=0:= by
  refine (tsum_congr (g:=fun _=>0) ?_).trans tsum_zero; intro i; split
  · rename_i h'; have hh : F.forced i=0:=Classical.byContradiction fun H=> hp (h'▸ show 0∈(identifier Q i).val.1 from h.carried i H); dsimp only; rw [hh];rfl
  rfl

-- dot selector commutes densely with sums and integrals along pushes recorded
lemma dot_zero (z : Prop):dot z 0=0:=by unfold dot; split<;> simp
lemma dot_real (z : Prop) (x : ℝ): dot z (x:ℂ)=x:=by unfold dot; split<;>simp
lemma dot_mul (z : Prop) (x y : ℂ) : dot z (x*y)=dot z x*dot z y:=by unfold dot; split<;>simp


def horn (R : Neat n) : Support n := swath s x R.val.1
lemma flag_shift (u : ℝ) (U : Config G n) {p q : Support n} :
    p ∩ flags u (pull s x U)=q ↔ swath s x p∩ flags u U=swath s x q := by rw [←s_flags s x u U]; exact (image_inj (sends s x).injective |>.symm.trans (by rw [image_inter p (flags u (pull s x U)) (sends s x).injective];rfl))

variable (H' : F.Format 0 H Q)
variable (a : Prop) (β : ℂ)

-- true origin move for marker f. ζ: anchor (force includes all tests and history)
def chip (j : V) (x : Rootage n) : Lifted G ζ Q.p.threshold where
  extent := horn s (ζ j) x.val
  inventory:= swath s (ζ j) x.val.val.2
  needed:= x.val.property.1.image _
  records:= swell s (ζ j) _ _ x.val.property.2
  fires:= slot j
  remembers i hi:=by
    obtain rfl : i=j:=mem_singleton.mp hi
    have hv:= x.property; exact (by simpa [affine,horn,swath] using mem_image_of_mem (affine s (ζ i)) hv)
  value U:= dot a (β*foam F Q x.val (pull s (ζ j) U))
  meas:= (dot_meas _).comp (measurable_const.mul ((foamy H' _).comp (continuous_pull ..|>.measurable)))
  inv i U:= by
    dsimp only; rw [s_gauge,shore H']
  flag U hn:=by
    refine (flag_shift s (ζ j) ..).1 (foamp H' _ _ ?_)
    exact fun h=>hn (by rw [h,mul_zero,dot_zero])
  only U V he hf:= congr_arg (dot a) (congr_arg (β*·) (final_swath s (ζ j) _ Q.p.threshold (F:=foam F Q x.val) (fun U V=> foamed H' _ U V) U V he hf))

lemma seal_chip (i : V) (x : Rootage n) : attached (chip (ζ:=ζ) s H' a β i x)=sent s (ζ i) x.val := Subtype.ext (sent_one s (ζ i) x.val|>.symm)

-- Cost per marker old exact

include H'
lemma root_budget {d : ℝ} {P : ℕ→ℝ} (hp : ∀ i,0≤ P i ∧ ∀ U, ‖F.forced i U‖≤ P i)
    (hB : SumBudget (fun i=> Q.p.mass (Q.activities.forced i).support (P i)) d)
    (i : V) (r : V→ℝ) (hr : 0 ≤ r i) :
    let K:= chip (ζ:=ζ) s H' a β i
    ∃ m : Rootage n→ℝ,(∀ j,heavy (K j) r (m j)) ∧ ∑ j,m j *Value.charge Q.p Q.p.supportExponent (K j).extent ≤ r i * ‖β‖ * d := by
  intro K
  let p:= Q.p; let X:= Q.activities; let E:=identifier Q
  let x y:=∑' j,pay P (fun i=> E i=y) j
  let M (y:Neat n):= x y*Value.charge p p.supportExponent y.val.1
  have hx i:0≤ x i:= by apply tsum_nonneg; intro j; unfold pay; split; exact (hp _).1; exact le_rfl
  have hv i:0≤M i:=mul_nonneg (hx _) (Real.exp_pos _).le
  have hy : ∑ i,M i≤d := by
    apply le_trans _ hB.2.2
    rw [← pack_all (x:= E) (h:=hB.2.1)];apply sum_le_sum;intro i _; apply le_of_eq; unfold M x; rw [← tsum_mul_right];apply tsum_congr; intro j; unfold pay; split_ifs with hi
    · rw [← hi]; exact mul_comm ..
    rw [zero_mul]
  have hT : Summable P:= hB.2.1.of_nonneg_of_le (fun i=> (hp i).1) (fun i=> Q.p.loMass _ _ (hp i).1)
  have hz (i : Rootage n) (U:Config G n): ‖foam F Q i.val U‖≤x i.val:= by
    let H:=fun j=> if E j=i.val then F.forced j U else 0
    have hf j: ‖H j‖≤ pay P (fun j=> E j=i.val) j := by unfold H pay; split_ifs; exact (hp j).2 U; rw [norm_zero]
    have hh : Summable (pay P (fun j=> E j=i.val)):=hT.indicator (s:={j|E j=i.val})
    have hN:=hh.of_nonneg_of_le (fun i=> norm_nonneg (H i)) hf; exact (norm_tsum_le_tsum_norm hN).trans (hN.tsum_le_tsum hf hh)
  let w:= r i*‖β‖;have he:0≤w:=mul_nonneg hr (norm_nonneg _)
  refine ⟨fun j=> w*x j.val,fun j=>⟨mul_nonneg he (hx _),fun U=> ?_⟩,?_⟩
  · dsimp only [K,chip]; rw [dot_norm,norm_mul,Poly.solo_toll,← mul_assoc]; exact mul_le_mul_of_nonneg_left (hz ..) he
  have hM : ∑ j : Rootage n,M j.val≤ d := by
    apply le_trans _ hy
    let A:= (univ : Finset (Rootage n)).image Subtype.val
    have ht:= sum_le_sum_of_subset_of_nonneg (subset_univ A) (fun i _ _=>hv i);rwa [sum_image (fun _ _ _ _ h=>Subtype.ext h)] at ht
  dsimp only [K,chip, Value.charge,horn]; simp_rw [swath_cover]; simp_rw [mul_assoc w]
  change (∑ j : Rootage n,w *M j.val)≤ w *_; rw [← Finset.mul_sum];exact mul_le_mul_of_nonneg_left hM he
end YM.Next.Rank.Edition

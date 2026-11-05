import YM.Push.RELAY_DIFFERENCE.Applications
import YM.Work.A15

/-!
# Uniform across source combinations at a given grade

Don't ask a priced calendar for uncountably many independent column
estimates. For both mark and both vet contributions, suffice finitely many
at the level. Need the discrepancy rate proved above (and transports of
that strong rate to ALL tiles/sides). Actual Wilson normalization, even
in taking the cutoff-row linear combinations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Lattice Cells Marker Overlay Stock Bid Mix
open scoped Topology Matrix.Norms.Frobenius BigOperators
open Next.Extract
variable {G : Gauge} {C : Family G} {d : ℕ} {W : Worth} {f : Extraction.Order} {F : Trial C} {b : Presentation C}

/-! ### Collect comparisons -/

variable {ι : Type*} [Fintype ι]

/-- Coefficients fixed throughout all offsets for each given cutoff. -/
def gathered (Q : ι → Trial C) (r : ι → Cutoffs → ℂ) : Trial C :=
    fun N p i => ∑ s : ι, r s (N,p) • Q s N p i

def readings (s : ι → Rowe C d) (r : ι → Cutoffs → ℂ) : Rowe C d := fun i => ∑ j : ι,r j i • s j i

lemma dollar_read (s : ι → Rowe C d) (hs : ∀ i,dollar C f (s i)) (r : ι → Cutoffs → ℂ) (hr : ∀ i, Slow C f (r i)) :
    dollar C f (readings s r) := by
  simp only [dollar_slow, readings, map_sum,map_smul] at *
  exact Slow.sum _ _ fun i _ => (hr i).smul (hs i)

lemma reading_correct (p : ι → Rowe C d) (r : ι → Cutoffs → ℂ) : upper C (readings p r) = gathered (fun i => upper C (p i)) r := by
  funext N i j
  let H : C.label d →ₗ[ℂ] (Config G (C.side N i) → ℂ) := (C.linearO N i d j).mk' _
  change H (∑ s : ι, _) = ∑ s : ι, r s (N,i) • H _
  rw [map_sum]; simp_rw [map_smul]

lemma gathering_sub (s t : ι → Trial C) (r : ι → Cutoffs → ℂ) :
    gathered s r - gathered t r = gathered (fun i => s i-t i) r := by
  funext N p i
  simp only [Pi.sub_apply,gathered,smul_sub, Finset.sum_sub_distrib]

lemma gather_fitted (Q : ι → Trial C) (r : ι → Cutoffs → ℂ) (h : ∀ i, Stencilled f (Q i)) :
    Stencilled f (gathered Q r) := by
  classical
  choose X hX using h
  let Y : Finset Cover := Finset.univ.biUnion X
  refine ⟨Y,?_⟩
  filter_upwards [eventually_all.mpr hX] with i hi
  have ht (j : ι) : Local Y fun x => r j i • Q j i.1 i.2 x := (hi j).smul _ |>.larger (by
    intro x hx; exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hx⟩)
  suffices hh : ∀ s : Finset ι, Local Y fun x => ∑ j∈s, r j i • Q j i.1 i.2 x from hh _
  intro s; induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact ⟨fun _ _ => rfl, fun _ => Interior.constant _ _⟩
  | insert j s he ih => simpa only [Finset.sum_insert he,Finset.union_self] using (ht j).add ih

/-- Combine in every T via the centered-to-literal-orientation proof, not
by intersecting cofinal lease sets (that argument by itself doesn't work).
Restores e^{-δ s_N} in rents after each slow multiplier, even for varying
rows. -/
theorem gather_close (hc : C.Makes) (Q : ι → Trial C) (r : ι → Cutoffs → ℂ) (hr : ∀ i, Slow C f (r i))
    (γ : ℝ) (he : 0 < γ) (h : ∀ i, CenterRents (Q i) (flight C (-γ)) f) : Bid.close C f (gathered Q r) := by
  classical
  let δ := γ/2
  let x : Cutoffs → ℝ := flight C (-δ)
  refine ⟨curry x, ?_,?_⟩
  · rw [Function.uncurry_curry]; exact flight_lands (half_pos he)
  intro j m
  let w : Cutoffs → ℝ := fun a => ∑ i : ι, ‖r i a‖
  have hw : Slow C f w := Slow.sum _ _ fun i _ => (hr i).norm
  let J := 8*(j+1)
  have ht (i : ι) := (h i).every hc m J (by unfold J; omega)
  have hv := (Order.fused f _).mp (hw.sink (show δ < γ from half_lt_self he))
  unfold Order.late at ht hv
  refine ⟨m,le_rfl,?_⟩
  unfold Order.late
  filter_upwards [eventually_all.mpr ht,hv] with a ha hh
  filter_upwards [eventually_all.mpr ha,hh,f.mesh.cofinal.eventually_ge_atTop m] with k hk hp he
  let N := f.mesh k; let p := f.per a
  refine ⟨he,fun T hT _ z hz => ?_⟩
  let β := C.beta N p
  have ht (i : ι) : Interior (T.chamber 0) (Q i N p z) ∧ T.rootTest β (Q i N p z) ≤ flight C (-γ) (N,p) :=
    (hk i).choose_spec T hT z hz
  let y (i : ι) := Q i N p z
  obtain ⟨hf,hg⟩ := Next.Extract.rooted T β (seamless hc ..) Finset.univ y (fun i => r i (N,p)) fun i _ => (ht i).1
  refine ⟨hf,hg.trans ?_⟩
  refine (Finset.sum_le_sum (g:=fun i => ‖r i (N,p)‖*flight C (-γ) (N,p)) (fun i _ =>
    mul_le_mul_of_nonneg_left (ht i).2 (norm_nonneg _))).trans ?_
  rw [← Finset.sum_mul]; exact hp

private lemma solo_value {N p n : ℕ} (F : Trial C) (q : Fin n→C.book.Token) (i : Fin n) (u) :
    featuring F q i N p u = moment (C.beta N p) (fun U => F N p (u i) U *
      ∏ j∈Finset.univ.erase i,C.seen (q j) (u j) U) := by
  unfold featuring; congr! 2 with U
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), if_pos rfl]
  congr 1; exact Finset.prod_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)

/-- Combining equations uses all spectators; coefficients can vary, we
combine BEFORE limit, only on the ordered tails of exact zeros. -/
theorem gather_silent (s : ι → Trial C) (r : ι → Cutoffs → ℂ) (hr : ∀ i,Stencilled f (s i))
    (h : ∀ i,exactOnSep C f (s i)) : exactOnSep C f (gathered s r) := by
  classical
  intro n q i δ hδ
  have he j := h j n q i δ hδ
  have hc (j : ι) := (hr j).sober
  unfold sober Order.late at *
  filter_upwards [eventually_all.mpr he,eventually_all.mpr hc] with k hk hp
  filter_upwards [eventually_all.mpr hk,eventually_all.mpr hp] with a ha hf x hx
  let N := f.mesh a; let p := f.per k
  let μ := law G (C.side N p) (C.beta N p)
  let Z (U : Config G (C.side N p)) := ∏ j∈ Finset.univ.erase i,C.seen (q j) (N:=N) (p:=p) (x j) U
  have hz : Continuous Z := continuous_finsetProd _ fun b _ => C.continuousO N p (q b).1 (q b).2 _
  let G (j : ι) := fun U => s j N p (x i) U * Z U
  have hG (j) : Integrable (G j) μ := by
    obtain ⟨hm,A,hA⟩ := hf j (x i)
    exact (continuous_integrable _ hz).bdd_mul hm.aestronglyMeasurable (Eventually.of_forall hA)
  have hV j : (∫ U, G j U ∂μ)=0 := by
    have hh := ha j x hx; rw [solo_value] at hh; exact hh
  rw [solo_value]
  unfold moment
  simp only [gathered, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,mul_assoc]
  change (∫ U, ∑ j : ι, (r j (N,p)) * G j U ∂μ) = 0
  rw [integral_finsetSum _ (fun j _ => (hG j).const_mul _)]
  simp_rw [integral_const_mul,hV,mul_zero,Finset.sum_const_zero]

theorem gather_vet (Q : ι → Trial C) (r : ι → Cutoffs → ℂ) (S : ∀ i,Solo C (Q i) d)
    (hS : ∀ i, Provisions (S i) W f) (hr : ∀ i, Slow C f (r i)) (h : Shop C W) (hQ : ∀ i, Stencilled f (Q i)) :
    vet C f d (gathered Q r) := by
  let V i := (S i).row
  have hh := fun i => (hS i).complete h (hQ i)
  refine ⟨readings V r,dollar_read _ (fun i => (hh i).1) _ hr,?_⟩
  rw [reading_correct,gathering_sub]; exact gather_close h.frame (fun i => (S i).diff)
    r hr (1/16) (by norm_num) (fun i => (hh i).2 _ (by norm_num [gamma]))
end YM.Push.RelayDifference

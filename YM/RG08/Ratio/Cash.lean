import YM.RG08.Ratio.Coord

/-! # Principal operations as paired treasury. Sum all event costs before
 iteration; bills use announced widths. Calibration rank2 is SAME event prune-Q. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Conductor
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix Reflect PowerSeries
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I : Type} {y δ a b c d η σ : I → ℝ}
variable {G : Gauge}{r : ℕ} (i : G.ColorIndex)

structure Lease (y δ f g : I→ℝ) : Prop where
  has : Weighed y (fun i=> ‖f i‖)
  also : Weighed y (fun i=> ‖g i‖)
  asset : ∃ B : I→ℝ, Weighed y B ∧ ∀ i, ‖f i-g i‖≤ B i * δ i

lemma Lease.same (h : Weighed y (fun i=> ‖a i‖)) : Lease y δ a a := ⟨h,h,0,Weighed.zero,fun i=> by simp⟩
lemma Lease.const (y δ : I→ℝ)(c:ℝ) : Lease y δ (fun _=>c) (fun _=>c) := Lease.same (Weighed.constant y (norm_nonneg _))
lemma Lease.plus (h : Lease y δ a b)(hp : Lease y δ c d) (he : Audience y) : Lease y δ (a+c) (b+d) := by
  refine ⟨(h.has.plus hp.has he).mono (fun i=> norm_nonneg _) (fun i=> norm_add_le ..), (h.also.plus hp.also he).mono (fun i=> norm_nonneg _) (fun i=> norm_add_le ..),?_⟩
  obtain ⟨C,hC,hv⟩:= h.asset; obtain ⟨V,hV,H⟩:= hp.asset; refine ⟨C+V,hC.plus hV he,fun i=>?_⟩
  rw [show (a+c) i-_= (a i-b i)+(c i-d i) by dsimp; abel]; exact (norm_add_le ..).trans ((add_le_add (hv _) (H _)).trans_eq (add_mul ..).symm)
lemma Lease.times (h : Lease y δ a b)(hp : Lease y δ c d) (he : Audience y) : Lease y δ (a*c) (b*d) := by
  refine ⟨(h.has.times hp.has).mono (fun i=> norm_nonneg _) (fun i=> norm_mul_le ..), (h.also.times hp.also).mono (fun i=>norm_nonneg _) (fun i=> norm_mul_le ..),?_⟩
  obtain ⟨C,hC,hv⟩:= h.asset; obtain ⟨V,hV,H⟩:= hp.asset; refine ⟨_,(hC.times hp.has).plus (h.also.times hV) he,fun i=>?_⟩
  simp only [Pi.mul_apply,Pi.add_apply]; rw [show a i*_ - _ = (a i-b i)*c i+b i*(c i-d i) by ring, add_mul];
  refine (norm_add_le ..).trans (add_le_add ?_ ?_)
  · rw [norm_mul,mul_right_comm (C i)]; exact mul_le_mul_of_nonneg_right (hv i) (norm_nonneg _)
  rw [norm_mul,mul_assoc ‖b i‖]; exact mul_le_mul_of_nonneg_left (H i) (norm_nonneg _)
lemma Lease.list {J : Type} {s : Finset J} {f g : J→ I→ℝ} (he : Audience y)(h : ∀ i∈s, Lease y δ (f i) (g i)) : Lease y δ (∑ i∈s,f i) (∑ i∈s,g i) := by
  induction s using Finset.induction_on with
  | empty=> rw [sum_empty,sum_empty]; exact Lease.const ..
  | insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact (h i (mem_insert_self ..)).plus (ih fun j hj=> h j (mem_insert_of_mem hj)) he
lemma Lease.lists {J : Type} {s : Finset J} (f g : J→ I→ℝ) (he : Audience y)(h : ∀ i∈s, Lease y δ (f i) (g i)) : Lease y δ (fun j=>∑ i∈s,f i j) (fun j=>∑ i∈s,g i j) := by
  have hp (f : J→I→ℝ): (∑ i∈s,f i)=(fun j=>∑ i∈s,f i j) := funext fun i=>Finset.sum_apply i ..
  rw [← hp, ← hp]; exact Lease.list he h
lemma Lease.rangers {ι:I→Type}{F H : ∀ i,Shale (ι i) r} (h : Lease y δ a b)(hp : Both y δ F H η)(hy : Audience y) :
    Both y δ (fun i=> a i • F i) (fun i=> b i • H i) η := by
  refine ⟨hp.1.scale h.1,hp.2.scale h.2,?_⟩
  obtain ⟨V,hV,Hv⟩:= h.asset
  have hz:= hp.moves.scale h.1; let S:= fun i=> (a i-b i) • H i
  have ht : Voucher y δ S η := by
    obtain ⟨p,he,hx⟩:= hp.again
    refine ⟨V*p,hV.times he,fun i=> glow_less ((hx i).scale _) le_rfl ?_⟩
    change ‖a i-b i‖*(p i*1) ≤ V i*p i*δ i; rw [mul_one,mul_right_comm]; exact mul_le_mul_of_nonneg_right (Hv _) (he.positive i)
  convert hz.plus ht hy using 1; funext i; change a i • F i - b i • H i=a i • (F i - H i)+(a i-b i) • H i; rw [smul_sub,sub_smul]; abel

-- pre-block cost probe. Extend trivially off η positive small.
def probeFee (G : Gauge) (u : ℝ) := if h:0<u then (kProbe_quote G u h).choose else 0
lemma probe_fee (G : Gauge)(u : ℝ) : 0 ≤ probeFee G u := by unfold probeFee; split; next h=> exact (kProbe_quote G u h).choose_spec.1
                                                            exact le_rfl
lemma assesses {F : Pot G 2}{w A : ℝ} (h : Glow F w A) (hp : 0<w) : ‖probeK i F‖≤ probeFee G w*A := by
  unfold probeFee; rw [dif_pos hp]; exact (kProbe_quote G w hp).choose_spec.2 F h i
lemma cost_probe {F H : I→Pot G 2} (hp : ∀ i,0<η i) (h : Both y δ F H η)(hs : Weighed y (fun i=> probeFee G (η i))) : Lease y δ (probeK i ∘ F) (probeK i ∘ H) := by
  obtain ⟨A,hA,H'⟩:= h.fresh; obtain ⟨B,hB,he⟩:= h.again; obtain ⟨C,hC,hv⟩:= h.moves
  simp only [Pi.one_apply,mul_one] at H' he
  refine ⟨(hs.times hA).mono (fun _=>norm_nonneg _) (fun j=> assesses i (H' j) (hp j)),(hs.times hB).mono (fun _=>norm_nonneg _) (fun j=> assesses i (he j) (hp j)), _,hs.times hC,fun j=>?_⟩
  rw [Pi.mul_apply,mul_assoc]; erw [← probe_diff i (H' j) (he j) (hp j) (hp j)]; exact assesses i (hv j) (hp j)

section
variable {f g : I → ℕ → ℝ}
lemma Lease.powerT (h : Audience y) {k : ℕ}(hf : ∀ j≤k, Lease y δ (fun i=> f i j) (fun i=>g i j)) (j n)(hp : n≤k) :
    Lease y δ (fun i=> powT (f i) j n) (fun i=>powT (g i) j n) := by
  induction j generalizing n with
  | zero=> simp_rw [pow_zeroT]; exact Lease.const ..
  | succ j ih=> simp_rw [pow_suit]; refine Lease.lists (f:=fun (a:ℕ×ℕ) i=> powT (f i) j a.1 * f i a.2) _ h (fun p hp=>?_); exact Lease.times (ih _ (by have ht:=mem_antidiagonal.mp hp; omega)) (hf _ (by have ht:=mem_antidiagonal.mp hp; omega)) h
lemma Lease.reforming (h : Audience y) {k : ℕ} (hf : ∀ j≤k,Lease y δ (fun i=> f i j) (fun i=> g i j)) (n : ℕ) (hp : n≤k) :
    Lease y δ (fun i=> reform (f i) n) (fun i=>reform (g i) n) := by
  induction n using Nat.caseStrongRecOn with
  | zero=> simp_rw [reform_zero]; exact hf _ hp
  | ind n ih=>
    have he : ∀ j≤n, Lease y δ (fun i=> reform (f i) j) (fun i=> reform (g i) j) := fun j hj=> ih j hj (by omega)
    simp_rw [reform_succ]; refine Lease.lists _ _ h (fun j hj=> ?_)
    exact Lease.times (hf _ (by have ht:=mem_range.mp hj; omega)) (Lease.powerT (f:=fun i=>reform (f i)) (g:=fun i=>reform (g i)) h he (j+1) (n-j) (by omega)) h
lemma Lease.undo (h : Audience y) {k : ℕ} (hf : ∀ j≤k, Lease y δ (fun i=> f i j) (fun i=> g i j)) (he : ∀ i, f i 0=1) (hv : ∀ i,g i 0=1) (n : ℕ) (hp : n≤k) :
    Lease y δ (fun i=> PowerSeries.coeff n (PowerSeries.mk (f i))⁻¹) (fun i=> PowerSeries.coeff n (PowerSeries.mk (g i))⁻¹) := by
  induction n using Nat.caseStrongRecOn with
  | zero=> simp_rw [coeff_inv 0,constantCoeff_mk,he,hv]; exact Lease.const ..
  | ind n ih=>
    rw [show (fun i=> PowerSeries.coeff (n+1) (PowerSeries.mk (f i))⁻¹)=(fun i=> -(1:ℝ)* (∑ j∈wheel (n+1), if j.2 < n + 1 then f i j.1 * coeff j.2 (PowerSeries.mk (f i))⁻¹ else 0)) from ?_,
        show (fun i=> coeff (n+1) (PowerSeries.mk (g i))⁻¹)=(fun i=> -(1:ℝ)*(∑ j∈wheel (n+1), if j.2 < n + 1 then g i j.1 * coeff j.2 (PowerSeries.mk (g i))⁻¹ else 0)) from ?_]
    · refine Lease.times (Lease.const y δ (-1)) (Lease.lists _ _ h (fun j hj=> ?_)) h
      split; next ht=> exact Lease.times (hf _ (by have he:=mem_antidiagonal.mp hj; omega)) (ih _ (by omega) (by omega)) h
      next ht=> exact Lease.const y δ 0 -- must split both
    · funext i; conv_lhs => rw [coeff_inv]; simp only [constantCoeff_mk,hv,coeff_mk,inv_one]; rw [if_neg (by omega)]
    funext i; conv_lhs => rw [coeff_inv]; simp only [constantCoeff_mk,he,coeff_mk,inv_one]; rw [if_neg (by omega)]
lemma Lease.rePrice (h : Audience y) {k : ℕ} (hf : ∀ j≤k, Lease y δ (fun i=> f i j) (fun i=> g i j)) (he : ∀ i, f i 0=1) (hv : ∀ i,g i 0=1) {q l : ℕ} (hp : q-l≤k) :
    Lease y δ (fun i=> recitalR (f i) q l) (fun i=> recitalR (g i) q l) := by
  cases l with
  | zero=> exact Lease.undo (f:=fun i=>reform (f i)) (g:=fun i=>reform (g i)) h (Lease.reforming h hf) (fun i=> by rw [reform_zero,he]) (fun i=> by rw [reform_zero,hv]) q hp
  | succ l=> exact Lease.powerT (f:=fun i=>reform (f i)) (g:=fun i=>reform (g i)) h (Lease.reforming h hf) _ _ hp
end
end YM.RG08.Conductor

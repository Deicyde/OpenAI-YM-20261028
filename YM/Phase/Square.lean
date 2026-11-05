import YM.Ground.Spectrum
import YM.Phase.Approx

/-!
# Graft transport from *actual approximants* on ordinary anti pair

Need plug real placements from later oriented grid, pass all large t before send d↑. -/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Grid
open Function Set Filter MeasureTheory Measure Complex Analysis Extraction Ground Table Row Lattice Wilson Word
open scoped Topology InnerProductSpace NNReal ENNReal ContDiff BigOperators ComplexOrder
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order} {V : Chamber S timeAxis}

private lemma finite {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {n : ℕ} (x : Fin n → X → ℝ) (r : ℝ)
    (h : ∀ i, Measurable (x i) ∧ ∀ q, |x i q| ≤ r) (A : Fin n → Fin n → ℝ) (hx : ∀ i j, i < j →
      ∫ q,x i q*x j q∂μ ≤ A i j) :
    0 ≤ ∑ i, ∑ j, (if i=j then r^2 else if i<j then A i j else A j i) := by
  have ht i : 0≤∫ q, (x i q)^2∂μ := integral_nonneg fun q => sq_nonneg _ -- not needed
  have hp (i j) : ∀ q, |x i q*x j q| ≤ r^2 := fun q => (abs_mul ..).le.trans ((mul_le_mul ((h i).2 _) ((h j).2 _)
    (abs_nonneg _) ((abs_nonneg _).trans ((h i).2 q))).trans_eq (pow_two r).symm)
  have hf i j : Integrable (fun q => x i q*x j q) μ := Integrable.of_bound ((h i).1.mul (h j).1).aestronglyMeasurable (r^2)
    (Eventually.of_forall (hp i j))
  calc
    _ ≤ (∫ q,(∑ i,x i q)^2 ∂μ) := integral_nonneg fun _ => sq_nonneg _
    _ = ∑ i,∑ j, ∫ q, x i q*x j q ∂μ := by
      simp_rw [pow_two,Finset.sum_mul,Finset.mul_sum]; rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hf i j)]
      apply Finset.sum_congr rfl; intro i hi; exact integral_finsetSum _ fun j _ => hf i j
    _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      split
      · exact (integral_mono (hf i j) (integrable_const _) (g := fun _ => r^2) (fun q => (le_abs_self _).trans (hp i j q))).trans_eq (by simp)
      rename_i hb; split
      · exact hx i j (by assumption)
      simp_rw [mul_comm (x i _)]; exact hx _ _ (lt_of_not_ge (by intro H; have hh : i<j := lt_of_le_of_ne H hb; contradiction))

variable (P : Spread V) (h : ℕ) (v : Fin h → C.book.Token) -- change names

lemma horizon (H : Steady V) (Y : S.Hierarchy) (w z : C.book.Word) (hv : distinct w) (hz : distinct z)
    (i j : ℕ) (p : i<j) : Tendsto (fun t => compareA (S:=S) h t i j w z) atTop
      (𝓝 (inner ℂ V.omega0 ((M P w hv*M P z hz : P.algebra).val V.omega0))) := by
  let A : Car C.book := (⟨w,hv⟩, fun t => force (C:=C) h t i)
  let B : Car C.book := (⟨z,hz⟩, fun t => force (C:=C) h t j)
  have he : line [A,B] := by
    simp [line,A,B,flight,force]
    -- formula
    have hp := mul_pos (C.S.a_pos h) (sub_pos.mpr (by exact_mod_cast p : (i:ℝ)<j))
    apply (Tendsto.atTop_mul_const hp tendsto_natCast_atTop_atTop).congr
    intro t; simp [Schedule.gridPoint]; ring
  have hh := (arcs P H Y _ he).2
  simpa only [all,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,starU,List.prod_cons,List.prod_nil,mul_one,A,B] using! hh

def θ (P : Spread V) (w : C.book.Word) (p : distinct w) : P.algebra := M P w p - M P (anti w) (apart p)
def answer (P : Spread V) (w : C.book.Word) (p : distinct w) := (inner ℂ V.omega0 (((θ P w p)^2 : P.algebra).val V.omega0)).re

variable {n : ℕ}
lemma estimates (v : Fin n → C.book.Token) (x : Fin n → Cover) (p : distinct (Tag h v x)) (H : Steady V) (Y : S.Hierarchy)
    (i j : ℕ) (hp : i<j) : Tendsto (fun t => event (S:=S) h v x t i j) atTop (𝓝 (answer P (Tag h v x) p)) := by
  let w := Tag h v x
  have hx (w z : C.book.Word) (hv : distinct w) (hz : distinct z) := continuous_re.continuousAt.tendsto.comp (horizon P h H Y w z hv hz i j hp)
  convert ((hx w w p p).sub (hx w (anti w) p (apart p))).sub ((hx (anti w) w (apart p) p).sub (hx (anti w) (anti w) (apart p) (apart p))) using 1
  · rfl
  unfold answer θ; simp only [pow_two,mul_sub,sub_mul]; congr 1
  simp [inner_sub_right,w]; ring
private def charge (n : ℕ) (r : ℝ) (A : ℕ→ℕ→ℝ) :=
    ∑ i : Fin n, ∑ j : Fin n, (if i=j then r^2 else if i<j then A i j else A j i)

private lemma att (n : ℕ) (r a) : charge (n+1) r (fun _ _ => a) = ((n+1:ℕ):ℝ) * (r^2+n*a) := by
  have hp (i : Fin (n+1)) : (∑ j : Fin (n+1), (if i=j then r^2 else a))=r^2+n*a := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl]
    congr 1
    trans ∑ _j∈ (Finset.univ.erase i), a
    · apply Finset.sum_congr rfl; intro j hj; rw [if_neg (Finset.mem_erase.mp hj).1.symm]
    simp
  simp [charge,hp]; ring

private lemma charged {M : Type*} (ℓ : Filter M) (n : ℕ) {r A} (G : M→ℕ→ℕ→ℝ) :
    (∀ i j : Fin n, i<j → Tendsto (fun u => G u i j) ℓ (𝓝 (A i j))) →
    Tendsto (fun u => charge n r (G u)) ℓ (𝓝 (charge n r A)) := by
  intro h; unfold charge
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  rcases lt_trichotomy i j with e|e|e
  · simpa [e,e.ne] using h i j e
  · subst j; simp; exact tendsto_const_nhds
  simpa [not_lt.mpr e.le,e.ne'] using h j i e

lemma Covering.square (v : Fin n → C.book.Token) (x : Fin n → Cover) (p : distinct (Tag h v x))
    (W : Covering h v x) (he : W.Works h v x f)
    (H : Steady V) (Y : S.Hierarchy) (hx : Expects (S:=S) (f:=f) h v x) : 0 ≤ answer P (Tag h v x) p := by
  let a := answer P (Tag h v x) p
  have he' k q : 0 ≤ charge (q+1) (W.reserve k) (fun _ _ => a+W.small k) := by
    let U t := fun i j => event (S:=S) h v x t i j+W.small k
    apply ge_of_tendsto (charged atTop (q+1) U (fun i j hij => (estimates P h v x p H Y (i.val) (j.val) hij).add_const _))
    have ht i j (hk : (i:Fin (q+1))<j) : ∀ᶠ t : ℕ in atTop,
        (Tendsto (fun u : ℕ×ℕ=> bill h v x i j u.1 u.2 t+W.small k) f.fuse (𝓝 (U t i j))) ∧
        f.late fun N l => ∫ w, W.plots k N l t i w * W.plots k N l t j w∂law G _ (C.beta N l) ≤ bill h v x i j N l t+W.small k := by
      filter_upwards [hx _ _ (show i.val<j.val from hk),he.fillings k _ _ (show i.val<j.val from hk)] with t hc hh
      refine ⟨hc.add_const _,?_⟩
      unfold Extraction.Order.late at *; refine hh.mono fun r hr => hr.mono fun N hN => ?_
      exact sub_le_iff_le_add'.1 ((abs_le.mp hN).2)
    filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (fun j => eventually_all.mpr (ht i j)))] with t hp
    let B (i : ℕ × ℕ) (p r : ℕ) := bill h v x p r i.1 i.2 t+W.small k
    apply ge_of_tendsto (charged f.fuse (q+1) B (fun i j h => (hp i j h).1))
    have heI : ∀ i (j : Fin (q+1)), ∀ _ : i<j, ∀ᶠ u in f.fuse, ∫ w, W.plots k u.1 u.2 t i w * W.plots k u.1 u.2 t j w∂law G _ (C.beta u.1 u.2) ≤ B u i j :=
      fun i j hij => (hp i j hij).2
    have hF (i : Fin (q+1)) : ∀ᶠ u in f.fuse, Measurable (W.plots k u.1 u.2 t i) ∧
        ∀ y, |W.plots k u.1 u.2 t i y| ≤ W.reserve k := he.controls k t i
    filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (fun j => eventually_all.mpr (heI i j))),eventually_all.mpr hF] with u hv hl
    exact finite (law G _ (C.beta u.1 u.2)) (fun j : Fin (q+1) => W.plots k u.1 u.2 t j) (W.reserve k) hl (fun i j => B u i j) hv
  have hh k : 0 ≤ a+W.small k := by
    by_contra! ht
    have hp := Tendsto.atTop_mul_const_of_neg ht tendsto_natCast_atTop_atTop
    obtain ⟨n,hN⟩ := (hp.eventually (eventually_lt_atBot (-W.reserve k^2))).exists
    have hz := he' k n; rw [att n] at hz
    exact (mul_neg_of_pos_of_neg (by positivity) (show _ + (n:ℝ)*_ < 0 by linarith)).not_ge hz
  have hu : Tendsto (fun k => a+W.small k) atTop (𝓝 a) := by simpa using W.grows.const_add a
  exact ge_of_tendsto' hu hh
end YM.OS.Grid

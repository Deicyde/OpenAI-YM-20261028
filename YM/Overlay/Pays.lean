import YM.Overlay.Table
import YM.Vac.Caps

/-!
# Stop at ANY m with these costs. Marker number and site count visible.

Merges don't give independent coefficients on arbitrary power sets. But the
total absolute bound uses that relaxation as an inequality, proving existence
of the relevant sums rather than assuming smallness of their values.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Overlay
open Function Marker RG Lattice Wilson MeasureTheory Filter
open Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n : Side} {V : Type*} [Fintype V] [DecidableEq V] {R : Census V} {P : Rep G n}
variable (a : Bands R P) {w : V → ℝ} {u c d b : ℝ} (h : a.Active) (t : a.Radial w u c d b)

lemma per_system {α : Type*} {f : α → ℝ} {P : α → R.Mode} {c : ℝ} (h : ∀ i,0≤f i) (hv : ∀ i, (P i).val.Nonempty)
    (ht : ∀ i : V, SumBudget (fun j => if i∈ (P j).val then f j else 0) c) :
    SumBudget f (Fintype.card V * c) := by
  let q (x : V) k := if x∈(P k).val then f k else 0
  have he := summable_sum (s:=Finset.univ) (f:=q) fun i (_ : i∈Finset.univ) => (ht i).2.1
  have hh (i) : f i ≤ ∑ x, q x i := by
    obtain ⟨y,hy⟩ := hv i
    calc
      _ = q y i := by simp only [q,if_pos hy]
      _ ≤ _ := Finset.single_le_sum (fun i _ ↦ (ht i).1 _) (mem_univ _)
  have HF := he.of_nonneg_of_le h hh
  refine ⟨h, HF,(HF.tsum_le_tsum hh he).trans ?_⟩
  rw [Summable.tsum_finsetSum (f:=q) (fun i _ ↦ (ht i).2.1)]
  exact (sum_le_sum fun i _ => (ht i).2.2).trans (by simp)

namespace Bands

include h t
lemma bulkBound (U : Config G n) : Summable (fun i => a.ray i U) ∧
    Poly.price w (a.extra U) ≤ Fintype.card V*(u+c) := by
  obtain ⟨q,hq,H⟩ := t.bulk
  let C (i : ℕ) := Poly.toll w (a.rays i)*P.p.mass (a.support i) (q i)
  have hn (i) : 0≤ C i := mul_nonneg (Poly.worth t.pure _).le (le_trans (hq i).1 (P.p.loMass _ _ (hq i).1))
  have he := per_system hn h.proper H
  have hf (i) : Poly.price w (a.ray i U) ≤ C i := by
    rw [ray,Poly.solo]; apply mul_le_mul_of_nonneg_left _ (Poly.worth t.pure _).le
    apply le_trans _ (P.p.loMass _ _ (hq i).1)
    obtain ⟨x,hx⟩ := h.proper i
    by_cases hy : Healthy P.p.threshold (a.support i) U
    · rw [masked_eq _ _ _ _ hy]; exact ((hq i).2 x hx).2 U hy [] (by simp) (by simp)
    rw [masked_ne _ _ _ _ hy,norm_zero]; exact (hq i).1
  obtain ⟨he,hC⟩ := Poly.budgeted t.pure he.2.1 hf
  refine ⟨he, (Poly.addition t.pure _ _).trans (add_le_add (le_trans (Poly.batch t.pure ..) ?_) (hC.trans ‹SumBudget C _›.2.2) |>.trans_eq (mul_add _ _ _).symm)⟩
  simp_rw [Poly.solo,Poly.solo_toll]
  exact le_trans (sum_le_sum (f:=fun i => w i*‖a.units i‖) fun i _ => t.localU i) (by simp)

lemma baseBound {δ κ : ℝ} (H : P.activities.Valid P.p δ κ) (U : Config G n) :
    (∀ i : ℕ,Summable (fun j => a.tagged i j U)) ∧ SumBudget (fun i => Poly.price w (a.each i U))
      (Fintype.card (Site n)*κ+Fintype.card V*(d*b)) := by
  obtain ⟨q,hq,hH⟩ := H.boundK
  let k := fun i => P.activities.forced i
  have ha (i) : (k i).support.Nonempty := (k i).inventory_ne.mono (k i).inventory_sup
  have he : Summable q := Activities.summable_charge ha (fun i => (hq i).1) hH
  have h' := sumRoot ha (fun i => (hq i).1) hH
  obtain ⟨f,hf,hB⟩ := t.hits
  let T (x : ℕ × ℕ) := Poly.toll w (a.marks x.1 x.2)*P.p.mass (k x.1).support (f x)
  have hw (i) : 0≤f i := (hf i.1 i.2).1
  have hp : SumBudget T (Fintype.card V*(d*b)) := per_system (fun i =>
    mul_nonneg (Poly.worth t.pure _).le (le_trans (hw i) (P.p.loMass _ _ (hw i))))
    (P:=fun i => a.marks i.1 i.2) (fun i => h.occurs i.1 i.2) hB
  let x (i : ℕ) := ∑' j,T (i,j)
  obtain ⟨hi,hx⟩ := (summable_prod_of_nonneg (show 0 ≤ T from hp.1)).mp hp.2.1
  have hs (i : ℕ) : Summable (fun j => a.tagged i j U) ∧ Poly.price w (∑' j,a.tagged i j U) ≤ x i := by
    refine Poly.budgeted t.pure (hi i) fun j => ?_
    rw [tagged,Poly.solo]; exact mul_le_mul_of_nonneg_left (((hf i j).2 _).trans (P.p.loMass _ _ (hw _))) (Poly.worth t.pure _).le
  have ht (i : ℕ) : Poly.price w (a.each i U) ≤ q i+x i := by
    rw [each]
    apply (Poly.addition t.pure ..).trans (add_le_add ?_ (hs i).2)
    simpa only [Poly.solo,Poly.quiet_toll,Complex.norm_real,one_mul] using (hq i).2 U
  have hy := he.add hx
  have H := hy.of_nonneg_of_le (fun i => Poly.nonnegative t.pure _) ht
  refine ⟨fun i => (hs i).1,fun i => Poly.nonnegative t.pure _,H,(H.tsum_le_tsum ht hy).trans ?_⟩
  rw [Summable.tsum_add he (f:=q) (g:=x) (show Summable x from hx)]
  exact add_le_add h' ((hp.2.1.tsum_prod).symm.trans_le hp.2.2)

lemma population {δ κ : ℝ} (H : P.activities.Valid P.p δ κ) (U : Config G n) :
    Summable (fun i => a.packet i U) ∧ Poly.price w (a.cluster U) ≤ Real.exp (Fintype.card (Site n)*κ+Fintype.card V*(d*b)) := by
  obtain ⟨hn,hs,hg⟩ := (a.baseBound h t H U).2
  let f (i) := Poly.price w (a.each i U)
  obtain HH : Summable fun t => ∏ i∈t,f i := summable_finsetProd_of_summable_nonneg hn hs
  have hp (s : Finset ℕ) : Poly.price w (a.packet s U)≤ ∏ i∈s,f i := by
    unfold packet; split
    · exact Poly.multiple t.pure _ _
    rw [Poly.zero_price]; exact prod_nonneg fun i _ => hn i
  have hh := Poly.budgeted t.pure HH hp
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply le_of_tendsto HH.hasSum; refine Eventually.of_forall fun s => ?_
  let l := s.biUnion id
  calc
    _ ≤ ∑ v∈l.powerset, ∏ i∈v,f i := sum_le_sum_of_subset_of_nonneg (fun x hx => mem_powerset.mpr fun i hi => mem_biUnion.mpr ⟨x,hx,hi⟩) (fun i _ _ => prod_nonneg fun i _ => hn i)
    _ = ∏ i∈l, (1+f i) := (Finset.prod_one_add l).symm
    _ ≤ ∏ i∈l, Real.exp (f i) := prod_le_prod (fun i _ => add_nonneg zero_le_one (hn i))
      (fun i _ => le_trans (le_of_eq (add_comm _ _)) (Real.add_one_le_exp (f i)))
    _ = Real.exp (∑ i∈l, f i) := (Real.exp_sum ..).symm
    _ ≤ _ := Real.exp_monotone ((hs.sum_le_tsum _ fun i _ => hn i).trans hg)

lemma same {δ κ : ℝ} (H : P.activities.Valid P.p δ κ) (U : Config G n) :
    (a.density U).part R.quiet=(P.eval U:ℂ) := by
  have hh (i : R.Mode) (hx : i.val.Nonempty) (x : ℂ) : (Poly.send i x).part R.quiet=0 := by rw [Poly.part_send,if_neg (show R.quiet≠i from fun H => nonempty_iff_ne_empty.mp hx (congr_arg Subtype.val H.symm))]
  have hE : (a.extra U).part R.quiet=0 := by
    rw [extra,Poly.part_plus,Poly.share ((a.bulkBound h t U).1),Poly.part_sum]
    simp_rw [ray, hh _ (h.proper _),hh _ (show (R.fire _).val.Nonempty from Finset.singleton_nonempty _), tsum_zero,sum_const_zero,zero_add]
  have he := (a.population h t H U).1
  have hg (i : ℕ) : (a.each i U).part R.quiet= (P.activities.K i U : ℂ) := by
    rw [each,Poly.part_plus,Poly.share ((a.baseBound h t H U).1 i)]
    simp only [tagged, hh _ (h.occurs _ _), Poly.part_send, ↓reduceIte, tsum_zero,add_zero] -- rewrite order
  rw [density,Poly.part_smul,Poly.quiet_mul,Poly.pass_part _ hE,one_mul, Rep.eval,Complex.ofReal_mul]
  congr 1
  unfold cluster Activities.gas
  rw [Poly.share he, Complex.ofReal_tsum]
  refine tsum_congr fun b => ?_
  unfold packet Activities.gasOccurrence; split
  · rw [Complex.ofReal_prod]
    let e : Poly R →* ℂ := { toFun := fun v => v.part R.quiet, map_one' := by simp only [Poly.one_part,↓reduceIte], map_mul' := fun i j => Poly.quiet_mul _ _ }
    refine Eq.trans (map_prod e ..) ?_
    exact prod_congr rfl fun i _ ↦ hg i
  simp
end Bands
end YM.Overlay

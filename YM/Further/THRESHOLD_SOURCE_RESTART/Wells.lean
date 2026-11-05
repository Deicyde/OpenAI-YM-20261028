import YM.Next.FOUNDATIONS.SU2
import YM.Push.CORRECTED_COLUMNS.Infuse
import YM.Push.CORRECTED_COLUMNS.Reprint

/-!
# Move W terms onto *same-head* masks 

Not yet C-corrected. Build the heads from actual unscaled atoms;
each selected history attached to just one head; others left intact
and not required to fit there. Need true local-on-head in look (don't
infer that the large mask itself is local on just the head). Here only
on real configurations, value regularity per Prepare port.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart
open Function Filter Set MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Prepare Width
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {I V α : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    {G : Gauge} {n : Side} {p : BudgetPoint} {o : I × V → Site n}

/-- At the current level. Include all additionally needed sites in `area`
(and still pay for them). -/
structure Wells (F : Atoms p (Marks.all (I×V)) o G α) where
  area : I → Support n
  attends (i : I × V) : o i ∈ area i.1
  distinct : ∀ i j,i≠j → Disjoint (area i) (area j)
  nonempty i : (area i).Nonempty
  host : α → Option I
  keeps i j : host i=some j → F.sites i ⊆ area j

namespace Wells
variable {F : Atoms p (Marks.all (I×V)) o G α} (W : Wells F)

def fibre (F : Atoms p (Marks.all (I×V)) o G α) (j i) := Marks.fibre (F.tag i).val j

lemma valued {i j} (h : W.host i=some j) : Marks.located (F.tag i).val {j} := by
  intro k hk; apply Finset.mem_singleton.mpr
  by_contra H
  exact (Finset.disjoint_left.mp (W.distinct k.1 j H)) (W.attends k) (W.keeps i j h (F.pin i k hk))
lemma name {i j} (h : W.host i=some j) : (F.tag i).val = Marks.injectSubset j (fibre F j i) := Marks.listed (W.valued h)


-- full values about j only on future good sets. Off-domain total defined,
-- not invoking summability there. This rep doesn't promise levelwise
-- differentiability of these witnesses; see kernel ports.

def raw (j : I) (i : α) (U) := if W.host i = some j then Poly.send (Marks.mode (fibre F j i)) (F.H i U) else 0






variable [Countable α]


def orphan : Atoms p (Marks.all (I×V)) o G α where
  tag := F.tag
  sites := F.sites
  pin := F.pin
  proper := F.proper
  H i := if W.host i=none then F.H i else 0
  footprint i := by split; exact F.footprint _; exact fun _ _ _ => rfl
  borel i := by split; exact F.borel _; exact measurable_const
  gauge i := by split; exact F.gauge _; exact fun _ _ => rfl

-- honest masked relocations for the selected atoms

def lifted (j i) U := if W.host i=some j ∧ Healthy p.threshold (W.area j) U then F.portion i U else 0

omit [Countable α] in
lemma lifted_with {j i U} (h : W.host i = some j) (hp : Healthy p.threshold (W.area j) U) :
    W.lifted j i U = F.portion i U := if_pos ⟨h,hp⟩
omit [Countable α] in
lemma replaceable (j U) (hp : Healthy p.threshold (W.area j) U) (i) : W.lifted j i U=Marks.into (W.raw j i U) j := by
  by_cases h : W.host i = some j
  · rw [W.lifted_with h hp,raw,if_pos h, Marks.into_atom,Atoms.portion,
      masked_eq _ _ _ _ (hp.mono_left (W.keeps i j h)),show F.tag i= Marks.mode (Marks.injectSubset j (fibre F j i)) from Subtype.ext (W.name h)]
  rw [lifted, if_neg (fun he => h he.1),raw,if_neg h]; exact ((Marks.emb j).map_zero).symm

variable {w a b : ℝ}
omit [Countable α] in
lemma summable_raw {M} (hw : 0 < w) (ha : 0 ≤ a) (h : F.Cost (fun _=>w) M a b) (j U) (hp : Healthy p.threshold (W.area j) U) :
    Summable fun i => W.raw j i U := by
  obtain ⟨g,hg,h⟩ := h
  let X (i : α) := Poly.toll (fun _=>w) (F.tag i)*g i*emit M a (F.sites i)
  have hX i : 0 ≤ X i := mul_nonneg (mul_nonneg (Poly.worth (fun _=>hw) _).le (hg i).1) (emit_pos ..).le
  have he := per_system (R:=Marks.all (I × V)) hX F.proper h
  refine (Poly.budgeted (V:=V) (fun _=>hw) he.2.1 ?_).1; intro i
  unfold raw; split
  next H =>
    rw [Poly.solo]
    have hf := W.name H
    have ht : Poly.toll (fun _=>w) (Marks.mode (fibre F j i))=Poly.toll (fun _=>w) (F.tag i) := by
      have hB : (fibre F j i).card=(F.tag i).val.card := by
        have hx : Injective (fun v : V => (j,v)) := fun _ _ hh => congr_arg Prod.snd hh
        exact Eq.symm ((congr_arg Finset.card hf).trans (Finset.card_image_of_injective (fibre F j i) hx))
      unfold Poly.toll; simp only [Finset.prod_const, hB]
    rw [ht]; apply le_trans _ (le_mul_of_one_le_right (mul_nonneg (Poly.worth (V:=I×V) (fun _=>hw) _).le (hg i).1)
      (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg (α:=ℝ) _))))
    exact mul_le_mul_of_nonneg_left ((hg i).2 U (hp.mono_left (W.keeps i j H))) (Poly.worth (fun _=>hw) _).le
  rw [Poly.zero_price]; exact hX _


end Wells
end YM.Further.ThresholdSourceRestart

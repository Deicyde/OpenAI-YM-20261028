import YM.Next.BOUNDARY.Core
import YM.Next.FOUNDATIONS.TestBounds
import YM.Push.RELAY_DIFFERENCE.Opening
import YM.Work.A05
import YM.Work.B18

/-!
# Issue one-body top estimates for both vet calls

Additional input ONLY address room at top in actual rep (needed for dormant
labels etc; see Reader/Budget) and explicit order/support-exponent numerical
requirements on the actual schedule. Use C.Makes, no additional hypotheses
of a propagating source beyond that. Connection theorem lets continued steps
use these data once prepared. We haven't proved the continued steps! E.L.15668--83
includes initialization of *array* representations too; keep that requirement
for multi-source steps. This delivers one-body budget b and exact placed
source at N.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Lattice Cells Marker Overlay Stock Bid Mix Source Labels
  Next.Foundations Attach Opening
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {C : Family G} {N p d e : ℕ} {W : Worth} {f : Extraction.Order} {F : Trial C}

/-- Addresses at birth. Requires that the *actual history already has
these slots* -- E address padding problem, not constructing it in C. -/
def padded (C : Family G) (f : Extraction.Order) := ∀ D : Finset Cover, 0∈D → f.late fun N p =>
    Nonempty (Slots (regional D (0: Site (C.side N p))) (C.path.rep N p N))

def roof (C : Family G) (f : Extraction.Order) := Slow C f fun j => Real.exp ((C.path.levels.budget j.1).supportExponent)

lemma cover_tops (h : G.Simple) (D : Finset Cover) : ∀ᶠ N in atTop,∀ p : ℕ,
    coverNumber (C.path.levels.budget N).B (regional D (0:Site (C.side N p))) ≤ 81 := by
  have ht : Tendsto C.path.levels.clock.hatBeta atTop atTop := tendsto_atTop_add_const_left _ _
    (C.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos h))
  have hb : Tendsto (fun i => (C.path.levels.budget i).B) atTop atTop := Work.E01.radiusB_tendsto.comp ht
  have hs : ∀ᶠ N in atTop,∀ i∈D,∀ j, (i j).natAbs ≤ (C.path.levels.budget N).B :=
    eventually_all_finset _ |>.mpr fun i hi => eventually_all.mpr fun j => hb.eventually_ge_atTop _
  filter_upwards [hs] with i hi p
  let b := (C.path.levels.budget i).B
  let z : Site (C.side i p) := 0
  have hr : coverNumber b (halo b {z}) ≤ 81 := by
    simpa using Corona.tile z 1 b (C.path.levels.budget i).B_pos
  refine (Corona.cover_mono ?_ b).trans hr
  rintro j hj; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hj
  refine halo_spec.mpr ⟨z,Finset.mem_singleton_self _,?_⟩
  rw [add_zero,separation_comm,separation,show z=0 from rfl,sub_zero]
  exact Finset.sup_le fun j _ => (Corona.lap ..).trans (hi x hx j)

/-- A top datum exactly for the listed Solo.Encoded fields at N. -/
structure Start (C : Family G) (F : Trial C) (e : ℕ) where
  source (N p : ℕ) : Coefficient (C.labels.level e) (C.side N p)
  ticket : Cutoffs → ℝ
  total : Cutoffs → ℝ

namespace Start
variable (S : Start C F e)

structure ReadyAt (N p : ℕ) : Prop where
  active : C.ref e ≤ N
  valid : (S.source N p).Format 0 C.params (C.path.rep N p N)
  cap : (S.source N p).remBound 0 (C.path.rep N p N)
    (Real.sqrt (C.path.levels.clock.forcedAllowance N)) (S.ticket (N,p))
  put (U) : (S.source N p).density 0 (C.localSection e) (C.path.rep N p N) U =
      weight C e N * (bare (C.beta N p) U : ℂ) * F N p 0 U
  positive : 0 < S.total (N,p)
  afford : S.ticket (N,p) + (C.labels.level e).coeffSize (S.source N p).x ≤ S.total (N,p)

def Prepared (f : Extraction.Order) := Slow C f S.total ∧ f.late S.ReadyAt

/-- Still need continuation and LOCAL bounds even using birth. Does the
actual continued Solo pin this very Start? Don't allow changing when
exporting. -/
structure Extends (P : Solo C F e) (N p : ℕ) : Prop where
  source : P.source N p N=S.source N p
  ticket : P.ticket N p N=S.ticket (N,p)
  total : P.total (N,p)=S.total (N,p)
  valid i : C.ref e ≤ i → i < N → (P.source N p i).Format 0 C.params (C.path.rep N p i)
  cap i : C.ref e ≤ i → i < N → (P.source N p i).remBound 0 (C.path.rep N p i)
    (Real.sqrt (C.path.levels.clock.forcedAllowance i)) (P.ticket N p i)
  step (i) : C.ref e ≤ i → i < N →
      (P.source N p i).density 0 (C.localSection e) (C.path.rep N p i) =
        ((C.S.block i).val : ℂ)^e • (C.path.levels.clock.op i p).push (C.path.β N p (i+1))
          ((P.source N p (i+1)).density 0 (C.localSection e) (C.path.rep N p (i+1)))


end Start

theorem RawProtected.birth (hc : C.Makes) (K : G.Simple) (ht : padded C f) (hp : roof C f)
    (h : RawProtected C f F d) : ∃ S : Start C F d, S.Prepared f := by
  classical
  let H := C.path
  let L := C.labels.level d
  let T := C.localSection d
  obtain ⟨X,hX,c,b,hc',hb,H'⟩ := h
  let D := X ∪ T.stencil
  have hD : 0∈D := Finset.mem_union_left _ hX
  obtain ⟨k,hk,h₁⟩ := price_of_readout C.params L
  obtain ⟨t,ht',h₂⟩ := offmask C d
  let score (j : Cutoffs) := k*c j
  let r (j : Cutoffs) := badCost C d j.1 t (score j) (b j)
  let g (j : Cutoffs) := regCost C j.1 (score j) (c j)
  let M : ℝ := (D.card:ℝ)*Real.exp D.card
  let A (j : Cutoffs) := Real.exp ((H.levels.params j.1).supportExponent) ^ (81:ℕ)
  let box (j : Cutoffs) := A j*(g j+r j*M)
  let total (j : Cutoffs) := 1 + (box j + score j)
  -- Select at all the wanted cutoffs with separate support and true address
  -- price. Keep S afterwards. First show event budget.
  have he : f.late fun N p => let R := C.path.rep N p N
                              let j := (N,p); let o : Site (C.side N p) := 0
    -- use let continuation
                              C.ref d ≤ N ∧ 0 < total j ∧
                              ∃ P : Coefficient L (C.side N p), P.Format o C.params R ∧
      P.density o (C.localSection d) R = (fun U => weight C d N * (bare (C.beta N p) U:ℂ) * F N p 0 U) ∧
      (L.coeffSize P.x + box j ≤ total j) ∧ P.remBound o R (Real.sqrt (C.path.levels.clock.forcedAllowance N)) (box j) := by
    have slot := ht D hD
    have hA := cover_tops (C:=C) K D
    unfold Order.late at *
    filter_upwards [slot,H'] with l hh hh'
    filter_upwards [hh,hh',f.mesh.cofinal.eventually hA,f.mesh.cofinal.eventually_ge_atTop (C.ref d)] with i hs he ha hv
    let N := f.mesh i; let p := f.per l; let j := (N,p)
    let R := C.path.rep N p N
    let o : Site (C.side N p) := 0
    let Y := regional D o; let B := H.levels.budget N
    obtain ⟨hy⟩ := hs
    have hz : X ⊆ D := Finset.subset_union_left
    have he' : regional X o ⊆ Y := Finset.image_subset_image hz
    obtain ⟨he,hc'',hb',hm⟩ := he o
    have hq := regular_larger he he'
    have hx := bound_larger hc'' he'
    obtain ⟨Q,hi,hf,hQ,hb⟩ := Opening.opens (C:=C) hc N d p (score:=score j) hv ht' h₂ Y o (unpriced C F d N p o) hy
      (Finset.image_subset_image Finset.subset_union_right) ⟨hq,hx,hb',hm⟩ (fun z hz => h₁ _ o Y B _ _
        (Nat.le_of_succ_le ((hc.stages d).2 N hv).1) ((hc.stages d).2 N hv).2 hq hx z hz)
    have h₀ : 0 ≤ score j := (coeff_pos L _).trans hQ
    have hn : 0 ≤ (C.path.levels.params N).columns := zero_le_one.trans (C.path.levels.params N).columns_ge
    have hz' : 0 ≤ r j := add_nonneg hb' (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans ht')) (seats_nonneg ..)) h₀)
    have hg : 0 ≤ g j := add_nonneg hx.1 (mul_nonneg hn h₀)
    have hk : 0 ≤ box j := by unfold box M A; positivity
    have hu : ceilingCost C d N p Y t (score j) (c j) (b j) ≤ box j := by
      have he : (Y.card:ℝ) ≤ D.card := by exact_mod_cast Finset.card_image_le
      have hy : Real.exp (B.supportExponent * coverNumber B.B Y) ≤ A j := by
        unfold A
        rw [← Real.exp_nat_mul]
        apply Real.exp_monotone
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast ha p) B.exponent_pos.le
      let e := Real.exp (B.supportExponent * coverNumber B.B Y)
      change e * g j + e*r j*Y.card*Real.exp Y.card ≤ _
      unfold box; rw [mul_add]
      apply add_le_add (mul_le_mul_of_nonneg_right hy hg)
      refine le_trans (mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_right hy hz') he (Nat.cast_nonneg _) ?_)
        (Real.exp_monotone he) (Real.exp_pos _).le ?_) (le_of_eq ?_)
      · exact mul_nonneg (pow_nonneg (Real.exp_pos _).le _) hz'
      · exact mul_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos _).le _) hz') (Nat.cast_nonneg _)
      unfold M; simp only [mul_assoc]
    refine ⟨hv, (show 0 < (1:ℝ) + (box j + score j) from add_pos_of_pos_of_nonneg zero_lt_one (add_nonneg hk h₀)),Q,hi,?_,?_,?_⟩
    · rw [hf]; funext U; unfold unpriced; simp only [Pi.smul_apply,smul_eq_mul]; ring
    · change L.coeffSize Q.x + box j ≤ 1+_
      exact (add_le_add_left hQ _).trans ((add_comm _ _).le.trans (le_add_of_nonneg_left zero_le_one))
    obtain ⟨x,y,H1,H2,H3,H4,H5⟩ := hb; exact ⟨x,y,H1,H2,H3.trans hu,H4,H5⟩
  have hs : Slow C f (fun j => score j) := (Slow.const (C:=C) k).mul hc'
  have ho : Slow C f r := hb.add ((((Slow.const (C:=C) (f:=f) ((2:ℝ)*t))).mul (seats_slow K)).mul hs)
  have hx : Slow C f total := (Slow.const (C:=C) (f:=f) (1:ℝ)).add (((Slow.pow hp 81).mul
    ((hc'.add (columns_slow.mul hs)).add (ho.mul (Slow.const M)))).add hs)
  -- classical padding
  let Ready (N p) (P : Coefficient L (C.side N p)) := let R := C.path.rep N p N
      P.Format 0 C.params R ∧ P.density 0 T R=(fun U => weight C d N * (bare (C.beta N p) U:ℂ)* F N p 0 U) ∧
      (L.coeffSize P.x + box (N,p) ≤ total (N,p)) ∧ P.remBound 0 R (Real.sqrt (C.path.levels.clock.forcedAllowance N)) (box (N,p))
  have hf (N p : ℕ) : ∃ P, (∃ Q,Ready N p Q) → Ready N p P := by
    by_cases h : ∃ Q,Ready N p Q; exact ⟨Classical.choose h,fun _ => Classical.choose_spec h⟩
    exact ⟨⟨0,fun _ => ∅,0,0⟩,fun hh => False.elim (h hh)⟩
  choose P hP using hf
  let S : Start C F d := ⟨P,box,total⟩
  refine ⟨S,hx,he.mono fun l hl => hl.mono fun i hi => ?_⟩
  let j := (f.mesh i,f.per l)
  obtain ⟨hi,hb,H⟩ := hi
  obtain ⟨h1,h2,h3,h4⟩ := hP j.1 j.2 H
  exact ⟨hi,h1,h4,congr_fun h2,hb,(add_comm ..).le.trans h3⟩


end YM.Push.RelayDifference

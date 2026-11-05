import YM.SectorNext.RECONNECTED_LOCALITY.Imprint

set_option warningAsError false

/-!
# First component marginals and exact disconnected factorization 

Measurability & local integration assumptions exposed; pricing and assembly
still to come. Compare marginals (the matrix A, root of C etc may be QUITE
different even nearby outside the used window; no recipe to invert it here).
Use a ‘completion’ only to evaluate local functions of the used coordinates.
Reference θ is the entire table in each component computation; prove this is
legitimate without treating the actual kernel/choices as an independent product.
Layouts failing flags/sector address tests are zeroed by the caller; no assertion
of integrability of ratio products even where the prerequisites fail.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect.Cellular

open RG Lattice Filter Function MeasureTheory Words Wilson
open Bind Window

variable {G : Gauge} {c : Side} {ι η κ : Type*} {Y : η → Type*}
variable [∀ i,MeasurableSpace (Y i)]
variable {X : Form G c ι κ Y} {N : StageLaw G c ι κ Y}
variable [Fintype κ] (H : Cellular X N)
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq η]

private abbrev projection (p : Finset ι) := Window.scan (Subtype.val : ↥(X.window p) → κ)

variable (X)
-- Used only to feed component functions; taking a product of Gaussians on completed/full arrays
-- with the SAME off-support entries could certainly give the wrong moments.
private def fill (p : Finset ι) (z : Z ↥(X.window p)) : Z κ := fun i =>
    if h : i ∈ X.window p then z ⟨i,h⟩ else 0

omit [Fintype κ] [DecidableEq ι] [∀ i,MeasurableSpace (Y i)] [DecidableEq η] in
@[fun_prop] private lemma fill_meas (p : Finset ι) : Measurable (fill X p) := by
  refine measurable_pi_lambda _ fun i => ?_
  unfold fill
  split
  · exact measurable_pi_apply _
  exact measurable_const

variable {X}
include H

variable {p s : Finset ι} {V U : Config G c} {t q : Tables Y} {ρ : ℝ → ℝ}

omit [DecidableEq ι] [∀ i,MeasurableSpace (Y i)] in
private lemma mood {p s : Finset ι} (h : p ⊆ s) (he : ∀ i∈s, ¬Disjoint (X.land p) (X.foot i) → i∈p)
    (hv : Agrees (X.land p) V U) (ht : Tied (X.staged p) t q) (z : Z κ) :
    X.roll s p V t z=X.roll p p U q (fill X p (projection p z)) :=
  (H.survey h he hv ht).1 _ _ (by intro i hi; simp [fill,hi,projection,scan])

/-- Used by p at the standalone law (compare full selections to this). Could just
as well evaluate on the full marginal if calling estimates already proved there. -/
private def clipped (p : Finset ι) (V : Config G c) (t : Tables Y) :=
    (N.map p V t).map (projection (X:=X) p)

omit [DecidableEq ι] [DecidableEq η] [∀ i,MeasurableSpace (Y i)] in
private lemma splitLaw (p : Finset ι) (V : Config G c) (t : Tables Y) :
    Says (clipped (X:=X) (N:=N) p V t) (fun i j => N.cov p V t i j) :=
  (H.states _ _ _).view _

omit [DecidableEq ι] [∀ i,MeasurableSpace (Y i)] in
private lemma sameLaw (p : Finset ι) (hv : Agrees (X.land p) V U) (ht : Tied (X.staged p) t q) :
    clipped (X:=X) (N:=N) p V t=clipped (X:=X) (N:=N) p U q := by
  have he (i j : ↥(X.window p)) : N.cov p V t i j=N.cov p U q i j :=
    (H.survey (Finset.Subset.refl _) (fun _ h _ => h) hv ht).2 _ i.property _ j.property
  apply (splitLaw H p V t).unique
  simp_rw [he]
  exact splitLaw H p U q

variable (L : Printed X N)
include L

omit H [DecidableEq ι] [DecidableEq κ] [DecidableEq η] in
lemma at_time (s p : Finset ι) (V : Config G c) (t : Tables Y) (hρ : Measurable ρ) :
    Measurable (fun z => ρ (X.roll s p V t z)) := (L.roll (s:=s) (p:=p) hρ).comp (measurable_prodMk_left (x:=(V,t)))

omit [DecidableEq ι] in
private theorem used (hρ : Measurable ρ) :
    X.booth N p p V ρ t = ∫ z,ρ (X.roll p p V t (fill X p z)) ∂clipped (X:=X) (N:=N) p V t := by
  let f := fun z => ρ (X.roll p p V t (fill X p z))
  have hf : Measurable f := (at_time L p p V t hρ).comp (fill_meas X p)
  change _ = ∫ z,f z ∂(N.map p V t).map (projection (X:=X) p)
  rw [integral_map (Window.scan_meas _).aemeasurable hf.aestronglyMeasurable]
  unfold Form.booth
  exact integral_congr_ae (Eventually.of_forall fun z => congr_arg ρ
    (mood H (Finset.Subset.refl _) (fun _ h _ => h) (fun _ _ _ => rfl) (fun _ _ => rfl) z))

omit [DecidableEq ι] in
/-- Numerical formulas before flag check (legitimate on their admitted domains). -/
theorem localTables (hv : Agrees (X.land p) V U) (ht : Tied (X.staged p) t q) (he : Measurable ρ) :
    X.booth N p p V ρ t=X.booth N p p U ρ q := by
  rw [used H L he, used H L he, sameLaw H p hv ht]
  apply integral_congr_ae
  filter_upwards with z
  exact congr_arg ρ ((H.survey (Finset.Subset.refl _) (fun _ h _ => h) hv ht).1 _ _ (fun _ _ => rfl))

omit [DecidableEq ι] in
theorem localCoeff [Fintype η] (m : ∀ i,Measure (Y i)) (p : Finset ι) (he : Measurable ρ) :
    LocalOn (X.land p) fun V => X.edition N m p p V ρ := by
  intro V U hv
  exact integral_congr_ae (Eventually.of_forall fun t => localTables H L hv (fun _ _ => rfl) he)

section factor

-- Distinctness of repeated Z lookups is NOT imposed. But if a coordinate in both, it should
-- already be connected. θ includes every Y/tag address even in patches/halo only.
omit H L [DecidableEq ι] [DecidableEq κ] [DecidableEq η] in
private theorem joint {j : Type*} {ζ : Type*} [DecidableEq ζ] (a b : Finset j) (W : j → Finset ζ)
    (hw : ∀ i∈a,∀ k∈b,Disjoint (W i) (W k)) : Disjoint (a.biUnion W) (b.biUnion W) := by
  refine Finset.disjoint_left.mpr ?_
  intro x h1 h2
  obtain ⟨i,hi,h⟩:=Finset.mem_biUnion.mp h1
  obtain ⟨i',hi',h'⟩:=Finset.mem_biUnion.mp h2
  exact Finset.disjoint_left.mp (hw _ hi _ hi') h h'

omit L [∀ i,MeasurableSpace (Y i)] in
theorem physically (s : Finset ι) (a b : ↥(Ac.Parts X.foot s)) (hn : a ≠ b) :
    Disjoint (X.window a.val) (X.window b.val) ∧ Disjoint (X.staged a.val) (X.staged b.val) := by
  have he (i) (hi : i∈a.val) (j) (hj : j∈b.val) : Disjoint (X.foot i) (X.foot j) := by
    have he := Ac.separate X.foot s a.property b.property (mt Subtype.ext hn)
    refine Finset.disjoint_left.mpr fun x hx hy => ?_
    exact Finset.disjoint_left.mp he (Finset.mem_biUnion.mpr ⟨i,hi,hx⟩) (Finset.mem_biUnion.mpr ⟨j,hj,hy⟩)
  exact ⟨joint _ _ _ (fun i hi j hj => H.linePos i j (he i hi j hj)),joint _ _ _ (fun i hi j hj => H.stagePos i j (he i hi j hj))⟩





end factor
end YM.SectorNext.Reconnect.Cellular

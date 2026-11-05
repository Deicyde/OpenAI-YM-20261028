import YM.Extra.MULTISOURCE_TRAJECTORIES.Signals
import YM.Next.BOUNDARY.Stage
/-!
# Gauge invariant localization of exact connected coefficients

Finite anchored inclusion/exclusion, integrating over *all* exterior links
using dummy Haar (not replacing the law used in the RG evolution). A physical
output piece reads only internal links of its declared support, including for
disconnected or wrapping supports. Under the integral it may involve the
entire lattice of old variables and global tag array; no fictitious assertion
that the same small stencil controls dependence on the integrated argument.
No uniform cluster decay for the signed localized pieces is asserted here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Function Wilson RG Lattice Finset MeasureTheory Marker
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side}

def hybrid {E : Type*} (X : Support n) (a b : Edge (Site n) → E) (i : Edge (Site n)) :=
    if i.1∈X ∧ i.1+Lattice.step i.2∈X then a i else b i

lemma smooth_hybrid (X : Support n) : ContDiff ℝ ∞ (fun p : Field G n × Field G n => hybrid X p.1 p.2) := by
  refine contDiff_pi.mpr fun i => ?_
  unfold hybrid; split
  · exact (contDiff_apply ℝ _ i).comp contDiff_fst
  exact (contDiff_apply ℝ _ i).comp contDiff_snd

lemma field_hybrid (X : Support n) (U W : Config G n) : hybrid X (matrixField U) (matrixField W) = matrixField (hybrid X U W) := by
  funext i; unfold hybrid matrixField; dsimp only [comp_apply]; split <;> rfl

lemma hybrid_gauge (X : Support n) (U W : Config G n) (t : Site n → G.El) :
    hybrid X (gauge t U) (gauge t W) = gauge t (hybrid X U W) := by
  funext i; simp only [hybrid,Lattice.gauge]; split <;> rfl

/-- Ambient extension of the projection. Selects by tests of site membership;
does not replace a near-threshold configuration by a promised healthy one. -/
def project (X : Support n) (f : Field G n → ℂ) (a : Field G n) := ∫ W, f (hybrid X a (matrixField W)) ∂prior G n

lemma project_smooth (X : Support n) {f : Field G n → ℂ} (h : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (project X f) := by
  haveI : TopologicalSpace.PseudoMetrizableSpace G.Mat := inferInstanceAs
    (TopologicalSpace.PseudoMetrizableSpace (Fin G.repDim → Fin G.repDim → ℂ))
  exact integral_smooth (p:=matrixField) matrixField_cont.aestronglyMeasurable (isCompact_range matrixField_cont)
      (fun _ => Set.mem_range_self _) (h.comp (smooth_hybrid X))

lemma project_univ (f : Field G n → ℂ) : project univ f = f := by
  funext a; simp only [project, show ∀ U, hybrid univ a (matrixField U) = a from fun U => by funext i; simp [hybrid]]
  simp

lemma project_local (X : Support n) (f : Field G n → ℂ) : LocalOn X (project X f ∘ matrixField) := by
  intro U W h
  have he (a : Config G n) : hybrid X (matrixField U) (matrixField a) = hybrid X (matrixField W) (matrixField a) := by
    funext i; unfold hybrid; split
    next hi => exact congrArg G.mat (h i hi.1 hi.2)
    rfl
  simp only [comp_apply, project, he]

lemma project_gauge (X : Support n) {f : Field G n → ℂ} (hf : ContDiff ℝ ∞ f)
    (h : GaugeInvariant (f ∘ matrixField)) : GaugeInvariant (project X f ∘ matrixField) := by
  intro t U
  let Z := gauge t U
  have hc : Continuous fun W => f (hybrid X (matrixField Z) (matrixField W)) :=
    ((hf.comp (smooth_hybrid X)).continuous.comp (continuous_const.prodMk matrixField_cont))
  have hm := Wilson.prior_gauge (n:=n) t
  have he := integral_map (f:=fun W => f (hybrid X (matrixField Z) (matrixField W))) hm.aemeasurable
    (by rw [hm.map_eq]; exact hc.aestronglyMeasurable)
  rw [hm.map_eq] at he
  change project X f (matrixField Z) = _
  simp only [project, comp_apply]; rw [he]; simp only [Z,field_hybrid,hybrid_gauge]
  exact integral_congr_ae (Filter.Eventually.of_forall fun W => h t _)

section Mobius
variable {ι : Type*} [DecidableEq ι] {E : Type*} [Ring E]

def delta (f : Finset ι → E) (s : Finset ι) := ∑ u∈s.powerset,(-1:E)^(s.card - u.card)*f u
lemma delta_insert {s : Finset ι} {i : ι} (hi : i∉s) (f : Finset ι → E) :
    delta f (insert i s) = delta (fun t => f (insert i t)) s - delta f s := by
  rw [delta,sum_powerset_insert hi]; simp_rw [card_insert_of_notMem hi]
  rw [sub_eq_neg_add,delta,delta,← sum_neg_distrib]
  congr 1
  · exact sum_congr rfl fun t ht => by rw [show s.card+1-t.card = (s.card-t.card)+1 by
                                             have := card_le_card (mem_powerset.mp ht); omega, pow_succ]; simp
  · refine sum_congr rfl fun t ht => ?_
    rw [card_insert_of_notMem (fun he => hi ((mem_powerset.mp ht) he)),Nat.add_sub_add_right]

lemma delta_exact (s : Finset ι) (f : Finset ι → E) : ∑ u∈s.powerset,delta f u = f s := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp [delta]
  | insert i s hi ih =>
    rw [sum_powerset_insert hi, show ∑ t∈s.powerset,delta f (insert i t) =
        ∑ t∈s.powerset,(delta (fun t => f (insert i t)) t - delta f t) from
      sum_congr rfl fun t ht => delta_insert (fun he => hi ((mem_powerset.mp ht) he)) f, sum_sub_distrib,ih,ih]; abel
end Mobius

/-- A finite covering menu of test blocks at one scale; overlap permitted. -/
structure Windows (n : Side) where
  blocks : Finset (Support n)
  full : blocks.biUnion id = univ

namespace Windows
variable (B : Windows n) (core : Support n) (f : Field G n → ℂ)
abbrev Piece := ↥B.blocks.powerset

def patch (core : Support n) (T : Finset (Support n)) := core ∪ T.biUnion id

def gain (u : B.Piece) (x : Field G n) := delta (fun T => project (patch core T) f x) u.val

lemma exact_sum (x : Field G n) : ∑ u,B.gain core f u x = f x := by
  unfold gain
  rw [sum_coe_sort,delta_exact,patch,B.full,show core ∪ univ = univ by simp,project_univ]

lemma gain_smooth (u : B.Piece) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (B.gain core f u) :=
    ContDiff.sum fun i _ => contDiff_const.mul (project_smooth (patch core i) hf)

lemma gain_local (u : B.Piece) : LocalOn (patch core u.val) (B.gain core f u ∘ matrixField) := by
  intro U W h
  unfold gain delta
  apply sum_congr rfl
  intro t ht; congr 1
  exact project_local _ f U W (agrees_mono h (coe_subset.mpr (Finset.union_subset_union_right
    (by intro i hi; obtain ⟨s,hs,hx⟩ := mem_biUnion.mp hi; exact mem_biUnion.mpr ⟨_,mem_powerset.mp ht hs,hx⟩))))

lemma gain_gauge (u : B.Piece) (hf : ContDiff ℝ ∞ f) (hg : GaugeInvariant (f ∘ matrixField)) :
    GaugeInvariant (B.gain core f u ∘ matrixField) := by
  intro t U; unfold gain delta; exact sum_congr rfl fun j _ => congrArg (_ * ·) (project_gauge _ hf hg t U)

/-- Simplest test menu (no effective localization by the empty vs whole
choice if the core itself is full). -/
def whole (n : Side) : Windows n := ⟨{univ},by simp⟩
end Windows

variable {V : Type} [Fintype V] [DecidableEq V] (R : Census V)
abbrev Hot := {s : R.Mode // s.val.Nonempty}

variable {N p : ℕ} {H : RG.History G}
namespace Insertions
variable (A : Insertions H V N p) {j : ℕ} (B : Windows (H.S.side j p))
    (atSite : V → Site (H.S.side j p)) (core : V → Support (H.S.side j p))

def fragments : Layers (H.rep N p j) R (Hot R × B.Piece) where
  origins := atSite
  units _ := 0
  tag a := a.1.val
  region a := Windows.patch (a.1.val.val.biUnion core) a.2.val
  H a := B.gain (a.1.val.val.biUnion core) (A.cumulant j a.1.val) a.2 ∘ matrixField

lemma anchored (hc : ∀ i, atSite i ∈ core i) : (A.fragments R B atSite core).Anchored :=
  ⟨fun i => i.1.property,fun _ s hs => mem_union_left _ (mem_biUnion.mpr ⟨s,hs,hc s⟩)⟩

lemma ready (h : A.Symmetric) (hj : j≤N) (hc : ∀ i,atSite i∈core i) : (A.fragments R B atSite core).Ready where
  toAnchored := A.anchored R B atSite core hc
  regular i := regular_matrix _ (B.gain_smooth _ _ i.2 (A.cumulant_smooth hj i.1.val))
    (B.gain_gauge _ _ i.2 (A.cumulant_smooth hj i.1.val) (A.cumulant_gauge h hj i.1.val)) (B.gain_local _ _ i.2)

lemma logPart_eq (hj : j≤N) (U : Config G (H.S.side j p)) :
    (A.fragments R B atSite core).logPart U = Poly.inject fun s => A.cumulant j s (matrixField U) := by
  ext s; change Poly.part ((A.fragments ..).logPart U) s = A.cumulant j s (matrixField U)
  rw [Layers.logPart,Fintype.sum_prod_type,Poly.part_plus,Poly.part_sum]
  dsimp only [fragments]; simp_rw [comp_apply,Poly.send_zero,Poly.part_nil,sum_const_zero,zero_add,Poly.part_sum]
  by_cases he : s.val.Nonempty
  · rw [sum_eq_single (⟨s,he⟩ : Hot R)]
    · simpa only [Poly.part_send,↓reduceIte] using (B.exact_sum ..)
    · intro b _ h; simp [Poly.part_send,show s ≠ b.val from fun e => h (Subtype.ext e.symm)]
    simp
  have hs := show s=R.quiet from Subtype.ext (not_nonempty_iff_eq_empty.mp he)
  rw [hs,A.cumulant_quiet hj]
  exact sum_eq_zero fun b _ => sum_eq_zero fun c _ => by simp [Poly.part_send,show R.quiet ≠ b.val from
      fun e => b.property.ne_empty (congrArg Subtype.val e.symm)]

lemma fragments_exact [Nonempty V] (h : H.Selected) (ho : Aperture (H.rep N p j)) (hc : ∀ i,atSite i∈core i)
    (hj : j≤N) (U : Config G (H.S.side j p)) (s : R.Mode) :
    (((A.fragments R B atSite core).bands).density U).part s = A.total s j (matrixField U) := by
  let X := A.fragments R B atSite core
  rw [X.exact_density ho (A.anchored R B atSite core hc) (h.represents _ _ _ hj).good.labels,A.logPart_eq R B atSite core hj U,
      A.compound_eq hj,Poly.part_smul,A.part_ratios,← vac_eq h hj,comp_apply,Complex.ofReal_inv,mul_left_comm,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (vac_pos hj _).ne'),mul_one]
end Insertions
end YM.Extra.Trajectories

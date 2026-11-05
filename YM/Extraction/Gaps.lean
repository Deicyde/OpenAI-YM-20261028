import Mathlib.MeasureTheory.Group.IntegralConvolution
import YM.Extraction.Orders
import YM.Extraction.Round
import YM.Source.Construction
import YM.TimeKernel.Trace


/-!
# Transport compact distances to native torus directions

No ties includes *any* coordinate when oriented. NoHit includes AT LEAST
one per pair. Prove uniform constants independent of expanding period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction.Gaps
open MeasureTheory Metric Function Filter Set Wilson Lattice
open scoped Topology ContDiff BigOperators
variable (S : Schedule) {n : ℕ}

def distances {n : ℕ} (x : Points n) (i j : Fin n) (b : Axis) : ℝ := x j b-x i b

def off (S : Schedule) (p) (d r : ℝ) := ∀ i : ℤ, r ≤ dist d (i * length S p)

def allFine {n : ℕ} (p : ℕ) (s : ℝ) (x : Points n) := ∀ i j, i≠j → ∀ a,
    off S p (distances x i j a) s

def someFine {n : ℕ} (p : ℕ) (s : ℝ) (x : Points n) := ∀ i j, i≠j → ∃ a,
    off S p (distances x i j a) s

@[fun_prop] lemma ct (i j : Fin n) (a : Axis) : Continuous (fun x : Points n => distances x i j a) := by unfold distances; fun_prop

def fraction {n : ℕ} (p : ℕ) (x : Points n) (i j : Fin n) (a : Axis) :=
    infDist (distances x i j a) (Set.range fun z : ℤ => z* length S p)

@[fun_prop] lemma ct_frac (p) (i j : Fin n) (a) : Continuous (fun x : Points n => fraction S p x i j a) :=
  (continuous_infDist_pt _).comp (ct i j a)

lemma interval (p) (x : Points n) (i j a) : off S p (distances x i j a) (fraction S p x i j a) :=
    fun k => infDist_le_dist_of_mem (mem_range_self k)
lemma fraction_pos (p) (x : Points n) (i j a) : ¬ periodic S p (x j a) (x i a) ↔ 0 < fraction S p x i j a := by
  have he : (Set.range fun i : ℤ => i*length S p).Nonempty := range_nonempty _
  rw [fraction,(periodicClosed S p).notMem_iff_infDist_pos he |>.symm]; unfold periodic distances; simp [eq_comm]

private theorem pick {ι : Type*} [Finite ι] (Q : ι → ℝ → Prop) (h : ∀ i, ∃ r : ℝ, 0<r ∧ Q i r)
    (hp : ∀ i r t, t ≤ r → Q i r → Q i t) : ∃ r : ℝ, 0<r ∧ ∀ i, Q i r := by
  classical
  have ht (F : Finset ι) : ∃ r : ℝ, 0<r ∧ ∀ i∈F,Q i r := by
    induction F using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨r,hr,Hr⟩ := h i
      obtain ⟨t,ht,H⟩ := ih
      refine ⟨min r t, lt_min hr ht, fun j hJ => ?_⟩
      rcases Finset.mem_insert.mp hJ with hx|hx
      · rw [hx]; exact hp i r _ (min_le_left ..) Hr
      exact hp j t _ (min_le_right ..) (H j hx)
  haveI := Fintype.ofFinite ι
  simpa using ht Finset.univ

private abbrev Pair (n : ℕ) := {x : Fin n × Fin n // x.1 ≠ x.2}

lemma some (p : ℕ) {K : Set (Points n)} (h : IsCompact K) (hv : K ⊆ NoHit S p n) :
    ∃ r : ℝ, 0<r ∧ ∀ x ∈ K, someFine S p r x := by
  classical
  rcases K.eq_empty_or_nonempty with hh|hh
  · exact ⟨1,zero_lt_one,by rw [hh];simp⟩
  let g (i : Pair n) x := (Finset.univ : Finset Axis).sup' Finset.univ_nonempty (fraction S p x i.val.1 i.val.2)
  have he (i) (x : Points n) (hx : x ∈ K) : 0<g i x := by
    obtain ⟨a,ha⟩ := hv hx i.val.2 i.val.1 i.property.symm
    exact lt_of_lt_of_le ((fraction_pos S p x _ _ a).1 ha) (Finset.le_sup' (fraction S p x i.val.1 i.val.2) (Finset.mem_univ a))
  have hm i : ∃ r : ℝ, 0<r ∧ ∀ x∈K, r ≤ g i x := by
    obtain ⟨x,hx,H⟩ := h.exists_isMinOn hh
      (show Continuous (g i) from (Continuous.finset_sup'_apply _ fun a _ => ct_frac S p _ _ a)).continuousOn
    exact ⟨g i x,he i x hx, fun x hx => H hx⟩
  obtain ⟨r, hr,H⟩ := pick _ hm fun i r w he hp x hx => he.trans (hp _ hx)
  refine ⟨r,hr,fun x hx i j hJ => ?_⟩
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fraction S p x i j)
  refine ⟨a,fun u => (H (⟨(i,j),hJ⟩) x hx).trans ?_⟩
  unfold g; rw [ha]; exact interval S p x i j a _

lemma all (p : ℕ) {K : Set (Points n)} (h : IsCompact K) (hv : K ⊆ Cyclic S p n) :
    ∃ r : ℝ, 0<r ∧ ∀ x ∈ K, allFine S p r x := by
  classical
  rcases K.eq_empty_or_nonempty with hh|hh
  · exact ⟨1,zero_lt_one,by rw [hh];simp⟩
  let g (i : Pair n × Axis) x := fraction S p x i.1.val.1 i.1.val.2 i.2
  have hm (i) : ∃ r : ℝ, 0<r ∧ ∀ x∈K, r ≤ g i x := by
    obtain ⟨x,hx,H⟩ := h.exists_isMinOn hh
      (show Continuous (g i) from ct_frac S p _ _ _).continuousOn
    exact ⟨g i x, (fraction_pos ..).1 (hv hx _ _ (Ne.symm i.1.property) _), fun _ hx => H hx⟩
  obtain ⟨r, hr,H⟩ := pick _ hm fun i r w he hp x hx => he.trans (hp _ hx)
  exact ⟨r,hr,fun x hx i j hh a q => (H (⟨(i,j),hh⟩,a) x hx).trans (interval S p x i j a q)⟩

lemma expand_equivalent {K : Set (Points n)} (h : IsCompact K) :
    ∀ᶠ p : ℕ in atTop, ∀ x∈K, ∀ i j a, off S p (distances x i j a) |distances x i j a| := by
  have he (i j : Fin n) (a : Axis) : ∀ᶠ p : ℕ in atTop, ∀ x∈K,
      |distances x i j a|≤S.radius p := by
    obtain ⟨D,hD⟩ := (h.image (ct i j a |>.abs)).bddAbove
    filter_upwards [S.radius_diverges.eventually (eventually_ge_atTop D)] with p hp x hx
    exact (hD ⟨x,hx,rfl⟩).trans hp
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (fun j => eventually_all.mpr (he i j)))] with p hp x hx i j a
  let t := distances x i j a
  have hh : |t| ≤ S.radius p := hp i j a x hx
  have hu : length S p=2*S.radius p := by unfold Schedule.radius length; ring
  intro u; change |t| ≤ _
  rw [Real.dist_eq]; change |t| ≤ |t-u*_|
  rcases lt_trichotomy u 0 with e|e|e
  · have hf :(u:ℝ) ≤ -1 := by exact_mod_cast (show u ≤ -1 by omega)
    have hg : (u:ℝ)*length S p ≤ -(2*S.radius p) := by rw [hu]; nlinarith [S.radius_pos p]
    have hw := (abs_le.mp hh).1
    linarith [le_abs_self (t-(u:ℝ)*length S p)]
  · rw [e]; simp
  have hf :(1:ℝ) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
  have hg : 2*S.radius p ≤ (u:ℝ)*length S p := by rw [hu]; nlinarith [S.radius_pos p]
  have hw := (abs_le.mp hh).2
  linarith [neg_le_abs (t-(u:ℝ)*length S p)]

lemma allGrows {K : Set (Points n)} (h : IsCompact K) (hp : K ⊆ generic n) :
    ∃ r : ℝ, 0<r ∧ ∀ᶠ p : ℕ in atTop, ∀ x∈K, allFine S p r x := by
  obtain ⟨p,hp'⟩ := (room S h).exists
  obtain ⟨r,hr,H⟩ := all S p h (fun i hi => (no_wrap_tie S (hp' hi)).2 (hp hi))
  refine ⟨r,hr,?_⟩
  filter_upwards [expand_equivalent S h] with q hq x hx i j hh a u
  have hi := H x hx i j hh a 0
  simp [Real.norm_eq_abs] at hi
  exact hi.trans (hq x hx i j a u)

lemma someGrows {K : Set (Points n)} (h : IsCompact K) (hp : K ⊆ conf n) :
    ∃ r : ℝ, 0<r ∧ ∀ᶠ p : ℕ in atTop, ∀ x∈K, someFine S p r x := by
  obtain ⟨p,hp'⟩ := (room S h).exists
  obtain ⟨r,hr,H⟩ := some S p h (fun i hi => (no_wrap_hit S (hp' hi)).2 (hp hi))
  refine ⟨r,hr,?_⟩
  filter_upwards [expand_equivalent S h] with q hq x hx i j hh
  obtain ⟨a,ha⟩ := H x hx i j hh
  have hi := ha 0; simp [Real.norm_eq_abs] at hi
  exact ⟨a,fun u => hi.trans (hq x hx i j a u)⟩

lemma torus {p N : ℕ} {u : Fin n → Cover} {i j : Fin n} {a : Axis} (y : ℤ) (h : wrap (S.side N p) (u j - u i) a = ((y:ℤ):Per (S.side N p))) {r : ℝ}
    (ht : off S p (distances (tag (S.a N) u) i j a) r) : r ≤ S.a N*|(y:ℝ)| := by
  change ((↑(u j a-u i a : ℤ)) : Per (S.side N p)) = _ at h
  obtain ⟨z,H⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp h
  have hw := ht (-z)
  change r ≤ dist (S.a N*(u j a:ℝ)- S.a N*(u i a:ℝ)) _ at hw
  have hh : (u j a:ℝ) - u i a= y- ((S.side N p).val : ℝ)*z := by
    exact_mod_cast (show u j a-u i a = y- ((S.side N p).val:ℤ)*z by omega)
  rw [← mul_sub,hh,Real.dist_eq, ← show S.a N *((S.side N p).val:ℝ)= length S p from S.span_side N p,Int.cast_neg,
    show _ - -(z:ℝ)*_ = S.a N*y by ring,abs_mul,abs_of_pos (S.a_pos _)] at hw
  exact hw

lemma gridSeparation {p N : ℕ} {u : Fin n → Cover} (x : Fin n → Site (S.side N p)) (h : x = wrap _ ∘ u) {r : ℝ}
    (he : someFine S p r (tag (S.a N) u)) : ∀ i j, i≠j → r ≤ S.a N * separation (x j) (x i) := by
  intro i j hij; obtain ⟨a,ha⟩ := he _ _ hij
  let y : Cover := lift (x j-x i)
  have hp := torus S (y a) (show wrap (S.side N p) (u j-u i) a = wrap (S.side N p) y a by rw [wrap_lift (x j-x i),map_sub,h];rfl) ha
  rw [show |(y a:ℝ)|=(((y a).natAbs:ℕ) : ℝ) by rw [← show (((↑(y a).natAbs:ℤ):ℝ))=_ from Int.cast_natCast _, Int.natCast_natAbs, Int.cast_abs]] at hp
  apply hp.trans (mul_le_mul_of_nonneg_left ?_ (S.a_pos _).le)
  exact_mod_cast (component_le (x j-x i) a)

lemma gridAxis {p N : ℕ} {u : Fin n → Cover} (x : Fin n→Site (S.side N p)) (h : x= wrap _ ∘ u) {r : ℝ}
    (he : allFine S p r (tag (S.a N) u)) : ∀ i j, i≠j → ∀ a, r ≤ S.a N * ((x j a-x i a).val:ℝ) := by
  intro i j hij a
  let y := (x j a-x i a).val
  have hh : wrap (S.side N p) (u j-u i) a = ((y:ℤ):Per (S.side N p)) := by
    unfold y; rw [map_sub,h]
    simp [Per]
  simpa only [Int.cast_natCast,Nat.abs_cast] using torus S (p := p) y hh (he i j hij a)
end YM.Extraction.Gaps

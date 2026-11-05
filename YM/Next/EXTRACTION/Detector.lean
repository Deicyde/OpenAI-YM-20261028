import YM.Next.EXTRACTION.Relay

/-!
# A finite-family gate for the shortage premise of D04

Require quantitative detection on a finite physical family of tests of the
*actual* Wilson family, on the range of the finite cutoff projection. RShort
still has to address proving a bound like this; see  for the
proposed source through weak comparison, not assumed to work. This version
can be asked before we have any chosen limit, or used at a particular
extraction already found to support the estimates -- it mentions *only*
cutoffs and order of quantifiers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Extract
open Function Filter Extraction Dash Set
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {b : Presentation C} {f g : Order} {d : ℕ} {S : Table C.book}

/-- One fixed finite family at d (no bounded weight condition on its
spectators). `snapshots i d (N,p)` uses `Order.smears` on `Shot.record`:
update precisely `Shot.i` with the label of weight d, ordinary products,
against `Wilson.law G (C.side N p) (C.beta N p)` (normalized Wilson measure relative to
product Haar on the cutoff configurations), test `i.f`, mesh volume weight
`(C.S.a N)^(4*i.n)`. Includes tests with no other spectators, distinguished
slot is always present. Test is smooth, compact, supported off coincidences;
uses actual torus positions in the fundamental cell for p (each fixed test
fits eventually in the outer limit). Bound on ordered tails uniformly in v.
`c>0` fixed for these d and f. (Outer period
threshold before the mesh threshold.)
`I` permitted empty (force fixed space zero on these tails). -/
def Detector (b : Presentation C) (f : Order) (d : ℕ) : Prop :=
  ∃ (I : Finset (Shot C.book)) (c : ℝ), 0 < c ∧ f.late fun N p =>
    ∀ v : C.label d, b.step d (N,p) v = v → c * ‖v‖ ≤ ∑ i ∈ I, ‖snapshots i d (N,p) v‖

lemma Tails.detects (h : Tails g f) (H : Detector b f d) : Detector b g d := by
  obtain ⟨I,c,hc,hw⟩ := H
  exact ⟨I,c,hc,h.late hw⟩

/-- Pass the finite lower bound on the varying projected vectors to the
limiting projection, using the actual test limits. -/
theorem detection_limit {R : Bin S} (H : Live S) (ho : f.Ordered C S) (hm : Bin.Matrix R d f)
    (hc : b.step d = (R d).step) {I : Finset (Shot C.book)} {c : ℝ}
    (ht : f.late fun N p => ∀ v : C.label d, b.step d (N,p) v = v → c * ‖v‖ ≤ ∑ i ∈ I, ‖snapshots i d (N,p) v‖)
    (x : C.label d) (hx : (R d).trueP x = x) : c * ‖x‖ ≤ ∑ i ∈ I, ‖i.core (d:=d) S H x‖ := by
  let v (u : ℕ × ℕ) := b.step d u x
  have hv : Tendsto v f.fuse (𝓝 x) := by
    have hh : Tendsto (b.step d) f.fuse (𝓝 (R d).trueP) := by rw [hc]; exact hm
    have he := Dash.arcing hh (tendsto_const_nhds (x := x))
    rwa [hx] at he
  have hl (i : Shot C.book) : Tendsto (fun u : ℕ×ℕ => snapshots i d u (v u)) f.fuse (𝓝 (i.core S H x)) :=
    Dash.arcing (i.ready H ho d) hv
  apply le_of_tendsto_of_tendsto (hv.norm.const_mul c) (tendsto_finsetSum I fun i _ => (hl i).norm)
  change ∀ᶠ u in f.fuse, c * ‖v u‖ ≤ ∑ i ∈ I, ‖snapshots i d u (v u)‖
  rw [Order.fused]
  unfold Order.late at *
  filter_upwards [ht] with k hk
  filter_upwards [hk] with j hj
  exact hj _ (b.projected d _ _)

/-- D04's shortage dimension inequality from a finite Wilson test
estimate and projection convergence. Does not require the upper-rank part
to use this estimate. -/
theorem shortage_of_detector {R : Bin S} (H : Live S) (ho : f.Ordered C S) (hm : Bin.Matrix R d f)
    (hc : b.step d = (R d).step) (h : Detector b f d) : Bin.shortage R H d := by
  let m := monitor S H d
  let p : C.label d →ₗ[ℂ] C.label d := (R d).trueP.toLinearMap
  have he (x : C.label d) (hx : x ∈ m) (hp : p x = x) : x = 0 := by
    obtain ⟨I,c,hc',hh⟩ := h
    have hi := detection_limit H ho hm hc hh x hp
    have hz (i : Shot C.book) : i.core (d:=d) S H x = 0 :=
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hx i)
    simp_rw [hz,norm_zero,Finset.sum_const_zero] at hi
    by_contra hne
    exact (mul_pos hc' (norm_pos_iff.mpr hne)).not_ge hi
  -- monitor injects into the kernel by projection along p
  let a : m →ₗ[ℂ] C.label d := (LinearMap.id - p).comp m.subtype
  let w : m →ₗ[ℂ] LinearMap.ker p := a.codRestrict _ fun x => by
    apply LinearMap.mem_ker.mpr
    change p ((x : C.label d) - p (x : C.label d)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr ((R d).final _).symm
  have H0 (x : m) (hx : w x = 0) : x = 0 := by
    have h0 : (x : C.label d) - p (x : C.label d) = 0 := congr_arg Subtype.val hx
    exact Subtype.ext (he x x.property (sub_eq_zero.mp h0).symm)
  have hw : Injective w := by
    intro x y hxy
    exact sub_eq_zero.mp (H0 _ (by rw [map_sub,hxy,sub_self]))
  exact LinearMap.finrank_le_finrank_of_injective hw

/-!
The Detector input is also precise if called later: once upper comparison
and rank succeed for an extraction, fixed finite detectors with uniform
quantitative lower bound are *provable* on that extraction. Thus it isn't
some extra completeness conjecture about the ranks. Of course we do not
appeal circularly to this direction in the construction.
-/

/-- A finite subfamily bound on a finite-dimensional level over ℂ. -/
lemma finite_detectors {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (p : V →L[ℂ] V) (A : ι → V →L[ℂ] ℂ) (H : ∀ x : V, p x = x → (∀ i, A i x = 0) → x = 0) :
    ∃ (I : Finset ι) (c : ℝ), 0 < c ∧ ∀ x : V, c * ‖x‖ ≤ ‖p x-x‖ + ∑ i ∈ I, ‖A i x‖ := by
  classical
  let K : Set V := Metric.sphere 0 1
  have hk : IsCompact K := isCompact_sphere ..
  let b (I : Finset ι) (x : V) := ‖p x-x‖ + ∑ i ∈ I, ‖A i x‖
  have hc I : Continuous (b I) := by unfold b; fun_prop
  let u (I : Finset ι) : Set V := {x | 0 < b I x}
  have ho I : IsOpen (u I) := isOpen_lt continuous_const (hc I)
  have hh : K ⊆ ⋃ I, u I := by
    intro x hx
    have ht : ‖x‖ = 1 := by simpa [K,Metric.sphere] using hx
    have hx : x ≠ 0 := fun e => one_ne_zero (ht.symm.trans (by rw [e,norm_zero]))
    apply mem_iUnion.mpr
    by_cases he : p x = x
    · have hm : ∃ i, A i x ≠ 0 := not_forall.mp (fun w => hx (H x he w))
      obtain ⟨i,hi⟩ := hm
      exact ⟨{i},by simp [u,b, he, norm_pos_iff,hi]⟩
    exact ⟨∅,by simp [u,b,norm_pos_iff, sub_ne_zero.mpr he]⟩
  obtain ⟨F,hF⟩ := hk.elim_finite_subcover u ho hh
  let I := F.biUnion id
  have ht : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ b I x := by
    by_cases he : K.Nonempty
    · obtain ⟨x,hx,h0⟩ := hk.exists_isMinOn he (hc I).continuousOn
      obtain ⟨J,hJ⟩ := mem_iUnion.mp (hF hx)
      obtain ⟨hp,hp'⟩ := mem_iUnion.mp hJ
      refine ⟨b I x,lt_of_lt_of_le hp' ?_,fun _ hw => h0 hw⟩
      refine add_le_add_right ?_ _
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => Finset.mem_biUnion.mpr ⟨J,hp,hi⟩) (fun _ _ _ => norm_nonneg _)
    exact ⟨1,one_pos,fun x hx => (he ⟨x,hx⟩).elim⟩
  obtain ⟨c,hc,hu⟩ := ht
  refine ⟨I,c,hc,fun x => ?_⟩
  by_cases he : x = 0
  · subst x; simp
  have hq := norm_pos_iff.mpr he
  let l := (‖x‖⁻¹ : ℝ)
  have hv : ‖(l:ℂ)‖ = l := Complex.norm_real _ |>.trans (Real.norm_of_nonneg (inv_pos_of_pos hq).le)
  have hd : (l:ℂ) • x ∈ K := by
    suffices ‖(l:ℂ) • x‖ = 1 from (by simpa [K,Metric.sphere] using this)
    rw [norm_smul,hv]
    exact inv_mul_cancel₀ hq.ne'
  have hi := hu ((l:ℂ) • x) hd
  have hb : b I ((l:ℂ) • x) = l * b I x := by
    simp only [b,map_smul,← smul_sub,norm_smul,hv,mul_add,Finset.mul_sum]
  rw [hb, mul_comm, ← div_eq_mul_inv] at hi
  exact (le_div_iff₀ hq).mp hi

/-- With the projection data and actual kernels converging, `Good`
identification implies the finite quantitative bound at cutoffs. -/
theorem detector_of_good {R : Bin S} (H : Live S) (ho : f.Ordered C S) (hm : Bin.Matrix R d f)
    (hc : b.step d = (R d).step) (he : Bin.Good R H d) : Detector b f d := by
  let q := (R d).trueP
  let B (i : Shot C.book) := i.core (d:=d) S H
  obtain ⟨I,c,hc',ht⟩ := finite_detectors q B (fun x hx h => by
    have hv : x ∈ monitor S H d := (Submodule.mem_iInf _).2 fun i => LinearMap.mem_ker.mpr (h i)
    have hw : x ∈ LinearMap.ker q.toLinearMap := he.symm ▸ hv
    exact hx.symm.trans (LinearMap.mem_ker.mp hw))
  let p := b.step d
  let A (i : Shot C.book) (u : ℕ×ℕ) := snapshots i d u
  have hg : Tendsto p f.fuse (𝓝 q) := by rwa [show p = (R d).step from hc]
  let E (u : ℕ×ℕ) := ‖q - p u‖ + ∑ i ∈ I, ‖B i - A i u‖
  have hv : Tendsto E f.fuse (𝓝 0) := by
    have hr : Tendsto (fun u => ‖q - p u‖) f.fuse (𝓝 0) := by
      simpa only [sub_self,norm_zero] using (tendsto_const_nhds (x := q) |>.sub hg).norm
    have hb i : Tendsto (fun u => ‖B i - A i u‖) f.fuse (𝓝 0) := by
      have ht : Tendsto (A i) f.fuse (𝓝 (B i)) := i.ready H ho d
      simpa only [sub_self,norm_zero] using (tendsto_const_nhds (x := B i) |>.sub ht).norm
    simpa only [Finset.sum_const_zero,add_zero] using hr.add (tendsto_finsetSum I fun i _ => hb i)
  refine ⟨I,c/2,half_pos hc',(f.fused (fun u => ∀ v : C.label d, p u v = v →
    c/2*‖v‖ ≤ ∑ i ∈ I, ‖A i u v‖)).mp ?_⟩
  filter_upwards [hv.eventually (gt_mem_nhds (half_pos hc'))] with u hu v hfix
  have hs : c * ‖v‖ ≤ E u * ‖v‖ + ∑ i ∈ I, ‖A i u v‖ := by
    refine le_trans (ht v) ?_
    have he : ‖q v-v‖ ≤ ‖q-p u‖ * ‖v‖ := by
      simpa only [sub_apply,hfix] using (q - p u).le_opNorm v
    have hb i : ‖B i v‖ ≤ ‖B i-A i u‖ * ‖v‖ + ‖A i u v‖ := calc
      ‖B i v‖ = ‖(B i-A i u) v + A i u v‖ := by rw [sub_apply,sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add_left ((B i-A i u).le_opNorm v) _
    have hl := add_le_add he (Finset.sum_le_sum (s := I) fun i _ => hb i)
    dsimp only [E]
    rw [add_mul, Finset.sum_mul,add_assoc]
    simpa only [Finset.sum_add_distrib] using hl
  have hE : E u * ‖v‖ ≤ c/2 * ‖v‖ := mul_le_mul_of_nonneg_right (show E u < c/2 from hu).le (norm_nonneg v)
  linarith


end YM.Next.Extract

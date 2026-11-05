import YM.Bid.Drops
import YM.Next.FOUNDATIONS.JetReads
import YM.Org.Theatre
import YM.Work.G01
import YM.Work.G02
import YM.Work.G05.Taylor

/-!
# The curvature-jet projection exists on B70 Regular coefficients

Compute jets at **this** gauge group's genuine exp chart and actual test
holonomies. Finite Taylor expansion in the Snap space, then weighted
truncation. We spell out that this recovers exactly the labels evaluated
with the h test; invariance of the projected polynomial is from invariance
of the field (prior to any continuum limits). Thus the actual sections of
Primary have the readout that later, *finite-history*, consumers can use –
not just an abstract derivative or linearized plaquette comparison.

Quantitative estimates on
it (still local at the anchors, independent of any future block step) are
separate below this.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Foundations
open Lattice Wilson RG Source Source.Drops Labels Work
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge} {d : ℕ} {n : Side}

lemma one_healthy (X : Support n) (θ : ℝ) (h : 0 ≤ θ) :
    Healthy θ X (1 : Config G n) := by
  apply Finset.disjoint_left.mpr
  intro x _ he
  obtain ⟨p, -, hp⟩ := (flags_spec ..).mp he
  rw [show faceValue (1 : Config G n) p = 1 by simp [faceValue, square, travel],
    G.chord_one] at hp
  exact h.not_gt hp

lemma test_scaled (H : Hol G) (o : Site n) (J : Jet G) (t : ℝ) :
    H.testLinks d o J t = H.testLinks d o (expand d (trunk d (scaleJet J t))) 1 := by
  funext l
  exact congr_fun (scales H J t) (lift (l.1-o),l.2)

lemma test_one (H : Hol G) (o : Site n) (J : Jet G) :
    H.testLinks d o J 0 = 1 := funext fun _ => congr_fun (H.flat d J) _

lemma test_colored (H : Hol G) (o : Site n) (u : G.El) (J : Jet G) (h : ℝ) :
    H.testLinks d o (colored u J) h = gauge (fun _ => u) (H.testLinks d o J h) := by
  funext l
  exact congr_fun (G01.links_colored H d u J h) (lift (l.1-o),l.2)

section Germ
open Filter Function

private def atSnap (H : Hol G) (o : Site n) (X : Snap G d) := H.testLinks d o (expand d X) 1

private lemma snap_analytic (H : Hol G) (o : Site n) (l : Edge (Site n)) :
    AnalyticAt ℝ (fun X : Snap G d => G.mat (atSnap H o X l)) 0 ∧
      atSnap H o (0 : Snap G d) l = 1 :=
  let h := G02.linkGerm H d (lift (l.1-o),l.2)
  ⟨h.1, h.2.1⟩

private def logSnap (H : Hol G) (o : Site n) (X : Snap G d) : Directions G n := fun l =>
  G.plog (G.mat (atSnap H o X l))

private lemma logSnap_analytic (H : Hol G) (o : Site n) :
    ContDiffAt ℝ ω (logSnap H o : Snap G d → Directions G n) 0 := by
  refine contDiffAt_pi.mpr fun i => ?_
  have he := snap_analytic (d:=d) H o i
  exact (show ContDiffAt ℝ ω G.plog (G.mat (atSnap H o (0 : Snap G d) i)) by
    rw [he.2, G.mat_one]; exact G.plog_diff).comp (0 : Snap G d) he.1.contDiffAt

private lemma snap_def (H : Hol G) (o : Site n) :
    atSnap H o =ᶠ[𝓝 (0 : Snap G d)] increment 1 ∘ logSnap H o := by
  suffices hh : ∀ i : Edge (Site n), ∀ᶠ X in 𝓝 (0 : Snap G d),
      atSnap H o X i = increment 1 (logSnap H o X) i by
    filter_upwards [eventually_all.mpr hh] with X hX
    exact funext hX
  intro i
  have he := snap_analytic (d:=d) H o i
  have hl : ContinuousAt (fun X : Snap G d => atSnap H o X i) 0 :=
    (G.continuous_mat.isClosedEmbedding G.mat_injective).isInducing.continuousAt_iff.mpr he.1.continuousAt
  have ht : Tendsto (fun X : Snap G d => atSnap H o X i) (𝓝 0) (𝓝 1) := by
    rw [← he.2]; exact hl.tendsto
  filter_upwards [ht.eventually G.plog_right] with X hX
  change _ = G.lieExp (G.plog (G.mat (atSnap H o X i))) * 1
  rw [mul_one]
  exact hX.symm

private lemma trunk_scale (J : Jet G) (d : ℕ) : ContDiff ℝ ω (fun t => trunk d (scaleJet J t)) := by
  refine contDiff_pi.mpr fun i => ?_
  have he {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) (c : F) :
      ContDiff ℝ ω (fun t : ℝ => t^j • c) := (contDiff_id.pow j).smul contDiff_const
  exact he (i.val+2) (J i.val)

private lemma trunk_zero (J : Jet G) (d : ℕ) : trunk d (scaleJet J 0) = 0 := by
  funext l; simp [trunk, scaleJet]

/-- The test log (only near h=0 will this be used). No common analytic radius
as a function of the torus size is being promised. -/
def testLog (H : Hol G) (d : ℕ) (o : Site n) (J : Jet G) (h : ℝ) : Directions G n := fun e =>
  G.plog (G.mat (H.testLinks d o J h e))

private lemma testLog_def (H : Hol G) (d : ℕ) (o : Site n) (J : Jet G) (h : ℝ) :
    testLog H d o J h = logSnap H o (trunk d (scaleJet J h)) := by
  unfold testLog; rw [test_scaled]; rfl

lemma testLog_diff (H : Hol G) (d : ℕ) (o : Site n) (J : Jet G) :
    ContDiffAt ℝ ω (testLog H d o J) 0 := by
  rw [funext (testLog_def H d o J)]
  exact (show ContDiffAt ℝ ω (logSnap H o) (trunk d (scaleJet J 0)) by
    rw [trunk_zero]; exact logSnap_analytic H o).comp 0 (trunk_scale J d).contDiffAt

lemma testLog_zero (H : Hol G) (d : ℕ) (o : Site n) (J : Jet G) : testLog H d o J 0 = 0 := by
  funext i; simp [testLog, test_one]

lemma increment_testLog (H : Hol G) (d : ℕ) (o : Site n) (J : Jet G) :
    H.testLinks d o J =ᶠ[𝓝 0] increment 1 ∘ testLog H d o J := by
  have he : Tendsto (fun t => trunk d (scaleJet J t)) (𝓝 0) (𝓝 0) := by
    rw [← trunk_zero J]; exact (trunk_scale J d).continuous.tendsto _
  filter_upwards [he.eventually (snap_def (d:=d) H o)] with x hx
  rw [test_scaled, comp_apply, testLog_def]
  exact hx

end Germ

section Taylor
open Function

private theorem slot_polynomial {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (X : Jet G → E) (V : ι → E)
    (L : ι → Key G) (r : Jet G → ι → ℝ) (hr : ∀ J i, (r J i : ℂ) = coord J (L i))
    (ht : ∀ J, X J = ∑ i, r J i • V i) (m : ℕ) (A : Tensor.T E ℂ m) :
    ∃ p : Pol G, ∀ J : Jet G, read J p = Tensor.diagonal A (X J) := by
  classical
  induction m with
  | zero =>
    refine ⟨MvPolynomial.C (Tensor.diagonal A 0), fun J => ?_⟩
    simp only [Labels.read, MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
    exact congr_arg A (Subsingleton.elim ..)
  | succ m ih =>
    choose p hp using fun i : ι => ih (A.curryLeft (V i))
    refine ⟨∑ i, MvPolynomial.X (L i) * p i, fun J => ?_⟩
    have he (x : E) : Tensor.diagonal A x = Tensor.diagonal (A.curryLeft x) x := by
      apply congr_arg A
      ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have hv : A.curryLeft (X J) = ∑ i, r J i • A.curryLeft (V i) := by rw [ht, map_sum]; simp
    rw [he, hv, Tensor.diagonal, _root_.map_sum, sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, hp, Labels.read, MvPolynomial.aeval_X, smul_apply, Complex.real_smul, hr]
    rfl

/-- Diagonal polynomial in the real (underlying) radial jet. Compare
`G05.diagonal_polynomial` for the other direction's space of samples. -/
private theorem snap_polynomial (m : ℕ) (A : Tensor.T (Snap G d) ℂ m) :
    ∃ p : Pol G, ∀ J : Jet G, read J p = Tensor.diagonal A (trunk d J) := by
  classical
  let I := (i : Fin (d-1)) × Fin (dim G i.val)
  let V (i : I) : Snap G d := Pi.single i.1 (axes G i.1.val i.2)
  let r (J : Jet G) (k : I) := ((axes G k.1.val).repr (J k.1.val)) k.2
  refine slot_polynomial (trunk d) V (fun i => ⟨i.1.val,i.2⟩) r (fun _ _ => rfl) ?_ m A
  intro J
  symm
  funext j
  rw [Fintype.sum_sigma, Finset.sum_apply, Finset.sum_eq_single j]
  · simp only [Finset.sum_apply, Pi.smul_apply, V, Pi.single_eq_same]
    exact (axes G j.val).sum_repr (J j.val)
  · intro i _ hij; simp [Finset.sum_apply, V, Pi.single_eq_of_ne (Ne.symm hij)]
  · simp

private theorem raw_readout (H : Hol G) (f : Config G n → ℂ) (o : Site n) (d : ℕ)
    (hf : ContDiffAt ℝ (d : WithTop ℕ∞) (f ∘ increment 1) 0) :
    ∃ p : Pol G, p ∈ limited G d ∧ ∀ J : Jet G,
      ContDiffAt ℝ (d : WithTop ℕ∞) (f ∘ H.testLinks d o J) 0 ∧
      ∀ k ≤ d, iteratedDeriv k (f ∘ H.testLinks d o J) 0 =
        iteratedDeriv k (fun h => read (scaleJet J h) p) 0 := by
  let F : Snap G d → ℂ := f ∘ atSnap H o
  have hx : logSnap H o (0 : Snap G d) = 0 := funext fun i => by
    unfold logSnap
    rw [(snap_analytic H o i).2, G.mat_one, G.plog_one]
    rfl
  have hs : ContDiffAt ℝ d F 0 := by
    have hQ : ContDiffAt ℝ d ((f ∘ increment 1) ∘ logSnap H o) (0 : Snap G d) :=
      (hx.symm ▸ hf).comp _ ((logSnap_analytic H o).of_le le_top)
    refine hQ.congr_of_eventuallyEq ?_
    filter_upwards [snap_def (d:=d) H o] with x he
    exact congr_arg f he
  let T := G05.blockTaylor d F
  choose P hP using fun k : ℕ => snap_polynomial k (Tensor.coeff F k 0)
  let p₀ := ∑ k ∈ Finset.range (d+1), P k
  have hT (J : Jet G) : read J p₀ = T (trunk d J) := by
    unfold T p₀ G05.blockTaylor
    rw [_root_.map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hP i J
  refine ⟨capRead d p₀, cap_limited .., fun J => ?_⟩
  let r (t : ℝ) := trunk d (scaleJet J t)
  have hr : r 0 = 0 := trunk_zero J d
  have hd : ContDiffAt ℝ d r 0 := ((trunk_scale J d).contDiffAt).of_le le_top
  have hs' : ContDiffAt ℝ d F (r 0) := by rw [hr]; exact hs
  have he : f ∘ H.testLinks d o J = F ∘ r := by
    funext i; rw [comp_apply, test_scaled]; rfl
  rw [he]; refine ⟨hs'.comp 0 hd, fun k hk => ?_⟩
  have hy : iteratedFDeriv ℝ k (F ∘ r) 0 = iteratedFDeriv ℝ k (T ∘ r) 0 :=
    G05.jets_comp hd hd hs' (G05.blockTaylor_contDiff d F _).contDiffAt rfl (fun _ _ => rfl)
      (fun l hl => by rw [hr]; exact (G05.blockTaylor_jets hs _ hl).symm) k hk
  calc
    iteratedDeriv k (F ∘ r) 0 = iteratedDeriv k (T ∘ r) 0 := by unfold iteratedDeriv; rw [hy]
    _ = iteratedDeriv k (fun x => read (scaleJet J x) p₀) 0 := by rw [funext fun x => hT (scaleJet J x)]; rfl
    _ = iteratedDeriv k (fun h => read (scaleJet J h) (capRead d p₀)) 0 := by
      rw [deriv_read, deriv_read, tier_capRead d p₀ k hk]

/-- Even at small order and trivial Snap. As with `JetTest`, interpret
physically on supports where the formula is to be used, i.e., with the
nonwrapping/locality conditions. -/
theorem read_projection (H : Hol G) (o : Site n) (d : ℕ) (f : Config G n → ℂ)
    (he : GaugeInvariant f) (hf : ContDiffAt ℝ (d : WithTop ℕ∞) (f ∘ increment 1) 0) :
    ∃! p : Label G d, JetTest H o p f := by
  obtain ⟨p, hp, hh⟩ := raw_readout H f o d hf
  have hu (J : Jet G) (g : G.El) : read (colored g J) p = read J p := by
    have hk (k : ℕ) (hk : k ≤ d) : read (colored g J) (tier k p) = read J (tier k p) := by
      have hs : f ∘ H.testLinks d o (colored g J) = f ∘ H.testLinks d o J := by
        funext v; simp only [Function.comp_apply, test_colored]; exact he _ _
      have hb := (hh (colored g J)).2 k hk
      rw [hs, (hh J).2 k hk, deriv_read, deriv_read] at hb
      exact smul_right_injective ℂ (show (k.factorial : ℝ) ≠ 0 by positivity) hb.symm
    rw [← limited_cap d p hp, capRead, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i hi => hk i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  let x : Label G d := ⟨p,hp,hu⟩
  have hX : JetTest H o x f := fun J => ⟨(hh J).1, (read_smooth J _ _).contDiffAt, (hh J).2⟩
  exact ⟨x,hX,fun _ Hy => JetTest.unique Hy hX⟩

/-- Includes the constant-only (wrapping) convention. This is the
projection from finite-order `Regular`. No extra analyticity/direction-
budget assumed on f. -/
theorem exists_read (H : Hol G) (d : ℕ) (o : Site n) (B : BudgetPoint) {X : Support n}
    {f : Config G n → ℂ} (h : d ≤ B.order) (hf : B.Regular X f) :
    ∃! p : Label G d, Reads H o X p f := by
  classical
  by_cases hX : Nonwrapping X o
  · have hs : ContDiffAt ℝ (d : WithTop ℕ∞) (f ∘ increment 1) 0 :=
      (hf.smooth 1 (one_healthy X _ B.threshold_pos.le)).of_le
        (show (d : WithTop ℕ∞) ≤ (B.order : WithTop ℕ∞) from Nat.cast_le.mpr h)
    simpa only [Reads, if_pos hX] using read_projection H o d f hf.symmetry hs
  simp [Reads, hX, existsUnique_eq]

end Taylor
end YM.Next.Foundations

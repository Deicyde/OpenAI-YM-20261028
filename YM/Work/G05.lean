import YM.Work.G05.Pose

/-!
# G05: real invariant slot polynomials with lower degrees retained

Approximate the *shared recovery map* by its d-jet, then substitute in
all labels. Thus needn't cut terms out of the resulting polynomials (they
may have degree > d). They see ordinary real Snap values, even away from 0,
and have the literal slot-degree lower bounds in `lows`. The approximation
is for taking derivatives through d after the scaled radial substitution;
we never identify a nonlinear stencil value with a label at finite h.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.G05
open Function Filter Bid Labels Source Drops Lattice Wilson RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {m d : ℕ}

/-- Color acts linearly so the Taylor approximation respects it as well. -/
theorem Cast_blockTaylor {f : GaugePanel G m → Snap G d} (hf : ContDiffAt ℝ d f 0) (u : G.El)
    (h : ∀ᶠ x in 𝓝 0, f (rotates u x) = Cast u (f x)) (x : GaugePanel G m) :
    blockTaylor d f (rotates u x) = Cast u (blockTaylor d f x) := by
  let L : GaugePanel G m →L[ℝ] GaugePanel G m :=
    { toFun := rotates u
      map_add' := fun _ _ => funext fun _ => map_add (G.adjoint u) _ _
      map_smul' := fun _ _ => funext fun _ => map_smul (G.adjoint u) _ _
      cont := rotates_cont }
  let R : Snap G d →L[ℝ] Snap G d :=
    { toFun := Cast u
      map_add' := fun _ _ => funext fun _ => map_add (Taylor.paint u) _ _
      map_smul' := fun _ _ => funext fun _ => map_smul (Taylor.paint u) _ _
      cont := Cast_cont }
  exact blockTaylor_equivariant hf L R h x

theorem snap_read_smooth (d : ℕ) (v : Pol G) (k : WithTop ℕ∞) :
    ContDiff ℝ k (fun A : Snap G d => read (expand d A) v) := by
  induction v using MvPolynomial.induction_on with
  | C a => simp only [Labels.read, MvPolynomial.aeval_C]; exact contDiff_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, Labels.read, MvPolynomial.aeval_X, ← snapCoord_eq]
    exact hp.mul (snapCoord d i).contDiff

theorem recovery_projects {H : Hol G} {B : Fin m → Slot} {f : GaugePanel G m → Snap G d}
    (hf : ContDiffAt ℝ d f 0) (he : ∀ᶠ x in 𝓝 0, f (bring H d B x) = x) (hp : Peg H d)
    (v : Label G d) (p : Pose G m)
    (hv : ∀ x, lumin p x = read (expand d (blockTaylor d f x)) v.val) :
    Projects H v (lumin p ∘ mapped B) := by
  intro J
  -- A is the truncated Snap of the newly scaled Jet at EACH parameter h.
  let A (h : ℝ) := trunk d (scaleJet J h)
  let W := bring H d B ∘ A
  let R (x : Snap G d) := read (expand d x) v.val
  have hA : ContDiffAt ℝ (d : WithTop ℕ∞) A 0 := by
    have T {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) (c : F) :
        ContDiffAt ℝ d (fun x : ℝ => x^j • c) 0 := ContDiffAt.smul (contDiffAt_id.pow _) contDiffAt_const
    apply contDiffAt_pi.mpr; intro i
    exact T (i.val+2) (J i.val)
  have h0 : A 0 = 0 := by funext i; simp [A,trunk,scaleJet]
  have hr : ContDiff ℝ (d : WithTop ℕ∞) R := snap_read_smooth ..
  have hW : ContDiffAt ℝ (d : WithTop ℕ∞) W 0 := by
    have hb : ContDiffAt ℝ (d : WithTop ℕ∞) (bring H d B) (A 0) := by
      rw [h0]; apply contDiffAt_pi.mpr
      intro i; exact ((hp.shot (B i)).contDiffAt).of_le le_top
    exact hb.comp 0 hA
  have hz : W 0 = 0 := by
    rw [show W 0 = bring H d B (A 0) from rfl, h0]; exact funext fun i => takes_zero ..
  have hw (x) : mapped B (H.links d J x) = W x := by rw [Drops.scales H]; rfl
  -- Work locally, in parameter space, not asserting smoothness of links as
  -- one huge ambient configuration map.
  change ContDiffAt ℝ (d : WithTop ℕ∞) (fun x => lumin p (mapped B (H.links d J x))) 0 ∧ _
  have hleft : (fun x => (lumin p ∘ mapped B) (H.links d J x)) = R ∘ (blockTaylor d f ∘ W) := by
    funext x
    change lumin p (mapped B (H.links d J x)) = _
    rw [hw]; exact hv (W x)
  have hright : (fun x => read (scaleJet J x) v.val) = R ∘ A := funext fun x => (racts v _).symm
  have hc : ContDiffAt ℝ (d : WithTop ℕ∞) (blockTaylor d f ∘ W) 0 :=
    (blockTaylor_contDiff d f _).comp_contDiffAt 0 hW
  have ht : Tendsto A (𝓝 0) (𝓝 0) := by simpa only [h0] using hA.continuousAt.tendsto
  have hg : f ∘ W =ᶠ[𝓝 0] A := ht.eventually he
  have hj : ∀ k ≤ d, iteratedFDeriv ℝ k (blockTaylor d f ∘ W) 0 = iteratedFDeriv ℝ k A 0 := by
    intro k hk
    refine Eq.trans (b := iteratedFDeriv ℝ k (f ∘ W) 0) ?_ ((hg.iteratedFDeriv ℝ k).eq_of_nhds)
    refine jets_comp hW hW (blockTaylor_contDiff d f _).contDiffAt ?_ rfl (fun _ _ => rfl) ?_ k hk
    · rw [hz]; exact hf
    · rw [hz]; exact blockTaylor_jets hf
  have hi : (blockTaylor d f ∘ W) 0 = A 0 := by
    simp only [comp_apply, hz, blockTaylor_zero]
    have hu := hg.eq_of_nhds
    rwa [comp_apply,hz] at hu
  refine ⟨?_,?_,fun k hk => ?_⟩
  · change ContDiffAt _ _ (fun x => (lumin p ∘ mapped B) (H.links d J x)) 0
    rw [hleft]; exact hr.comp_contDiffAt 0 hc
  · rw [hright]; exact hr.comp_contDiffAt 0 hA
  · rw [hleft,hright]
    unfold iteratedDeriv
    rw [jets_comp hc hA hr.contDiffAt hr.contDiffAt hi hj (fun _ _ => rfl) k hk]

/-- Evaluate the polynomial substitution on a panel as honest real Snap-jet
substitution into the multivariate (complex) label polynomial. -/
theorem substituted {P : Key G → Pose G m} (x : GaugePanel G m) (J : Jet G)
    (h : ∀ i, lumin (P i) x = coord J i) (v : Pol G) :
    lumin (MvPolynomial.aeval P v) x = read J v := by
  let L : Pose G m →ₐ[ℂ] ℂ := MvPolynomial.aeval fun i : Fin m × G.ColorIndex =>
    ((x i.1 i.2 : ℝ) : ℂ)
  have he : L.comp (MvPolynomial.aeval P) = read J := by
    ext i; rw [AlgHom.comp_apply,MvPolynomial.aeval_X,Labels.read,MvPolynomial.aeval_X]; exact h i
  exact DFunLike.congr_fun he v

theorem answer : YM.Bid.G05 := by
  intro G H d F m B hp f h
  obtain ⟨he, hz, hi, hr⟩ := h
  letI : CompleteSpace (Snap G d) := FiniteDimensional.complete ℝ _
  have hf : ContDiffAt ℝ d f 0 := he.contDiffAt.of_le le_top
  choose Q hQ using fun j : Key G => block_polynomial f j
  let P (i : F.Index) := MvPolynomial.aeval Q (F.basis i).val
  have hP (i x) : lumin (P i) x = read (expand d (blockTaylor d f x)) (F.basis i).val :=
    substituted x (expand d (blockTaylor d f x)) (fun j => hQ j x) _
  refine ⟨P, ?_, ?_, ?_, (fun i => recovery_projects hf hi hp _ _ (hP i)), fun i => ?_⟩
  · unfold P; rw [F.starts_unit]; exact map_one _
  · intro i u x
    rw [hP, hP, Cast_blockTaylor hf u (hr u)]
    have ht (y : Snap G d) : expand d (Cast u y) = colored u (expand d y) := by
      funext j
      by_cases hj : j < d-1 <;> simp [expand, colored, Cast, hj]
    rw [ht]; exact (F.basis i).property.2 _ u
  · intro i x
    have hw : conjPol (F.basis i).val = (F.basis i).val :=
      congr_arg (fun v : Label G d => v.val) (F.realForm i)
    rw [hP, ← conj_value, hw]
  apply lows_substitute
  · intro j; apply lows_of_zero
    rw [hQ, blockTaylor_zero, hz, expand_zero]; simp [coord]
  intro a ha
  have hq := ((pure_grade _ (F.basis i)).mp (F.pure i)) (MvPolynomial.mem_support_iff.mp ha)
  rw [weight_slot] at hq; exact congr_arg Prod.snd hq.symm

end YM.Work.G05

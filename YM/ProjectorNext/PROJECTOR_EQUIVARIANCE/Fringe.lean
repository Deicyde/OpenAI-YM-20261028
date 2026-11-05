import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Anchors
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Hues
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Line
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Matrices
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Move


/-!
# Relaxed transfer-action gate: just price the short regular addresses!

When only the **wrapping** remainder operations are known termwise
covariant. Sometimes easier than replay of labels on every short-support
part (e.g. proving naturality through local projections when some linear
representations used different short addresses). State the relaxed input,
still at the physical operations, and get the same x identity using the
actual `Format` plus `remBound`. No loss even for infinitely many short
addresses.  matters: cannot infer wrapping addresses are annihilated
by the projection similarly!
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Labels Lattice Wilson RG Source Analysis MeasureTheory Next.Foundations Push.CutoffProjectors
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d}
    {Q T : Coefficient F n} {R : Rep G n} {o : Site n} {H : Hol G}

/-- Untested for termwise covariance at this gate. -/
def short (Q : Coefficient F n) (o : Site n) (i : ℕ) := Nonwrapping (Q.support i) o ∨ Q.regular i = 0

/-- Can omit `along` comparison entirely at short regular supports, even
with different decompositions. But where either term is long and nonzero,
pay the indexed operation moves. -/
structure Fringe (s : Signed) (b o : Site n) (Q T : Coefficient F n) where
  π : Equiv.Perm ℕ
  step (i) : (short Q o i ∧ short T (affine s b o) (π i)) ∨
    (T.support (π i) = (Q.support i).image (affine s b) ∧ ∀ U, T.regular (π i) U = Q.regular i (pull s b U))

structure Rim (o : Site n) (Q T : Coefficient F n) where
  π : Equiv.Perm ℕ
  step (i) : (short Q o i ∧ short T o (π i)) ∨
    (T.support (π i) = Q.support i ∧ ∀ U, T.regular (π i) U = star (Q.regular i U))

private lemma extract_cost (h : ∃ v c, Q.remBound o R v c) :
    ∃ E : ℕ → ℝ, (∀ i, R.p.supBounds o (Q.support i) (Q.regular i) (E i)) ∧ Summable E := by
  obtain ⟨_,_,_,_,_,_,_,_,⟨E,hE,he⟩,_⟩ := h
  exact ⟨E,he,hE.2.1.of_nonneg_of_le (fun i => (he i).1) fun i => R.p.loMass _ _ (he i).1⟩

private lemma short_lives (h : Q.Format o H R) (i : ℕ) (he : short Q o i) : H.PiVanish d o (Q.regular i) := by
  cases he with
  | inl he => exact h.projects i he
  | inr he =>
    rw [he]; intro J; refine ⟨contDiffAt_const,fun k _ => ?_⟩
    exact iteratedDeriv_fun_const_zero

/-- Use true summability at the flat test. Compare at a common anchor.
As usual `o` in the API is literally the anchor, not a recentered box. Need
canonical section chart smoothness at flat through at least d, supplied e.g.
by the family's purchased price as below. Equality in `hg` is of densities. -/
theorem coords_near (hQ : Q.Format o H R) (hT : T.Format o H R) (hq : ∃ v c, Q.remBound o R v c)
    (ht : ∃ v c, T.remBound o R v c) (hd : d ≤ R.p.order)
    (C : SectionData F) (hc : C.Sound H)
    (hf : ∀ v, HasOrderAt (C.places v o) 1 d)
    (hb : ∀ x ∈ C.stencil, ∀ i : Axis, 20*((x i).natAbs + 1) ≤ n.val)
    (hg : Q.density o C R = T.density o C R) (π : Equiv.Perm ℕ)
    (hy : ∀ i : ℕ, (short Q o i ∧ short T o (π i)) ∨ T.regular (π i) = Q.regular i) : Q.x = T.x := by
  let P := R.p
  obtain ⟨a,h1a,ha⟩ := extract_cost hq
  obtain ⟨b,h1b,hh⟩ := extract_cost ht
  let X i := Q.support i ∪ T.support (π i)
  let E (i : ℕ) := Q.regular i - T.regular (π i)
  have Hu (i : ℕ) : P.Regular (X i) (E i) ∧ P.supBounds o (X i) (E i) (a i + b (π i)) := by
    have hu := regular_larger (u := X i) (hQ.smooth i) Finset.subset_union_left
    have hv := regular_larger (u := X i) (hT.smooth (π i)) Finset.subset_union_right
    exact ⟨regular_sub hu hv,bound_sub hu hv (bound_larger (h1a i) Finset.subset_union_left)
      (bound_larger (h1b (π i)) Finset.subset_union_right)⟩
  let θ := P.threshold
  let v := F.scaled θ⁻¹ Q.x
  let w := F.scaled θ⁻¹ T.x
  let f := C.places w o - C.places v o
  have hh0 : f =ᶠ[𝓝 (1:Config G n)] fun U => ∑' i, E i U := by
    filter_upwards [offFlags θ P.threshold_pos] with U hu
    have hx i : Healthy P.threshold (Q.support i) U := by unfold Healthy; rw [hu]; simp
    have hw i : Healthy P.threshold (T.support i) U := by unfold Healthy; rw [hu]; simp
    have hV : Summable fun i => Q.regular i U := Summable.of_norm_bounded ha fun i =>
      (h1a i).2 U (hx i) [] (by simp) (by simp)
    have hW : Summable fun i => T.regular i U := Summable.of_norm_bounded hh fun i =>
      (h1b i).2 U (hw i) [] (by simp) (by simp)
    have he := congr_fun hg U; rw [noFlagCharge Q _ _ hc hu,noFlagCharge T _ _ hc hu] at he
    have hp := mul_left_cancel₀ (noFlagEval hu) he
    simp only [f,E,Pi.sub_apply]; rw [hV.tsum_sub (show Summable (fun i => T.regular (π i) U) from π.summable_iff.mpr hW), π.tsum_eq (fun i => T.regular i U)]
    exact sub_eq_sub_iff_add_eq_add.mpr (hp.symm.trans (add_comm ..))
  have hS (J : Jet G) (i k : ℕ) (hk : k ≤ d) :
      iteratedDeriv k (fun t => E i (H.testLinks d o J t)) 0 = 0 := by
    cases hy i with
    | inl he =>
      have hx := short_lives hQ i he.1 J
      have hz := short_lives hT (π i) he.2 J
      simp only [E,Pi.sub_apply]; rw [iteratedDeriv_fun_sub, hx.2 k hk,hz.2 k hk,sub_self]
      · exact hx.1.of_le (Nat.cast_le.mpr hk)
      exact hz.1.of_le (Nat.cast_le.mpr hk)
    | inr he =>
      simp [E,he]
  apply (show Injective (F.scaled θ⁻¹) from ((show LeftInverse (F.scaled θ) (F.scaled θ⁻¹) from
    F.scaled_inv P.threshold_pos.ne').injective))
  change v=w
  have hv v := placed_reads C o hb hc v
  simp only [Reads,if_pos (nonwrapping_placement C o hb)] at hv
  apply F.coords.symm.injective
  refine jet_test_ext _ _ fun J k hk => ?_
  have hx := jet_sum (fun i => (Hu i).1) (fun i => (Hu i).2) (ha.add (π.summable_iff.mpr hh)) hh0 d
    (ContDiffAt.sub (hf w) (hf v)) hd H J k hk
  have hz := hx.tsum_eq; simp_rw [fun i => hS J i k hk,tsum_zero] at hz
  have hw := hv w J; have hv := hv v J
  rw [← hw.2.2 k hk,← hv.2.2 k hk]
  simp only [f,comp_def, Pi.sub_apply] at hz
  rw [iteratedDeriv_fun_sub (hw.1.of_le (Nat.cast_le.mpr hk)) (hv.1.of_le (Nat.cast_le.mpr hk))] at hz
  exact (sub_eq_zero.mp hz.symm).symm
section Packets
variable {N p : ℕ} {C : Family G} {E : Packet C d N p} {X : Finset Cover}

lemma sections_visit (hc : C.Makes) {d m p} (hr : C.ref d ≤ m) (o : Site (C.side m p)) :
    ∀ v, HasOrderAt ((C.localSection d).places v o) 1 d := by
  let P := C.path.levels.budget m
  have hj : d ≤ P.order := Nat.le_of_lt ((hc.stages d).2 m hr).1
  intro v
  let F := C.labels.level d
  let D := C.localSection d
  let L : F.Coeff →ₗ[ℂ] Config G (C.side m p) → ℂ := {
    toFun x := D.places x o
    map_add' a b := funext fun U => congr_fun (D.eval_linear.map_add a b) (expandAt o U)
    map_smul' a b := funext fun U => congr_fun (D.eval_linear.map_smul a b) (expandAt o U) }
  have he : (C.localSection d).places v o = ∑ i:F.Index,v i • L (Pi.single i 1) := by
    change L v = _
    simp_rw [← map_smul,← map_sum]; exact congr_arg L (by ext1 i; simp [Pi.single_apply])
  rw [he]; unfold HasOrderAt
  simp_rw [Function.comp_def,Finset.sum_apply]
  refine ContDiffAt.sum fun i _ => ?_
  have ht : HasOrderAt (L (Pi.single i 1)) (1 : Config G (C.side m p)) P.order := (hc.priced d m p hr o i).1.smooth _
    (one_healthy _ _ P.threshold_pos.le)
  exact ContDiffAt.const_smul (v i) (ht.fewer hj)

/-- A covariance hypothesis only where there are wrapping regular
operations. Need no count assumption (# potentially infinitely many). In
the zero or all-short case both last conditions can use any reindexing. -/
structure LocalPrice (E : Packet C d N p) : Prop where
  weights : PhysicalAction E.weights
  rolls m : C.ref d ≤ m → m≤N → ∀ (v : SourceSpace (C.labels.level d)) (s : Signed),
    Nonempty (Fringe s 0 0 (E.chain m v) (E.chain m (sw _ s v)))
  costs m : C.ref d ≤ m → m≤N → ∀ v : SourceSpace (C.labels.level d),
    Nonempty (Rim 0 (E.chain m v) (E.chain m (cw _ v)))



lemma LocalPrice.reads (h : LocalPrice E) (hc : C.Makes) (he : E.ComesFrom X) (m : ℕ) (hr : C.ref d ≤ m)
    (hm : m ≤ N) : ReadsCovariantly (E.matrixAt m) := by
  let F := C.labels.level d
  let R := C.path.rep N p m
  let D := C.localSection d
  have hC := hc.wilson.represents N p m hm
  have hb := hc.places d m p hr
  have hd : d ≤ R.p.order := by unfold R; rw [hC.vac]; exact Nat.le_of_lt ((hc.stages d).2 m hr).1
  have ht := sections_visit hc hr (0 : Site (C.side m p))
  have hv (v : SourceSpace F) : ∃ a b, (E.chain m v).remBound 0 R a b := ⟨_,he.cap m hr hm v⟩
  have hf (v : SourceSpace F) := he.format m hr hm v
  constructor
  · intro s v
    let w := sw F s v
    obtain ⟨M⟩ : Nonempty (R.activities.Moves s 0) := hC.good.labels.moves s 0
    obtain ⟨f⟩ := h.rolls m hr hm v s
    let L := shifted M (E.chain m v)
    have ho : affine s (0:Site (C.side m p)) 0 = 0 := by simp [affine]
    have hy : L.Format 0 C.params R := ho ▸ shifted.format M 0 (always_room C m _) (hf v)
    have hx : ∃ a b,L.remBound 0 R a b := by
      obtain ⟨a,b,hK⟩ := hv v
      have hr := shifted.cap M (hf v) hK; rw [ho] at hr; exact ⟨_,_,hr⟩
    have hy' : L.density 0 D R = (E.chain m w).density 0 D R := by
      have hY := shifted.density M D (hc.sections d) (E.chain m v) 0
      rw [ho] at hY
      exact hY.trans (charge_roll hc he h.weights m hr hm v s).symm
    change _ = turn _ s _
    refine (coords_near hy (hf w) hx (hv w) hd D (hc.sections d) ht hb hy' f.π ?_).symm
    intro i; obtain ⟨h1,h2⟩|⟨h1,h2⟩ := f.step i
    · refine Or.inl ⟨?_,?_⟩
      · cases h1 with
        | inl hL =>
          refine Or.inl ?_; have hr := (wraps s 0 0 _).2 hL; rw [ho] at hr; exact hr
        | inr hL => refine Or.inr ?_; change (E.chain m v).regular i ∘ pull s 0 = _; rw [hL]; rfl
      rw [ho] at h2; exact h2
    exact Or.inr (funext h2)
  intro v
  let w := cw F v
  obtain ⟨f⟩ := h.costs m hr hm v
  let L := pigment (E.chain m v)
  have hy : L.Format 0 C.params R := pigment_format (hf v)
  have hx : ∃ a b,L.remBound 0 R a b := by obtain ⟨a,b,hk⟩ := hv v; exact ⟨a,b,pigment_cap hk⟩
  have hw : L.density 0 D R = (E.chain m w).density 0 D R :=
    (pigment_density D (hc.sections d) 0).trans (charge_star he h.weights m hr hm v).symm
  refine (coords_near hy (hf w) hx (hv w) hd D (hc.sections d) ht hb hw f.π ?_).symm
  intro i; obtain ⟨h1,h2⟩|⟨h1,h2⟩ := f.step i
  · apply Or.inl; refine ⟨?_,h2⟩
    cases h1 with
    | inl hL => exact Or.inl hL
    | inr hL => apply Or.inr; change star ((E.chain m v).regular i) = _; rw [hL,star_zero]
  exact Or.inr (funext h2)


end Packets
end YM.ProjectorNext.Equivariance

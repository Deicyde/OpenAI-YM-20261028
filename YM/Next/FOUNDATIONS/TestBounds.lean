import YM.Next.FOUNDATIONS.LinkBounds


/-!
# Local weighted cost of Π

No estimate on sums over supports,
placements aligning in a history, or taking any limits. The constants
for reading a regular germ can be chosen with just the local label data/weight
(so before L or the tori are chosen).

Proof: For each fixed J and test order k, use the previous uniform link
lemma in the finite-order chain rule. At the identity, charge Fréchet
jets in normalized chart using true ordered increments. Use compactness
at **fixed tensor order** here (pull back to coefficient spaces indexed
just by the number of test directions, no dimension-dependence on the
torus!). Don't assert symmetry of iterated left derivatives. And
rather than claiming componentwise equivalence without cost in t, evaluate
the test directly on `t • J`. Then the estimate is exactly for the
reference frame norm with the desired slot threshold powers.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Foundations

open Function Filter Lattice Wilson Source RG Labels
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

section Detect

/-- Any probes that separate (on a fixed finite-dimensional real stage)
suffice here, with *probe-dependent* costs permitted. -/
private theorem budget_probes {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (p : ι → V →L[ℝ] W) (h : ∀ x : V, (∀ i, p i x = 0) → x = 0) (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) : ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c →
      ∀ x : V, (∀ i, ‖p i x‖ ≤ b i*c) → ‖x‖ ≤ C*c := by
  by_contra! hu
  let B (n : ℕ) := (n : ℝ)+1
  have he (n) : 0 < B n := by unfold B; positivity
  choose c hc x hp hN using fun n : ℕ => hu (B n) (he n)
  have hx (n) : 0 < ‖x n‖ := lt_of_le_of_lt (mul_nonneg (he n).le (hc n)) (hN n)
  let y (n : ℕ) := ‖x n‖⁻¹ • x n
  have hy (n) : y n ∈ Metric.sphere (0:V) 1 := by simp [y,norm_smul,(hx n).ne']
  haveI : ProperSpace V := FiniteDimensional.proper ℝ _
  obtain ⟨z,hz,m,hm,ha⟩ := (isCompact_sphere (0:V) 1).isSeqCompact hy
  suffices z = 0 by simp [this] at hz
  apply h
  intro i
  have ht (n) : ‖p i (y n)‖ ≤ b i/B n := by
    unfold y
    rw [map_smul,norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hx n)).le]
    calc
      _ ≤ ‖x n‖⁻¹ * (b i*c n) := by
        apply mul_le_mul_of_nonneg_left (hp ..) (inv_pos.mpr (hx n)).le
      _ ≤ ‖x n‖⁻¹ * (b i*(‖x n‖/B n)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (hb i))
          (inv_pos.mpr (hx n)).le
        rw [le_div_iff₀ (he n), mul_comm]; exact (hN n).le
      _ = _ := by field_simp [(hx n).ne', (he n).ne']
  have hs : Tendsto (fun n => ‖p i (y n)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) ht
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:=(1:ℝ)))
  exact norm_eq_zero.mp (tendsto_nhds_unique (((p i).continuous.continuousAt.tendsto.comp ha).norm)
    (hs.comp hm.tendsto_atTop))

end Detect

section Left

variable {G : Gauge} {n : Side} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem increments_add (U : Config G n) (A : Directions G n) (s t : ℝ) :
    increment (increment U (t • A)) (s • A) = increment U ((s+t) • A) := by
  funext i
  apply G.mat_injective
  simp only [increment, G.mat_mul, Pi.smul_apply, G.mat_lieExp, map_smul, add_smul, map_add, ← mul_assoc]
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  apply congr_arg (fun x => x * G.mat (U i))
  exact (NormedSpace.exp_add_of_commute (((Commute.refl (G.colorMat (A i))).smul_left s).smul_right t)).symm

/-- Only repeated same direction. -/
theorem leftDerivs_diag (U : Config G n) (A : Directions G n) (f : Config G n → Y) (k : ℕ) (t : ℝ) :
    leftDerivs f (List.replicate k A) (increment U (t • A)) =
      iteratedDeriv k (fun s : ℝ => f (increment U (s • A))) t := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ,leftDerivs,increments_add, ih, iteratedDeriv_succ]
    rw [deriv_comp_add_const]; simp

private def tensorSpace (k : ℕ) : Submodule ℝ (Tensor.T (Fin k → ℝ) ℂ k) where
  carrier := {A | Tensor.Sym A}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {A B} (ha : Tensor.Sym A) (hb : Tensor.Sym B) x s => by
    simp only [add_apply, ha x s, hb x s]
  smul_mem' r A ha x s := by
    change Tensor.Sym A at ha
    simp only [smul_apply, ha x s]

private lemma tensor_budget (k : ℕ) (q : Fin k → (Fin k → ℝ)) (b : (Fin k → ℝ) → ℝ)
    (hb : ∀ x, 0 ≤ b x) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Tensor.T (Fin k → ℝ) ℂ k,
      Tensor.Sym T → ∀ c : ℝ, 0 ≤ c → (∀ x, ‖Tensor.diagonal T x‖ ≤ b x*c) → ‖T q‖ ≤ C*c := by
  let u (x : Fin k → ℝ) : tensorSpace k →L[ℝ] ℂ :=
    (ContinuousMultilinearMap.apply ℝ _ ℂ fun _ => x) ∘L (tensorSpace k).subtypeL
  have hd (T : tensorSpace k) (ht : ∀ i, u i T = 0) : T = 0 := by
    apply Subtype.ext
    show T.val = 0
    apply Tensor.ext_diag T.val 0 T.property (fun _ _ => rfl)
    exact funext fun i => ht i
  obtain ⟨C,hC,hh⟩ := budget_probes (V:=tensorSpace k) (W:=ℂ) u hd b hb
  let K := ∏ j, ‖q j‖
  have hK : 0 ≤ K := Finset.prod_nonneg fun i _ => norm_nonneg _
  refine ⟨C*K, mul_nonneg hC.le hK, fun A hA c hc hx => ?_⟩
  have hi : ‖A‖ ≤ C*c := hh c hc ⟨A,hA⟩ hx
  calc
    ‖A q‖ ≤ ‖A‖*K := A.le_opNorm _
    _ ≤ C*c*K := mul_le_mul_of_nonneg_right hi hK
    _ = C*K*c := by ring

private theorem mixed_budget (G : Gauge) (k : ℕ) (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : BudgetPoint) (n : Side) (X : Support n) (o : Site n)
      (f : Config G n → ℂ) (c : ℝ), k ≤ B.order → B.Regular X f → B.supBounds o X f c →
        ∀ w : Fin k → Directions G n,
          (∀ i l, ‖w i l‖ ≤ a i*B.threshold*(1+(separation l.1 o : ℝ))^B.power) →
          ‖iteratedFDeriv ℝ k (f ∘ increment 1) 0 w‖ ≤ C*c := by
  classical
  let r (x : Fin k → ℝ) := 1 + ∑ i, ‖x i‖*a i
  have hr (x) : 0 < r x := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ =>
    mul_nonneg (norm_nonneg _) (ha _))
  obtain ⟨C,hC,h⟩ := tensor_budget k (fun i => Pi.single i 1) (fun x => r x^k) (fun x => pow_nonneg (hr x).le _)
  refine ⟨C,hC,fun B n X o f c hk hf hc w hw => ?_⟩
  let L : (Fin k → ℝ) →L[ℝ] Directions G n := ∑ i : Fin k,
    (ContinuousLinearMap.proj (R:=ℝ) i).smulRight (w i)
  have ht (x : Fin k → ℝ) : L x = ∑ i, x i • w i := by simp [L]
  let A := iteratedFDeriv ℝ k (f ∘ increment 1) 0
  let T := A.compContinuousLinearMap (fun _ => L)
  have hy : Healthy B.threshold X (1 : Config G n) := one_healthy X _ B.threshold_pos.le
  have hf' : ContDiffAt ℝ k (f ∘ increment 1) 0 :=
    (hf.smooth 1 hy).of_le (show (k : WithTop ℕ∞) ≤ (B.order : WithTop ℕ∞) from Nat.cast_le.mpr hk)
  have hp : Tensor.Sym T := by
    intro u e
    exact Analysis.sym_Jet (F:=ℂ) hf' (L ∘ u) e
  have he (x : Fin k → ℝ) : ‖Tensor.diagonal T x‖ ≤ r x ^ k * c := by
    let p := (r x)⁻¹ • L x
    have hb : B.dirBound o p := by
      intro l
      let u := B.threshold * (1+(separation l.1 o : ℝ))^B.power
      have hU : 0 ≤ u := mul_nonneg B.threshold_pos.le (pow_nonneg (by positivity) _)
      have H : ‖L x l‖ ≤ r x*u := calc
        ‖L x l‖ = ‖∑ i, x i • w i l‖ := by rw [ht]; simp [Finset.sum_apply]
        _ ≤ ∑ i, ‖x i • w i l‖ := norm_sum_le ..
        _ ≤ ∑ i, (‖x i‖*a i)*u := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (le_of_le_of_eq (hw i l) (mul_assoc ..)) (norm_nonneg _)
        _ ≤ r x*u := by
          unfold r; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left zero_le_one) hU
      change ‖(r x)⁻¹ • L x l‖ ≤ u
      rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hr x)).le]
      exact le_trans (mul_le_mul_of_nonneg_left H (inv_pos.mpr (hr x)).le) (by simp [(hr x).ne'])
    have hi : ‖Tensor.diagonal A p‖ ≤ c := by
      rw [show Tensor.diagonal A p = iteratedDeriv k (fun t : ℝ => f (increment 1 (t • p))) 0 from
        (iteratedDeriv_on_line hf' p).symm, ← leftDerivs_diag, zero_smul, Work.G07.at_zero_increment]
      refine hc.2 _ hy _ ?_ ?_
      · rw [List.length_replicate]; exact hk
      intro i hI; rw [(List.mem_replicate.mp hI).2]; exact hb
    change ‖Tensor.diagonal A (L x)‖ ≤ _
    calc
      ‖Tensor.diagonal A (L x)‖ = ‖Tensor.diagonal A (r x • p)‖ := by
        congr 2; unfold p; rw [smul_smul, mul_inv_cancel₀ (hr x).ne',one_smul]
      _ = r x ^ k * ‖Tensor.diagonal A p‖ := by
        rw [Tensor.homogeneous, norm_smul, Real.norm_of_nonneg (pow_nonneg (hr x).le _)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hi (pow_nonneg (hr x).le _)
  have hT : T (fun i => Pi.single i 1) = A w := by
    unfold T; rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    apply congr_arg A
    funext i
    simp [ht, Pi.single_apply, ite_smul]
  change ‖A w‖ ≤ _
  rw [← hT]; exact h T hp c hc.1 he
end Left

section Estimate

variable {G : Gauge}

/-- Price for a *fixed probe*, independent of period, placement, threshold
and support, given the f bounds (no extra dependence on visit counts here). No reliance on derivatives
of the mask. -/
theorem test_bound (H : Hol G) (J : Jet G) (d k : ℕ) (hk : k ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : Side) (o : Site n) (X : Support n) (B : BudgetPoint)
        (f : Config G n → ℂ) (c : ℝ),
      d ≤ B.order → d ≤ B.power → B.Regular X f → B.supBounds o X f c →
        ‖iteratedDeriv k (f ∘ H.testLinks d o (B.threshold • J)) 0‖ ≤ C*c := by
  choose a ha h using fun i : ℕ => testLog_bound H d i J
  choose b hb e using fun r : OrderedFinpartition k => mixed_budget G r.length
    (fun i => a (r.partSize i)) (fun i => (ha _).le)
  refine ⟨∑ i, b i, Finset.sum_nonneg fun i _ => hb i, fun n o X B f c hv hP hf hc => ?_⟩
  let Z := testLog H d o (B.threshold • J)
  let F := f ∘ increment (1 : Config G n)
  have hz : Z 0 = 0 := testLog_zero ..
  have he : f ∘ H.testLinks d o (B.threshold • J) =ᶠ[𝓝 0] F ∘ Z := by
    filter_upwards [increment_testLog H d o (B.threshold • J)] with q hq
    exact congr_arg f hq
  have hU := one_healthy (G:=G) X B.threshold B.threshold_pos.le
  have hg : ContDiffAt ℝ (B.order : WithTop ℕ∞) F (Z 0) := hz.symm ▸ hf.smooth 1 hU
  have hd : ContDiffAt ℝ (B.order : WithTop ℕ∞) Z 0 := (testLog_diff ..).of_le le_top
  rw [he.iteratedDeriv_eq, iteratedDeriv_vcomp_eq_sum_orderedFinpartition hg hd
    (Nat.cast_le.mpr (hk.trans hv)), hz, Finset.sum_mul]
  apply le_trans (norm_sum_le ..)
  refine Finset.sum_le_sum fun r _ => e r B n X o f c (r.length_le.trans (hk.trans hv)) hf hc _ ?_
  intro i l
  let j := r.partSize i
  have hj : j ≤ B.power := (r.partSize_le i).trans (hk.trans hP)
  let y : ℝ := 1+(separation l.1 o : ℝ)
  have hy : 1 ≤ y := by simp [y]
  apply (h (r.partSize i) n o l _ B.threshold_pos.le B.threshold_le).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy ((Nat.sub_le j 1).trans hj))
    (mul_nonneg (ha _).le B.threshold_pos.le)

private def functional {d : ℕ} (F : Labels.Frame G d) (J : Jet G) (k : ℕ) : F.Coeff →L[ℝ] ℂ :=
    (k.factorial : ℝ) •
      ((((read J).toLinearMap ∘ₗ tier k ∘ₗ (localFields G d).subtype ∘ₗ F.coords.symm.toLinearMap
        ).restrictScalars ℝ).toContinuousLinearMap)

private lemma measured {d : ℕ} (F : Labels.Frame G d) (J : Jet G) (k : ℕ) (v : F.Coeff) :
    functional F J k v = iteratedDeriv k (fun t => read (scaleJet J t) (F.coords.symm v).val) 0 :=
  (deriv_read J _ _).symm

private lemma coeff_bound {d : ℕ} (H : Hol G) (F : Labels.Frame G d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : Side) (o : Site n) (X : Support n) (B : BudgetPoint)
      (f : Config G n → ℂ) (c : ℝ), d ≤ B.order → d ≤ B.power → B.Regular X f →
      B.supBounds o X f c → ∀ p, JetTest H o p f → F.coeffSize (F.scaled B.threshold (F.coords p)) ≤ C*c := by
  let b (i : Jet G × Fin (d+1)) := functional F i.1 i.2.val
  choose C hC hh using fun i : Jet G × Fin (d+1) => test_bound H i.1 d i.2.val
    (Nat.le_of_lt_succ i.2.isLt)
  have hd (v : F.Coeff) (he : ∀ i, b i v = 0) : v = 0 := by
    apply F.coords.symm.injective
    refine jet_test_ext _ _ fun J k hk => ?_
    rw [← measured, ← measured]
    simpa only [map_zero] using! (show functional F J k v = 0 from he (J,⟨k,Nat.lt_succ_of_le hk⟩))
  obtain ⟨K,hK,h⟩ := budget_probes (V:=F.Coeff) (W:=ℂ) b hd C hC
  refine ⟨∑ _i : F.Index, K, Finset.sum_nonneg fun i _ => hK.le,
    fun n o X B f c hv hP hf hc p hp => ?_⟩
  let x := F.scaled B.threshold (F.coords p)
  have he (i : Jet G × Fin (d+1)) : ‖b i x‖ ≤ C i*c := by
    change ‖functional F i.1 i.2.val (F.scaled _ _)‖ ≤ _
    rw [measured]
    have hu : (fun t => read (scaleJet i.1 t) (F.coords.symm x).val) =
        fun t => read (scaleJet (B.threshold • i.1) t) p.val := by
      funext t
      unfold x
      rw [read_frame_scaled, F.coords.symm_apply_apply, show B.threshold • scaleJet i.1 t =
        scaleJet (B.threshold • i.1) t by
          funext j
          exact smul_comm B.threshold (t^(j+2)) (i.1 j)]
    rw [hu, ← (hp (B.threshold • i.1)).2.2 _ (Nat.le_of_lt_succ i.2.isLt)]
    exact hh i n o X B f c hv hP hf hc
  change (∑ i, ‖x i‖) ≤ _
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => (norm_le_pi_norm x i).trans (h c hc.1 x he)

/-- E (`psproj`). All quantifiers using the actual norm conventions. Includes
singular cases p=unit and d=0, c=0, etc., only the original support criterion
for `Reads`. Notice **one** constant (no dependence even on X or the side).
Note no converse claiming control of f off this domain. -/
theorem price_of_readout {d : ℕ} (H : Hol G) (F : Labels.Frame G d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : Side) (o : Site n) (X : Support n) (B : BudgetPoint)
      (f : Config G n → ℂ) (c : ℝ), d ≤ B.order → d ≤ B.power →
        B.Regular X f → B.supBounds o X f c → ∀ p : Label G d, Reads H o X p f →
          F.coeffSize (F.scaled B.threshold (F.coords p)) ≤ C*c := by
  classical
  obtain ⟨C,hC,h⟩ := coeff_bound H F
  refine ⟨1+C,le_add_of_nonneg_right hC,fun n o X B f c hv hP hf hc p hp => ?_⟩
  unfold Reads at hp
  split at hp <;> rename_i hq
  · exact (h n o X B f c hv hP hf hc p hp).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left zero_le_one) hc.1)
  have hy : ‖f 1‖ ≤ c := hc.2 1 (one_healthy X B.threshold B.threshold_pos.le) [] (by simp) (by simp)
  rw [hp, map_smul, F.coords_unit, map_smul, F.scaled_unit]
  simp only [Frame.coeffSize, Pi.smul_apply, norm_smul, Frame.e0, Pi.single_apply]
  rw [Finset.sum_eq_single 0]
  · rw [if_pos rfl, norm_one, mul_one]
    exact hy.trans (le_mul_of_one_le_left hc.1 (le_add_of_nonneg_right hC))
  · intro b _ hb; simp [hb]
  simp

end Estimate
end YM.Next.Foundations

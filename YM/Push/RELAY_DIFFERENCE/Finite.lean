import YM.Push.RELAY_DIFFERENCE.Combination

/-!
# One finite list of D04 calls per grade

Marks require arbitrary kernel rows *of top inverse coordinates*.
Cannot presume that decomposition coefficients in a well-conditioned fixed
reference frame will also be `dollar`-paid. Generate the projection-
kernel rows in the TOP spaces; suffices to produce comparison/equation
estimates for only these finitely many rows. Uses no eventual kernel dimension
or rank equality, any cutoff step projections at all. See ;
a way to pay for finite multiple comparisons before getting there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Lattice Cells Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators
open Next.Extract
variable {G : Gauge} {C : Family G} {d : ℕ} {W : Worth} {f : Extraction.Order} {F : Trial C} {b : Presentation C}

abbrev Fields (C : Family G) (d : ℕ) := (C.labels.level d).Index

def needle (C : Family G) (d : ℕ) (i : Fields C d) : C.label d := Pi.single i 1

lemma recompose (x : C.label d) : ∑ i : Fields C d,x i • needle C d i = x := by
  ext1 i
  simp [needle, Pi.single_apply]

/-- TOP, not terminal read. No continuity across cutoffs. `step`'s
kernel contains the equations. Project orthogonally only IN THIS AUX
GENERATION of testing calls; no claim that step was itself orthogonal. -/
def top_space (b : Presentation C) (d : ℕ) (u : Cutoffs) : Submodule ℂ (C.label d) := LinearMap.ker
    ((b.step d u).toLinearMap.comp (C.factory d u.1 u.2).terminal.toLinearMap)

def l2 (C : Family G) (d : ℕ) : EuclideanSpace ℂ (Fields C d) ≃L[ℂ] C.label d := PiLp.continuousLinearEquiv 2 ℂ _

def eu_kernel (b : Presentation C) (d : ℕ) (u : Cutoffs) : Submodule ℂ (EuclideanSpace ℂ (Fields C d)) :=
    Submodule.comap (l2 C d).toContinuousLinearMap.toLinearMap (top_space b d u)

def land (b : Presentation C) (d : ℕ) (u : Cutoffs) : C.label d →L[ℂ] C.label d :=
    ((l2 C d).toContinuousLinearMap.comp (eu_kernel b d u).starProjection).comp (l2 C d).symm.toContinuousLinearMap

def needles (b : Presentation C) (d : ℕ) (i : Fields C d) : Rowe C d := fun u =>
    (C.factory d u.1 u.2).terminal (land b d u (needle C d i))

lemma needles_drop (b : Presentation C) (i : Fields C d) (u : Cutoffs) : b.step d u (needles b d i u)=0 :=
  Submodule.starProjection_apply_mem (eu_kernel b d u) _

lemma needles_pay (b : Presentation C) (i : Fields C d) : dollar C f (needles b d i) := by
  let L : _ →L[ℂ] C.label d := (l2 C d).toContinuousLinearMap
  let v := (l2 C d).symm (needle C d i)
  let B : ℝ := ‖L‖*‖v‖
  simp only [dollar_slow,needles,LinearEquiv.symm_apply_apply]
  apply (Slow.const (C:=C) (f:=f) B).reduce
  refine Eventually.of_forall fun u => ?_
  exact (L.le_opNorm ((eu_kernel b d u).starProjection v)).trans
    ((mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le _ v) (norm_nonneg L)).trans (Real.le_norm_self B))

/-- Any `dollar`-row in b's null tests decomposes with slow multipliers
exactly, even when projection rank changes on cutoffs. -/
lemma cheap_generators (x : Rowe C d) (H : dollar C f x) (h : ∀ j,b.step d j (x j)=0) :
    ∃ p : Fields C d → Cutoffs → ℂ, (∀ i, Slow C f (p i)) ∧ x=readings (needles b d) p := by
  let w (i : Cutoffs) := (C.factory d i.1 i.2).terminal.symm (x i)
  have hw : Slow C f w := (dollar_slow x).mp H
  refine ⟨fun j i => w i j, fun j => hw.reduce (Eventually.of_forall fun i => norm_le_pi_norm (w i) j),?_⟩
  funext u
  have hm : (l2 C d).symm (w u) ∈ eu_kernel b d u := by
    change b.step d u ((C.factory d u.1 u.2).terminal ((l2 C d) ((l2 C d).symm (w u)))) = 0
    rw [ContinuousLinearEquiv.apply_symm_apply, show _ = x u from LinearEquiv.apply_symm_apply ..]; exact h _
  have ht : land b d u (w u)=w u := by
    unfold land; simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      Submodule.starProjection_eq_self_iff.mpr hm,ContinuousLinearEquiv.apply_symm_apply]
  unfold readings
  let X := (C.factory d u.1 u.2).terminal.toLinearMap.comp (land b d u).toLinearMap
  change _ = ∑ j : Fields C d, w u j • X _
  simp_rw [←map_smul,← map_sum]
  rw [show (∑ j : Fields C d, w u j • _) = w u from recompose (w u)]
  change _=(C.factory d u.1 u.2).terminal (land b d u (w u))
  rw [ht, show _=x u from LinearEquiv.apply_symm_apply ..]

lemma gathering_primary (x : C.label d) :
    Bid.visits C d x = gathered (fun i => Bid.visits C d (needle C d i)) fun i _ => x i := by
  unfold Bid.visits
  refine Eq.trans ?_ (reading_correct (fun i _ => needle C d i) (fun i _ => x i))
  exact congr_arg _ (funext fun _ => (recompose x).symm)

lemma height_linear (N p : ℕ) (v : Axis) (o : Site (C.side N p)) : IsLinearMap ℂ
    (fun x : C.label d => heighten C d x v N p o) := by
  let L (t) : C.label d →ₗ[ℂ] _ := (C.linearO N p d t).mk' _
  exact (((C.S.a N:ℂ)⁻¹ • (L (o+step v) - L o)).isLinear)

lemma gathering_height (x : C.label d) (v : Axis) :
    heighten C d x v = gathered (fun i => heighten C d (needle C d i) v) fun i _ => x i := by
  funext N p o
  let L : C.label d →ₗ[ℂ] _ := (height_linear N p v o).mk' _
  change L x = ∑ i : Fields C d,x i • L _
  simp_rw [← map_smul, ← map_sum]
  exact congr_arg L (recompose x).symm

/-- Stencilled
IBP partners, using actual Wilson reads. -/
structure Tickets (b : Presentation C) (f : Extraction.Order) (W : Worth) (d : ℕ) : Prop where
  erase (i : Fields C d) :
    ∃ F : Trial C, Stencilled f F ∧ exactOnSep C f F ∧
      ∃ S : Solo C F d, (S.row =ᶠ[f.fuse] needles b d i) ∧ Provisions S W f
  lift (v : ℕ) : v < d → ∀ i : Fields C v, ∃ S : Solo C (Bid.visits C v (needle C v i)) d, Provisions S W f
  farther (a : Axis) (i : Fields C d) : ∃ S : Solo C (Bid.heighten C d (needle C d i) a) (d+1), Provisions S W f

/-- Relay entry after only the finite lists (all copy/spectator estimates
within those calls still needed). Not asking for an assumption uniform in
all top images or arity restrictions in `exactOnSep`. -/
theorem finite_relay (H : Shop C W) (p : Tickets b f W d) : RelayCosts b f d := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro x hx hp
    choose F hf he S hS hz using p.erase
    obtain ⟨c,hc,rfl⟩ := cheap_generators x hp hx
    let V : Trial C := gathered F c
    have hv := gather_fitted F c hf
    refine ⟨V,hv.sober,gather_silent F c hf he,?_⟩
    let B := readings (fun i => (S i).row) c
    have hg : Bid.close C f (upper C B - V) := by
      unfold B V
      rw [reading_correct,gathering_sub]
      exact gather_close H.frame (fun i => (S i).diff) c hc (1/16) (by norm_num) fun i =>
        ((hz i).complete H (hf i)).2 _ (by norm_num [gamma])
    refine close_change hg ?_
    have hm := (Order.fused f _).mp (eventually_all.mpr hS)
    refine hm.mono fun k hk => hk.mono fun j hj => ?_
    funext a
    have ha : B (f.mesh j,f.per k)=readings (needles b d) c (f.mesh j,f.per k) := by
      dsimp only [B,readings]; apply Finset.sum_congr rfl
      intro i _; rw [hj i]
    change C.O _ _ (B _) a-_ = C.O _ _ (readings _ _ _) a-_
    rw [ha]
  · intro v h x
    rcases eq_or_lt_of_le h with rfl|hr
    · exact constant_vet H.frame _
    choose Q hQ using p.lift v hr
    rw [gathering_primary x]
    exact gather_vet _ _ Q hQ (fun i => Slow.const _) H (fun i => Stencilled.visits H.frame _)
  intro x a
  choose Q hQ using p.farther a
  rw [gathering_height x a]
  exact gather_vet _ _ Q hQ (fun i => Slow.const _) H (fun i => Stencilled.heighten H.frame ..)
end YM.Push.RelayDifference

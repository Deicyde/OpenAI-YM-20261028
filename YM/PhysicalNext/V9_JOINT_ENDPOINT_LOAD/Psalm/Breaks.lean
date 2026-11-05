import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Factors

/-!
# Companion and default-trigger support even for moving/held reads,
at threshold equality. Through the pg links only; the local word must still
prove its genuine U-patches and agreements in these neighborhoods. No
combination of bids at this sublist without a full component traversal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm.Pitch
open Function Filter Set Lattice Wilson RG Tree Pressure Precision Next Next.SectorChange Wisps Bid
   Push.SectorMeasure WardBin.Lies Planned.AtomRegular.Foliage AnalyticBridge.LocalGaussianLaws
   AnalyticBridge.LocalGaussian Heir
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {k : S.Choices} {d : Desk G S}
    {I : Type} [Fintype I] {X X' : Support f} {Y : Support c} {n l : ℕ} {Pt : Teller G} {C : Libretto G n} {D : Record} {Bt : Baton G}
    {r : ℝ} {V : Config G c} {p : Pitch S I}

abbrev Protected (d : Desk G S) (s : Finset I) (z : I → G.Color) := ∀ i∈s, ‖z i‖ < 4*d.radius
omit [Fintype I] in
lemma protects (d : Desk G S) (s : Finset I) (hd : 0<d.radius) (z : I → G.Color) (h : openedPatch d s z ≠ 0) : Protected d s z := by
  intro i hi; have he := broad_span d.broadCut (d:=2*d.radius) (by positivity) (z i) (Finset.prod_ne_zero_iff.mp h i hi); linarith only [he]

variable (k D) (b : Finset ℕ) (a : Museum F d.betaHat A X Y I) (U : Config G c → Config G f) (w : Config G c → Prices G I)
lemma closure {p : Pitch S I} {z : Config G f} {y : I → G.Color} {w : Prices G I} (he : ∀ i, p≠.door i) (h : p.stopped k D a b V w z y ≠ 0) (hd : 0 < d.radius) : Protected d (p.carriers a) y := by
  refine protects _ _ hd _ ?_; unfold stopped at h; intro h'
  cases p
  all_goals dsimp only at h h'
  all_goals first | exact he _ rfl | exact h (by unfold patched; simp [stripped,unmasked,h'])

variable {D} (h : Sounded Pt C D Bt r d) (hw : ContinuousAt w V) (hV : Healthy d.out.threshold Y V)
include h hV hw
omit hw hV in
private lemma cost_all {t : ℝ} {w : Prices G I} (ht : d.g * ‖tape w‖ ≤ t) (y : Set (Site f)) : Guarded a y d.g t w := fun _ _ => (mul_le_mul_of_nonneg_left (norm_le_pi_norm ..) h.heat.le).trans ht

/-- Mask tests all strictly on and broad charts open if Γ-supported. -/
theorem supported (he : (inherit l).Eligibility a) (hz : w V ∈ tsupport (muffler d I D)) :
    ∀ᶠ W in 𝓝 V, Healthy d.input.p.threshold (d.labels.reg l).support (field k a U w W) ∧
      (∀ i, ‖liftU k a U w W i‖ < d.radius) ∧ (inherit l).patched a (liftU k a U w W)=1 := by
  have hz := (guard_silent (I:=I) (n:=n) d.profile h.heat (mul_pos D.guards d.input.p.threshold_pos)).stay (w V) hz
  have hh := eventually_all.mpr (fun i => (h.quiet_link (k:=k) a U w hw hV i ((mul_le_mul_of_nonneg_left (norm_le_pi_norm ..) h.heat.le).trans hz)).2)
  filter_upwards [hh, h.quiet_good a U w hw hV he (fun p _ => cost_all a h hz (touched p))] with W hw hv
  exact ⟨hv,fun i => (hw i).1, Finset.prod_eq_one fun i _ => (hw i).2.2⟩



variable {a}
def Small (D : Record) (a : Museum F d.betaHat A X Y I) (p : Pitch S I) (y : Prices G I) := ∀ i∈p.carriers a, d.g*‖tape y i‖ ≤ cap D d/16
omit h hV hw in
private lemma low_score {w : Prices G I} (hp : ∀ i, Needs p.ground (a.address i) → i∈p.carriers a) (h' : Small D a p w) : Score a D p.ground w := by
  have h := mul_pos D.guards d.input.p.threshold_pos; exact fun i hi => (h' i (hp i hi)).trans (by unfold cap; linarith)

variable (he : p.Eligibility a)
include he
/-- Strict small guard -> identically zero *germ* of the trigger-charged
variant, before a support telescope and for arbitrary variation of other
parameters in the reel. Q & flags here are those evaluated on field;
continuity of `w` is all that's needed for this branch of the estimate.
-/
theorem vanquished (hz : Small D a p (w V)) : p.continued k D a b U w =ᶠ[𝓝 V] 0 := by
  have hp := d.input.p.threshold_pos; have ht := D.guards
  cases p with
  | door i =>
    have h' := (h.quiet_link (k:=k) a U w hw hV i ((hz i (Finset.mem_singleton_self _)).trans (by unfold cap; nlinarith))).2
    exact h'.mono (fun W h => sub_eq_zero.mpr h.2.1)
  | fine e =>
    have h' := low_score (by exact fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩) hz
    filter_upwards [h.quiet_face (k:=k) a U w hw hV he h'] with W hh; exact mul_eq_zero_of_left (sub_eq_zero.mpr hh.2) _
  | frame o =>
    have h' := low_score (by exact fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩) hz
    filter_upwards [h.quiet_frame (k:=k) a U w hw hV o he h'] with W hh; exact mul_eq_zero_of_left (sub_eq_zero.mpr hh.2) _
  | connector j =>
    have h' := low_score (by exact fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩) hz
    filter_upwards [h.quiet_noise (k:=k) a U w hw hV j he h'] with W hh; exact mul_eq_zero_of_left (sub_eq_zero.mpr hh.2.1) _
  | noise j =>
    have h' := low_score (by exact fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩) hz
    filter_upwards [h.quiet_noise (k:=k) a U w hw hV j he h'] with W hh; exact mul_eq_zero_of_left (sub_eq_zero.mpr hh.2.2) _
  | void x =>
    have h' := low_score (by exact fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩) hz
    filter_upwards [h.quiet_good (k:=k) a U w hw hV (Finset.singleton_subset_iff.mpr he) (fun p h i hi => h' i ⟨Tests.retain h hi.1, Tests.retain h hi.2⟩)] with W hh
    exact mul_eq_zero_of_left (sub_eq_zero.mpr (if_pos (Or.inr (Finset.disjoint_left.mp hh (Finset.mem_singleton_self _))))) _
  | inherit l =>
    have h' : ∀ᶠ W in 𝓝 V, muffler d I D (w W) = 1 := by
      have hi i := (((continuous_apply i).continuousAt.comp (gaugeCount.continuous.continuousAt.comp hw)).norm.const_mul d.g).eventually (gt_mem_nhds (show d.g * ‖gaugeCount (w V) i‖ < cap D d/8 from
        (hz i (Finset.mem_univ i)).trans_lt (by unfold cap; nlinarith)))
      filter_upwards [eventually_all.mpr hi] with W hi
      exact guard_open d.profile h.heat (mul_pos ht hp) (fun i => (hi i : _ < _).le)
    have hs := supported k a U w h hw hV he (subset_tsupport _ (show w V ∈ support (muffler d I D) by change muffler d I D (w V) ≠ 0; rw [h'.self_of_nhds]; exact one_ne_zero))
    filter_upwards [hs,h'] with W hh h; unfold continued stopped; dsimp only [stripped,unmasked,Pi.zero_apply,Activities.regularOccurrence]
    rw [masked_eq _ _ _ _ hh.1,h,one_mul,sub_self]
end YM.PhysicalNext.JointLoad.Psalm.Pitch

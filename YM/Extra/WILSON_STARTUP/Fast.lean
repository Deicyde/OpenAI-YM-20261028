import YM.Extra.WILSON_STARTUP.Author


/-!
# Common scheduling receipt for startup-only costs

Every SectionData family fixed as in the physical `Family` before scheduling,
with finite asks d ≤ j (sufficient when j ≥ d+3; see `Family.Makes.stages`).
Allows only looks at cutoff scale (no large-field step advances, Deal / RG path
pricing, or protected powers paid by this receipt). The lower bound `betaEntry`
respects future increases. Set pre-data simultaneously including `Suitable`
and direct condition, tighten after L/delays if needed, BEFORE calling for
Directed. Does not pay `RRequirements`' continuation obligations.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Timing
open Function Filter RG Wilson Lattice Design Start Source Shoot
open scoped Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {C : Supply.Sheet G} {D : Supply.Rolls C} {T : Supply.Protection D}
  {W : Supply.Delays T} {Y : Supply.Bar W} {I : Supply.Wait Y} (S : Labels.Frames G)
  (X : ∀ d, SectionData (S.level d))

def funded (C : Supply.Sheet G) (f : ℕ → ℝ) := ∀ j ≥ C.first, ∀ x : ℝ, f j ≤ x → ∀ A : Levels G, ∀ N,
    A.params N = C.profile j → A.clock.hatBeta N = x → Allows A N ∧ ∀ d ≤ j, Mark.Ready A (X d) N

theorem choose (W : Supply.Delays T) (h : ∀ i ≥ C.first,(C.profile i).clip.direct ≤ 1) : ∃ v : ℕ → ℝ,
    W.betaEntry ≤ v ∧ ∀ w : ℕ → ℝ,v ≤ w → funded S X C w := by
  have he (i) : ∀ᶠ x : ℝ in atTop, ∀ A : Levels G, ∀ N,
      C.first ≤ i → A.params N = C.profile i → A.clock.hatBeta N = x → Allows A N ∧ ∀ d ≤ i, Mark.Ready A (X d) N := by
    by_cases hk : C.first ≤ i
    · have ht := eventually_all.mpr fun d : Fin (i+1) => Mark.attain (X d.val)
      filter_upwards [enough G _ (h i hk),ht] with x hx hd A N _ ha hb
      exact ⟨hx A N ha hb,fun d hv => hd (⟨d,Nat.lt_succ_of_le hv⟩:Fin (i+1)) A N hb⟩
    exact Eventually.of_forall fun _ _ _ hx => False.elim (hk hx)
  choose f hf using fun i => eventually_atTop.mp (he i)
  refine ⟨fun i => max (W.betaEntry i) (f i),fun _ => le_max_left ..,fun w hw i hi x hx A N => ?_⟩
  exact hf i x ((le_max_right ..).trans ((hw i).trans hx)) A N hi

theorem hat_mono (a : Levels G) (hG : 0 ≤ G.slopeConstant) : Monotone a.clock.hatBeta := monotone_nat_of_le_succ fun i => by
  unfold Calendar.hatBeta; rw [Schedule.scale_succ]; exact add_le_add_right (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right <| Real.log_nonneg (x:=↑(a.S.block i).val) (by exact_mod_cast (a.S.block i).property)) hG) _

theorem receive (hG : G.Simple) (h : funded S X C W.betaEntry) {a : Levels G} (ha : Supply.Paid I a) (N : ℕ) :
    Allows a N ∧ ∀ d ≤ a.clock.J N, Mark.Ready a (X d) N := by
  have he : W.betaEntry (a.clock.J N) ≤ a.clock.hatBeta N := by
    cases N with
    | zero => simpa only [Calendar.hatBeta,Schedule.scale_zero,mul_zero, add_zero,ha.firstZero,ha.bar] using Y.ready
    | succ j => exact (ha.pays j).trans (hat_mono a (Gauge.slopeConstant_pos hG).le j.le_succ)
  refine h _ (ha.firstZero ▸ a.fits.mono (Nat.zero_le N)) _ he a N ?_ rfl
  unfold Levels.params Calendar.params; rw [ha.stage]

end YM.WilsonStartup.Timing

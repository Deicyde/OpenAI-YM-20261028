import YM.Extra.ITERATION_NO_LOSS.Rebuild
import YM.Push.PRICE_COMPILER.Post

/-!
# Delay after the Rolls

Pay halos needed for finite cluster fusions, on a single calendar, not by changing the
schedule for each horizon. When two child anchors first become insufficiently separated
at step `m+1 → m`, their spacing at `m+1` can involve the *ratio* L as well as B from
either stage, not just B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Filter Function Lattice RG Wilson Pressure RG.Supply Push.PriceCompiler Extra.Iteration.Scales
open scoped Topology
variable {G : Gauge} {P : Sheet G} {D : Rolls P} {T : Protection D}

/-- Post-L and per-step cost of a halo. Multiplies of this fixed power (fixed per cluster)
will still have subpower cost after taking an exponential. -/
def haloUnits (L : Side) (B B' : ℕ) : ℕ := (1 + L.val * (B+B'+1)^2)^4

def HaloGate (Q : Levels G) := ∀ m : ℕ,
    ((Q.budget (m+1)).supportExponent+1) * haloUnits (Q.S.block m) (Q.budget m).B (Q.budget (m+1)).B ≤
      Real.sqrt (Q.clock.hatBeta m)

lemma halo_feasible (L : Side) (A : ℝ) : ∀ᶠ x : ℝ in atTop, A * haloUnits L (radiusB x)
    (radiusB (betaF G x L)) ≤ Real.sqrt x := by
  let c : ℝ := G.slopeConstant * Real.log L.val
  have hz : Tiny id (fun _ : ℝ => (L.val:ℝ)) := Tiny.const tendsto_id _ (by positivity)
  have hu := Tiny.cover_size
  let f (x : ℝ) := 4*(1+(radiusB x:ℝ))
  have hf : Tiny id f := (Tiny.const tendsto_id (4:ℝ) (by norm_num)).mul hu tendsto_id
  have he : Tiny id (fun x => |A| *(1+(L.val:ℝ)*(f x)^2)^4) := (Tiny.const tendsto_id _ (abs_nonneg _)).mul
    (((Tiny.const tendsto_id 1 zero_le_one).add (hz.mul (hf.pow tendsto_id 2) tendsto_id) tendsto_id).pow tendsto_id 4) tendsto_id
  filter_upwards [Extra.Iteration.Rebuild.geometry c,he (1/2) (by norm_num)] with x hx hk
  have hb : (↑(radiusB (betaF G x L)):ℝ) ≤ 2*(radiusB x:ℝ) :=
    by exact_mod_cast (hx.1.1 : radiusB (betaF G x L) ≤ 2*radiusB x)
  have hf : ((radiusB x : ℕ):ℝ) + (↑(radiusB (betaF G x L)):ℝ) + 1 ≤ f x := by
    unfold f; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]
  rw [Real.sqrt_eq_rpow]
  apply le_trans _ hk.2
  unfold haloUnits; push_cast; gcongr; apply le_abs_self

lemma halo_delay (V : Delays T) : ∃ W, DelayLe V W ∧ ∀ W', DelayLe W W' →
    ∀ {X : Bar W'} (P : Wait X) (Q : Levels G), Paid P Q → HaloGate Q := by
  obtain ⟨W,hW,-,h'⟩ := delay_extra V (fun j => fun x => ((P.profile j).supportExponent+1) *
    haloUnits (D.L j) (radiusB x) (radiusB (betaF G x (D.L j))) ≤ Real.sqrt x)
    (fun _ _ _ => True) (fun _ => halo_feasible ..) (fun _ _ => by simp)
  refine ⟨W,hW,fun W' hW' _ Z Q hQ m => ?_⟩
  have hx := (h' W' hW').1 _ _ (hQ.pays m)
  set j := Q.clock.J (m+1)
  change ((Q.clock.stage j).supportExponent+1) * haloUnits (Q.S.block m) (radiusB _) (radiusB (Q.clock.hatBeta (m+1))) ≤ _
  rw [Extra.Iteration.block_beta, Extra.Iteration.block_eq hQ, hQ.stage]; exact hx
end YM.OPE

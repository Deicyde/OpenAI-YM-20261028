import YM.Fields.Motion
import YM.Fields.Spectrum

/-!
# Vector limits and existence of ACTUAL polynomial word action given

same heat embeddings, mixed heights, W transforms, etc. Does not prepare
actual `Data` (stars, actual motion spells, spreading field limits and
bounds) by itself. No mesh inputs may be erased when using these in C.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open Function Set Filter MeasureTheory Measure OS Mink Probe Spectral Complex
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {L : Register G} {S T : Table L} {C : Chamber T timeAxis} {X : Hilbert}
abbrev till : Filter ℝ := 𝓝[>] (0:ℝ)

lemma norms_kernel (Y : Hilbert) (Ω : ℝ → Y) (x : ℂ) (h : Tendsto (fun p : ℝ × ℝ => inner ℂ (Ω p.1) (Ω p.2))
    (till ×ˢ till) (𝓝 x)) : ∃ y, Tendsto Ω till (𝓝 y) := by
  let F := till ×ˢ till
  have hn : Tendsto (fun p : ℝ × ℝ => ⟪Ω p.1,Ω p.1⟫_ℂ) F (𝓝 x) := h.comp (tendsto_fst.prodMk tendsto_fst)
  have hp : Tendsto (fun p : ℝ × ℝ => ⟪Ω p.2,Ω p.2⟫_ℂ) F (𝓝 x) := h.comp (tendsto_snd.prodMk tendsto_snd)
  have hc : Tendsto (fun p : ℝ × ℝ => ⟪Ω p.2,Ω p.1⟫_ℂ) F (𝓝 x) := h.comp (tendsto_snd.prodMk tendsto_fst)
  have he : Tendsto (fun p : ℝ × ℝ => inner ℂ (Ω p.1-Ω p.2) (Ω p.1-Ω p.2)) F (𝓝 0) := by
    simp_rw [inner_sub_right,inner_sub_left]
    simpa only [sub_self] using! (hn.sub hc).sub (h.sub hp)
  apply cauchy_map_iff_exists_tendsto.mp (cauchy_map_iff'.mpr (tendsto_uniformity_iff_dist_tendsto_zero.mpr ?_))
  change Tendsto (fun p : ℝ × ℝ => dist (Ω p.1) (Ω p.2)) F (𝓝 0)
  simp_rw [dist_eq_norm,@norm_eq_sqrt_re_inner ℂ]
  simpa using! (Real.continuous_sqrt.continuousAt.tendsto.comp (Complex.continuous_re.continuousAt.tendsto.comp he))

/-- integrated (literal, full word) heat vectors of fixed positive heights
only. Real port: equality at ALL independent slope pairs then permits Cauchy.
Build from F strict-time and Phi later.
-/
structure Cups (W : Surface S) (J : StarOp S) (K : Spins S) (C : Chamber T timeAxis) where
  hot : Sentence S → ℝ → C.H
  here (v w) : Tendsto (fun p : ℝ×ℝ => inner ℂ (hot v p.1) (hot w p.2)) (till ×ˢ till) (𝓝 (W.kernel J v w))
  omega : Tendsto (hot []) till (𝓝 C.omega)
  time (v b) : hot (K.po (Poincare.translation b) v) =ᶠ[till] (fun s => C.flow.unit.translation b (hot v s))

structure Outfield (W : Surface S) (J : StarOp S) (K : Spins S) (C : Chamber T timeAxis) where
  toFun : Sentence S → C.H
  at_pair x y : inner ℂ (toFun x) (toFun y)=W.kernel J x y
  vacuum : toFun []=C.omega
  volume (v b) : toFun (K.po (Poincare.translation b) v) = C.flow.unit.translation b (toFun v)

namespace Cups
variable {W : Surface S} {J : StarOp S} {K : Spins S} (Z : Cups W J K C)

def cold (i : Sentence S) := (norms_kernel C.H _ _ (Z.here i i)).choose
lemma chase (i) : Tendsto (Z.hot i) till (𝓝 (Z.cold i)) := (norms_kernel _ _ _ (Z.here i i)).choose_spec

def out : Outfield W J K C where
  toFun := Z.cold
  at_pair x y := tendsto_nhds_unique (((Z.chase x).comp tendsto_fst).inner ((Z.chase y).comp tendsto_snd)) (Z.here x y)
  vacuum := tendsto_nhds_unique (Z.chase _) Z.omega
  volume v x := tendsto_nhds_unique_of_eventuallyEq (Z.chase _)
    ((C.flow.unit.translation x).continuous.continuousAt.tendsto.comp (Z.chase _)) (Z.time v x)
end Cups

namespace Outfield
variable {W : Surface S} {J : StarOp S} {K : Spins S} (Z : Outfield W J K C)

include Z in
lemma safe : W.wordsPositive J := by
  have he := Fields.hilbertNonnegative C.H Z.toFun
  unfold Surface.wordsPositive
  rw [show W.kernel J = _ from funext fun x => funext fun y => (Z.at_pair x y).symm]
  exact he
include Z in
lemma soak (p : T.Basic) : W.expect []=1 := by
  have he : inner ℂ C.omega C.omega=W.expect [] := by rw [← Z.vacuum,Z.at_pair];rfl
  rw [← he,inner_self_eq_norm_sq_to_K,show ‖C.omega‖=1 from OS.nil_norm C.GNS p]; simp
lemma daylight {W : Surface S} {J : StarOp S} (Q : Soil W J) (Z : Outfield W J K C) (Y : Action Q.H) (h : ∀ i p, Y.V p (Q.plant i)=Q.plant (K.po p i)) :
    ∃ U,Y.Intervenes (C:=C) U (Q.plant []) := by
  obtain ⟨U,-,hU,hu⟩ := Q.universal_embed (M:=C.H) Z.toFun Z.at_pair
  refine ⟨U,⟨hu,fun p => Q.by_bud ?_,(hU _).trans Z.vacuum⟩⟩
  intro i
  change U (Y.V _ (Q.plant i))= C.flow.unit.translation p (U (Q.plant i))
  rw [h,hU,hU,Z.volume]
end Outfield

lemma harvest {R : S.Rotation} {W : Surface S} {h : S.RealSpin} (J : StarOp S) (K : Spins S) (hm : K.Descends R h) (hz : starRead J h) (ht : Involutive J)
    (p : W.Symbol) (hc : W.Cam J) (he : W.Persists) (hx : W.Regional)
    (hu : W.Strong J K) (hTm : W.Transforms J K)
    (H : C.UniqueHeat) (hT : T.Basic) (O : Cups W J K C) : ∃ Z : Wightman S, Z.Realizes (W:=W) R h := by
  let F := O.out
  let Z := Classical.choice (Kernel.host F.safe)
  obtain ⟨Y,hY⟩ := Soil.mobilize (show Soil W J from Z) K hm hTm hu
  obtain ⟨U,hw⟩ := F.daylight Z Y hY
  exact ⟨{ operators := Soil.starter (W:=W) Z p, J := J, action := Y, momentum := Y.orbit.P, spin := K },
    ⟨hz,hm,Soil.usable Z p hc (F.soak hT),Soil.sharp Z p,Soil.relishes Z p,Soil.regional Z p hx,Soil.sees Z p ht he,
    Soil.cultivates Z K Y hY p,Y.orbit.total,Y.spectrum hw,Y.only hw H⟩⟩
end YM.Boundary

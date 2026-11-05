import YM.Extension.UV.Station.JetFunds
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.StationaryData
open Set Filter Function Lattice RG Wilson Work.F02
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace

lemma ink.transmit_tracks {E F ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
   (V : ℕ→ι→ℝ)(v:ι→ℝ)(l:ι→ℕ)(hf:∀ M:ℕ,Set.Finite {i|l i≤M}) (x:E)(Q:ι→E→F) (hQ:∀ i,ContDiff ℂ ω (Q i)){σ τ C A R:ℝ}(hh:R>0)(hσ:τ<σ)(hA:∀ i y, y∈Metric.ball x R→‖Q i y‖ ≤ A*Real.exp (τ*l i)) (h:Tendsto V atTop (nhds v)) (hM:∀ᶠ n in atTop,tight.mass (V n) σ l C):Tracks ∞ (fun n=>ink.transmit Q (V n)) (ink.transmit Q v) x:= by
   let w (i:ι):= A * Real.exp (τ*l i)
   have hy f (h:tight.mass f σ l C) : Summable (fun i=> |f i| *w i) :=by
      let g i:=|f i| *Real.exp (τ*l i)
      have he: Summable g:=h.2.1.of_nonneg_of_le (fun _=>by unfold g; positivity) (fun i=>show |f i| * _ ≤ |f i| * _ by gcongr)
      rw [show (fun i=> |f i| *w i)=(fun i=>A*g i) from funext (fun i=> mul_left_comm ..)]
      exact he.mul_left A
   have hx (n): (∑' i, |V n i - v i| *w i) = A*tight.read (V n-v) τ l:= by rw [tight.read,← tsum_mul_left]; exact tsum_congr fun i=>mul_left_comm ..
   apply ink.tracks hh _ _ w Q hQ hA (hM.mono fun n=>hy _) (hy v (tight.mass_closed hM h)) ?_
   simp_rw [hx]; simpa only [mul_zero] using ((tight.strict_limit hM h hf hσ).const_mul A)

namespace Tracks
variable {F E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
 {f f':ℕ→E→F} {w w':E→F} {r:WithTop ℕ∞}{x:E}
lemma replace (h:Tracks r f w x) (he:f' =ᶠ[atTop] f) (hw:w'=w): Tracks r f' w' x:= by
  rw [hw]; exact ⟨(h.at_each.and he).mono (fun i hg=>hg.2.symm ▸ hg.1),h.at_limit,fun k hk=> (h.jet k hk).congr' (he.mono fun i hi=> congr_arg (fun a : E → F => iteratedFDeriv ℝ k a x) (Eq.symm (show f' i=f i from hi)))⟩
end Tracks

section row
variable {G:Gauge} {m:Side}(T:ℕ→PathData G) {p:Clip}{t A L:ℝ}(f:BookKey G→ℝ) (h:t>0) (ht:Tendsto (book_get ∘ T) atTop (nhds f)) (hT:∀ᶠ n in atTop,(T n).Bounds p t A L)
include h ht hT
lemma row_ball (U:Config G m) b c: let q:=fun i:Slot=>slotExt i c (G:=G)
    Tracks ∞ (fun n=>ink.transmit q (book_row (T n) b)) (ink.transmit q (fun i:Slot=>f (.inl (b,i)))) (physical U):= by
   intro q
   exact ink.transmit_tracks _ _ (fun i=>i.length) (fun M=> Set.finite_coe_iff.mp (slot_roster M)) _ q (fun i=>slotExt_contDiff ..) (radius_pos (half_pos h)) (half_lt_self h) (fun i y hy=>slotExt_bound U (half_pos h) _ (_root_.Metric.ball_subset_closedBall hy) _ _) (tendsto_pi_nhds.mpr (fun i=>tendsto_pi_nhds.mp ht (.inl (b,i)))) (hT.mono fun n hn=>(row_budget _ hn b)) -- fix params

variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (B:E→ Config G m) {x:E} (hA: ContDiffAt ℝ ∞ (physical ∘ B) x)
include hA
lemma row_real (b : Face (Per m)): Tracks ∞ (fun n y=> (compactify (T n)).ell (B y) b) (fun y=> (book_path f).ell (B y) b) x:= by
  have he:=row_ball T f h ht hT (B x) b.2 b.1
  dsimp only at he
  have hi (f:BookKey G→ℝ) y (hh:(book_path f).Bounds p t A L): ink.transmit (fun i:Slot=>slotExt i b.1) (fun s=>f (.inl (b.2,s))) (physical (B y)) = colorUp G ((book_path f).ell (B y) b) := by
     exact Eq.trans ((roster.tsum_eq (fun s=> f (.inl (b.2,s)) • slotExt s b.1 (physical (B y)))).symm) (rowExt_real hh ..)
  have hl: (book_path f).Bounds p t A L:=limit_bounds f T hT ht
  apply (((Tracks.unswerving (physical∘ B) hA).comply he (Eventually.of_forall fun _=>rfl)).linear (colorReal G) |>.replace)
  · filter_upwards [hT] with n hn; exact funext (fun y=> Eq.symm ((congr_arg (colorReal _) (hi _ y (compact_bounds _ hn))).trans (colorReal_up ..)))
  exact funext (fun y=> ((congr_arg (colorReal _) (hi f y hl)).trans (colorReal_up ..)).symm)
end row
end YM.Extension.UV.StationaryData

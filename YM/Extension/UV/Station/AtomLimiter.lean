import YM.Extension.UV.Station.RowLimiter
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Extension.UV.StationaryData
open Set Filter Function Lattice RG Wilson Precision Exterior Work.F02
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge} {m:Side}
def needle {k:Fin 3}(x:Site m)(b:Colors G k)(s: Pattern (k.1+2))(M:Ambient G m):ℂ:= ∏ i,slotExt (s i) x M (b i)
def needle_report (f:BookKey G→ℝ) (x:Site m)(k:Fin 3)(b:Colors G k) := ink.transmit (needle x b) (fun s=>f (.inr ⟨k,b,s⟩))
section jet
variable (T:ℕ→PathData G) {p:Clip}{t A L:ℝ}(f:BookKey G→ℝ) (h:t>0) (ht:Tendsto (book_get ∘ T) atTop (nhds f)) (hT:∀ᶠ n in atTop,(T n).Bounds p t A L)
include h ht hT
lemma needle_ball (U:Config G m) x k b: Tracks ∞ (fun n=>needle_report (book_get (T n)) x k b) (needle_report f x k b) (physical U):= by
    let K := k.val+2
    let q:=needle x b; let σ:=t/2; have hσ:=half_pos h
    have hq s: ContDiff ℂ ω (q s):=contDiff_prod fun i _=> (contDiff_apply ℂ _ _).comp (slotExt_contDiff ..)
    let v:= slotConst G
    have he (s: Pattern K) (y:Ambient G m) (hy: y∈ _root_.Metric.ball (physical U) (radius σ)): ‖q s y‖ ≤ v^K*Real.exp (σ*pat_len s):=by
       rw [pat_len,Nat.cast_sum,Finset.mul_sum,Real.exp_sum] -- card issue
       calc ‖q s y‖ ≤ (∏ i:Fin K,‖slotExt (s i) x y (b i)‖) := (by simp only [q,needle, norm_prod]; exact le_rfl)
            _ ≤ ∏ i:Fin K, v * Real.exp (σ*(s i).length) := by exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=>le_trans (norm_le_pi_norm ..) (slotExt_bound U hσ _ (_root_.Metric.ball_subset_closedBall hy) _ _))
            _ = _ := by simp [Finset.prod_mul_distrib]
    exact ink.transmit_tracks _ _ pat_len (pattern_roster _) _ q hq (radius_pos hσ) (half_lt_self h) he (tendsto_pi_nhds.mpr (fun s=>(tendsto_pi_nhds.mp ht (.inr ⟨k,b,s⟩)))) (hT.mono fun n hn=>book_budget _ hn k b)
end jet

section real
lemma needle_physical {k:Fin 3} {x:Site m} {f:BookKey G→ℝ} (h:Summable fun i=>(payload f k i).magnitude) (U:Config G m):
    (∑ b:Colors G k,needle_report f x k b (physical U))=((∑' i,(payload f k i).unmasked U x):ℝ):=by -- coerces RHS
    let K:=k.val+2; haveI : NeZero K:=⟨by omega⟩
    let g (b:Colors G k) j := f (.inr ⟨k,b,(slots K j)⟩) *∏ i, (slots K j i).atSite U x (b i)
    have hv (b:Colors G k) : Summable (g b):=by
       apply (h.mul_right ((2:ℝ)^K)).of_norm_bounded; intro i
       dsimp only [g]; rw [norm_mul,Real.norm_eq_abs (∏ z, (slots K i z).atSite U x (b z)),Finset.abs_prod]
       refine mul_le_mul (Finset.single_le_sum (f:=fun b=> |(payload f k i).coeff b|) (fun _ _=>abs_nonneg _) (Finset.mem_univ b)) ?_ (by exact Finset.prod_nonneg (fun _ _=>abs_nonneg _)) (by unfold Atom.magnitude; positivity)
       have hp: (2:ℝ)^K=∏ i:Fin K, 2:=by simp
       rw [hp]
       exact Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun z hz=>le_trans (PiLp.norm_apply_le ((slots K i z).atSite U x) (b z)) (show ‖(slots K i z).atSite U x‖ ≤2 from Slot.eval_norm ..)) -- EuclideanSpace
    rw [show (∑' i,(payload f k i).unmasked U x) = ∑ b,∑' j,g b j from Summable.tsum_finsetSum (fun b _=> by exact hv b)]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro b hb
    let h (s:Pattern K):= f (.inr ⟨k,b,s⟩)*∏ i, (s i).atSite U x (b i)
    rw [show (∑'j,g b j)=∑' s,h s from (slots K).tsum_eq h,Complex.ofReal_tsum]
    apply tsum_congr; intro s
    simp [h,needle,slotExt_physical,colorUp_apply,Complex.real_smul]; exact Or.inl rfl -- unfolding tsum??? needle_report not before tsum. Need unfold on LHS
end real
end YM.Extension.UV.StationaryData

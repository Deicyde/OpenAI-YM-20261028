import YM.TraceExtension.Slate.Spite
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Slate
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W) (hT:supportQ C.path.levels)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} (hb:(𝓛:Filter (ℕ×ℕ))≤F.fuse)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.path
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "H!"=> C.path.levels.clock.hatBeta
variable {t:Tickets C} (hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
open Zn
variable {d:ℕ}{Z:Arch C}(hz:steep 𝓛 Z)
open Finset StressFlux
local notation "Fᵣ"=> C.labels.level 4
local notation "Zᵣ"=> C.labels.level 5
-- qualitative starts plus sharper cost at the aperture rho.
variable {i:Bend}{L:PaceBook C}(hV:Rod t i (𝓛:Filter (ℕ×ℕ)) L)
def vCard (F:Frame G 5):(Fin 3→ℝ)→L[ℝ] Bowl F:=LinearMap.toContinuousLinearMap ((plate F).symm.toLinearMap ∘ₗ bareVector)
lemma leaseV (F:Frame G 5)(h:G.Simple)(v): Lease F h (Vivid F v)=rho h (bareVector v):=by change rho h ((plate F) ((plate F).symm _))=_; rw[LinearEquiv.apply_symm_apply]
lemma lace {X Y:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y](F:X→L[ℝ]Y)(x y:X)(p:ℝ)(hp:‖x-y‖≤p): ‖F x-F y‖ ≤ ‖F‖*p:=by rw[← map_sub]; exact (F.le_opNorm _).trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
include hb hz hV P h hu
lemma tiara : Tendsto (fun j=> (Shine4 Z L j,Shine5 Z L.Z j)) atTop (𝓝 ((BillC Fᵣ (BornZ i)),Vivid (Zᵣ) (BornZ i))):=by
    let S:= OrbitT (Fᵣ); let R:= OrbitR (Zᵣ); let T:= LinearMap.toContinuousLinearMap (BillC (Fᵣ)); let W:=vCard (Zᵣ); let c:= ‖S‖+‖R‖; let y:= ‖T‖+‖W‖; let b:= BornZ i
    have ht:0 ≤ c:= add_nonneg (norm_nonneg S) (norm_nonneg R); have hf:0 ≤ y:=add_nonneg (norm_nonneg T) (norm_nonneg W);
    let v:= (T b,W b)
    apply Metric.tendsto_nhds.mpr; intro ε hε; let τ:= ε/(4*(1+y)); have hτ: 0 < τ:= div_pos hε (by positivity)
    have hr:Tendsto (fun k=> c*loss A k) atTop (𝓝 0):=by simpa only [loss,mul_zero] using (Age_rate A (by norm_num:(-(1/4:ℝ))<0) h).const_mul c
    filter_upwards [article h hu i τ hτ,roofs P h hb hu hV,shipping hz hV,hr.eventually (ge_mem_nhds (div_pos hε (show (0:ℝ)<4 by norm_num)))] with k hk hR hT hY
    let f(p:ℕ×ℕ):= (S (Road k p L), R (Roll k p L.Z))
    have hx:Tendsto (fun p:ℕ×ℕ=> ‖f p - v‖) b! (𝓝 ‖(Shine4 Z L k,Shine5 Z L.Z k)-v‖):= ((hT.1.prodMk_nhds hT.2).sub_const v).norm
    rw[dist_eq_norm]; apply lt_of_le_of_lt (le_of_tendsto hx (b:=ε/2) ?_) (half_lt_self hε)
    filter_upwards [hk,hR] with p hp hu; obtain ⟨w,hw,ht',hu',hE⟩:=hp
    have he : ‖f p-(T w,W w)‖ ≤ ε/4:=by
       rw [Prod.norm_def,max_le_iff]
       have hc:0 ≤ loss (A) k:= Zn.wake ..|>.le; constructor
       · change ‖S _-T w‖ ≤ _; rw [← show S _=T w from ht']; exact (lace S _ _ _ hu.1).trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg R)) hc).trans hY)
       change ‖R _-W w‖ ≤ _; rw [← show R _=W w from hu']; exact (lace R _ _ _ hu.2).trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg S)) hc).trans hY)
    have hh: (4*(1+y))*τ=ε:= mul_div_cancel₀ _ (by positivity)
    have hL : y*τ ≤ ε/4:=by nlinarith only [hh,hτ]
    have hζ: ‖(T w,W w)-v‖ ≤ ε/4:=by
        rw [Prod.norm_def,max_le_iff];exact ⟨(lace T w b τ hw).trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg W)) hτ.le).trans hL), (lace W w b τ hw).trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg T)) hτ.le).trans hL)⟩
    linarith only [norm_sub_le_norm_sub_add_norm_sub (f p) (T w,W w) v,he,hζ]
lemma diadem : Tendsto (fun k=> taxA (A) k*(Lease (Zᵣ) h (Shine5 Z L.Z k)-Lease (Zᵣ) h (Vivid (Zᵣ) (BornZ i)))) atTop (𝓝 0):=by
   let V:= Vivid (Zᵣ) (BornZ i);let ρ:=Lease (Zᵣ) h; let T:= OrbitR (Zᵣ); have hP:∀ᶠ k in atTop, ‖ρ (Shine5 Z L.Z k)-ρ V‖ ≤ ‖ρ‖*(‖T‖*loss (A) k):=by
        filter_upwards [shipping hz hV,article h hu i 1 zero_lt_one,roofs P h hb hu hV] with k hk ht he
        refine le_of_tendsto (f:=fun p:ℕ×ℕ=>‖ρ (T (Roll k p L.Z))-ρ V‖) (((ρ.continuous.continuousAt.tendsto.comp hk.2).sub_const (ρ V)).norm) ?_; filter_upwards [ht,he] with p ht hu
        obtain ⟨w,hw,h₁,h₂,h₃⟩:=ht; have hp : ρ V= ρ (T (coin5 k p t i)):=by rw [h₂]; unfold ρ V; rw[leaseV,leaseV,h₃]
        rw [hp]; exact lace ρ _ _ _ (lace T _ _ _ hu.2)
   apply tendsto_zero_iff_norm_tendsto_zero.mpr; have hv :Tendsto (fun i=> ‖ρ‖*‖T‖*AgeK A (1/5+ -(1/4:ℝ)) i) atTop (𝓝 0):= by simpa using (Age_rate A (by norm_num:1/5+ -(1/4:ℝ)<0) h).const_mul (‖ρ‖*‖T‖)
   refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ hv; filter_upwards[hP] with i hi
   have ht :0 ≤ taxA A i:=Zn.wake ..|>.le; change ‖taxA A i*(ρ _-ρ V)‖ ≤_; rw[norm_mul, Real.norm_of_nonneg ht]; apply le_trans (mul_le_mul_of_nonneg_left hi ht); rw [← AgeK_mul]; change taxA A i*(‖ρ‖*(‖T‖*loss (A) i)) ≤ ‖ρ‖*‖T‖*(taxA A i*loss A i); apply le_of_eq; ring
end YM.Trace.Slate

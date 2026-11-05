import YM.FullVolume.Tess.Tan
/-
 # Holomorphic transfer to grid derivatives tests. Scalar CLM focus first.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp.Beam
open Filter Function Finset Set RG Push.AbsoluteSums Ray Asymptotics
open scoped Topology BigOperators Classical ContDiff
abbrev optics := Metric.ball (0:ℂ) 1
abbrev light := ContinuousLinearMap.id ℝ ℂ
-- CLM ℂ to pass complex scalars in tests
abbrev heartX (X:Beam ℂ) (z:ℂ):ℂ:=Amp.shine light X z
lemma heartL (X:Beam ℂ)(v:sun): heartX X (v.val:ℂ)= read ℂ v X:= Amp.opening light X v
private lemma opticsN (X: Beam ℂ) {z:ℂ} (h:z∈optics): SumBudget (fun i=> ‖z^i*X i‖) ‖X‖:= budget_mono (togg X) (fun _=>norm_nonneg _) (fun i=>by rw [norm_mul,norm_pow]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp h|>.le)))
lemma emitsN (X:Beam ℂ) {z:ℂ} (h:z∈optics) : ‖heartX X z‖≤‖X‖:= (norm_tsum_le_tsum_norm (f:=fun i=> z^i * X i) (opticsN X h).2.1).trans (opticsN X h).2.2
def haloC {z:ℂ} (h:z∈optics) : Beam ℂ →L[ℂ] ℂ:= by
    let e:Beam ℂ →ₗ[ℂ] ℂ:= { toFun:=fun x=>heartX x z,
                               map_add':=fun x y=>by
                                  change ∑' i,z^i*((x+y) i)= (∑' i,z^i*x i)+(∑' i,z^i*y i); simp_rw [lp.coeFn_add,Pi.add_apply,mul_add]; exact Summable.tsum_add ((opticsN x h).2.1.of_norm) ((opticsN y h).2.1.of_norm),
                               map_smul':=fun c x=>by
                                  change ∑' i,z^i*((c • x) i)= c*∑' i:ℕ,z^i*x i; simp_rw [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,mul_left_comm (z^_) c]; exact tsum_mul_left }
    exact e.mkContinuous 1 (fun x=>by rw [one_mul]; exact emitsN x h)
lemma halos (x:Beam ℂ) {z:ℂ}(h:z∈optics): haloC h x=heartX x z:=rfl
lemma hearts (x:Beam ℂ): AnalyticOnNhd ℂ (heartX x) optics:=fun z hz=> Amp.hol light x z (mem_ball_zero_iff.mp hz)
lemma deluge (P:ℕ→ Beam ℂ) {X:Beam ℂ}(hv:Tendsto P atTop (𝓝 X))(K:Set ℂ)(hK:IsCompact K)(hp:K⊆optics)(d:ℕ): TendstoUniformlyOn (fun i=>iteratedDeriv d (heartX (P i))) (iteratedDeriv d (heartX X)) atTop K:=by
    have ht : BddAbove (Set.range (fun i=> ‖P i‖)):= hv.norm.bddAbove_range
    obtain ⟨C,h⟩:=ht; have hP i: ‖P i‖≤ C:= h ⟨i,rfl⟩; have hx:= le_of_tendsto' hv.norm hP
    have hh (i:ℕ): Tendsto (fun k=>P k i) atTop (𝓝 (X i)):=((lp.evalCLM ℂ (fun _:ℕ=>ℂ) 1 i).continuous.continuousAt.tendsto.comp hv) -- name
    exact (tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball).mp (version light X hx hP hh d) K hp hK
end YM.FullVolume.Amp.Beam
#print axioms YM.FullVolume.Amp.Beam.deluge
#print axioms YM.FullVolume.Amp.Beam.halos

import YM.Pert.Align.Flux
/-! Same-root contraction price from common curl stencils, including engineering powers. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pert.Align
open Lattice Topology Filter Orb Function Atom Maxwell
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {u : ℝ}
variable {j k : ℕ}
def singlePrice (a : Atom j) (b : Atom k) (u : ℝ) (p v : G.Color):=if a.rotated=b.rotated then cost a u * cost b u * inner ℝ p v * unroll a b else 0
def fluxPrice (a : Atom j) (b : Atom k) (u : ℝ) (p v : G.Color):= singlePrice a b u p v-singlePrice a (swap b) u p v-(singlePrice (swap a) b u p v-singlePrice (swap a) (swap b) u p v)
lemma single_ret (a : Atom j) (b : Atom k) (u v : G.Color) (T : Itinerary) (x : StepPath T) {z:E4} (hx:Finale T x x z) :
    Tendsto (fun m=>jointB G (T.period m) (single a (T.gap m) (x m) u) (single b (T.gap m) (x m) v)-singlePrice a b (T.gap m) u v) atTop (𝓝 0) := by
  let D:=DFactor j k*inner ℝ u v
  by_cases h : a.rotated=b.rotated; swap; · simp_rw [singlePrice,single_eval,if_neg h]; simpa using (tendsto_const_nhds (x:=0))
  have H := ((self_burst a b T).sub (final_burst a b _ _ _ z hx (step a.rotated))).const_mul D
  simp_rw [sub_zero,mul_zero] at H; refine H.congr (fun i=>?_); simp only [single_eval,singlePrice,if_pos h, sub_self,leave a b (T.positive _)];unfold D;ring
lemma two_ply {A B Z : Type*} [AddGroup A] [AddGroup B] [AddCommGroup Z] (F : A →+ B →+ Z) (u v i j) : F (u-v) (i-j)=F u i -F u j - (F v i- F v j) := by rw [F.map_sub, AddMonoidHom.sub_apply,map_sub,map_sub]
lemma flux_return (a : Atom j) (b : Atom k) (u v : G.Color) (T : Itinerary) (x : StepPath T) {z:E4} (hx:Finale T x x z):
    Tendsto (fun m=>jointB G (T.period m) (flux a (T.gap m) (x m) u) (flux b (T.gap m) (x m) v)-fluxPrice a b (T.gap m) u v) atTop (𝓝 0) := by
  have e (a:Atom j) (b:Atom k):= single_ret a b u v T x hx
  refine Tendsto.congr (fun i=>?_ ) (by simpa only [sub_zero] using ((e a b).sub (e a (swap b))).sub ((e (swap a) b).sub (e (swap a) (swap b))))
  simp only [flux,b_sub,fluxPrice];abel
lemma flux_limit (a : Atom j) (b : Atom k) (u v : G.ColorIndex) (T : Itinerary) (x y : StepPath T) {z:E4} (hz:z≠0) (h₁:Scene T x y z) (h₂:Finale T x y z) : Tendsto (fun m=>jointB G (T.period m) (flux a (T.gap m) (x m) (unitColor G u)) (flux b (T.gap m) (y m) (unitColor G v))) atTop (𝓝 (fluxTarget a b u v z)) := by
  simp_rw [flux,b_sub,← scalar_diff a b u v _ hz]
  apply Tendsto.sub (Tendsto.sub ?_ ?_) (Tendsto.sub ?_ ?_)
  all_goals exact single_limit T x y z hz h₁ h₂ _ _ _ _
section charts
def probes (u : G.Color) (q : Atom j) : Module.Dual ℝ (YM.Pert.Bare.Response G j) := (innerSL (𝕜:=ℝ) u).toLinearMap ∘ₗ -- wrong type. not use clm? convert
  (LinearMap.proj (R:=ℝ) q.γ ∘ₗ LinearMap.proj (R:=ℝ) q.channel ∘ₗ LinearMap.proj (R:=ℝ) q.slash)
def chart {Z : Type*} [AddCommGroup Z] [One Z] (j:ℕ) (s : Signed) (h:ℝ) (o : Four Z) : Lattice.Links Z G.Color →ₗ[ℝ] YM.Pert.Bare.Response G j := gain h j • (YM.Pert.Bare.wideCore G j (Lattice.affine s⁻¹ 0 o) ∘ₗ YM.Pert.Bare.wideLink G s)
def chartOrb (j : ℕ) (s : Signed) (h:ℝ) (o : Site n) : (↥(LinkP G n)) →ₗ[ℝ] YM.Pert.Bare.Response G j := chart j s h o ∘ₗ (LinkP G n).subtype
lemma pro_out (a : Atom j) (h : ℝ) (o : Site n) (u : G.Color) : probes u a ∘ₗ chartOrb j a.rot h o = flux a h o u := by
  ext v
  change inner ℝ u (chart j a.rot h o v.val a.slash a.channel a.γ) = flux a h o u v
  erw [real_inner_comm]
  unfold chart
  change inner ℝ (gain h j • (YM.Pert.Bare.wideCore G j _ (YM.Pert.Bare.wideLink G a.rot v.val) a.slash a.channel a.γ):G.Color) u = _
  rw [real_inner_smul_left]
  erw [Atom.core_combine,real_inner_smul_left,inner_sub_left]; unfold flux single; simp only [map_sum,LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul,LinearMap.sub_apply]
  simp_rw [read_wrap, sum_inner, real_inner_smul_left]

  unfold cost swap formElem; dsimp; ring_nf
end charts
end YM.Pert.Align

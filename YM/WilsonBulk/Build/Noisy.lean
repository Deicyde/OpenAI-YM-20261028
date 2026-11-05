import YM.WilsonBulk.Build.Shuffle
import YM.Work.F04.Choices
import YM.WilsonBulk.Series.Second

/-!
# Wilson branch exponent (full analytic log conditional term)

No real unnormalized density or window restriction used in algebra. Verify
germ is actual one with all tags before energy construction, supplies real
Leg identity for Taylor. Gram leading kinetic.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Atelier
open Function Filter Matrix Sheet Precision RG Exterior Lattice Wilson FreeResolvent
open Stationary (Army patron)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {α A κ : Type} [CommRing A] [Algebra ℝ A] [Fintype κ] {G : Gauge} {c f n : Side} {S : StepData c f}
attribute [local instance] Gauge.frobInner
abbrev ReadingV (G : Gauge) (c f : Side) := Tabletop (Chamber (Pennant G f) (Pennant G c))
def canonWeight (G : Gauge) (S : StepData c f) (t : S.Choices) (z : ReadingV G c f) := noiseTaylor S (signal G c (lower _ _ z)) (signal G f (upper _ _ z)) t

def breach (G : Gauge) (S : StepData c f) (x : Pennant G f→ A) (y : Pennant G c → A) : A := S.kernel.penalty • ((1/2:ℝ) • knot (y- quill (probeX G S) x) (y-quill (probeX G S) x))
lemma breach_map {B : Type} [CommRing B] [Algebra ℝ B] (W : A→ₐ[ℝ]B) (x : Pennant G f → A) (y : Pennant G c → A) : W (breach G S x y)=breach G S (fun i=>W (x i)) (fun i=>W (y i)) := by simp only [breach,knot,map_sum,map_mul,map_smul,map_sub,Pi.sub_apply,quill]
lemma canonWeight_jet (t : S.Choices) (h : S.patch.Branches S.kernel G) : ContDiffAt ℝ ω (canonWeight G S t) 0 := by
  let U := upper (Pennant G f) (Pennant G c); let L:= lower (Pennant G f) (Pennant G c); let W := traces G f 1 ∘ U
  have he : W 0=0 := by simp only [W,Function.comp_apply,map_zero]
  have hh : ContDiffAt ℝ ω W 0 := (traces G f 1).contDiff.contDiffAt.comp _ U.contDiff.contDiffAt
  have hf : Army (fun z : ReadingV G c f=> S.prediction (signal G f (U z)) t) 0:= fun e=> ((show ContDiffAt ℝ ω (fun v=> G.mat (S.prediction (represent v) t e)) (W 0) from he.symm ▸ (Push.prediction_cont S h e t)).comp _ hh)
  let H z:= signal G c (L z)
  have hx : Army H 0:= signal_force L.contDiff.contDiffAt
  refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun i _=>?_) -- def unfold
  exact Work.F03.price_smooth (A:=fun z=> (H z* (S.prediction (signal G f (U z)) t)⁻¹) i) ((hx.mul hf.inv) i)

abbrev static (G : Gauge) (S : StepData c f) : Formula (Chamber (Pennant G f) (Pennant G c)) := breach G S (fun i=>MvPolynomial.X (Sum.inl i)) (fun j=>MvPolynomial.X (Sum.inr j))
lemma pay_breach : PowerSeries.C (static G S) = breach G S (privateName (ι:=Pennant G c)) viewer := breach_map (S:=S) (post (Formula (Chamber (Pennant G f) (Pennant G c)))) (fun i=> MvPolynomial.X (Sum.inl i)) (fun i=> MvPolynomial.X (Sum.inr i))
lemma w_f_tow (x : ReadingV G c f) : MvPolynomial.eval x (static G S) = breach G S (upper _ _ x) (lower _ _ x) := by
  change MvPolynomial.aeval x _= _; rw [static,breach_map]; simp_rw [MvPolynomial.aeval_X]; rfl

lemma tuned_root (z : ReadingV G c f) (t : S.Choices) (h : S.patch.Branches S.kernel G) : Tendsto (fun w:ℝ=> canonWeight G S t (w • z) / w^2) (𝓝[≠] 0) (𝓝 (breach G S (upper _ _ z) (lower _ _ z))) := by
  let x := upper (Pennant G f) (Pennant G c) z; let y:= lower (Pennant G f) (Pennant G c) z
  let zz : Work.F03.Logs G c f := (traces G c 1 y, traces G f 1 x)
  let a := Work.F03.residual S zz
  have hi : flatten a=y-quill (probeX G S) x := by
    suffices he : flatten (Bid.bills S (traces G f 1 x))=quill (probeX G S) x by
      rw [← he]; ext1 ⟨i,j,k⟩; rfl
    unfold probeX; rw [quill_real,match_tensor]; ext1 i; rcases i with ⟨i,j,k⟩; change _=component (tensor _ _ *ᵥ x) k (i,j)
    rw [component_mul]; rfl
  have hz : ∑ i:Body 1 c, inner ℝ (a i) (a i)=knot (y-quill (probeX G S) x) (y-quill (probeX G S) x):= by rw [← flat_dot a a, ← hi]; rfl
  have hw:= Work.F03.noise_limit h t zz; change Tendsto _ _ (𝓝 (S.kernel.penalty * (∑ i:Body 1 c, inner ℝ (a i) (a i))/2)) at hw; rw [hz] at hw;
  convert hw using 1
  · ext1 x; simp only [canonWeight,signal,map_smul]; rfl
  apply congr_arg; unfold breach; simp only [x,y,smul_eq_mul] at *; ring

variable (G S)
def gossip (t : S.Choices) : StageD (Pennant G f) (Pennant G c) := zoom (zoom (ink (canonWeight G S t)))
variable {G S}
lemma gossip_line (t : S.Choices) (h : S.patch.Branches S.kernel G) :
    PowerSeries.X^2* gossip G S t= ink (canonWeight G S t) ∧ Steps 1 (gossip G S t) (breach G S (privateName (ι:=Pennant G c)) viewer) := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩:= ink_floor (canonWeight_jet t h) (static G S) (fun i=> by rw [w_f_tow]; exact tuned_root i t h)
  constructor
  · rw [pow_two,mul_assoc,gossip, zoom_key, zoom_key]; · exact ink_root h₁
    rw [zoom_const]; exact h₄
  rw [steps_initial,gossip,← pay_breach]; rw [zoom_const,zoom_power,h₅,PowerSeries.constantCoeff_C]
-- clarify actual likelihood normalized at fixed fine
lemma total_branch (t : S.Choices) (h : S.patch.Branches S.kernel G) : ∀ᶠ x in 𝓝 (1:Config G f), ∀ β:ℝ, ∀ y:Config G c,
    S.density β x y= ((S.penaltyZ β G)⁻¹)^ (Fintype.card (Edge (Site c))) * Real.exp (-β * noiseTaylor S y x t) := by
  filter_upwards [eventually_all.mpr (fun i:S.Choices=> Work.F04.prediction_germ h i t)] with x hx
  intro β y
  unfold StepData.density; simp_rw [hx]; rw [← Finset.sum_mul,S.chosen h x,one_mul]
  unfold StepData.noise; rw [Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ]; exact congr_arg _ (by unfold noiseTaylor StepData.penaltyWeight; rw [← mul_assoc _ S.kernel.penalty, Finset.mul_sum, Real.exp_sum])
-- invariants under reroute, tag any
lemma prediction_ward (k : Site f→G.El) (x : Config G f) (t) (h : S.patch.Branches S.kernel G) : S.prediction (Lattice.gauge k x) t=Lattice.gauge (k ∘ S.ratio.embed) (S.prediction x t) := by
  funext i; unfold StepData.prediction; rw [S.updateGauged h, (S.patch.bond_gauge (h:=h) ..).2]; rfl
lemma noise_ward (k : Site f→G.El) (x : Config G f) (y : Config G c) (t) (h : S.patch.Branches S.kernel G) :
    noiseTaylor S (Lattice.gauge (k ∘ S.ratio.embed) y) (Lattice.gauge k x) t=noiseTaylor S y x t := by
  unfold noiseTaylor; rw [prediction_ward k _ _ h]; congr 1; refine Finset.sum_congr rfl fun i _=>?_ ; unfold Lattice.gauge
  have hp (x y a b : G.El) : G.price (a*x*b⁻¹*(a*y*b⁻¹)⁻¹)=G.price (x*y⁻¹) := by rw [show a*x*b⁻¹*(a*y*b⁻¹)⁻¹=a*(x*y⁻¹)*a⁻¹ by group,G.price_conj]
  rw [hp]
lemma noise_spin (s : Signed) (b : Site c) (x : Config G f) (y : Config G c) (t) (h : S.patch.Branches S.kernel G) : noiseTaylor S (pull s b y) (pull s (S.ratio.embed b) x) t=noiseTaylor S y x (S.withinChoice s b t) := by
  unfold noiseTaylor; rw [S.prediction_channel h]; conv_rhs => rw [← Equiv.sum_comp (StepData.sendBonds s b)]
  congr 1; refine Finset.sum_congr rfl fun i _=>?_; unfold pull Step.read; split
  · have he (x y:G.El):G.price (x⁻¹*(y⁻¹)⁻¹)=G.price (x*y⁻¹):= by rw [← G.price_inv (x*y⁻¹), show (x*y⁻¹)⁻¹=x*(x⁻¹*(y⁻¹)⁻¹)*x⁻¹ by group,G.price_conj]
    exact he ..
  rfl
end YM.WilsonBulk.Atelier

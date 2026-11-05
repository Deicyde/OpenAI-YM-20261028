import YM.Further.ROOTED_INTERACTING_REMAINDER.Levy
import YM.Further.ROOTED_INTERACTING_REMAINDER.Normalization
import YM.Further.ROOTED_INTERACTING_REMAINDER.Radius
/-!
# Intact all-volume constant money

Survey actual `leftOver` * pointwise growth queries. Prove a constant
budget PER SITE on partition normalized integral for arbitrarily many copies,
and also retaining **half the actual coarse sieve** even pointwise, with scalar
jump normalization (for this second result see file Pulse; requires
post-Gaussian Counter incl flat matches). Hitting-norm versions still
separate. All residual assumptions here before the Gaussian work. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder.Levy
open MeasureTheory Filter Function Lattice RG RG.Supply Axial Wilson Finset Precision Tree
open Pressure Pressure.Stores Pressure.Teller Pressure.Tube Bid Next.Fluctuations
open Next.Fluctuations.Sector Push.SectorMeasure Oriented Presented SectorNext.Vacuum
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x W : ℝ}
    {F : Forest S.ratio} {T : Tube G S} {P : Teller G} {R : Rep G f} {D : Allocation G S x W}
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {g : GaugeProbe G S F X}

local notation "t" => fiery G x S.patch.L
local notation "Δ" => Module.finrank ℝ G.Color
local notation "eV" => Fintype.card (Bond c)
local notation "nP" => Fintype.card PlaqAxes
local notation "ΔI" => rich f+eV
local notation "ΔV" => rich f+(Fintype.card (Site c)-1)

def halfprice (T : Tube G S) (x β : ℝ) (V : Config G c) :=
    Real.exp (-(β/2)*averaged (fun i=>coarse T x (pull i 0 V)))
lemma halfprice_pos (T : Tube G S) (x β : ℝ) (V : Config G c) : 0<halfprice T x β V := Real.exp_pos _


private lemma exp_cost {η τ : ℝ} (hη : 0<η) (ht : 0<τ) : ∀ v : ℝ, Real.exp (-(τ^2)*(η*v^2)) ≤ Real.exp η⁻¹*Real.exp (-τ*v) := by
  intro v
  have he := sq_nonneg (η*τ*v-1/2)
  have h1 := mul_inv_cancel₀ hη.ne'
  rw [←Real.exp_add]; apply Real.exp_monotone
  apply le_of_mul_le_mul_left (a:=η) _ hη; nlinarith only [he,h1]

/-- Kinetic growth bill. Physical probe on *intact* profiled question; ALL
threshold and tag dependencies may be read. Needs no relation to an E/K
label denominator. Allows e.g. gauge-scale polynomial in all plaquette
fluctuations simultaneously even on defect complements. Not after
post-hole change of coordinates/marginals. -/
structure Elastic (R : Rep G f) (F : Forest S.ratio) (T : Tube G S) (D : Allocation G S x W)
    (g : GaugeProbe G S F X) (b q θ φ : ℝ) : Prop where
  stretch (A : Stores S) (i) (a : F.Slice G) (V : Config G c) : D.bill A i (F.drape a) V ≠ 0 → Alive S (F.drape a) i →
    ‖g A i (a,V)‖ ≤ Real.exp (b*sites c + q*(R.beta*t^2*A.shares))*
      Real.exp (R.beta*(θ*coin A x (F.drape a) (S.prediction (F.drape a) i) V+φ*averaged (fun j=>coarse T x (pull j 0 V))))

lemma inflexible (T : Tube G S) {b q θ φ : ℝ} (hθ : 0≤θ) (hφ : 0≤φ) (hβ : 0≤R.beta)
    (h : CargoBill R D F g b q) : Elastic R F T D g b q θ φ := by
  constructor
  intro A i a V hd he
  have hn := coin_nn (G:=G) A x (F.drape a) (S.prediction (F.drape a) i) V
  have ht : 0 ≤ averaged (fun j=>coarse T x (pull j 0 V)) :=
    (av_const (0:ℝ)).symm.le.trans (av_mono fun i=>coarse_nn ..)
  exact (h.issues A i a V hd he).trans (le_mul_of_one_le_right (Real.exp_pos _).le
    (Real.one_le_exp (by positivity)))

def kinetic (T : Tube G S) (x β χ : ℝ) (V : Config G c) :=
    Real.exp (-(β*χ)*averaged (fun i=>coarse T x (pull i 0 V)))
lemma kinetic_pos (T : Tube G S) (x β χ : ℝ) (V : Config G c) : 0<kinetic T x β χ V := Real.exp_pos _
lemma kinetic_one (T : Tube G S) (x β χ : ℝ) (h : 0≤β) (hc : 0≤χ) (V : Config G c) : kinetic T x β χ V ≤ 1 := by
  apply Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by nlinarith) ?_)
  exact (av_const (0:ℝ)).symm.le.trans (av_mono fun i=>coarse_nn ..)
lemma half_kinetic (T : Tube G S) (x β : ℝ) (V : Config G c) : kinetic T x β (1/2) V=halfprice T x β V := by
  unfold kinetic halfprice; ring_nf

-- exactly the holes: per-turn store is not needed in the conclusion
private def mapped (A : Stores S) (x : ℝ) : Stores S := ⟨A.limit x,A.intern x,A.flags⟩
private def ante (A : Stage) (b Λ δ η : ℝ) (R : Rep G f) (x : ℝ) (c : Side) := sites f*(R.exCost A.paths Λ δ + R.beta*(nP*wound A.width A.paths R.p.threshold (till x) 1)) + (b+1)*sites c +
    (Fintype.card (Cell f)+ (Fintype.card (Bond c):ℝ))*η⁻¹

private lemma reduction (ρ : Teller G) {b q δ y Λ τ K κ θ χ : ℝ}
    (h : Elastic R F T D g b q θ (1/2-χ))
    (s : Survey ρ S T F R x W 1 Λ δ y K τ κ (κ/4) (κ/4))
    {η ξ : ℝ} (hp : 0<η) (hξ : η+θ=ξ)
    (H : ∀ A U k V,SliceSet S F U → Alive S U k → Seeded A U k V x W →
          R.beta*(ξ*coin A x U (S.prediction U k) V) - sites c ≤ R.beta*(meanRest A T x U k V + averaged (fun j=>coarse T x (pull j 0 V))/2))
    (A : Stores S) (i : S.Choices) (a : F.Slice G) (V : Config G c) :
    let L := kinetic T x R.beta χ V * Real.exp (ante ρ.top b Λ δ η R x c + q*(R.beta*t^2*A.shares))
    sieve T R.beta x V * (D.bill A i (F.drape a) V * carrier (x:=x) F T R g A i V a) ≤
      L*flight (mapped A x) τ⁻¹ i V (F.drape a) := by
  intro L
  let U := F.drape a
  have ht := zero_lt_one.trans_le s.lift
  have hr : 0≤R.beta := s.rate.symm ▸ sq_nonneg _
  have hw := s.hot
  have hV := kinetic_pos T x R.beta χ V
  have hL : 0≤L := mul_nonneg hV.le (Real.exp_pos _).le
  have hm := mul_nonneg hL (flight_nonneg (mapped A x) τ⁻¹ i V U)
  by_cases h0 : D.bill A i U V = 0
  · change sieve _ _ _ V*(D.bill A i U V*_) ≤ _; rw [h0,zero_mul,mul_zero]; exact hm
  by_cases ha : Alive S U i
  swap
  · change sieve _ _ _ V*(D.bill A i U V*(_*_*(S.likelihood U i*_))) ≤ _
    simp_rw [dead ha,zero_mul,mul_zero]; exact hm
  let C := averaged fun j=>coarse T x (pull j 0 V)
  let m := meanRest A T x U i V
  let r := coin A x U (S.prediction U i) V
  let W' := Real.exp (R.beta*(θ*r+(1/2-χ)*C))
  have hw' : 0 ≤ W' := (Real.exp_pos _).le
  have he : W'*(sieve T R.beta x V * Real.exp (-R.beta*m)) ≤ kinetic T x R.beta χ V * Real.exp (sites c-(R.beta*(η*r))) := by
    unfold kinetic W'; change Real.exp _*(Real.exp (-R.beta*C)*Real.exp _)≤ Real.exp (-(R.beta*χ)*C)*Real.exp _
    repeat rw [←Real.exp_add]
    apply Real.exp_monotone; have hz := H A U i V (fun i hI=>F.on_tree _ ⟨i,hI⟩) ha (D.actual _ _ _ _ <| h0)
    change R.beta*(ξ*r)-sites c ≤ R.beta*(m+C/2) at hz
    rw [←hξ] at hz; linarith only [hz]
  have hF {J : Type} [Fintype J] (z : Finset J) (u : J → G.El) :
      Real.exp (-R.beta*(η*∑ j∈z,(G.chord (u j))^2)) ≤ Real.exp (Fintype.card J*η⁻¹)*∏ i∈z,draught τ (u i) := by
    have hx : Real.exp (-R.beta*(η*∑ j∈z,(G.chord (u j))^2)) = ∏ i∈z,Real.exp (-R.beta*(η*(G.chord (u i))^2)) := by
      rw [Finset.mul_sum,Finset.mul_sum,Real.exp_sum]
    rw [hx,s.rate]
    calc
      _ ≤ ∏ i∈z,(Real.exp η⁻¹*draught τ (u i)) := prod_le_prod (fun i _ => (Real.exp_pos (-(τ^2)*(η*(G.chord (u i))^2))).le) (fun i _=>exp_cost hp ht _)
      _ ≤ _ := by
        rw [prod_mul_distrib,prod_const,←Real.exp_nat_mul];
        exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_univ _)) (by positivity))) (prod_nonneg (fun i _ => (Real.exp_pos _).le))
  let pM := sites f*(R.exCost ρ.top.paths Λ δ + R.beta*(nP*(wound ρ.top.width ρ.top.paths R.p.threshold (till x) 1)))
  let w := Real.exp (b*sites c + q*(R.beta*t^2*A.shares))
  let z := S.likelihood U i
  have hf := h.stretch A i a V h0 ha
  have hB := launched ρ.top s.input s.cut hr s.halt (till x) U
  let N := ‖Real.exp (-R.scalar)*exposed R (till x) U‖
  let Y := ‖g A i (a,V)‖
  have H1 : D.bill A i U V * N *Y*z ≤ Real.exp pM * (w*W') * z :=
    mul_le_mul_of_nonneg_right (mul_le_mul
      ((mul_le_of_le_one_left (by unfold N; positivity) (D.range ..)).trans hB) hf (norm_nonneg _) (Real.exp_pos _).le) (S.likelihood_pos ..)
  let Q := S.prediction U i
  let u := ration (mapped A x).costs τ⁻¹ U
  let j := gapper (mapped A x).aisles τ⁻¹ V Q
  let v : ℝ := Fintype.card (Cell f) * η⁻¹
  let k : ℝ := eV * η⁻¹
  have hT : Real.exp (-R.beta*(η*r)) ≤ Real.exp (v+k)*(u*j) := by
    unfold r coin; rw [mul_add,mul_add,Real.exp_add,Real.exp_add]
    unfold u j v k ration gapper; simp only [mapped,inv_inv]
    let x₁ := (∑ i ∈ (A.limit x)ᶜ,(toll U i)^2)
    let x₂ := (∑ i ∈ (A.intern x)ᶜ,(wire Q V i)^2)
    change Real.exp (-R.beta*(η*x₁))*Real.exp (-R.beta*(η*x₂)) ≤ _
    rw [mul_mul_mul_comm]
    exact mul_le_mul (hF _ (faceValue U)) (hF _ (fun i=>V i*(Q i)⁻¹)) (Real.exp_pos _).le
      (mul_nonneg (Real.exp_pos _).le (prod_nonneg (fun i _=> (Real.exp_pos _).le)))
  unfold carrier leaves
  change sieve T _ _ V*(D.bill A i U V*(N*Y*(z*Real.exp (-R.beta*m)))) ≤ _
  have hy1 := mul_le_mul_of_nonneg_right H1 (show 0 ≤ sieve T R.beta x V * Real.exp (-R.beta*m) by unfold sieve; positivity)
  have hQ := mul_le_mul_of_nonneg_left he (a:=Real.exp pM*w*z) (by
    unfold z w; have h := S.likelihood_pos U i; positivity)
  calc
    _ = D.bill A i U V*N*Y*z*(sieve T R.beta x V*Real.exp (-R.beta*m)) := by ring
    _ ≤ _ := hy1
    _ = Real.exp pM * w * z * (W'*(sieve T R.beta x V*Real.exp (-R.beta*m))) := by ring
    _ ≤ _ := hQ
    _ = Real.exp pM * w * z * (kinetic T x R.beta χ V*(Real.exp (sites c)*Real.exp (-R.beta*(η*r)))) := by rw [sub_eq_add_neg,Real.exp_add,neg_mul]
    _ ≤ Real.exp pM * w * z * (kinetic T x R.beta χ V*(Real.exp (sites c)*(Real.exp (v+k)*(u*j)))) := by
      have hW : 0≤w := (Real.exp_pos _).le; have hx : 0≤z := S.likelihood_pos ..; gcongr
    _ = _ := by unfold pM w z v k u j Q U L ante flight; simp_rw [Real.exp_add,add_mul,one_mul,Real.exp_add]; ring

/-- Stronger station test, produced in `branch` and `cash_holes`.
We don't import a solution of RG step to buy it. -/
structure Ample (T : Tube G S) (x W β κ η : ℝ) (F : Forest S.ratio) : Prop where
  quote : 0<η
  remaining : ∀ A U k V,SliceSet S F U → Alive S U k → Seeded A U k V x W →
    β*(η*coin A x U (S.prediction U k) V) - sites c ≤ β*(meanRest A T x U k V + averaged (fun j=>coarse T x (pull j 0 V))/2)
  cash : Real.exp (-(κ/2)*(β*(fiery G x S.patch.L)^2))*(Real.sqrt β^Δ)^(density S.patch.L x) ≤ 1

private lemma seals (ρ : Teller G) {κ b δ y Λ τ K K' η θ χ ξ : ℝ}
    (h : Elastic R F T D g b (κ/4) θ (1/2 - χ)) (hξ : η+θ=ξ) (hi' : 0<η) (ht1 : 0≤χ)
    (s : Survey ρ S T F R x W 1 Λ δ y K τ κ (κ/4) (κ/4))
    (a : Ample T x W R.beta κ ξ F)
    (hk : 1≤K') (hc : 2≤c.val) (hS : (∫ i,draught (τ⁻¹)⁻¹ i ∂G.probHaar) ≤ K'*(τ⁻¹)^Δ)
    (A : Stores S) (he : ∀ i,Envelope (g A i)) :
    let L := Real.exp (ante ρ.top b Λ δ η R x c)
    let C := Real.exp (-(κ/4)*(R.beta*t^2*A.shares))
    let P := prefactor S G R.beta*L
    (∀ V,earn S G x κ R.beta A.shares*cargo F T R D g A V ≤
      P * (K'*τ⁻¹^Δ)^ΔV * C * kinetic T x R.beta χ V) ∧
      (∫ V,(earn S G x κ R.beta A.shares*cargo F T R D g A V)∂prior G c) ≤
      P * (K'*τ⁻¹^Δ)^ΔI * C := by
  intro L C P
  have ht := s.lift; have hT : 0<τ := zero_lt_one.trans_le ht
  have hh : τ⁻¹ ≤ 1 := by simpa using inv_anti₀ zero_lt_one ht
  let α := R.beta*t^2
  let M := mapped A x
  let r := L*Real.exp (κ/4*(α*A.shares))
  let g' := flight (G:=G) M τ⁻¹
  let z := fun V => ∑ k : S.Choices,∫ i:F.Slice G, g' k V (F.drape i) ∂F.order G
  have h (V) : cargo F T R D g A V ≤ kinetic T x R.beta χ V * r * z V := by
    have hf := (fun k i=>reduction (κ:=κ) (χ:=χ) ρ h s hi' hξ a.remaining A k i V)
    unfold cargo z Allocation.column tagTotal
    rw [Finset.mul_sum,Finset.mul_sum]
    apply sum_le_sum; intro k _
    rw [←integral_const_mul,←integral_const_mul]
    let V' := F.Slice G×Config G c
    have he' : Measurable (fun i : F.Slice G=> (i,V)) := measurable_id.prodMk measurable_const
    let f (p' : V') := D.bill A k (F.drape p'.1) p'.2*carrier (x:=x) F T R g A k p'.2 p'.1
    have h1 : Envelope f := (actual F R D g s.supports s.input A k (he k)).1
    have hi : Integrable (fun i:F.Slice G=>f (i,V)) (F.order G) :=
      Env.integrableX (Env.along (g:=fun i:F.Slice G=> (i,V)) h1 he') _
    refine integral_mono (hi.const_mul _) (((wing (funds_branch s.supports) M τ⁻¹ k (V:=fun (_:F.Slice G)=>V) measurable_const F.continuous_drape.measurable).integrable _).const_mul _) ?_
    intro i
    exact (hf k i).trans_eq (by dsimp only [r,L,g',α,M]; rw [Real.exp_add])
  let N := M.costs.card+M.aisles.card
  let Q := fun j:ℕ=> (K'*τ⁻¹^Δ)^j*(τ^Δ)^N
  have heC : Real.sqrt R.beta=τ := by rw [s.rate,Real.sqrt_sq hT.le]
  have hQ : Real.exp (-(κ/2)*(α*A.shares))*(τ^Δ)^N ≤ 1 := calc
    _ ≤ Real.exp (-(κ/2)*(α*A.shares))*(τ^Δ)^(density S.patch.L x*A.shares) := by
      apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_pow₀ ht) (unit_density ..)) (Real.exp_pos _).le
    _ = (Real.exp (-(κ/2)*(R.beta*t^2))*(Real.sqrt R.beta^Δ)^(density S.patch.L x))^A.shares := by
      rw [mul_pow, heC, pow_mul (τ^Δ),←Real.exp_nat_mul]; congr 2; unfold α; ring
    _ ≤ _ := pow_le_one₀ (by positivity) a.cash
  have hy (j) : earn S G x κ R.beta A.shares * r * Q j ≤ P*(K'*τ⁻¹^Δ)^j*C := by
    have hx : 0≤P*(K'*τ⁻¹^Δ)^j*C := by
      have hK' : 0<K' := zero_lt_one.trans_le hk
      have h0 : 0<P := mul_pos (prefactor_pos R.beta) (Real.exp_pos _); have hC : 0<C := Real.exp_pos _; positivity
    calc
      _ = P*(K'*τ⁻¹^Δ)^j*C * (Real.exp (-(κ/2)*(α*A.shares))*(τ^Δ)^N) := by
        have he : Real.exp (-R.beta*(κ*t^2*A.shares))*Real.exp (κ/4*(α*A.shares)) = C*Real.exp (-(κ/2)*(α*A.shares)) := by
          unfold C α; rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
        unfold r Q earn P
        calc
          _ = prefactor S G R.beta * L * ((K'*τ⁻¹^Δ)^j*(τ^Δ)^N) *
            (Real.exp (-R.beta*(κ*t^2*A.shares))*Real.exp (κ/4*(α*A.shares))) := by ring
          _ = _ := by rw [he]; ring
      _ ≤ _ := mul_le_of_le_one_right hx hQ
  have hNN : 0≤r := by unfold r L; positivity
  constructor
  · intro V
    have hp := (kinetic_pos T x R.beta χ V).le
    have hc := circuit F M τ⁻¹ K' V hc (funds_branch s.supports) (inv_pos.mpr hT) hh hk hS
    rw [inv_inv] at hc
    calc
      _ ≤ earn S G x κ R.beta A.shares*(kinetic T x R.beta χ V*r*Q ΔV) := by
        apply mul_le_mul_of_nonneg_left _ (earn_pos ..).le
        exact (h V).trans (mul_le_mul_of_nonneg_left hc (mul_nonneg hp hNN))
      _ = earn S G x κ R.beta A.shares * r * Q ΔV * kinetic T x R.beta χ V := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hy _) hp
  have hi : Integrable z (prior G c) := by
    unfold z; apply integrable_finsetSum; intro i _
    exact (Env.marginal (g:=fun p:F.Slice G×Config G c=>g' i p.2 (F.drape p.1))
      (wing (funds_branch s.supports) M τ⁻¹ i (V:=Prod.snd) measurable_snd (F.continuous_drape.measurable.comp measurable_fst)) (F.order G)).integrable _
  have hl := circulation F M τ⁻¹ K' (hc.trans (by rw [S.sizes]; exact Nat.le_mul_of_pos_right _ S.patch.L.property)) (funds_branch s.supports) (inv_pos.mpr hT) hh hk hS
  change (∫ V,z V ∂prior G c) ≤ _ at hl
  rw [inv_inv] at hl
  calc
    _ ≤ ∫ V,(earn S G x κ R.beta A.shares*r)*z V ∂prior G c := by
      apply integral_mono (((cargo_portable F R D g s.supports s.input A he).integrable _).const_mul _)
        (hi.const_mul _)
      intro V; dsimp only; rw [mul_assoc]; refine mul_le_mul_of_nonneg_left ((h V).trans ?_) (earn_pos ..).le
      apply mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hNN (kinetic_one T x _ χ (s.rate.symm ▸ sq_nonneg _) ht1 V))
        (sum_nonneg (fun i _ => integral_nonneg (fun j=>flight_nonneg ..)))
    _ ≤ earn S G x κ R.beta A.shares*r*Q ΔI := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hl (mul_nonneg (earn_pos ..).le hNN)
    _ ≤ _ := hy _

/-- Per-volume pressure bill. Encoding it besides `rental` also covers all
ε profile widths even when used for typified LF integrations at very
small κ. -/
def duty (R : Rep G f) (ρ : Stage) (b Λ δ η x : ℝ) (n : Side) := ante ρ b Λ δ η R x n + supplicant n f

/-- Intact absolute remainder arrays (summed over true bookings). -/
theorem fulcrum (ρ : Teller G) {κ b δ y Λ τ K K' η θ χ ξ : ℝ}
    (h : Elastic R F T D g b (κ/4) θ (1/2 - χ)) (hξ : η+θ=ξ) (hi' : 0<η) (ht1 : 0≤χ) (he : ∀ A i,Envelope (g A i))
    (s : Survey ρ S T F R x W 1 Λ δ y K τ κ (κ/4) (κ/4))
    (a : Ample T x W R.beta κ ξ F)
    (hk : 1≤K') (hc : 2≤c.val) (hS : (∫ i,draught (τ⁻¹)⁻¹ i ∂G.probHaar) ≤ K'*(τ⁻¹)^Δ)
    (Y : Finset (Stores S)) (n : ℕ) (hY : ∀ A∈Y,n≤A.shares) :
    let L := Real.exp (duty R ρ.top b Λ δ η x c)
    let e := fun u : ℕ => Real.exp (-(κ/4)*(R.beta*t^2*u))
    let P := prefactor S G R.beta*L
    (∀ V,itinerary F T R D g κ Y V ≤
      P * (K'*τ⁻¹^Δ)^ΔV * e (max n (RG.flags (temp x) V).card) * kinetic T x R.beta χ V) ∧
      (∫ V,itinerary F T R D g κ Y V ∂prior G c) ≤ P * (K'*τ⁻¹^Δ)^ΔI * e n := by
  intro L e P
  let E := fun j : ℕ => prefactor S G R.beta * Real.exp (ante ρ.top b Λ δ η R x c) * (K'*τ⁻¹^Δ)^j
  have ht : 0 < τ := zero_lt_one.trans_le s.lift
  have hE j : 0≤E j := mul_nonneg (mul_nonneg (prefactor_pos _).le (Real.exp_pos _).le) (by have := hk; positivity)
  have h := fun A => seals (η:=η) (χ:=χ) ρ h hξ hi' ht1 s a hk hc hS A (he A)
  have hm : Antitone e := by
    intro i j hij
    apply Real.exp_monotone
    exact mul_le_mul_of_nonpos_left (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij)
      (mul_nonneg (s.rate.symm ▸ sq_nonneg _) (sq_nonneg _))) (neg_nonpos.mpr s.active)
  have hX (u : ℝ) (j : ℕ) (hU : 0≤u) : (∑ i∈Y,E j*u) ≤ P*(K'*τ⁻¹^Δ)^j*u := by
    rw [sum_const,nsmul_eq_mul]
    apply le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_univ _)) (mul_nonneg (hE _) hU))
    refine le_of_eq ?_
    unfold E P L duty; rw [plural,Real.exp_add]; ring
  constructor
  · intro V
    let l := max n (RG.flags (temp x) V).card
    let w := kinetic T x R.beta χ V
    have hw := (kinetic_pos T x R.beta χ V).le
    rw [mul_assoc (P * _) _ (kinetic T _ _ _ _)]
    refine le_trans ?_ (hX _ _ (show 0≤ e l*w from mul_nonneg (Real.exp_pos _).le hw))
    unfold itinerary; refine sum_le_sum fun i hi => ?_
    by_cases hh : RG.flags (temp x) V=i.flags
    · have he : l ≤ i.shares := by unfold l; rw [hh]; exact max_le (hY i hi) (by unfold Stores.shares; omega)
      rw [←mul_assoc]
      exact ((h i).1 V).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hm he) (hE _)) hw)
    rw [sees_flags (T:=T) (F:=F) (D:=D) (g:=g) (R:=R) hh,mul_zero]
    exact mul_nonneg (hE _) (mul_nonneg (Real.exp_pos _).le hw)
  refine le_trans ?_ (hX _ _ (show 0≤ e n from (Real.exp_pos _).le))
  unfold itinerary; rw [integral_finsetSum]
  · exact sum_le_sum fun i hi=> ((h i).2).trans (mul_le_mul_of_nonneg_left (hm (hY i hi)) (hE _))
  exact fun i _ => ((cargo_portable F R D g s.supports s.input _ (he _)).integrable _).const_mul _

/-- Intact absolute remainder arrays (summed over true bookings). -/
theorem relay (ρ : Teller G) {κ b δ y Λ τ K K' η : ℝ}
    (h : CargoBill R D F g b (κ/4)) (he : ∀ A i,Envelope (g A i))
    (s : Survey ρ S T F R x W 1 Λ δ y K τ κ (κ/4) (κ/4))
    (a : Ample T x W R.beta κ η F)
    (hk : 1≤K') (hc : 2≤c.val) (hS : (∫ i,draught (τ⁻¹)⁻¹ i ∂G.probHaar) ≤ K'*(τ⁻¹)^Δ)
    (Y : Finset (Stores S)) (n : ℕ) (hY : ∀ A∈Y,n≤A.shares) :
    let L := Real.exp (duty R ρ.top b Λ δ η x c)
    let e := fun u : ℕ => Real.exp (-(κ/4)*(R.beta*t^2*u))
    let P := prefactor S G R.beta*L
    (∀ V,itinerary F T R D g κ Y V ≤
      P * (K'*τ⁻¹^Δ)^ΔV * e (max n (RG.flags (temp x) V).card) * halfprice T x R.beta V) ∧
      (∫ V,itinerary F T R D g κ Y V ∂prior G c) ≤ P * (K'*τ⁻¹^Δ)^ΔI * e n := by
  simp_rw [← half_kinetic]
  apply fulcrum (ξ:=η) (θ:=0) (η:=η) (χ:=1/2) ρ _ (add_zero _) a.quote (by norm_num) he s a hk hc hS Y n hY
  exact inflexible _ le_rfl (by norm_num) (s.rate.symm ▸ sq_nonneg _) h

lemma duty_rental (R : Rep G f) (ρ : Stage) (b Λ δ W η x : ℝ) (wp : 0≤W) (hp : 0≤η) :
    duty R ρ b Λ δ η x c ≤ rental c R ρ 1 x W b Λ δ + (sites f*nP+sites c*4)*η⁻¹ := by
  unfold duty rental ante rooms
  have hi : (Fintype.card (Cell f):ℝ)=sites f * nP := by simp [sites,Cell,Site,Face]
  have hS : (eV:ℝ)=sites c*4 := wires_sites c
  rw [hi,hS]
  let y : ℝ := nP
  have he := (site_pos c).le
  have hG : 0 ≤ sites f*y := mul_nonneg (site_pos _).le (Nat.cast_nonneg _)
  linarith [mul_nonneg he wp]

end YM.Further.RootedInteractingRemainder.Levy

import YM.Pert.Align.Bilateral
/-!
Pair each independently averaged stencil with the inverse turn *on free equation solution slots*. No rotation of the relative endpoint positions.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
noncomputable section
namespace YM.Pert.Align
open Lattice Filter Maxwell Full Labels MeasureTheory Atom
open scoped Topology BigOperators Classical
variable {G : Gauge} {j k:ℕ} {n : Side}
abbrev TaylorDual (G : Gauge) (j : ℕ) := Module.Dual ℝ (Labels.Taylor G j)
def reduc (s : Signed) (P : TaylorDual G j) : Pad G j := P ∘ₗ Labels.Taylor.turn s.ortho ∘ₗ YM.Pert.Bare.radialMap
lemma plain_reduc (s : Signed) (P : TaylorDual G j) : plain s (reduc s P) = P ∘ₗ Maxwell.gaugeJet := by
  apply LinearMap.ext; intro y
  change P (Labels.Taylor.turn s.ortho (YM.Pert.Bare.radialize (sampleSol s y))) = _
  have he := Maxwell.match_leg (Push.FiniteDetection.Free.Hyper.turn s y)
  rw [show sampleSol s y = YM.Pert.Bare.components (gaugeJet (Push.FiniteDetection.Free.Hyper.turn s y)) from by
    unfold YM.Pert.Bare.components; rw [he]; rfl, YM.Pert.Bare.complete, Push.FiniteDetection.Free.Hyper.gaugeTurn,
    ← Labels.Taylor.turn_mul]; simp

def cAvg := (Fintype.card Signed:ℝ)⁻¹
lemma wide_avg {Z : Type*} [AddCommGroup Z] [One Z] (x : Four Z) (h : ℝ) (a : Lattice.Links Z G.Color) (P : TaylorDual G j) :
    P (YM.Pert.Bare.wideLinear G j h x a) = cAvg * ∑ s : Signed, reduc s P (chart j s h x a) := by
  unfold YM.Pert.Bare.wideLinear cAvg chart
  simp only [LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.sum_apply,map_smul,map_sum,smul_eq_mul]
  apply congrArg ((Fintype.card Signed:ℝ)⁻¹ * ·); apply Finset.sum_congr rfl; intro s _
  rw [reduc]; simp [gain]

def tayForm (z : E4) (hz : z≠0) : Biform (TaylorDual G j) (TaylorDual G k) := under (pairing hz) (pickDual Maxwell.gaugeJet) (pickDual Maxwell.gaugeJet)
lemma synth_turn (s t : Signed) (z : E4) (hz : z≠0) (P : TaylorDual G j) (Q : TaylorDual G k) : synthesis z hz s t (reduc s P) (reduc t Q) = tayForm z hz P Q := by rw [synthesis, tayForm, under_at, under_at,plain_reduc,plain_reduc];rfl
lemma slope_avg (x : Site n) (h : ℝ) (P : TaylorDual G j) : P ∘ₗ YM.Pert.Bare.slope h x j = cAvg • ∑ s : Signed, reduc s P ∘ₗ chartOrb j s h x := by
  apply LinearMap.ext; intro y
  change P (YM.Pert.Bare.slope h x j y) = _
  rw [←YM.Pert.Bare.slope_eq,wide_avg]
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul]; rfl
abbrev D := Signed × Signed
def duo (f : Signed → Signed → ℝ) := cAvg*cAvg*∑ i:D, f i.1 i.2
lemma duo_const (x : ℝ) : duo (fun _ _=>x)=x := by
  change (Fintype.card Signed:ℝ)⁻¹ * ((Fintype.card Signed : ℝ)⁻¹) * (∑ _ : Signed × Signed,x) = x
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul]
  have he : (Fintype.card Signed : ℝ)≠0 := by positivity
  field_simp
lemma duo_sub (f g : Signed→Signed→ℝ) : duo f - duo g = duo (fun s t => f s t - g s t) := by unfold duo; rw [Finset.sum_sub_distrib,mul_sub]
lemma duo_tend (f : ℕ→Signed→Signed→ℝ) (x : Signed→Signed→ℝ) (hf : ∀ s t, Tendsto (fun m=>f m s t) atTop (𝓝 (x s t))) : Tendsto (fun m => duo (f m)) atTop (𝓝 (duo x)) := Tendsto.const_mul _ (tendsto_finsetSum Finset.univ (fun i _ => hf i.1 i.2))
lemma avg_cross (f g : Signed → ℝ) (p : ℝ): p * ((cAvg*(∑ s,f s)) * (cAvg*(∑ s,g s))) = duo (fun s t => p*(f s*g t)) := by
  change _ = cAvg*cAvg*∑ i : Signed × Signed,p*(f i.1*g i.2)
  rw [Fintype.sum_prod_type]
  change _ = cAvg*cAvg*∑ s,∑ t, p*(f s*g t)
  simp_rw [←Finset.mul_sum,←Finset.sum_mul]
  ring

-- shellCover as average with same order for convenience

def shellForm (h : ℝ) (P : TaylorDual G j) (Q : TaylorDual G k) := duo (fun s t => sphereForm j k s t h (reduc s P) (reduc t Q))
def legP (h : ℝ) (P : TaylorDual G j) (c : Channel G) (q : E4) := P (YM.Pert.Bare.wideLinear G j h 0 (material c q))
lemma shell_at (h : ℝ) (P : TaylorDual G j) (Q : TaylorDual G k) (q): ((delta q)⁻¹ * ∑ c : Channel G, legP h P c q * legP h Q c q) = duo (fun s t =>coverPair j k s t h q (reduc s P) (reduc t Q)) := by
  let X (s : Signed) (J : ℕ) (a : TaylorDual G J) (c : Channel G) := reduc s a (chart J s h 0 (material c q))
  dsimp only [legP]; simp_rw [wide_avg,Finset.mul_sum]
  have L (c:Channel G) := avg_cross (fun s =>X s j P c) (fun s=>X s k Q c) ((delta q)⁻¹ : ℝ)
  have E : (∑ c : Channel G, (delta q)⁻¹*((cAvg*(∑ s,X s j P c)) * (cAvg* ∑ s,X s k Q c))) = ∑ c : Channel G, duo (fun s t => (delta q)⁻¹*(X s j P c*X t k Q c)) := Finset.sum_congr rfl fun c _=>L c
  -- reverse normalization if needed
  -- change _ = _
  dsimp [X] at E
  simp_rw [Finset.mul_sum] at E
  rw [E]; unfold duo coverPair; rw [←Finset.mul_sum,Finset.sum_comm];simp_rw [Finset.mul_sum]

def orbital (h : ℝ) (x y : Site n) (P : TaylorDual G j) (Q : TaylorDual G k) := jointB G n (P ∘ₗ YM.Pert.Bare.slope h x j) (Q∘ₗ YM.Pert.Bare.slope h y k)
lemma orbit_eq (h : ℝ) (x y : Site n) (P : TaylorDual G j) (Q : TaylorDual G k) : orbital h x y P Q = duo (fun s t => ordinary j k s t h x y (reduc s P) (reduc t Q)) := by
  rw [orbital,slope_avg,slope_avg]; unfold duo; simp only [map_smul,map_sum,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  -- simp sums. Need reorganize. test
  let f s t := (jointB G n) (reduc s P ∘ₗ chartOrb j s h x) (reduc t Q ∘ₗ chartOrb k t h y)
  change cAvg * (∑t,cAvg*∑d,f d t)=cAvg*cAvg*∑ v:Signed × Signed, f v.1 v.2
  rw [Fintype.sum_prod_type]
  change cAvg*∑ t,cAvg*∑ d,f d t= cAvg*cAvg*∑d,∑t,f d t
  rw [←Finset.mul_sum, Finset.sum_comm]; ring

variable {z : E4}
lemma orbit_limit (T : Itinerary) (x y : StepPath T) (hz : z≠0) (hs : Scene T x y z) (hf : Finale T x y z) (P : TaylorDual G j) (Q : TaylorDual G k):
    Tendsto (fun i:ℕ => orbital (T.gap i) (x i) (y i) P Q) atTop (𝓝 (tayForm z hz P Q)) := by
  let f (m : ℕ) (s t : Signed) := ordinary j k s t (T.gap m) (x m) (y m) (reduc s P) (reduc t Q)
  let g (s t:Signed) := synthesis z hz s t (reduc s P) (reduc t Q)
  have he (s t:Signed) := chart_limit T x y s t z hz hs hf (reduc s P) (reduc t Q)
  have H:= duo_tend f g he
  have HD : duo g = tayForm z hz P Q := by rw [show g = fun _ _=>tayForm z hz P Q from funext fun s=>funext fun t=>synth_turn ..]; exact duo_const _
  rw [HD] at H
  apply H.congr; intro m;exact (orbit_eq ..).symm
lemma orbit_contact (T : Itinerary) (x : StepPath T) (hf : Finale T x x z) (P : TaylorDual G j) (Q : TaylorDual G k):
    Tendsto (fun i:ℕ=> orbital (T.gap i) (x i) (x i) P Q - shellForm (T.gap i) P Q) atTop (𝓝 0) := by
  let f (m : ℕ) (s t : Signed) := ordinary j k s t (T.gap m) (x m) (x m) (reduc s P) (reduc t Q)
  let g (m : ℕ) (s t:Signed) := sphereForm j k s t (T.gap m) (reduc s P) (reduc t Q)
  have H := duo_tend (fun m=>fun s t=> f m s t - g m s t) (fun _ _=>0) (fun s t=> chart_return T x s t z hf (reduc s P) (reduc t Q))
  rw [duo_const] at H
  apply H.congr; intro m; rw [orbit_eq,shellForm,duo_sub]

variable (h : ℝ)
lemma leg_unfold (u : Key G) (c : Channel G) (q : E4) : leg h u c q = legP h ((axes G u.1).coord u.2 : TaylorDual G u.1) c q  := by
  unfold legP
  erw [wide_avg,Full.leg,wide_avg (0:Cover)]

def Kspectral (P : TaylorDual G j) (Q : TaylorDual G k) (q : E4) : ℝ := (delta q)⁻¹ * ∑ c : Channel G, legP h P c q *legP h Q c q
lemma shell_help (P : TaylorDual G j) (Q : TaylorDual G k) : volumeFactor * (∫ q in cube, Kspectral h P Q q) = shellForm h P Q := by
  unfold Kspectral; simp_rw [shellForm,shell_at,sph_eq]; unfold duo
  rw [integral_const_mul,integral_finsetSum Finset.univ]
  · simp_rw [←Finset.mul_sum];ring
  intro r _; apply cont_cost
lemma shell_exact (u v : Key G): link h u v = shellForm h ((axes G u.1).coord u.2) ((axes G v.1).coord v.2) := by
  let P : TaylorDual G u.1 := (axes G u.1).coord u.2
  let Q : TaylorDual G v.1 := (axes G v.1).coord v.2
  apply Eq.trans (show link h u v = volumeFactor * (∫ q in cube, Kspectral h P Q q) from ?_) (shell_help h P Q)
  apply congrArg (fun A : E4→ℝ => volumeFactor * (∫ q in cube, A q))
  funext q; unfold spectral Kspectral; apply congrArg ((delta q)⁻¹ * ·); apply Finset.sum_congr (by ext; simp); intro c _;rw [leg_unfold h u,leg_unfold h v]
end YM.Pert.Align

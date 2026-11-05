import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Affordable
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Chromosomes


/-!
# The two-beam real β experiment on the genuine words

Coupling arguments ONLY within this step, R frozen otherwise. Every pulse Le gives
actual multiplier before all integration. Galop carries complex interpolation incl. polar frame weights.
No promise of ContinuityRecord already meeting this ABI. Shape thresholds and Anchored income unchanged
parameters (ancillary anchored value itself is varying of course).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Plotter
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint Paths Chains Calls Mixed Cab Presented Canvas
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

def retime (R : Rep G f) (t : ℝ) : Rep G f := {R with beta := R.beta * hour t}

lemma fundsRet (T : Tube G S) (R : Rep G f) {σ C Λ δ w : ℝ} (h : R.Lawful σ C Λ δ w) (hv : Fits T R x) (t : ℝ) :
    (retime R t).Lawful σ C Λ δ w ∧ Fits T (retime R t) x :=
    ⟨⟨h.paths,h.labels⟩,⟨hv.path,hv.clip,hv.temp⟩⟩


section shaft
variable (T : Tube G S) (x W : ℝ) (R : Rep G f) (N : ChartRatio G)

lemma billTime {β t : ℝ} (h : 0<β) (hp : 0<1+t) : power (β*hour t)=power β / (1+t) := by
  unfold power hour; rw [Real.sqrt_mul h.le,Real.sqrt_sq hp.le]; field_simp
lemma mislaid {β t : ℝ} (h : 0<β) (hp : 0<1+t) (hv : LocalRatio N) :
    Real.log (sLink G N (β*hour t))=Real.log (sLink G N β)-(Fintype.card G.ColorIndex:ℝ)*Real.log (1+t) := by
  rw [show sLink G N (β*hour t)=sLink G N β/(1+t)^(Fintype.card G.ColorIndex) by
          unfold sLink; rw [billTime h hp, mul_div_assoc',div_pow]; ring,
    Real.log_div (sLink_pos G N β hv h).ne' (pow_pos hp _).ne', Real.log_pow]

lemma scatter (Y : Mint T F A x) (β t : ℝ) (h : 0<β) (hp : 0<1+t) (z : ArrayR G f) :
    cashB Y (β*hour t) ((1+t) • z) = cashB Y β z := by
  unfold cashB; rw [billTime h hp, smul_smul, div_mul_cancel₀ _ hp.ne']

def pulse (L : Finset ℕ) (Y : Mint T F A x) (z : ArrayR G f) (i : Tab S) (t : ℝ) :=
    leaf T x W (retime R t) N L Y ((1+t) • z) i

def pulp (F : Forest S.ratio) (G : Gauge) (m : Stores S) (x : ℝ) := (freeze F m (radiusB x)).card * Fintype.card G.ColorIndex

lemma evolution (L : Finset ℕ) (Y : Mint T F A x) (z : ArrayR G f) (m : Stores S) (hr : 0<R.beta) (he : LocalRatio N) :
    Voyage (pulp F G m x) (pulse T x W R N L Y z (.inl m)) := by
  let J := pulp F G m x; let b := R.beta; let a := cashB Y b z; let n := (freeze F m (radiusB x)).card
  let P := (∑ i ∈ padB m (200*radiusB x), paired Y i) - Real.log (sLink G N b)*n
  let B := -b*coverEnergy Y a m
  refine ⟨noMore m R.activities L Y a * curb m Y.V Y.k W x Y.q (Y.build a)*chambers Y m N a, P, B, fun t ht => ?_⟩
  simp only [pulse,Cab.leaf,Sum.elim_inl,retime,scatter T x Y _ t hr ht,parses,mislaid N hr ht he]
  rw [show -(R.beta*hour t)*coverEnergy Y a m + ∑ i∈padB m (200*radiusB x), paired Y i -
      (Real.log (sLink G N b)-(Fintype.card G.ColorIndex:ℝ)*Real.log (1+t))*n =
      (pulp F G m x : ℝ)*Real.log (1+t) + (P+B*hour t) by unfold P B n b pulp a; push_cast; unfold b; ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log ht]; unfold a b; ring

lemma chimera (Y : Mint T F A x) (z : ArrayR G f) (i : Back c f) (hr : 0<R.beta) :
    Fractional (fun t => back T x (retime R t) Y ((1+t) • z) i) := by
  let b := R.beta; let a := cashB Y b z
  rcases i with i|(p|p|p)|(p|p)
  · refine Or.inl ⟨heir R Y i a, fun t ht => ?_⟩; simp only [back,Sum.elim_inl,retime,scatter T x Y _ t hr ht]; rfl
  · refine Or.inl ⟨atomic R.path.loop R.p Aff.weight Y p a,fun t ht => ?_⟩; simp [back,atoms,retime,scatter T x Y _ t hr ht,a,b]
  · refine Or.inr ⟨0,axisFee R.path.cubic R.p (b*Aff.weight) Y p a,fun t ht => ?_⟩
    simp only [back,Sum.elim_inr,Sum.elim_inl,atoms,atomic,retime,scatter T x Y _ t hr ht]; unfold axisFee a b; ring_nf
  · refine Or.inr ⟨0,axisFee R.path.quartic R.p (b*Aff.weight) Y p a,fun t ht => ?_⟩
    simp only [back,Sum.elim_inr,Sum.elim_inl,atoms,atomic,retime,scatter T x Y _ t hr ht]; unfold axisFee a b; ring_nf
  · refine Or.inr ⟨0,cuts p R Y a,fun t ht => ?_⟩
    simp only [back,Sum.elim_inr,Sum.elim_inl,tails, cuts,retime,scatter T x Y _ t hr ht]; unfold a b; ring_nf
  refine Or.inr ⟨0,reset p x b T Y.V,fun t ht => ?_⟩
  simp only [back,Sum.elim_inr,tails,reset,retime]; unfold b; ring_nf
lemma clash (Y : Mint T F A x) (z : ArrayR G f) (i : Flick S) (hr : 0<R.beta) :
    Fractional (fun t => let b := (retime R t).beta; slash Y b N (cashB Y b ((1+t) • z)) i) := by
  let b := R.beta; let a := cashB Y b z
  cases i with
  | inl i =>
    by_cases h : crib S i ∈ A.dome (200*radiusB x)
    · exact .inl ⟨0,by simp [slash,h]⟩
    refine Or.inr ⟨0,-b*robe Y (pulls S (2*radiusB x) (crib S i)) a * pureBooth Y a i,fun t ht => ?_⟩
    simp only [retime,h,slash, ↓reduceIte,scatter T x Y _ t hr ht]
    unfold a b; ring_nf
  | inr i =>
    refine Or.inl ⟨slash Y b N a (.inr i),fun t ht => ?_⟩
    simp only [retime,scatter T x Y _ t hr ht]; cases i <;> rfl

lemma scales (M : Matrix (Vars G f) (Vars G f) ℝ) (x : ℝ) (p : Year S) (z : ArrayR G f) (t : ℝ) :
    excise S x M p ((1+t) • z)=hour t*excise S x M p z := by
  unfold excise amount; dsimp only
  rw [show (fun k => ((1+t) • z) (p.2.1,k))= (1+t) • (fun k => z (p.2.1,k)) from rfl,
    show (fun k => ((1+t) • z) (p.2.2.2,k))= (1+t) • (fun k => z (p.2.2.2,k)) from rfl,
    Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,smul_eq_mul]; unfold hour; ring

lemma reYear (Y : Mint T F A x) (z : ArrayR G f) (p : Year S) (t : ℝ) :
    celebration T F x Y.sheet p ((1+t) • z)=(celebration T F x Y.sheet p z - excise S x Y.sheet p z /2) +
      hour t * (excise S x Y.sheet p z/2) := by unfold celebration; rw [scales (G:=G)]; ring
lemma payments (Y : Mint T F A x) (z : ArrayR G f) (t : ℝ) (b : Bond f) (hr : 0<R.beta) (hv : 0<1+t) :
    snapCharge Y b (retime R t).beta ((1+t) • z)=snapCharge Y b R.beta z * hour t := by
  unfold retime snapCharge; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _
  dsimp only; rw [Pi.smul_apply,smul_eq_mul,billTime hr hv]; field_simp
lemma helical (L : Finset ℕ) (Y : Mint T F A x) (z : ArrayR G f) (i : LocalStep S) (hr : 0<R.beta) :
    Fractional (fun t => memory T x W (retime R t) N L Y ((1+t) • z) i) := by
  let a := cashB Y R.beta z
  rcases i with (i|i)|(i|i)
  · refine Or.inl ⟨chip Y R.activities L W a i,fun t ht => ?_⟩; simp only [memory,Sum.elim_inl,retime,scatter T x Y _ t hr ht,a]
  · exact clash T x R N Y z _ hr
  · refine Or.inr ⟨celebration T F x Y.sheet i z-excise S x Y.sheet i z/2,excise S x Y.sheet i z/2,fun t ht => ?_⟩
    simp only [memory,Sum.elim_inl,Sum.elim_inr,Chains.chain,reYear T x Y z _ t,mul_comm (hour t)]
  refine Or.inr ⟨0,snapCharge Y i R.beta z,fun t ht=>?_⟩
  simp [memory,snapSale,payments T x R Y z t _ hr ht]

lemma trails (L : Finset ℕ) (Y : Mint T F A x) (z : ArrayR G f) (i : Other S) (hr : 0<R.beta) :
    Fractional (pulse T x W R N L Y z (.inr i)) := by
  rcases i with i|i|i
  · refine Or.inl ⟨krill R Y i (cashB Y R.beta z),fun t ht => ?_⟩; simp only [pulse,Cab.leaf,retime,Sum.elim_inr,Sum.elim_inl,other,
       scatter T x Y _ t hr ht]; rfl
  · exact chimera T x R Y z _ hr
  exact helical T x W R N L Y z _ hr

def galop (L : Finset ℕ) (Y : Mint T F A x) (z : ArrayR G f) (i : Tab S) := let p := pulse T x W R N L Y z i
    Sum.elim (fun m => holm (pulp F G m x) (p pit) (p ridge)) (fun _ => coin (p pit) (p ridge)) i


lemma transitive (L : Finset ℕ) (Y : Mint T F A x) (z : ArrayR G f) (i : Tab S) :
    Differentiable ℂ (galop T x W R N L Y z i) := by
  rcases i with i|i
  · change Differentiable ℂ (fun t => holm (pulp F G i x) _ _ t); simp only [holm]; unfold zone; fun_prop
  dsimp only [galop,Sum.elim_inr]
  let q := pulse T x W R N L Y z (.inr i); change Differentiable ℂ (coin (q pit) (q ridge))
  by_cases he : q pit=q ridge
  · rw [show coin (q pit) (q ridge) = fun _ => (↑(q pit):ℂ) from funext (fun _=> if_pos he)]
    exact differentiable_const _
  change Differentiable ℂ (fun t => coin (q pit) (q ridge) t); simp only [coin, he, ↓reduceIte]; unfold zone; fun_prop
lemma registers {P : Teller G} (hT : P.Funds S T) (L : Finset ℕ) {r : ℝ} (h : Choice N r)
    {σ C Λ δ w : ℝ} (hR : R.Lawful σ C Λ δ w) (hs : Fits T R x) (A : Stores S) (F : Forest S.ratio)
    (V : Config G c) (k : S.Choices) (B : Chi) (i : Tab S) {α : Type} [MeasurableSpace α] {a : α→F.Slice G}
    {z : α→ArrayR G f} (he : Measurable a) (hp : Measurable z) (t : ℂ) :
    Measurable fun p => galop T x W R N L (figure T x r B A F V k (a p)) (z p) i t := by
  let f' (i : Tab S) w p := pulse T x W R N L (figure T x r B A F V k (a p)) (z p) i w
  have hh i w : Measurable (f' i w) := by
    have ht := shapes T hT x r W N h (retime R w) (fundsRet T R hR hs w).1 (f':=fun _ => V) measurable_const F A k B {i} L he
      (hp.const_smul (1+w)); simpa only [payfield,prod_singleton,f',pulse,Pi.smul_apply] using ht
  rcases i with i|i
  · change Measurable fun p => holm (pulp F G i x) (f' (.inl i) pit p) (f' (.inl i) ridge p) t
    unfold holm; dsimp only; fun_prop
  change Measurable fun p => coin (f' (.inr i) pit p) (f' (.inr i) ridge p) t
  unfold coin; apply Measurable.ite (measurableSet_eq_fun (hh _ _) (hh _ _)) <;> fun_prop
end shaft
end YM.AnalyticNext.ConnectedActivity.Plotter

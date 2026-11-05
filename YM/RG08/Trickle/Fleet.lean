import YM.RG08.Trickle.Airs
import YM.RG08.Glyph.Balance

/-!
# Finite prescription specialization at one external marker
Includes the whole ordinary joint Gibbs exponential with manifest mean
substitution, field-dependent denominator inversion, then (linear term in)
output log. Test/root weights can be pulled before the propagation.
-/
noncomputable section
namespace YM.RG08.Trickle
open Function Finset PowerSeries Jetty Skiff Forms Steam Glyph MvPolynomial Cloud
open scoped BigOperators Topology PowerSeries Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I J:Type}{n l:ℕ}{Γ:Forms.Line I}{V:Steam.Grain I}{S:GrainS I}

def mouth (K:I→J→ℝ)(S:GrainS I):GrainS J:= fun e n=>picture (candles (repeatLine K n)) (audio n n I J) (S e n)
lemma water (K:I→J→ℝ)(S:GrainS I)(f:Pearl)(e n:ℕ):brook f (mouth K S) e n=Forms.raft (repeatLine K n) (brook f S e n):=by
 unfold brook mouth picture raft during; funext x;unfold decker;apply tsum_congr;intro i
 change design _ _ _ * _=_ * _; rw [mul_comm]; rfl

variable [Fintype I][Fintype J]
private lemma lobby (μ:I→J→ℝ)(n:ℕ)(F:Flake n I):parley (Forms.raft (repeatLine μ n) F)=twistMean μ (parley F):=by
 -- use amended stock by packing at e=n. (lemma tilted private)
 let T:Grain I:=fun _ j=> if h:j=n then h.symm ▸ F else 0
 have hz : ∀ a,T a n=F:=by intro;simp [T]
 have hx a j (hh:j≠n):T a j=0:=by simp [T,hh]
 have he:= congrArg (PowerSeries.coeff n (R:=Inn J)) (amended_stock μ T)
 simp only [PowerSeries.coeff_map,stock,PowerSeries.coeff_mk,showV,amended,AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at he
 have hr:n∈range (n+3):=by simp
 rw [sum_eq_single_of_mem n hr (fun j _ hj=>?_),sum_eq_single_of_mem n hr (fun j _ hj=>?_)] at he
 · rw [hz n] at he; exact he
 · rw [hx n j hj,parley_zero]
 rw [hx n j hj,show Forms.raft (repeatLine μ j) 0=0 from ?_,parley_zero]; ext; simp [Forms.raft,vat]

lemma kissed (K:I→J→ℝ)(S:GrainS I)(f:Pearl):Trickle.mark l (mouth K S) f=PowerSeries.map (twistMean K).toRingHom (Trickle.mark l S f):=by
 ext e :1;rw [PowerSeries.coeff_map,Trickle.mark,Trickle.mark,PowerSeries.coeff_mk,PowerSeries.coeff_mk,shine,shine,map_sum]; apply sum_congr rfl;intro n _;rw [water,lobby];rfl

omit [Fintype J] in
lemma sky_birth {W Z:Season (Inn I)}(hΓ:∀ i j,Γ i j=Γ j i)(hV:Clockwise (axes I) (half Γ) W)(hf:Trickle.Note (axes I) (half Γ) W Z):sky Γ (summer 0 (rise W*Z))=summer 1 (rise W*Z):=by
 ext e :1
 let u:=summer 0 (rise W*Z); let f:=PowerSeries.coeff e u
 obtain ⟨n,hn⟩:=halts Γ hΓ f
 rw [sky,PowerSeries.coeff_mk,wick_budget (p:=PowerSeries.coeff e u) (n:=n+1) (fun i hi=>hn i (by omega))]
 have he(i:ℕ):takeoff (rise W*Z) e i=gust Γ i f:=by
   rw [hf.stamp (fun a b=>by unfold half;rw [hΓ b a]) hV];unfold gust f u radiator;rw [summer_initial]
 rw [summer_range _ n e 1]
 · change _=∑ i∈range (n+1),(1:ℝ)^i • takeoff (rise W*Z) e i; simp_rw [he,one_pow,one_smul];rfl
 intro i hi;rw [he,hn i hi.le]

/-- Numerator, same full kernel & penalty conventions as `capture`. No slot factorials. -/
theorem hymn (μ:I→J→ℝ)(he:Eligible V)(h:waxed V)(hc:Lit l S)(H:Combed S)(hΓ:∀ i j,Γ i j=Γ j i)(f:Pearl):house Γ μ (rise (stock V) * Trickle.mark l S f)=house Γ μ (rise (stock V)) * Trickle.mark l (mouth μ (Skiff.spin l Γ V S 1)) f:=by
 rw [house];have hu := sky_birth hΓ (cloudy he h hΓ) (notes he hc h H hΓ f)
 rw [_root_.map_mul,_root_.map_mul,summer_rise,summer_rise,flare he hc,morning he,breaktime he,sunrise he hc] at hu
 rw [hu,_root_.map_mul,house,sky_rise he h hΓ,kissed]

/-- Markov column identity used through recursion. Keep scalar pivot here. -/
theorem report (μ:I→J→ℝ)(he:Eligible V)(h:waxed V)(hc:Lit l S)(H:Combed S)(hΓ:∀ i j,Γ i j=Γ j i)(f:Pearl):
 Trickle.mark l (mouth μ (Skiff.spin l Γ V S 1)) f=house Γ μ (rise (stock V) * Trickle.mark l S f) * counter (house Γ μ (rise (stock V))):=by
 rw [hymn μ he h hc H hΓ f,housed μ he h hΓ,counter_pays _ _ (rise_unit (tiny_on (Γ:=Γ) μ he)),mul_comm (rise _),mul_assoc,rise_unit (tiny_on μ he),mul_one]

end YM.RG08.Trickle

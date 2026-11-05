import YM.RG08.Glyph.Wick
import YM.RG08.Steam.Ballot

/-!
# Shift upper/lower variables to evaluation point & exact all-order finite Wick identity.
-/
noncomputable section
namespace YM.RG08.Glyph
open Forms Steam Cloud Finset Function MvPolynomial
open scoped BigOperators Topology Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I J : Type}[Fintype I][Fintype J]{Γ: Line I}

def median (μ:I→J→ℝ)(i:I): Inn J:=∑ j, μ i j • X j
def twistMean (μ:I→J→ℝ):Inn I→ₐ[ℝ] Inn J:=MvPolynomial.aeval (median μ)

private lemma tilted (μ:I→J→ℝ)(n:ℕ)(F:Flake n I):parley (Forms.raft (repeatLine μ n) F)=twistMean μ (parley F):=by
 unfold parley raft vat word; simp only [tsum_fintype,Finset.sum_smul,map_sum,_root_.map_smul,twistMean,map_prod,MvPolynomial.aeval_X,median]
 rw [Finset.sum_comm];apply sum_congr rfl; intro x _
 have h:
    ∏ i:Fin n,(∑ j:J, μ (x i) j • (X j:Inn J))=∑ y:Fin n→J,∏ i:Fin n,(μ (x i) (y i) • (X (y i):Inn J)):=by
    -- Fintype.prod_sum ?
    exact Fintype.prod_sum ..
 rw [h,Finset.smul_sum]
 apply sum_congr rfl;intro y _
 have he(M:Finset (Fin n)): (∏ i∈M,(μ (x i) (y i) • (X (y i):Inn J)))=(∏ i∈M,μ (x i) (y i)) • (∏ i∈M,X (y i):Inn J):=by
   induction M using Finset.induction_on with
   | empty=>simp
   | insert a s ha ih=>rw [prod_insert ha,prod_insert ha,prod_insert ha, ih, smul_mul_assoc,mul_smul_comm,smul_smul]
 rw [he univ,smul_smul];rfl

def amended (μ:I→J→ℝ)(V:Grain I):Grain J:= fun e n=>raft (repeatLine μ n) (V e n)
lemma amended_stock (μ:I→J→ℝ)(V:Grain I):stock (amended μ V)=PowerSeries.map (twistMean μ).toRingHom (stock V):=by
 ext e :1;rw [PowerSeries.coeff_map,stock,stock,PowerSeries.coeff_mk,PowerSeries.coeff_mk,showV,showV,map_sum];apply Finset.sum_congr rfl;intro n _;exact tilted ..
lemma allG_on (μ:I→J→ℝ)(V:Grain I):stock (allG Γ V μ)=stock (amended μ (ember Γ V 1)):=by
 ext e :1;rw [smoulder]
 simp_rw [stock,PowerSeries.coeff_mk,showV,allG,strict,amended,parley_add,tilted,Pi.add_apply,parley_add,map_add]

def sky (Γ:Line I)(V:PowerSeries (Inn I)) : PowerSeries (Inn I):= PowerSeries.mk (fun e=>wick Γ (PowerSeries.coeff e V))

/-- `sky` converts ordinary series polynomials by the Wick recursion above; then substitute mean,
THEN take connected log. -/
def house (Γ:Line I)(μ:I→J→ℝ)(V:PowerSeries (Inn I)) := PowerSeries.map (twistMean μ).toRingHom (sky Γ V)

lemma sky_rise {V:Grain I}(hV:Eligible V)(h:waxed V)(hΓ:∀ i j,Γ i j=Γ j i) : sky Γ (rise (stock V))=rise (stock (ember Γ V 1)):=by
 let U:=kernel Γ V; have hu:Clockwise (axes I) (half Γ) U:=cloudy hV h hΓ
 ext e :1
 let f:=PowerSeries.coeff e (rise (stock V))
 obtain ⟨n,hn⟩:=halts Γ hΓ f
 rw [sky,PowerSeries.coeff_mk,wick_budget (p:=PowerSeries.coeff e (rise (stock V))) (n:=n+1) (fun i hi=>hn i (by omega)),←breaktime (Γ:=Γ) hV,← summer_rise]
 have he (j:ℕ) : takeoff (rise U) e j=gust Γ j f:=by
   rw [hu.jet]; unfold gust; rw [←summer_initial,summer_rise]
   unfold U;rw [morning hV]; rfl
 rw [summer_range _ n]
 · change _=∑ i∈range (n+1),(1:ℝ)^i • takeoff (rise U) e i
   simp_rw [he,one_pow,one_smul];rfl
 intro i hi;change takeoff (rise U) e i=_; rw [he,hn i hi.le]

def pushed (Γ:Line I)(μ:I→J→ℝ)(V:Grain I):PowerSeries (Inn J):=stock (allG Γ V μ)
lemma tiny_on (μ:I→J→ℝ){V:Grain I}(hV:Eligible V):tiny (pushed Γ μ V):=by
 unfold pushed;rw [allG_on];unfold tiny stock;rw [PowerSeries.coeff_mk]; unfold amended raft vat showV
 simp [(appropriate hV _).dark,parley,design]

theorem housed (μ:I→J→ℝ){V:Grain I}(hV:Eligible V)(h:waxed V)(hΓ:∀ i j,Γ i j=Γ j i) : house Γ μ (rise (stock V))=rise (pushed Γ μ V):=by rw [house,sky_rise hV h hΓ,rise_map, pushed,allG_on,amended_stock]
theorem logged (μ:I→J→ℝ){V:Grain I}(hV:Eligible V)(h:waxed V)(hΓ:∀ i j,Γ i j=Γ j i):fall (house Γ μ (rise (stock V)))=pushed Γ μ V:=by rw [housed μ hV h hΓ,ground (tiny_on _ hV)]

end YM.RG08.Glyph

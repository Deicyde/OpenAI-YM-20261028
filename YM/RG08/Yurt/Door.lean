import YM.RG08.Yurt.Tram
/-! # Deterministic rooted exponential beam collected. Before testing input D via earlier orders.
 Payment only <2×width> slot arithmetic BEFORE L. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Yurt
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Quarry Weald Hatch Carrel Laurent Filter RG Precision Exterior Skiff
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {I J:Type}{G:Gauge}{n p d e i:ℕ}{D C T B τ η σ δ s:ℝ}{L L':Side}{hh:0<τ}

-- combine product at point, sum all frequencies exactly. Useful others for difference-on-all-analytic too.
def load (τ:ℝ)(i:Market I):ℝ:=Real.exp (τ*length i.1)
def rate (I:Type)[Fintype I](τ:ℝ):ℝ:= (Fintype.card I:ℝ)*(∑' i:Cover,Real.exp (-τ*length i))
lemma rate_nn (I:Type)[Fintype I](τ:ℝ):0 ≤ rate I τ:=mul_nonneg (by positivity) (tsum_nonneg (fun _=> (Real.exp_pos _).le))
lemma amort [Fintype I](hs:0<τ):(∑' i:Market I,ENNReal.ofReal (load (-τ) i))≤ENNReal.ofReal (rate I τ):=by
 unfold rate;rw [ENNReal.ofReal_mul (by positivity:(0:ℝ)≤Fintype.card I),ENNReal.ofReal_natCast]
 apply Pert.Bulk.convert_market
 intro i;change (∑' x:Cover, ENNReal.ofReal (Real.exp (-τ*length x)))≤_
 rw [ENNReal.ofReal_tsum_of_nonneg (fun _=> (Real.exp_pos _).le)]
 exact (Laurent.Width.compactPay τ hs).2.1
lemma load_mul {x:Tape n (Market I)}:
 (∏ i, load τ (x i))= Real.exp (τ*∑ i,length (x i).1):=by rw [mul_sum,Real.exp_sum];rfl
lemma max_y (x:Tape n (Market I)): (stance I).cage x ≤ ∑ i,length (x i).1:= (stance I).racks x (sum_nonneg fun _ _=>abroad_nn _) (fun _=>single_le_sum (s:=Finset.univ) (f:=fun j=>length (x j).1) (fun i _=>abroad_nn (x i)) (mem_univ _))
lemma have_sings [Fintype I](F:Pack n (Market I))(h:0<τ)(hC:0 ≤ C)(hf:∀ (f:Pearl)(x:Tape n (Market I)),|((∏ i, load (2*τ) (x i))*F x f)|≤ C*beam d h f): Sings (stance I) d h F (C*rate I τ ^ n):=by
 unfold Sings
 let P(x:Tape n (Market I)):=∏ i,ENNReal.ofReal (load (-τ) (x i))
 refine (ENNReal.tsum_le_tsum (g:=fun x=>ENNReal.ofReal C * P x) (fun x=>?_)).trans ?_
 swap
 · rw [ENNReal.tsum_mul_left,ENNReal.ofReal_mul hC]
   apply mul_le_mul_right
   unfold P; rw [all_Δ (α:=Market I) (r:=n) (fun _ x=> ENNReal.ofReal (load (-τ) x)),ENNReal.ofReal_pow (rate_nn I τ)] -- implicit params? signature
   have he: (∏ _j:Fin n,∑' i:Market I,ENNReal.ofReal (load (-τ) i))≤ ∏ _j:Fin n,ENNReal.ofReal (rate I τ):= Finset.prod_le_prod' fun _ _=>amort h
   exact he.trans_eq (by rw [prod_const,card_univ,Fintype.card_fin])
 let w:= ∑ i,length (x i).1; let K:= Real.exp (-(2*τ)*w)
 have hK:0 ≤ K:= (Real.exp_pos _).le
 unfold gems weft
 apply (mul_le_mul' (purse_le _ (ENNReal.ofReal (C*K)) (F:=F x) (fun f he=>ENNReal.ofReal_le_ofReal ?_)) (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (max_y x) h.le)))).trans_eq
 swap
 · specialize hf f x; rw [load_mul,abs_mul,abs_of_pos (Real.exp_pos _)] at hf
   rw [mul_comm] at hf -- maybe wrong first 2*τ? targets search
   let a:= Real.exp ((2*τ)*w)
   have hp:0<a:=Real.exp_pos _
   have hs':a * |F x f| ≤ C:=by apply le_trans _ (mul_le_of_le_one_right hC he);unfold a w; simpa [mul_comm] using hf
   change _≤C * Real.exp _;rw [neg_mul,Real.exp_neg]; rw [mul_comm] at hs';exact (le_div_iff₀ hp).mpr hs'
 · unfold P; rw [←ENNReal.ofReal_prod_of_nonneg (f:=fun i=>load (-τ) (x i)) (fun i _=> (Real.exp_pos _).le),load_mul,←ENNReal.ofReal_mul (mul_nonneg hC hK),←ENNReal.ofReal_mul hC];congr 1;unfold K w;rw [mul_assoc,←Real.exp_add];ring_nf

/-- Pulled deterministic source, engineering factor kept out, *one* rooted offset.
+ lift conventions. Exact f evaluation (E & free grammar for Yamen). -/
def ferry {I J:Type}{n:ℕ}(K:Kernel I J)(F:Pack n (Market I))(a:ℝ)(u:E4)(o:Cover):Pack n (Market J):=
 fun y f=> sonic F (aisle a u f) (fun i=> tender K o 0 (y i))
lemma ferry_spin {F:Pack n (Market I)}(f:Pearl)(τ:ℝ)(K:Kernel I J)(a:ℝ)(u:E4)(o:Cover)(y:Tape n (Market J)):
 sonic F (aisle a u f) (fun i=>tender K o τ (y i))=(∏ i,load τ (y i))*ferry K F a u o y f:=by
 unfold ferry;rw [←sonic_pull];congr 1;ext i x; simp [tender,offer,load]
/-- h horizon, n rank, own-level input e, all pre displacement arithmetic (2× buffer)
PRE L. real f. Null-B may be 0. Coefficient budget output QUALITY analytic keyword.
-/
theorem trains (G:Gauge)(l h d e n:ℕ)(s C σ η δ:ℝ)(hη:0<η)(hh:0<σ)(hc:0≤C)(hs:0< s)(hd:h+1≤d)(hr:n≤l+e)(hδ:0≤δ)(hz:δ≤1)(ht:(↑((e+1)*(l+e)):ℝ)*δ≤σ/2)(hη':2*η ≤ s):∃ D:ℝ,0 ≤ D ∧ ∀ {Q T B V:ℝ}(L:Side)(o:Site L)(M:Carrier.Lines L)(N:Kernel G.ColorIndex (Loc G 1))(K:Kernel (Loc G 1) (Loc G 1))(F:GrainS (Ed G Cover)),Odd L.val→Tutor L s C M G h→Crest L M N K→(2*η)/(L.val:ℝ)≤δ→ η*unitStep L≤σ/2 → RowCost s L N Q →0≤Q→Calls l F→ Permit d l F →0≤T→0≤B→0≤V → Minored G h n (F e n) B →(∀ k≤l+e,Sings (stance _) d hh (F e k) T) →(∀ a<e,∀ k≤l+a,Sings (stance _) d hh (F a k) V) →
 let u:=unitStep L
 ; Sings (stance _) d hη (ferry K (F e n) u (ahead L o) (lift o)) (D*(B+T*u^(h+1)+(Q+C)^n*V)):=by
 obtain ⟨D,hD,H⟩:=prep G l h d e n s C σ η δ hη hh hc hs hd hr hδ hz ht
 refine ⟨D*rate (Loc G 1) η ^ n,mul_nonneg hD (pow_nonneg (rate_nn ..) _),?_⟩
 intro Q T B V L o M N K F ho hu hP hq hm hN hQ he hW hT hB hV hZ h₀ h₁ u
 let R:= (B+T*u^(h+1)+(Q+C)^n*V)
 have hr:0≤D*R:=by unfold R; have hu:0≤u:=(unitStep_pos L).le; positivity
 have hv(f y):= H L o M N K F f y ho hu (fun w hw=>hu w (by omega)) hP (show 0≤2*η by positivity) hη' hq hm hN hQ he hW hT hB hV hZ h₀ h₁
 simp_rw [ferry_spin] at hv
 exact (show (D*rate (Loc G 1) η ^ n)*R=D*R*rate (Loc G 1) η ^ n from by ring).symm ▸ have_sings _ hη hr hv
end YM.RG08.Yurt

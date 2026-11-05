import YM.Extra.SOURCE_HISTORIES.Pencil
import YM.Next.FREE_KERNELS.Signal
import YM.Planned.PRIMARY_INTEGRAL_295.Nimbuses
import YM.Planned.PRIMARY_INTEGRAL_295.Oval


/-!
# A supported profile on REAL array of non-tree stencils

Test on product of color blocks of the joint Gaussian. E.Pulse query, scale
ε p*, preserving smooth cut on every used and mask stencil. Polynomial dim
price, eventual post-L. No fake Gaussian tails included. Relabel choice of
blocks requires comparing measures also. To match Robe, builds actual torn
out of AxisChart with explicit support property for granting by charts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Icebergs
open Nimbuses Function Filter Set Oval Metric   MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Precision Tree 
open scoped Topology ContDiff BigOperators Classical
variable {k n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] {G : Gauge}

section Algebra
-- costs count parent positions, not a blowup per variable.
omit [Fintype ι] in
lemma bottles (s:Finset ι) (x:E) {u:ℝ} {f:ι→E→ℝ} (hf:∀ i, ContDiff ℝ k (f i)) (hu:0≤u)
     (he:∀ i n,n≤k → ‖iteratedFDeriv ℝ n (f i) x‖ ≤ u^n) {n:ℕ} (hn:n≤k) :
    ‖iteratedFDeriv ℝ n (fun z=>∏ i∈s,f i z) x‖ ≤ (s.card*u)^n := by
  induction s using Finset.induction generalizing n with
  | empty =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [Finset.prod_empty, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]; simp
  | @insert i s hx ih =>
    let g:=fun x:E=>∏ i∈s, f i x
    have hG : ContDiff ℝ k g := contDiff_prod (fun i _=> hf i)
    simp only [Finset.prod_insert hx,Finset.card_insert_of_notMem hx]; push_cast
    refine (norm_iteratedFDeriv_mul_le (hf i) hG x (Nat.cast_le.mpr hn)).trans ?_
    rw [add_mul,one_mul,add_comm _ u, add_pow]
    apply Finset.sum_le_sum; intro j hj; have hl:= Finset.mem_range.mp hj
    let t:=(s.card:ℝ)*u; let a:=(n.choose j : ℝ)
    have hw:= mul_le_mul_of_nonneg_left (he i j (by omega)) (show 0≤a by positivity)
    change _ ≤ u^j*t^(n-j)*a
    rw [mul_comm _ a,← mul_assoc]; exact mul_le_mul hw (ih (by omega)) (norm_nonneg _) (by positivity)
end Algebra

abbrev Index (ι:Type*) (G:Gauge) := ι × G.ColorIndex
variable (ι) (G)

def facet (i:ι):Sky (Index ι G) →L[ℝ] G.Color := LinearMap.toContinuousLinearMap
    ({ toFun v := WithLp.toLp 2 fun c:G.ColorIndex=>v (i,c), map_add' v w:= by rfl, map_smul' q v:=by rfl}: Sky (Index ι G) →ₗ[ℝ] G.Color)
lemma points (x:Sky (Index ι G)) : ∑ i : ι, ‖facet ι G i x‖^2 = ‖x‖^2 := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]; rfl
lemma piece_norm (i:ι) (x:Sky (Index ι G)) : ‖facet ι G i x‖ ≤ ‖x‖:= by
   have ht := Finset.single_le_sum (f:=fun j=>‖facet ι G j x‖^2) (fun i _=>sq_nonneg _) (Finset.mem_univ i)
   rw [points] at ht; nlinarith [norm_nonneg x]
lemma pea (i:ι) : ‖facet ι G i‖ ≤ 1 :=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> (piece_norm ι G i x).trans_eq (one_mul _).symm

structure Pulse where
  χ : G.Color→ℝ
  hk : ContDiff ℝ ∞ χ
  r (x) : χ x∈ Icc (0:ℝ) 1
  inner : ∀ x, ‖x‖ ≤ 1/8 → χ x=1
  outer : ∀ x, 1/2 ≤ ‖x‖ → χ x=0
  radial : ∀ x y, ‖x‖=‖y‖ → χ x=χ y

-- genuine choice admissible structurally (ε chosen elsewhere).


variable {G} (B : Pulse G) {ξ ε u M : ℝ}

-- compact fixed pulse pre, no assumption hit in production


def aiming (u:ℝ) (i:ι) := B.χ ∘ (u • facet ι G i)
def halo (ξ ε:ℝ) := fun z:Sky (Index ι G)=> ∏ i, aiming ι B (ξ/ε) i z

def pile (u : ℝ) (k:ℕ) := u+ ((u*u)*u)^k
lemma pile_power {u:ℝ} (h:1≤u) (k:ℕ) : u ≤ pile u k ∧ pile u k ≤ 2*u^(1+3*k) := by
  unfold pile; constructor
  · apply le_add_of_nonneg_right; positivity
  have ht := pow_le_pow_right₀ h (show 1≤1+3*k by omega)
  have hu := pow_le_pow_right₀ h (show 3*k≤1+3*k by omega)
  rw [show (u*u*u)^k=u^(3*k) by ring]; rw [pow_one] at ht; linarith

lemma aiming_price {u:ℝ} (hu: 1≤u) (hC: ∀ x, Oval.Envelope x k B.χ u) (i:ι)
    (c:ℝ) (hc:‖c‖≤u) (x:Sky (Index ι G)) (n:ℕ) (hn:n≤k) : ‖iteratedFDeriv ℝ n (aiming ι B c i) x‖≤ (u*u)^n:= by
  let L:= c • facet ι G i
  have hL : ‖L‖ ≤ u:= by rw [norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg c) (pea ι G i)).trans hc
  by_cases hq:n=0
  · rw [hq,pow_zero,norm_iteratedFDeriv_zero]; exact (Real.norm_of_nonneg (B.r (L x)).1).le.trans (B.r _).2
  have h : ContDiff ℝ n B.χ:= B.hk.of_le (WithTop.coe_le_coe.mpr le_top)
  change ‖iteratedFDeriv ℝ n (B.χ ∘ L) x‖ ≤ _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right L h x (le_refl _)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
  have hs : u ≤ u^n:= by simpa only [pow_one] using pow_le_pow_right₀ hu (by omega : 1≤n)
  rw [mul_pow]; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin];
  exact mul_le_mul (((hC (L x)).2 n hn).trans hs) (pow_le_pow_left₀ (norm_nonneg _) hL n) (by positivity) (by positivity)

lemma blaze (hx : ξ∈ Ioc (0:ℝ) 1) (he:ε ∈ Ioc (0:ℝ) 1) (hu:1≤u) (hC: ∀ x, Oval.Envelope x k B.χ u)
    (hs : 8 ≤ u*ε) (ht : (Fintype.card ι:ℝ) ≤ u) (hM : pile u k ≤ M) :
    let Q:= halo ι B ξ ε
    ContDiff ℝ k Q ∧ (∀ x, Oval.Envelope x k Q M) ∧ ∀ x, Q x∈Icc (0:ℝ) 1 ∧ (M*ξ*‖x‖ ≤ 1 → Q x=1) ∧ (M < ξ*‖x‖ → Q x=0) := by
  let Z:= aiming ι B (ξ/ε)
  let L(i:ι):=(ξ/ε) • facet ι G i
  have hx₀:=hx.1; have he₀:=he.1; have hu':= (pile_power hu k).1.trans hM
  have hm:=hu.trans hu'; let C:=(Fintype.card ι:ℝ)
  have hf (i:ι) : ContDiff ℝ k (Z i):=(B.hk.of_le (WithTop.coe_le_coe.mpr le_top)).comp (L i).contDiff
  intro Q; refine ⟨contDiff_prod (fun i _=> hf i),fun x=> ⟨by positivity,fun n hn=>?_⟩,fun x=>?_⟩
  · change ‖iteratedFDeriv ℝ n (fun x=>∏ i,Z i x) x‖ ≤ _
    have hR : ‖ξ/ε‖≤u:= by rw [Real.norm_of_nonneg (by positivity),div_le_iff₀ he₀]; have hp:=hx.2; linarith
    apply (bottles _ x hf (show 0≤u*u by positivity) (fun i n hn=> aiming_price ι B hu hC i _ hR x n hn) hn).trans
    change (C*(u*u))^n ≤ _
    have ht1:= pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right ht (show 0≤u*u by positivity)) n
    rw [mul_comm u (u*u)] at ht1
    exact (ht1.trans (pow_le_pow_right₀ (by nlinarith : 1≤u*u*u) hn)).trans ((le_add_of_nonneg_left (by positivity : 0≤u)).trans hM)
  have hy i : Z i x∈Icc (0:ℝ) 1 := B.r _
  have hv i : ‖L i x‖= (ξ/ε)* ‖facet ι G i x‖:= by change ‖(ξ/ε) • (facet ι G i x)‖ = _; rw [norm_smul,Real.norm_of_nonneg (by positivity)]
  change _∧ (_ → ∏ i,Z i x=1) ∧ (_ → ∏ i,Z i x=0)
  refine ⟨⟨Finset.prod_nonneg (fun i _=> (hy i).1),Finset.prod_le_one (fun i _=>(hy i).1) (fun i _=> (hy i).2)⟩,fun H=> ?_,fun H=>?_⟩
  · apply Finset.prod_eq_one; intro i _
    apply B.inner (L i x); rw [hv]; have hh:=piece_norm ι G i x
    have hw:= mul_le_mul_of_nonneg_left hh (show 0≤ξ/ε by positivity)
    apply hw.trans; rw [div_mul_eq_mul_div,div_le_iff₀ he₀]
    have hA: 8≤M*ε:=hs.trans (mul_le_mul_of_nonneg_right hu' he₀.le)
    nlinarith
  by_contra hr
  have hh (i:ι): ξ * ‖facet ι G i x‖ ≤ 1:= by
    have hw : ‖L i x‖ < 1/2:= by by_contra! hb; exact hr (Finset.prod_eq_zero (Finset.mem_univ i) (B.outer (L i x) hb))
    rw [hv,div_mul_eq_mul_div,div_lt_iff₀ he₀] at hw; have hb:=he.2; linarith
  have hN : (ξ*‖x‖)^2≤C:=by
    rw [mul_pow,←points, Finset.mul_sum]; have hz : ∀ i:ι, ξ^2*‖facet ι G i x‖^2 ≤ 1 := fun i=> by
      have hw := pow_le_pow_left₀ (by positivity) (hh i) 2; simpa [mul_pow] using hw
    exact (Finset.sum_le_sum (fun i _=> hz i)).trans_eq (by simp [C])
  change C≤u at ht; nlinarith

section Frost
variable {c f : Side} {r:Ratio c f} (F:Forest r) (G : Gauge)

def footage (T: Finset F.Free) : Sky (Index T G) →L[ℝ] AxisChart G F:=ContinuousLinearMap.pi fun i:F.Free =>
    if hi:i∈T then facet T G ⟨i,hi⟩ else (0: Sky (Index T G) →L[ℝ] G.Color)
lemma withered (T : Finset F.Free) (V:Sky (Index T G)) (o:F.Free):footage F G T V o=if hi:o∈T then facet T G ⟨o,hi⟩ V else 0 := by
   change (if hi:o∈T then facet T G ⟨o,hi⟩ else (0: Sky (Index T G) →L[ℝ] G.Color)) V= _; split <;> rfl
lemma frost_fee (T:Finset F.Free): ‖footage F G T‖ ≤ 1:= by
   apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one; intro v hv
   apply (pi_norm_le_iff_of_nonneg zero_le_one).2; intro i; rw [withered]; split
   · exact (piece_norm T G _ v).trans hv.le
   simp
end Frost
end YM.Planned.PrimaryIntegral295.Icebergs

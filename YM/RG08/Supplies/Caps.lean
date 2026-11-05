import YM.RG08.Cell.ReleaseHeat
 import YM.RG08.Flat.Entrance

/-!
# Kernel cost/difference supplies with pre-block common widths. Fixed-order scope at present:
flat quadratic, conditional Gaussian and tree-slice predictor. Height/delay asks *seen* by caller
constructing schedules. Costs common polynomial in the kbulk clock for all reporting k, arbitrary
scale i,N,k incl k≠i, post-length prices before the beta delay, no cofinal-period threshold. No
scalar nor any positive order coefficient claims here. In the bulk variables link rank-one is in
orthonormal (metric normalized trace) color coordinates.
-/
noncomputable section
namespace YM.RG08.Supplies
open Function Filter Lattice RG Tree Wilson Laurent Precision Pert.Bulk RG08.Flat RG08.Packets RG08.Line Stationary Bloch Matrix RG08.Rows RG08.Cell
open scoped Classical Matrix Topology BigOperators ENNReal
set_option autoImplicit false
variable {G : Gauge} {a : Levels G} {H : Horizon a} {P X : MapPrices}
abbrev stone (a:Levels G) (i:ℕ):= (a.clock.op i 0).patch

def PlanCurve (G:Gauge)(K:KernelChoices)(P : MapPrices) := fun i=> Classical.choose (warm_at G K P i)
set_option linter.defProp false in
def plan_hr (G:Gauge)(K:KernelChoices)(P:MapPrices) (i:ℕ) := Classical.choose_spec (warm_at G K P i)
def planSupply (G:Gauge)(K:KernelChoices)(P:MapPrices) := fun i=> Classical.choose (plan_hr G K P i|>.2.2)
set_option linter.defProp false in
def planSupply_spec (G:Gauge)(K:KernelChoices)(P:MapPrices)(i:ℕ) := Classical.choose_spec (plan_hr G K P i|>.2.2)

variable (G P X) (K:KernelChoices)
def peak (j:ℕ)(L : Side) (J: Patch) := -- post-L and nonnegative
   let p := planSupply G K P j L
   max 1 (max (Fintype.card (Co L (Loc G 1)):ℝ) (max p (max (key G J K) (max (Cell.allowance G J p) (laneTax L)))))

def delay (j:ℕ)(L : Side) := if he: ∃ T:Patch,T.J=j∧T.L=L then peak G P K j L he.choose else 1

lemma patch_peak (j:ℕ)(T:Patch)(he:T.J=j): delay G P K j T.L=peak G P K j T.L T:=by
  unfold delay
  let h : ∃ U:Patch,U.J=j∧U.L=T.L := ⟨T,he,rfl⟩
  rw [dif_pos h]; congr 1
  obtain ⟨ht,hH⟩:=Classical.choose_spec h
  have hx (P Q:Patch)(h:P.J=Q.J)(ht:P.L=Q.L):P=Q:=by cases P; cases Q; simp_all
  exact hx _ _ (ht.trans he.symm) hH

def Strip (j:ℕ) := min (PlanCurve G K P j) (curve X j)

variable {G P X K}
lemma positive_strip (j): 0 < Strip G P X K j := lt_min ((plan_hr G K P j).1) (curve_pos _ _)

variable (G P X a H) (Z : ℕ→ℝ)

-- When both covariances are indexed by actual steps of same calendar and supply. Don't claim if
-- switching auxiliary ratios at given mesh without their own rate costs. Y evaluated i+1 for
-- convenience to avoid skipping factor L outside powers. Additional shift to i can use L growth
-- gate in actual paid schedule. delay for every post cost and L can be stipulated jointly.
def Available := let K:=a.clock.kernel; ∀ i,delay G P K (a.clock.J (i+1)) (a.S.block i) ≤ Lambda a i

structure Holders (U : ℕ→ℕ→Kernel (Loc G 1) (Loc G 1)) (cross : Bool) (w : ℕ→ℝ) (A:ℝ) (d:ℕ)(c:ℝ) : Prop where
  est i k N : i<N →
    let L:=a.S.block i
    let coin:=A* clock a.S Z k (i+1)^d
    if cross then outward (U N i) L (w (a.clock.J (i+1))) coin else marketBill L (U N i) (w (a.clock.J (i+1))) coin
  step i k N m : i<N→N≤m→
    let L:=a.S.block i
    let p:=A*clock a.S Z k (i+1)^d*((a.S.a N / a.S.a (i+1))^c)
    if cross then outward (U N i-U m i) L (w (a.clock.J (i+1))) p else marketBill L (U N i-U m i) (w (a.clock.J (i+1))) p

def Sγ N i:= sliced (stone a i) a.clock.kernel G (H.H N (i+1))
def Sμ N i:= Cell.plotted (stone a i) a.clock.kernel G (H.H N (i+1))

variable {G P X a H Z}
private lemma warm_step (h : H.Suffices P)(i N:ℕ)(ht:i<N): Warm G a.clock.kernel (stone a i) (H.H N (i+1)) (PlanCurve G a.clock.kernel P (a.clock.J (i+1))) (planSupply G a.clock.kernel P (a.clock.J (i+1)) (a.S.block i)):=
   (planSupply_spec G a.clock.kernel P _).2 _ (a.blocks i 0).branches rfl _ (h.rows N (i+1) ht).2.1 _ _ (fun n=>h.all N (i+1) ht n)

-- buy-clock lemma
lemma delay_clock (hk : G.Simple) (hp: Available G a P) (i k :ℕ) : let T:=stone a i ; let j:=T.J
    peak G P a.clock.kernel j T.L T ≤ (2+G.slopeConstant)*clock a.S (Lambda' a) k (i+1) := by
  intro T j
  let c:= clock a.S (Lambda' a) k (i+1)
  have ht := hp i
  rw [← patch_peak G P a.clock.kernel j T rfl]
  refine ht.trans ?_
  unfold Lambda
  have hf:= a.fits.delayed k
  have hg := universeClock a hk k (i+1)
  have hβ : a.clock.hatBeta i≤ a.clock.hatBeta (i+1) := by
    unfold Calendar.hatBeta; change _≤_+_ * a.S.scale (i+1); rw [Schedule.scale_succ]; have h:=Gauge.slopeConstant_pos hk; gcongr; linarith only [Real.log_nonneg (show 1 ≤ ((a.S.block i).val:ℝ) from Nat.one_le_cast.mpr (a.S.block i).property)]
  have he := Real.log_le_log (zero_lt_one.trans (a.fits.delayed i)) hβ
  have hc:2≤ c:= by unfold c clock Lambda' Lambda; have hx:= Real.log_pos hf; have hp:=abs_nonneg (a.S.scale (i+1)-a.S.scale k); linarith
  change _ ≤ (2+G.slopeConstant)*c
  change _ ≤ (1+ G.slopeConstant)*c at hg
  nlinarith

 variable {θ η B A:ℝ}{J:Patch}{b : Bed}{K:KernelChoices}
lemma outbound (h:Warm G K J b η B)(he:0≤(θ:ℝ))(ht:θ ≤ η)(hσ:η≤1):
 marketBill J.L (sliced J K G b) θ (laneTax J.L*B) ∧ outward (Cell.plotted J K G b) J.L θ (laneTax J.L*(B*key G J K)):=by
  refine ⟨market_release (h.bill.toPriced.mono ht le_rfl) he (ht.trans hσ),?_⟩
  have hp:= ((predictor_price J K G b h (he.trans ht) hσ).toPriced.mono ht le_rfl)
  have hx := out_bill he hp
  have hv : (J.L.val:ℝ)^4 * Real.exp (4*θ) ≤ laneTax J.L:=by unfold laneTax; have hy:=ht.trans hσ; gcongr; linarith
  exact ⟨fun x i=>(hx.row x i).trans (by gcongr; exact hp.pos),fun i x=>(hx.col i x).trans (by gcongr; exact hp.pos),hx.marked⟩

private def quote (G:Gauge) (A:ℝ) := (2+G.slopeConstant)^3*(2*max A 1)
lemma quote_ge (hk:G.Simple) {W e A:ℝ}(d:ℕ)(hW:1≤W)(he:e≤(2+G.slopeConstant)*W)(hE:0≤e)(ha:0≤A) :
    e*e ≤ quote G A*W^(d+3) ∧ e*(e*e) ≤ quote G A*W^(d+3) ∧ e^3*(2*A*W^d) ≤ quote G A*W^(d+3) := by
 let h:=2+G.slopeConstant
 have ht:1≤h:=by unfold h; linarith [Gauge.slopeConstant_pos hk]
 have hp:0<h:=zero_lt_one.trans_le ht
 have hr: 0≤ max A 1:=le_trans zero_le_one (le_max_right ..)
 have hv: e^3 ≤ (h*W)^3 := pow_le_pow_left₀ hE he _
 have hT : (h*W)^3 ≤ quote G A*W^(d+3):=by
   have hh : W^3 ≤ W^(d+3):= pow_le_pow_right₀ hW (by omega)
   unfold quote; unfold h
   rw [mul_pow]; gcongr; have h': 1 ≤ max A 1:=le_max_right ..; exact le_mul_of_one_le_right (show 0 ≤ h^3 by positivity) (by linarith)
 refine ⟨?_,show _ from (by rw [show e*(e*e)=e^3 by ring]; exact hv.trans hT),?_⟩
 · have hh := pow_le_pow_right₀ (show 1 ≤ h*W from one_le_mul_of_one_le_of_one_le ht hW) (show 2 ≤ 3 by decide)
   exact (mul_self_le_mul_self hE he).trans ((show (h*W)*(h*W) ≤ _ from (by rw [← sq]; exact hh)).trans hT)
 calc _ ≤ (h*W)^3*(2*A*W^d):=by gcongr
      _ ≤ h^3*(2*(max A 1))*W^(d+3):= by rw [mul_pow,pow_add]; have hA:A≤max A 1:= le_max_left ..; calc _ = h^3*(2*A)*(W^d*W^3):=by ring
                                                                      _ ≤ _:=by gcongr

variable {H₀ : ℕ→Kernel Links Links}
/-- Quantitative transmission kfalt of slice line and A_tr on any actual plan with earlier kfalt
precision and delayed post length costs. Width `Strip` computed only in visible pre-length data.
Gaussians priced at relative coarse-unit distance (delta in our APIs, marketBill uses fine
sep/L); any further fine-unit widths of re-expression operations need explicit rescaling as in
the separate consumers.
-/
theorem vessel {A F c : ℝ}{d l:ℕ}(hk:G.Simple)(h:H.Suffices P)(hf : Quorum (curve X) H₀ 0 H A F d l c)
    (hp : Available G a P):
    ∃ B e,0≤B ∧ 0<c ∧ Holders G a (Lambda' a) (Sγ G a H) false (Strip G P X a.clock.kernel) B e c ∧ Holders G a (Lambda' a) (Sμ G a H) true (Strip G P X a.clock.kernel) B e c := by
  let k:= a.clock.kernel; let s := Strip G P X k
  let Y x i := clock a.S (Lambda' a) x (i+1)
  have hA:=hf.logged
  have hg : 0 ≤ quote G A:=by unfold quote; have he := Gauge.slopeConstant_pos hk; have hC:0≤max A 1:=le_trans zero_le_one (le_max_right ..); positivity
  have ht (i) := positive_strip (G:=G) (P:=P) (K:=k) (X:=X) ((a.clock.J i))
  have he x i : 1 ≤ Y x i := by have ht:=a.fits.delayed x; unfold Y clock Lambda' Lambda; have hh:=Real.log_pos ht; have hz:=abs_nonneg (a.S.scale (i+1)-a.S.scale x); linarith
  let cap x i := quote G A * Y x i ^ (d+3)
  let bill x i N := cap x i * ((a.S.a N/a.S.a (i+1))^c)
  have HH x i N m (hI:i<N)(hm:N≤m) : let w:=s (a.clock.J (i+1)); let L:=a.S.block i;
      (marketBill L (Sγ G a H N i) w (cap x i) ∧ outward (Sμ G a H N i) L w (cap x i)) ∧
        marketBill L (Sγ G a H N i-Sγ G a H m i) w (bill x i N) ∧ outward (Sμ G a H N i-Sμ G a H m i) L w (bill x i N):= by
    intro u L
    let j:=a.clock.J (i+1); let T:=stone a i
    let v:=PlanCurve G k P j; let p:= planSupply G k P j L
    let b:= H.H m (i+1); let b':=H.H N (i+1)
    have hz := lt_of_lt_of_le hI hm
    have hv : Warm G k T b v p:=warm_step h _ _ hz
    have hv' : Warm G k T b' v p:=warm_step h _ _ hI
    have hU : 0<u:=ht (i+1)
    have hV : u ≤ v:= min_le_left ..
    have hL: v≤1:= (plan_hr G k P j).2.1
    have hb : b.metric.strip (P.α j) (P.Ω j) := (h.rows m (i+1) hz).2.1
    have hb' : b'.metric.strip (P.α j) (P.Ω j) := (h.rows N (i+1) hI).2.1
    let g n := (a.S.a n /a.S.a (i+1))^c
    let r := A*Y x i ^ d
    have hR : 0≤r := mul_nonneg hA (pow_nonneg (zero_le_one.trans (he ..)) _)
    have ha n : 0 ≤ g n:= by unfold g; have h:=a.S.a_pos n; have he:=a.S.a_pos (i+1); positivity
    have hQ (n) (hn:i<n): RowCost (curve X j) 1 (fun x z=> output (H.H n (i+1)) x z-H₀ (i+1) x z) (r*g n):=hf.approximates x (i+1) n (by omega) hn
    have hh := subtract_row (hQ m hz) (hQ N hI) (mul_nonneg hR (ha _)) (mul_nonneg hR (ha _))
    have hS : r*g m+r*g N ≤ 2*r*g N := by
      have hw : g m≤g N:=by unfold g; have hbase:=a.S.a_pos (i+1); have hc := hf.positive.le; have ht:= a.S.a_pos m; gcongr; exact a.S.strictAnti.antitone hm
      nlinarith only [mul_le_mul_of_nonneg_left hw hR]
    have hf' : RowCost (curve X j) 1 (changeK b b') (2*r*g N):= by
      have hC : changeK b b' = fun v y => (fun v y=> output b v y-H₀ (i+1) v y) v y-(fun v y=> output b' v y-H₀ (i+1) v y) v y:=by funext i j; change output b i j-output b' i j=output b i j-_-(_-_); ring
      exact hC.symm ▸ fun v e=> (hh v e).trans (ENNReal.ofReal_le_ofReal hS)
    have hΞ: u ≤ (L.val:ℝ)*curve X j:= le_trans (min_le_right ..) (le_mul_of_one_le_left (curve_pos ..).le (by exact_mod_cast L.pos))
    let B:= Cell.allowance G T p*(2*r*g N)
    have hδ : Priced u B (warm T k G b'-warm T k G b):= earn_grid _ _ _ b b' hv hv' (h.all m _ hz) (h.all N _ hI) hf' (by have h1:=ha N; positivity) hb hb' (P.alpha_pos _).le (Ω_pos h _) hU.le hV (hV.trans hL) hΞ
    obtain ⟨hm0,ho0⟩:= outbound hv' hU.le hV hL
    obtain ⟨hm1,ho1⟩:= trays hv hv' hU hV hL hδ
    let e:= peak G P k j L T
    have hP0 : 1≤e:= le_max_left ..
    have hm0' : laneTax L ≤ e:= le_trans (le_max_right ..) (le_trans (le_max_right ..) ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))) -- count max
    have heP : p ≤ e:= le_trans (le_max_left ..) ((le_max_right ..).trans (le_max_right ..))
    have heW : key G T k ≤ e:= le_trans (le_max_left ..) (le_trans (le_max_right ..) ((le_max_right ..).trans (le_max_right ..)))
    have heA : Cell.allowance G T p ≤ e:= le_trans (le_max_left ..) (le_trans (le_max_right ..) ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))))
    obtain ⟨hr,hX,hY⟩ := quote_ge hk d (he x i) (delay_clock hk hp i x) (zero_le_one.trans (le_max_left ..) : (0:ℝ)≤e) hA
    have hkey : 0 ≤ p*key G T k:= (predictor_price T k G b hv (hU.le.trans hV) hL).pos
    have hPP:=hv.bill.pos
    have hB:B ≤ e*(2*A*Y x i^d*g N):=by
      unfold B r
      calc _ ≤ e*(2*(A*Y x i^d)*g N):= mul_le_mul_of_nonneg_right heA (by have h := he x i; have ht := ha N; positivity)
           _ = _:= by ring
    have hzN := ha N
    have hrN : laneTax T.L * B ≤ e^2*(2*A*Y x i^d)*g N := by
      exact (mul_le_mul hm0' hB hδ.pos (zero_le_one.trans hP0)).trans_eq (by ring)
    have hBn: laneTax T.L * B ≤ bill x i N := by
      have hw := pow_le_pow_right₀ hP0 (show 2 ≤ 3 by decide)
      exact hrN.trans (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hw (by have h:=he x i; positivity)).trans hY) hzN)
    have hN':0≤key G T k:= by unfold key; have h:0 ≤ toll_probe T k G:= (probes_on T k G).pos; have hh:=k.penalty_pos; positivity
    have hN : laneTax T.L*(key G T k*B) ≤ bill x i N := by
      calc _ ≤ e*(e*(e*(2*A*Y x i^d*g N))):=by gcongr <;> first | exact hm0' | exact hδ.pos | exact mul_nonneg hN' hδ.pos -- clean
           _ = (e^3*(2*A*Y x i^d))*g N:=by ring
           _ ≤ _:=mul_le_mul_of_nonneg_right hY hzN
    have h0 : laneTax T.L*p ≤ cap x i:= (mul_le_mul hm0' heP hPP (zero_le_one.trans hP0)).trans hr
    have h1 : laneTax T.L*(p*key G T k) ≤ cap x i:= (mul_le_mul hm0' (mul_le_mul heP heW hN' (zero_le_one.trans hP0)) hkey (zero_le_one.trans hP0)).trans hX
    exact ⟨⟨⟨fun v i=>(hm0.1 v i).trans (ENNReal.ofReal_le_ofReal h0),fun i v=>(hm0.2.1 i v).trans (ENNReal.ofReal_le_ofReal h0),hm0.2.2⟩,⟨fun v i=>(ho0.row v i).trans (ENNReal.ofReal_le_ofReal h1), fun i v=>(ho0.col i v).trans (ENNReal.ofReal_le_ofReal h1),ho0.marked⟩⟩,⟨fun v i=>(hm1.1 v i).trans (ENNReal.ofReal_le_ofReal hBn),fun i v=>(hm1.2.1 i v).trans (ENNReal.ofReal_le_ofReal hBn),hm1.2.2⟩,⟨fun v i=>(ho1.row v i).trans (ENNReal.ofReal_le_ofReal hN),fun i v=>(ho1.col i v).trans (ENNReal.ofReal_le_ofReal hN),ho1.marked⟩⟩
  refine ⟨quote G A,d+3,hg,hf.positive,⟨fun i k N h=>?_,fun i k N m h hh=>?_⟩,⟨fun i k N h=>?_,fun i k N m h hh=>?_⟩⟩
  · simp only [Bool.false_eq_true,↓reduceIte]; exact (HH k i N N h le_rfl).1.1 -- motive?
  · simp only [Bool.false_eq_true,↓reduceIte]; exact (HH k i N m h hh).2.1
  · simp only [↓reduceIte]; exact (HH k i N N h le_rfl).1.2
  simp only [↓reduceIte]; exact (HH k i N m h hh).2.2
end YM.RG08.Supplies

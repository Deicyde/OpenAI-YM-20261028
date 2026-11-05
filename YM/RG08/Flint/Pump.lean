import YM.RG08.Jetty.Chests

/-! # Cover evaluation on mildly growing cochain directions
Finitary charges & summation/elimination of covers. Can also use general summed-tape budgets
if widths η not transferred slotwise. Growth for Ward RHS. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Flint
open Jetty Forms Function Finset Filter Lattice
open scoped Topology ENNReal Classical BigOperators
variable {I J:Type}{p d n:ℕ}{σ δ C:ℝ}

def hustle (p:ℕ)(δ r:ℝ):ℝ:= (1+r)^p * Real.exp (δ*r)
lemma one_le_hustle (p:ℕ)(he:0≤δ){r:ℝ}(hr:0≤r):1≤hustle p δ r:= one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (Real.one_le_exp (mul_nonneg he hr))
lemma hustle_nn (p:ℕ)(δ:ℝ){r:ℝ}(hr:0≤r):0≤hustle p δ r:= mul_nonneg (pow_nonneg (le_add_of_nonneg_left zero_le_one|>.trans' hr) p) (Real.exp_pos _).le
lemma hustle_in (he:0≤δ){r t:ℝ}(hr:0≤r)(hu:r≤t):hustle p δ r≤hustle p δ t:=mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) _) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu he)) (Real.exp_pos _).le (pow_nonneg (by linarith) _)
lemma hustle_plus (_he:0≤δ){r t:ℝ}(hr:0≤r)(ht:0≤t):hustle p δ (r+t)≤hustle p δ r*hustle p δ t:=by
 unfold hustle;rw [mul_add,Real.exp_add]
 apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (show 1+(r+t)≤(1+r)*(1+t) from by nlinarith only [mul_nonneg hr ht]) p) (by positivity :0≤Real.exp (δ*r)*_)).trans_eq
 rw [mul_pow];ring
/-- powers of the envelope are another envelope -/
lemma hustle_pow (p k:ℕ)(δ r:ℝ):hustle p δ r ^ k=hustle (p*k) ((k:ℝ)*δ) r:=by rw [hustle,mul_pow,←pow_mul,← Real.exp_nat_mul,hustle,mul_assoc]
lemma hustle_fee (u:ℕ){r:ℝ}(h:0<σ)(hr:0≤r):(1+r)^u≤ blade 0 u σ * Real.exp (σ*r):=by
 unfold blade;push_cast;rw [one_mul]
 rcases Nat.eq_zero_or_pos u with hz|hz
 · subst u;simp only [pow_zero,one_mul];exact Real.one_le_exp (mul_nonneg h.le hr)
 have hu:0<(u:ℝ):=Nat.cast_pos.mpr hz
 let b:=σ*r/(u:ℝ)
 rw [show σ*r=(u:ℝ)*b from by unfold b;field_simp,Real.exp_nat_mul,←mul_pow]
 apply pow_le_pow_left₀ (by linarith)
 have H:1+r≤(1+(u:ℝ)/σ)*(1+b):=by unfold b;field_simp;nlinarith [mul_nonneg h.le hr]
 exact H.trans (mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp b]) (by positivity))

abbrev Top (L:Loom I)(x:Tape n I):=L.cage x
/-- one unit test **per exposed cochain**, before sum over y. -/
def Bearing (L:Loom I)(p:ℕ)(δ:ℝ)(K:ℝ)(X:I→ℝ):Prop:=0≤K ∧ ∀ i, |X i| ≤ K*hustle p δ (L.height i)
variable {L:Loom I}{K K':ℝ}{X Y:I→ℝ}
lemma Bearing.nil : Bearing L p δ 0 (0:I→ℝ):=by simp [Bearing]
lemma Bearing.up (he:Bearing L p δ K X)(hz:K≤K'):Bearing L p δ K' X:=⟨he.1.trans hz,fun i=>(he.2 i).trans (mul_le_mul_of_nonneg_right hz (hustle_nn p _ (L.nn _)))⟩
lemma Bearing.smul (he:Bearing L p δ K X)(a:ℝ):Bearing L p δ (|a| *K) (a • X):=by
 refine ⟨mul_nonneg (abs_nonneg _) he.1,fun i=>?_⟩; rw [Pi.smul_apply,smul_eq_mul,abs_mul,mul_assoc];exact mul_le_mul_of_nonneg_left (he.2 i) (abs_nonneg _)
lemma Bearing.add (he:Bearing L p δ K X)(hu:Bearing L p δ K' Y):Bearing L p δ (K+K') (X+Y):=by
 refine ⟨add_nonneg he.1 hu.1,fun i=>?_⟩;rw [Pi.add_apply,add_mul];exact (abs_add_le ..).trans (add_le_add (he.2 _) (hu.2 _))
lemma Bearing.sum {J:Type}{V:J→I→ℝ}{a:J→ℝ}(s:Finset J)(hs:∀ j∈s,Bearing L p δ (a j) (V j)):Bearing L p δ (s.sum a) (s.sum V):=by
 induction s using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty];exact Bearing.nil
 | @insert j s hj ih=>rw [sum_insert hj,sum_insert hj];exact (hs _ (by simp)).add (ih (fun i hi=>hs _ (by simp [hi])))

def Covering (L:Loom I)(σ:ℝ)(n:ℕ)(C:ℝ)(a:Tape n I→ℝ):Prop:=0≤C∧∀ i, |a i|≤C*Real.exp (σ*Top L i)

def flakes (V:Fin n→I→ℝ)(x:Tape n I):ℝ:= ∏ j:Fin n,V j (x j)
def tribute {n:ℕ}(p:ℕ)(σ:ℝ)(a:Fin n→ℝ):ℝ := blade 0 (p*n) (σ/2)*∏ j:Fin n,a j
lemma tribute_nn {a:Fin n→ℝ}(σ:ℝ)(h:0≤σ)(hs:∀ i,0≤a i)(p:ℕ):0≤tribute p σ a:= mul_nonneg (blade_nn _ _ (by positivity)) (prod_nonneg fun i _=>hs i)
lemma flakes_cover (h:0<σ)(he:0≤δ)(hs:(n:ℝ)*δ≤σ/2)(a:Fin n→ℝ)(V:Fin n→I→ℝ)(hb:∀ i,Bearing L p δ (a i) (V i)):
 Covering L σ n (tribute p σ a) (flakes V):=by
 have hv(j):0≤a j:=(hb j).1
 refine ⟨tribute_nn _ h.le hv p,fun x=>?_⟩
 let r:=Top L x; have hr:0≤r:=L.cage_nn _
 rw [flakes,Finset.abs_prod];calc
  _ ≤ ∏ j:Fin n,(a j*hustle p δ r):=prod_le_prod (fun _ _=>abs_nonneg _) fun i _=> ((hb i).2 _).trans (mul_le_mul_of_nonneg_left (hustle_in he (L.nn _) (L.float ..)) (hv i))
  _ = (∏ j,a j)*hustle (p*n) ((n:ℝ)*δ) r:=by rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,hustle_pow]
  _ ≤ _:=by
    let D:=blade 0 (p*n) (σ/2)
    have hz:=mul_le_mul (hustle_fee (p*n) (half_pos h) hr) (Real.exp_le_exp.mpr (show (n:ℝ)*δ*r≤σ/2*r by nlinarith only [hr,hs])) (Real.exp_pos ((n:ℝ)*δ*r)).le (mul_nonneg (blade_nn 0 _ (half_pos h).le) (Real.exp_pos _).le)
    rw [mul_assoc (blade 0 (p*n) (σ/2)),←Real.exp_add,show σ/2*r+σ/2*r=σ*r by ring] at hz
    unfold tribute
    exact (mul_le_mul_of_nonneg_left hz (prod_nonneg fun _ _=>hv _)).trans_eq (by ring)

-- purchase tape collectively (μ not needed for test evaluation).
def tote (F:Pack n I)(f:Pearl)(a:Tape n I→ℝ)(x:Tape n I):=F x f*a x
lemma tote_bound (F:Pack n I)(f:Pearl)(h:0<σ)(hv:Lyrics F){a:Tape n I→ℝ}(ha:Covering L σ n C a)(x:Tape n I):
 ENNReal.ofReal |tote F f a x| ≤ gems L d h F x * ENNReal.ofReal (C*beam d h f):=by
 rw [tote,abs_mul,ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_mul ha.1]
 apply (mul_le_mul' (purse_gives h d (hv x) f) (ENNReal.ofReal_le_ofReal (ha.2 x))).trans_eq
 rw [ENNReal.ofReal_mul ha.1];unfold gems weft; ring -- ENN? ring requires semiring
lemma tote_sums (F:Pack n I)(f:Pearl)(h:0<σ)(hv:Lyrics F)(B:ℝ)(hb:0≤B)(hh:Sings L d h F B){a:Tape n I→ℝ}(ha:Covering L σ n C a):
 Summable (fun x=> ‖tote F f a x‖) ∧ |∑' x,tote F f a x| ≤ C * B * beam d h f:=by
 let g(x:Tape n I):= ‖tote F f a x‖
 have he : (∑' x,ENNReal.ofReal (g x)) ≤ ENNReal.ofReal (B*(C*beam d h f)):=by
    rw [ENNReal.ofReal_mul hb];apply (ENNReal.tsum_le_tsum (g:=fun i=>gems L d h F i *ENNReal.ofReal (C*beam d h f)) (fun i=>by unfold g;rw [Real.norm_eq_abs];exact tote_bound _ _ _ hv ha i)).trans
    rw [ENNReal.tsum_mul_right]; exact mul_le_mul_left hh _
 have hs:= ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top he)
 have hg:Summable g:=hs.congr fun i=>ENNReal.toReal_ofReal (norm_nonneg _)
 rw [←ENNReal.ofReal_tsum_of_nonneg (fun i=>norm_nonneg _) hg] at he
 refine ⟨hg,(Real.norm_eq_abs _).symm.trans_le ((norm_tsum_le_tsum_norm hg).trans ?_)⟩
 rw [mul_comm C B,mul_assoc];exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hb (mul_nonneg ha.1 (beam_nn ..)))).mp he

/-- aligned cell stance, real labels BEFORE PSG -/
def sonic (F:Pack n I)(f:Pearl)(V:Fin n→I→ℝ):=∑' x,tote F f (flakes V) x
variable {F:Pack n I}{h:0<σ}{B:ℝ}
lemma sonic_le (he:Lyrics F)(hh:Sings L d h F B)(hb:0≤B)(f:Pearl)
  {a:Fin n→ℝ}{V:Fin n→I→ℝ}(hx:0≤δ)(hy:(n:ℝ)*δ≤σ/2)(hz:∀ i,Bearing L p δ (a i) (V i)):|sonic F f V|≤ tribute p σ a * B * beam d h f:= (tote_sums _ _ _ he _ hb hh (flakes_cover h hx hy _ _ hz)).2
lemma sonic_abs (he:Lyrics F)(hh:Sings L d h F B)(hb:0≤B)(f:Pearl){a:Fin n→ℝ}{V:Fin n→I→ℝ}(hx:0≤δ)(hy:(n:ℝ)*δ≤σ/2)(hz:∀ i,Bearing L p δ (a i) (V i)):Summable (fun x=>‖F x f*∏ i:Fin n,V i (x i)‖):= (tote_sums _ _ _ he _ hb hh (flakes_cover h hx hy _ _ hz)).1
end YM.RG08.Flint

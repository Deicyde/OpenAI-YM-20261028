import YM.OPE.Log.Plans
import YM.OPE.Prices.Space
import YM.OPE.Log.Wallet
/-! # Register short-coast licenses -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Function Set Filter Lattice RG Wilson MergeProof Accent Ribbons Source Overlay Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage ManyCopies
open scoped Topology BigOperators
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{ι I:Type*}{l: Filter ι}{T x:ι→ℝ}{a:ℝ}
    {m k:ι→ℕ} {W r D} (L : LogPackage C W r D)(hG : G.Simple)
local notation "Y"=> C.path.levels
local notation "S'"=> C.path.levels.budget
local notation "Γ"=> C.path.levels.clock
local notation "β"=> C.path.levels.clock.hatBeta
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
variable (hT:Tendsto T l atTop)
include hT
lemma scaleWallet (h:Height C.S l T m a) : Wallet l T (fun i=> C.S.scale (m i)):= by
    apply ((Wallet.from_tends hT h.pace).mul (Wallet.id hT)).congr
    filter_upwards [hT.eventually_gt_atTop 0] with i hi; field_simp
lemma betaStamp (h:Height C.S l T m a): ValueStamp l T (fun i=> C.path.levels.clock.hatBeta (m i)):=
    ⟨Eventually.of_forall (fun _=>zero_lt_one.trans ((Y).fits.delayed _)),
     (Wallet.const hT _).add hT ((Wallet.const hT _).mul (scaleWallet hT h)),
     ((ValueStamp.const hT one_pos).down).invLe (Eventually.of_forall (fun _ => one_pos)) (Eventually.of_forall (fun _=> ((Y).fits.delayed _).le))⟩
include L in
lemma blockWallet (h:Height C.S l T m a): ValueStamp l T (fun i=> (C.path.S.block (m i)).val):=
    ⟨Eventually.of_forall fun i=> zero_lt_two.trans_le (ManyCopies.size_enough C.path (m i)), 
     (betaStamp hT h).up.of_le (Eventually.of_forall fun i=> Nat.cast_nonneg _) (Eventually.of_forall fun i=> L.money.mesh _), (ValueStamp.const hT one_pos).down.invLe (Eventually.of_forall fun _=> one_pos) (Eventually.of_forall (fun _=> one_le_two.trans (size_enough C.path _)))⟩
lemma coverWallet (h:Height C.S l T m a) : Wallet l T (fun i=> ((C.path.levels.budget (m i)).B:ℝ)):=by
    apply (((betaStamp hT h).up.pow hT 2).add hT (Wallet.const hT (1:ℝ))).of_le (Eventually.of_forall fun i=> Nat.cast_nonneg _)
    refine Eventually.of_forall fun i=>?_ ; let u:= β (m i); have hu:1 < u:= (Y).fits.delayed _; refine le_trans (Nat.ceil_lt_add_one (sq_nonneg (Real.log u))|>.le) (add_le_add_left ?_ 1); exact pow_le_pow_left₀ (Real.log_nonneg hu.le) (Real.log_le_self (by linarith only [hu])) _
include L in
lemma columnsWallet (h:Height C.S l T m a): Wallet l T (fun i=> (C.path.levels.params (m i)).columns):=
    (betaStamp hT h).up.of_le (Eventually.of_forall fun _=> zero_le_one.trans ( (Y).params _).columns_ge) (Eventually.of_forall fun i=> L.money.present _)
omit hT in
lemma price_paid (Q:Levels G)(i:ℕ): renal Q i = (Q.clock.hatBeta (i+1)^2)⁻¹:= by unfold renal probe; rw [Real.rpow_neg (zero_le_one.trans (Q.fits.delayed _).le),Real.rpow_ofNat]
lemma renalStamp (h:Height C.S l T m a): ValueStamp l T (fun i => renal C.path.levels (m i)):= by
    simp_rw [price_paid]; exact ((betaStamp hT (h.step (Y).fits.mesh)).pow hT 2).inv
lemma nearStamp (h: Height C.S l T m a) : ValueStamp l T (fun i=> near C.path.levels (m i)):= (betaStamp hT (h.step (Y).fits.mesh)).inv
lemma flyStamp (h: Height C.S l T m a)(d:ℕ) : ValueStamp l T (fun i=> fly C.path.levels d (m i)):= ((betaStamp hT h).pow hT (MergeProof.winter G d)).inv

omit hT
local notation "L'"=> LogPackage C W r D
local notation "i'"=> (Nat.ceil (256*Real.log (C.path.levels.clock.hatBeta (_+1)))) -- leave?
include L
lemma shortened_choice i : ∃ w,8 ≤ w ∧ 1 ≤ renal C.path.levels i*mintK w:=by
    have he:= L.system.costs.stay.mint i (Nat.zero_le _); have hx:η i ≤ 1:= inv_le_one_of_one_le₀ ((Y).fits.delayed _).le
    exact ⟨_,L.system.costs.stay.support i (Nat.zero_le _), he.trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right ((L.system.costs.stay.water i (Nat.zero_le _)).2.le) hx) (Real.exp_pos _).le)⟩
open scoped Classical
-- canonical license cut, monotone in β
def short (i:ℕ) := Nat.find (shortened_choice L i)
lemma short_affords (i:ℕ): 8 ≤ short L i ∧ short L i ≤ (C.path.levels.budget i).B ∧ 1 ≤ renal C.path.levels i*mintK (short L i) :=by
    classical
    have he:= Nat.find_spec (shortened_choice L i); refine ⟨he.1,?_,he.2⟩; unfold short; refine Nat.find_min' _ ⟨L.system.costs.stay.support i (Nat.zero_le _),?_⟩
    have he:= L.system.costs.stay.mint i (Nat.zero_le _); have hx: η i ≤ 1:= inv_le_one_of_one_le₀ ((Y).fits.delayed _).le
    exact he.trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right ( (L.system.costs.stay.water i (Nat.zero_le _)).2.le) hx) (Real.exp_pos _).le)
include hG in
lemma renalAnti : Antitone (renal C.path.levels) :=by
    intro i j hi; rw [price_paid,price_paid]; let p:= G.slopeConstant; have hq:= Gauge.slopeConstant_pos hG
    have he: β (i+1) ≤ β (j+1):=add_le_add_right (mul_le_mul_of_nonneg_left ((scale_mono _).monotone (Nat.succ_le_succ hi)) hq.le) _ -- check order
    exact inv_anti₀ (pow_pos (zero_lt_one.trans ((Y).fits.delayed _)) _) (pow_le_pow_left₀ (zero_le_one.trans ((Y).fits.delayed _).le) he _)
omit hG
lemma short_mono (hG:G.Simple): Monotone (short L):= fun i j hij=> Nat.find_min' _ ⟨(short_affords L j).1,(short_affords L j).2.2.trans (mul_le_mul_of_nonneg_right (renalAnti L hG hij) (Real.exp_pos _).le)⟩
lemma short_upper i : (short L i:ℝ) ≤ 256*Real.log (C.path.levels.clock.hatBeta (i+1))+9:=by
    classical
    let x:=β (i+1); let u:=256*Real.log x; let y:=Nat.ceil u
    have hv:1<x:= (Y).fits.delayed _; have hp:0 ≤ u:= mul_nonneg (by norm_num) (Real.log_nonneg hv.le)
    have hu:u ≤ y:= Nat.le_ceil _; have hy:x^2 ≤ mintK (y+8):= by
        unfold mintK; calc
          x^2 = Real.exp ((↑(2:ℕ):ℝ)*Real.log x):= by rw [Real.exp_nat_mul,Real.exp_log (by linarith only [hv])]
          _ ≤ _:=by apply Real.exp_monotone; push_cast; unfold u at hu; linarith only [hu]
    have hf : short L i ≤ y+8:=Nat.find_min' _ ⟨by omega,by rw [price_paid,mul_comm, ← div_eq_mul_inv]; exact (one_le_div (pow_pos (zero_lt_one.trans hv) _)).2 hy⟩
    have hg : (short L i:ℝ) ≤ (y+8:ℕ):= Nat.cast_le.mpr hf; push_cast at hg; change (short L i:ℝ) ≤ u+9; linarith only [hg, show (y:ℝ) < u+1 from Nat.ceil_lt_add_one hp]

def solvency (H i:ℕ) := (license C.path δ H (short L i+2) i)*renal C.path.levels i
lemma solvency_pos (i:ℕ){H:ℕ} (hp:0<H):0 < solvency L H i:= mul_pos (license_pos _ _ (L.system.costs.stay.water _ (Nat.zero_le i)|>.2) hp) (L.system.costs.stay.water _ (Nat.zero_le i)|>.2)
lemma renal_le (i:ℕ):renal C.path.levels i≤1:= by rw [price_paid]; exact inv_le_one_of_one_le₀ (one_le_pow₀ ((Y).fits.delayed (i+1)|>.le))
lemma solvency_le (i:ℕ){H:ℕ}(h:0<H):solvency L H i ≤ 1:=by
    have hU:0<δ i:=(L.system.costs.stay.water i (Nat.zero_le _)).2; have ht:=renal_le L i; let x:=δ i; have hx:1 ≤ (H:ℝ):=(by exact_mod_cast h); let p:=license C.path δ H (short L i+2) i
    have hp : p≤1:= by unfold p license; exact (div_le_self (by positivity) (Real.one_le_exp (mul_nonneg (add_nonneg (S' i).exponent_pos.le (by norm_num)) (Nat.cast_nonneg _)))).trans ((mul_le_of_le_one_left hU.le ((div_le_self hU.le hx).trans ht)).trans ht)
    exact (mul_le_of_le_one_left hU.le hp).trans ht
lemma solvency_anti (H:ℕ)(h:0<H)(hG:G.Simple): Antitone (solvency L H):= by
    intro i j hi; have hr:= renalAnti L hG hi; have hU(i):0≤δ i:= (L.system.costs.stay.water i (Nat.zero_le _)|>.2).le; have hs: (short L i+2:ℕ) ≤ short L j+2:= Nat.add_le_add_right (short_mono L hG hi) _
    unfold solvency license; simp_rw [show ∀ i,(S' i).supportExponent = (100:ℝ) from L.support]
    have hf:=hU i; have hf':=hU j; gcongr

include hT
lemma solvency_stamp {H:ℕ} (h:Height C.S l T k a)(hp:0<H): ValueStamp l T (fun i=> solvency L H (k i)):= by
   let p i:=short L (k i)+2; let f i:= Real.exp ((100+(1/2:ℝ))* p i); let x i:=β (k i +1)
   have hx:ValueStamp l T x:= betaStamp hT (h.step (Y).fits.mesh)
   have he(i): Real.log (f i) ≤ (100+(1/2:ℝ))*11+ 25728*Real.log (x i):= by
       have hh : (p i:ℝ) ≤ 256*Real.log (x i)+11:=by unfold p; push_cast; linarith only [show (short L (k i):ℝ) ≤ 256*Real.log (x i)+9 from short_upper L (k i)]
       unfold f; rw [Real.log_exp]; linarith only [hh]
   have hf : ValueStamp l T f:=by
       refine ⟨Eventually.of_forall fun _=> Real.exp_pos _, ?_,(ValueStamp.const hT one_pos).down.invLe (Eventually.of_forall fun _=>one_pos) (Eventually.of_forall fun i=> Real.one_le_exp (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
       apply ((Wallet.const hT (Real.exp ((100+(1/2:ℝ))*11))).mul (hx.up.pow hT 25728)).of_le' (Eventually.of_forall fun _=> Real.exp_pos _) -- nat large simpl?
       filter_upwards [hx.profit] with i hi; let y:= Real.exp ((100+(1/2:ℝ))*11); have hz: y*x i^25728=Real.exp ((100+(1/2:ℝ))*11+25728*Real.log (x i)):= by rw [Real.exp_add,show (25728:ℝ)= (↑(25728:ℕ):ℝ) from (by norm_num),Real.exp_nat_mul,Real.exp_log hi]
       rw [show Real.exp _ * x i^25728= _ from hz]; exact Real.le_exp_of_log_le (he i)
   have hd:=renalStamp hT h; unfold solvency license; simp_rw [show ∀ i,(S' i).supportExponent=(100:ℝ) from L.support]; exact ((((hd.div (ValueStamp.const hT (Nat.cast_pos.mpr hp))).mul hd).div hf).mul hd)
end YM.OPE.Log

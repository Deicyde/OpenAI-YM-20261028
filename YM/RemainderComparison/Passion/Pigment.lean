import YM.RemainderComparison.Passion.Sounds
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Passion
open Function Filter Set Finset Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker
open Solos Mosaic Verse Serif Flues WickReps Ethereal Lacuna Lobby
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{D :ι→ Finset θ}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {G:Gauge}{n:Side}{I:Type}
variable (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι)
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
namespace SeatD
variable (S:SeatD G n) (X:Hol G) (K:Support n) (M:MaskType)
local notation "hold'" => Local.joint S.sectionQ S.origin K
local notation "A'"=> S.basis
local notation "e₀"=> S.basis.e0
local notation "L₂"=> seeing S K M
variable (z:ℝ)
local notation "o"=> S.origin
local notation "A"=> S.sectionQ
variable {b: ℝ} {k t:ℕ}{f:PairD S}
-- uniform bound literal without *roominess* growth assumed
lemma visits' (x:Site n) (h: x∈ SeatD.suit S) : separation S.origin x ≤ Local.atomRadius S.sectionQ:=by
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp h; rw [separation_comm,separation,add_sub_cancel_right]; refine Finset.sup_le fun i _=> (Corona.lap x i).trans ?_; exact (Finset.le_sup (f:=fun j=> (x j).natAbs) (Finset.mem_univ i)).trans (Finset.le_sup (f:=fun x:Cover=>Finset.univ.sup fun i=>(x i).natAbs) hx)
lemma Palette.extend {w:ℝ} (hX:Core p S X K M f) (hY:o∈K) (hp: Palette p S K M f o w) {u:Site n} (hv: u∈ hold') : Palette p S K M f u ((((1+(coverNumber p.B hold' * (4*p.B+2)+2*p.B:ℕ):ℝ)^p.power)^p.order)* w):=by
   have ht := Corona.extent hold' p.B (Finset.mem_union_left _ hY) hv; constructor
   · apply hp.termsC.trans; apply le_mul_of_one_le_left hp.core.1; apply one_le_pow₀; apply one_le_pow₀; apply le_add_of_nonneg_right; positivity
   · exact WickReps.postage o f.entry hX.regular hp.core u ht
   exact WickReps.postage _ _ hX.salt hp.astro u ht

-- post-era accounting holdership. Bunch ℝ interface cost trials with root distance
end SeatD
open SeatD
local notation "σ" => p.supportExponent
local notation "B" => p.B

def lengthK(p:BudgetPoint)(k:ℕ) : ℝ:=1+((k * (4*p.B+2)+2*p.B:ℕ):ℝ)
def coast :ℝ:= (((5*p.order^2)+2):ℕ)
local notation "N₁" => p.power*p.order

def traceWeight (k:ℕ):= (lengthK p k ^ p.power)^p.order
local notation "F"=>traceWeight p
lemma freight(k:ℕ) : 1 ≤ F k:=by unfold traceWeight; apply one_le_pow₀; apply one_le_pow₀; unfold lengthK; apply le_add_of_nonneg_right; positivity
-- pay with FIRST EXPONENT reserve: x B t pattern support. width finite denominator. p power may vary.
def gear (Bv power order:ℕ):ℝ := (((10*((Bv:ℝ)+1))*((power*order:ℕ)+1:ℝ))^(power*order))*Real.exp 1
lemma gap (k:ℕ) : traceWeight p k ≤ gear p.B p.power p.order* Real.exp k:=by
    let a : ℝ:= 1+k; have hx : 0 < N₁:= mul_pos (by have h:= p.power_ge; omega) (by have h:= p.order_ge; omega)
    let b:= (↑(p.power*p.order):ℝ); have hb:0<b:=Nat.cast_pos.mpr hx
    let uV:= 10*((p.B:ℝ)+1); have ht:0< uV:=by unfold uV; positivity
    have he : lengthK p k ≤ uV * (b * Real.exp (a/b)):=by
       have h: a/b≤ Real.exp (a/b):=by linarith only [Real.add_one_le_exp (a/b)]
       apply le_trans (b:= uV*a) ?_ (mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact (div_le_iff₀ hb).mp h) ht.le); unfold lengthK uV a; push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) k, Nat.cast_nonneg (α:=ℝ) p.B, show 0≤ (p.B:ℝ)*(k:ℝ) by positivity] -- edit
    unfold traceWeight; rw [← pow_mul]; apply le_trans (pow_le_pow_left₀ (show 0≤ lengthK p k by unfold lengthK; positivity) he _); rw [←mul_assoc,mul_pow,← Real.exp_nat_mul, show (↑(p.power*p.order):ℝ)*(a/b)=a from by change b* _=a; field_simp]
    change (uV*b)^N₁*Real.exp a ≤ ((uV*(b+1))^N₁* Real.exp 1)*Real.exp k; rw [mul_assoc ((uV*(b+1))^N₁)]; unfold a; rw [Real.exp_add]; apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) ht.le) _) (by positivity)
variable {b:ℝ}{w : ℝ}{k t:ℕ}

def budgetF (p:BudgetPoint)(n : Side)(X :Support n) (t:ℝ):= Real.exp ((p.supportExponent+1)*(coverNumber p.B X)) * t

def stems (k:ℕ):= (k+k+1)^4

def haloExpense (s:ℝ) (k:ℕ)(Power Order Bv:ℕ):ℝ:= Real.exp ((s+2)*stems k)*gear Bv Power Order
local notation "μ"=> haloExpense p.supportExponent
lemma gear_pay (k:ℕ) : 1 ≤ μ k p.power p.order p.B:=by
    apply one_le_mul_of_one_le_of_one_le; exact Real.one_le_exp (by linarith [p.exponent_pos,show 0≤(stems k:ℝ) by positivity, show 0 ≤ p.supportExponent*(↑(stems k):ℝ) by positivity [p.exponent_pos]])
    refine (freight p 0).trans ((gap p 0).trans_eq ?_); simp
lemma renewed (t:ℕ) (X:Support n) (a:ℝ)(Y:Support n)(ha:0≤a) (hk:coverNumber B Y ≤ coverNumber B X+ stems t): budgetF p n Y (a*traceWeight p (coverNumber p.B Y)) ≤ haloExpense p.supportExponent t p.power p.order p.B* (Real.exp ((p.supportExponent+2)*coverNumber p.B X)*a):=by
    unfold budgetF haloExpense
    apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (gap p _) ha) (Real.exp_pos _).le)
    let s:= (p.supportExponent+2); let y:ℝ:= coverNumber p.B Y; let x:ℝ:= coverNumber p.B X
    have hs : 0 ≤ s:= by unfold s; positivity [p.exponent_pos]
    have ht : y ≤ x+stems t:=by unfold y x; exact_mod_cast hk
    have he : Real.exp ((s-1)*y) * Real.exp y ≤ Real.exp (s*stems t)* Real.exp (s*x) := by
       rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone; nlinarith only [mul_le_mul_of_nonneg_left ht hs]
    have h': s-1=p.supportExponent+1:=by unfold s; linarith
    have hh:0 ≤ gear p.B p.power p.order:=by unfold gear; positivity
    rw [h'] at he
    unfold s x y at he; nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hh) ha] -- fix unfolding
end YM.RemainderComparison.Passion

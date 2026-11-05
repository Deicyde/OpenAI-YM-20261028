import YM.RG08.Flint.Hero
import YM.RG08.Aura.Cast
import YM.Planned.PRIMARY_INTEGRAL_295.Savings

/-!
# Pointwise row expansion BEFORE L; pull in colors, and price each weighted y also for interface
post averaging. Real. Remainder uniformly mild growth at all x (no need subtract affine
only on |x|≤L; using an exponential input width instead). Address propagation separate.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Yurt
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar
open Room Gallery Camera MvPolynomial Glyph Quarry Weald Hatch Carrel Laurent Filter RG Precision Exterior
open Planned.PrimaryIntegral295 Place Carrier Flint
open scoped Classical ContDiff BigOperators Topology PowerSeries ENNReal
variable {I J:Type}{G:Gauge}{n p d:ℕ}{C D τ s δ:ℝ}{L:Side}
local notation "A" => Loc G 1

abbrev Ballet (G:Gauge)(L:Side)(M:Carrier.Lines L)(w:List Axis):Kernel (Loc G 1) (Loc G 1):=Spar.prism G.ColorIndex (install (advanceC L M w))
variable (M:Carrier.Lines L)
lemma once (h:Odd L.val)(i:Axis)(w:List Axis): Ballet G L M (i::w)=Pert.Bulk.foot i (Ballet G L M w):=by
 unfold Ballet;rw [advanceC,←install_step h]
 ext ⟨x,a,c⟩ ⟨y,b,t⟩;unfold foot Spar.prism;dsimp only;split <;> simp

/-- Link or node column with displaced root o@lift o. May use any head alphabet.
Rows expressed in coarse distance. Units of L in volume fees through L first since weights
pre-announced with this unit. No negative orientations. -/
def offer (K:Kernel I J)(o:Cover)(τ:ℝ)(y:Market J)(x:Cover):I→ℝ:=fun i=>Real.exp (τ*length y.1)*K (x+o,i) y
lemma length_off (L:Side)(x y u:Cover):length y ≤ Pert.Bulk.delta L (x+u) y + length x/(L.val:ℝ) + length u/L.val:=by
 have h:=inv_scaled L 0 0 (x+u) y
 rw [sep_comm 0 y] at h;simp_rw [sep,sub_zero,zero_sub,length_neg,Pert.Bulk.delta,sep,smul_zero,sub_zero] at h
 have hx:length (x+u)/(L.val:ℝ) ≤ length x/L.val+length u/L.val:=by rw [←add_div];exact div_le_div_of_nonneg_right (length_add ..) (Nat.cast_nonneg _)
 unfold Pert.Bulk.delta sep
 have hh:length 0=0:=by simp [length,size]
 rw [hh,_root_.zero_div] at h
 linarith only [h,hx]
lemma row_h (_hs:0≤ s){K:Kernel I J}(h:RowCost s L K C)(hc:0≤C)(x:Market I)(y:Market J):|K x y| *Real.exp (s*Pert.Bulk.delta L x.1 y.1)≤ C:=
 (ENNReal.ofReal_le_ofReal_iff hc).mp ((ENNReal.le_tsum (f:=fun i:Cover=> bill (K x (i,y.2)) (s*Pert.Bulk.delta L x.1 i)) y.1).trans (h x y.2))

lemma promote (ht:0≤τ)(hs:τ≤ s){K:Kernel I J}(h:RowCost s L K C)(hc:0≤C)(o:Site L)(x:Cover)(y:Market J)(i:I):
   |offer K (lift o) τ y x i| ≤ C * Real.exp (4*s) * Real.exp ((τ/(L.val:ℝ))*length x):=by
 let q:= (x+lift o,i); let g:=Pert.Bulk.delta L q.1 y.1
 have hx : τ*length y.1 ≤ (s*g+4*s)+(τ/(L.val:ℝ))*length x:=by
    let a:ℝ:=length x; let b:=length (lift o); let c:ℝ:=L.val
    have hr:= length_off L x y.1 (lift o)
    have h0:0≤g:= Pert.Bulk.delta_nonneg L _ _
    have hv:τ*length y.1 ≤ τ*g+τ*(a/c)+τ*(b/c):=by nlinarith only [show length y.1 ≤ g+a/c+b/c from hr,ht]
    have hb : b/c ≤ 4 := length_lift L o
    have hd:τ*(a/c)=(τ/c)*a:=by ring
    change τ*_ ≤ _ + (τ/c)*a
    rw [hd] at hv;nlinarith only [hv, hb, h0, hs, ht, mul_nonneg (sub_nonneg.mpr hs) h0, mul_nonneg ht (sub_nonneg.mpr hb)]
 unfold offer;rw [abs_mul,abs_of_pos (Real.exp_pos _),mul_comm]
 apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) (abs_nonneg _)).trans
 rw [Real.exp_add,Real.exp_add,←mul_assoc,←mul_assoc]
 apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (row_h (ht.trans hs) h hc q y) (Real.exp_pos _).le) (Real.exp_pos _).le

-- commute list ranking on cover w/o sum. pay across entire cover, not only near elements of one period.
def auction (G:Gauge)(τ:ℝ)(o:Site L)(M:Carrier.Lines L)(y:Market (Loc G 1))(w:List Axis)(x:Cover): (Loc G 1)→ℝ:= offer (Ballet G L M w) (lift o) τ y x
lemma dancing (he:Odd L.val)(y:Market A)(o:Site L)(w:List Axis)(x:Cover): Trellis.delta (auction G τ o M y []) w x=auction G τ o M y w x:=by
 induction w generalizing x with
 | nil=>rfl
 | cons i w ih=>rw [Trellis.delta,Trellis.offset,ih,ih];ext b; unfold auction;rw [once M he]; unfold Pert.Bulk.foot offer; dsimp only [Pi.sub_apply]; rw [add_right_comm x]; ring

/-- announced absolute fee irrespective of y and level, Louis. -/
lemma dance_fare (h:Odd L.val){w:List Axis}(ht:0≤τ)(hs:τ≤ s)(hC:0≤C)(hP:RowCost s L (Ballet G L M w) (C/(L.val:ℝ)^(w.length+1)))
    (o:Site L)(y:Market A)(x:Cover):‖Trellis.delta (auction G τ o M y []) w x‖≤(C*Real.exp (4*s))*unitStep L ^ (w.length+1)*Real.exp ((τ/(L.val:ℝ))*(size x)):=by -- bad ':'
 rw [dancing M h]
 have hp : 0≤unitStep L:=(unitStep_pos _).le
 have hv:0≤C*Real.exp (4*s)*unitStep L^(w.length+1)*Real.exp ((τ/(L.val:ℝ))*(size x)):=by positivity
 refine (pi_norm_le_iff_of_nonneg hv).mpr (fun t=>?_)
 rw [Real.norm_eq_abs];refine (promote (L:=L) ht hs hP (by positivity) o x y t).trans_eq ?_; unfold length unitStep; rw [inv_pow];ring

variable {M}
def Tutor (L:Side)(s C:ℝ)(M:Carrier.Lines L)(G:Gauge)(n:ℕ):Prop:=∀ w:List Axis,w.length≤n→ RowCost s L (Ballet G L M w) (C/(L.val:ℝ)^(w.length+1))

def newton (G:Gauge)(τ:ℝ)(o:Site L)(M:Carrier.Lines L)(y:Market (Loc G 1))(i:ℕ):E4→ (Loc G 1)→ℝ:=Trellis.sector i (auction G τ o M y [])
lemma newton_price (G:Gauge)(s C:ℝ)(hC:0≤C)(_hs0:0≤ s)(i:ℕ):∃ D:ℝ,0 ≤ D ∧ ∀ (L:Side){τ:ℝ}(o:Site L)(M:Carrier.Lines L),Odd L.val→0≤τ→τ≤ s → Tutor L s C M G i→ ∀ y:Market (Loc G 1),
 let f := newton G τ o M y i
 ; f∈ Place.rangeLt ((Loc G 1)→ℝ) (i+1) ∧ ∀ x:E4,‖f x‖≤D*unitStep L ^ (i+1)*(1+‖x‖)^i :=by
 obtain ⟨D,hD,H⟩:=Trellis.price_point (E:=(Loc G 1)→ℝ) i
 use D*(C*Real.exp (4*s)); constructor
 · exact mul_nonneg (by linarith) (mul_nonneg hC (Real.exp_pos _).le)
 intro L τ o M hL hτ ht hP y f
 have hp:=unitStep_pos L
 let B:=C*Real.exp (4*s)*unitStep L^(i+1)
 have HN(w:List Axis)(hw:w.length=i):‖Trellis.delta (auction G τ o M y []) w 0‖≤B:=by
    simpa only [hw,show size (0:Cover)=0 by simp [size],Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using dance_fare M (w:=w) hL hτ ht hC (hP w hw.le) o y 0
 refine ⟨Trellis.sector_band (auction G τ o M y []) i,fun x=>(H _ B (by unfold B;positivity) HN x).trans_eq (by unfold B;ring)⟩

/-- Direct exponential alternative to piecewise near/far theorem -/
lemma remainder (h:Odd L.val)(ht:0≤τ)(hs:τ≤ s)(hC:0≤C)(hP:Tutor L s C M G n)
   (o:Site L)(y:Market A) (x:Cover):
   ‖Trellis.surplus (auction G τ o M y []) n x‖ ≤ (C*Real.exp (4*s))*unitStep L^(n+1)*(1+size x)^n*Real.exp ((τ/(L.val:ℝ))*(size x)):=by -- coercion issue Nat ^n after def
 let B:= (C*Real.exp (4*s))*unitStep L^(n+1)*Real.exp ((τ/(L.val:ℝ))*(size x))
 have hv:=unitStep_pos L; have hx:0≤B:=by unfold B;positivity
 have hy:=Trellis.accrue n (auction G τ o M y []) (size x) B hx (fun g hg y' hy'=>by
    apply (dance_fare M h ht hs hC (hP g hg.le) o y y').trans
    rw [hg];unfold B; gcongr) x le_rfl
 have hu:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (show (size x:ℝ)≤1+size x from le_add_of_nonneg_left zero_le_one) n) hx
 exact hy.trans (hu.trans_eq (by unfold B;ring))
end YM.RG08.Yurt

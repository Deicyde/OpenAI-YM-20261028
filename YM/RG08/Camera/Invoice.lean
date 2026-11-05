import YM.RG08.Camera.Pinpoint

/-!
# Tax rescaled powers and constrained graded bills; moving each symbol BEFORE gaussian.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Camera
open Glyph Cloud Room MvPolynomial Finset Filter Function
open scoped ContDiff Topology BigOperators PowerSeries Classical
variable {R:Type*}[CommRing R]

def Low (n:ℕ)(f:Cab R):Prop := ∀ i<n,tap i f=0
def tax (n:ℕ)(f:Cab R):Cab R:=(liftout^[n] f)
lemma audited (f:Cab R)(n e:ℕ):tap e (tax n f)=tap (e+n) f:=by
 induction n generalizing e with
 | zero=>simp [tax]
 | succ n he=>
   rw [tax, Function.iterate_succ_apply',look,←tax,he];congr 1; omega
lemma pay (n:ℕ){f:Cab R}(h:Low n f): PowerSeries.X^n *tax n f=f:=by
 ext i :1;rw [PowerSeries.coeff_X_pow_mul'];split_ifs with hi
 · change tap _ (tax n f)=_;rw [audited, Nat.sub_add_cancel hi]
 exact (h i (by omega)).symm

variable {I J:Type}[Fintype I][Fintype J]
omit [Fintype I][Fintype J] in
lemma wire_taxes (x:I→Port J)(n:ℕ){f:Port I}(h:Low n f): belt x (tax n f)=tax n (belt x f):=by
 have hx:Low n (belt x f):=fun i hi=>by
    rw [steady_belt x i f 0 (fun j hj=>by rw [h j (by omega)];exact (map_zero (PowerSeries.coeff (R:=Inn I) j)).symm),map_zero]; exact map_zero _
 apply (PowerSeries.X_pow_mul_inj (k:=n)).mp
 rw [ pay _ hx,← belt_g x,←_root_.map_pow,←_root_.map_mul,pay _ h] -- reverse etc

structure Leaf (I:Type)[Fintype I] where
 withholding : ℕ
 addOrder : ℕ -- valuation correction on already divided part
 word : Still I
def Leaf.present (a:Leaf I):Port I:=PowerSeries.X ^ a.addOrder * tax a.withholding (flask a.word)

structure Receipt (I J:Type)[Fintype I][Fintype J] (h:Strip J I) where
 a: Leaf I
 b: Leaf J
 fixed : a.withholding=b.withholding
 raised : a.addOrder=b.addOrder
 even : a.word=ᶠ[𝓝 0] b.word ∘ roll h
 sound : Pace b.word
 stock : Low b.withholding (flask b.word)

lemma Receipt.serves {h:Strip J I}(p:Receipt I J h)(hp:∀ i,Pace (h i))(he:roll h 0=0):p.a.present =belt (rescaleFields h) (p.b.present):=by
 unfold Leaf.present; rw [flask_same p.even,flask_comp hp he p.sound,p.fixed,p.raised,_root_.map_mul,_root_.map_pow,belt_g,wire_taxes _ _ p.stock]

end YM.RG08.Camera

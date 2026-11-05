import YM.UVExtension.Poppy.Sparrow
import YM.UVExtension.Tide.Basket
/-! # Coarse grids of differences via positive averages on a displaced
 lattice. The absolute-SUP and envelope already permit growth by lattice
 powers; comparison on the real segment uses ONE higher difference not
 analytic estimates on a spatial contour. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Beach
open Function Filter Set Metric Lattice RG Wilson
open Extraction Fallow Poppy Tide
open scoped Topology BigOperators Classical ContDiff
variable {n j N m:ℕ} (S:Schedule)
local notation "X"=> Tabletop n
-- carve integer coordinate arrays. Arbitrary offset centers for telescoping.
def scoop (p:ℕ)(h:j≤ N)(x:Tabletop n):Tabletop n:= (S.toDepth h p).count.val • x
lemma scoop_tag (p:ℕ)(h:j≤N) (x:Tabletop n): tag (S.a j) x= tag (S.a N) (scoop S p h x):=by
   let Z:=S.toDepth h p; have he := S.embeds_scale Z
   rw [← he]; ext i b; change S.a N * ↑Z.count.val * _= S.a N*(( (Z.count.val • x i b):ℤ):ℝ); rw [nsmul_eq_mul]; push_cast; ring
lemma scoop_map (p:ℕ)(h:j≤N) (x:Tabletop n): wrap (S.side N p) ∘ scoop S p h x= Push.GridApprox.anchor S p h ∘ wrap (S.side j p) ∘ x:=funext fun i=> (Ratio.embed_wrap ..).symm
-- absolute.C given vertices in support.NoHit ensures they exist.Use weighted recurrence without casting.Dec. Need operator at arbitrary offset to compare differenced arrays.
variable (F:Tabletop n→ℂ)
def car (t:ℝ)(u:ℕ)(F:Tabletop n→ℂ) : List (Axel n)→ Tabletop n →ℂ
  | []=> F
  | i::l=> fun x=> (t:ℂ)⁻¹*(car t u F l (x+u • hike i)-car t u F l x)
lemma canoe (r:ℕ)(h:j≤N)(L:List (Axel n))(x:X): rake (S.a j) (F ∘ scoop S r h) L x= car (S.a j) (S.toDepth h r).count.val F L (scoop S r h x):=by
    induction L generalizing x with
    | nil=> rfl
    | cons i l ih=> rw [rake, climbing,ih, ih, car, scoop,smul_add]; rfl -- hike

private lemma commuteC (a:ℝ)(k:ℕ)(b:Axel n)(s:ℝ)(l:List (Axel n)): climbing s (car a k F l) b= car a k (climbing s F b) l :=by
    induction l with
    | nil=> rfl
    | cons i l ih=>
       funext x; rw [car,car,← ih]; simp only [climbing]; rw [show x+hike b+k • hike i = x+k • hike i+hike b by abel]; ring
private lemma slide (b:Axel n)(s:ℝ)(l:List (Axel n)): rake s F (b::l)=rake s (climbing s F b) l:=by
   have h(l : List (Axel n))(F:X→ ℂ): rake s F l=car s 1 F l:=by
       induction l with
       | nil=> rfl
       | cons i l ih=> funext x; rw [rake,car,ih,one_smul]; rfl
   rw [rake,h l,h l]; exact commuteC F ..

private lemma avg (a:ℝ)(ha:0<a)(n':ℕ)(hn: 0 < n')(b:Axel n)(z:X): (((n':ℂ)*(a:ℂ)))⁻¹*(F (z+n' • hike b)- F z)=((n':ℂ))⁻¹*∑ k:Fin n', climbing a F b (z+k.val • hike b):=by
   let s: Poppy.Stride n:= ⟨b,0,n',hn⟩; have h:= Poppy.walks1 s a ha F z
   simpa only [Poppy.shift,s,add_zero,Complex.ofReal_mul, Complex.ofReal_natCast, mul_comm (a:ℂ)] using h
variable {a t:ℝ}
lemma tiered (F:Tabletop n→ℂ)(W:ℕ)(hw:0<W)(ha:0<a)(b:ℝ)(h:a*W=b) (d:ℝ)(u:ℂ)(L:List (Axel n))(x:X)(ht:∀ y:X, dist (tag a y) (tag a x) ≤ L.length*b → ‖rake a F L y-u‖ ≤ d): ‖car b W F L x-u‖ ≤ d:=by
   induction L generalizing x F with
   | nil=> exact ht x (by simp)
   | cons i l ih=>
       let s:= car b W F l; let t(k:Fin W):= climbing a s i (x+k.val • hike i); have he : car b W F (i::l) x=((W:ℂ))⁻¹*∑ k,t k:=by
          change (b:ℂ)⁻¹*(s _-s _)=_; rw [show (b:ℂ)=((W:ℂ)*(a:ℂ)) by rw [← h];push_cast; ring]; exact avg s a ha W hw i x -- includes h
       have hp(k:Fin W): ‖t k-u‖≤ d:=by
          let z:=x+k.val • hike i; unfold t s; rw [commuteC]; apply ih
          intro y hy; have hh: dist (tag a z) (tag a x) ≤ b:=by unfold z; rw [Poppy.lengthP ha,←h]; gcongr; exact k.2.le -- hp context
          rw [← slide]; refine ht y ((dist_triangle _ (tag a z) _).trans ?_); simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; rw [add_mul,one_mul]; exact add_le_add hy hh
       rw [he]; have hv:(W:ℂ)≠0:= Nat.cast_ne_zero.mpr hw.ne'; have hh:= inv_pos.mpr (show (0:ℝ)<W by exact_mod_cast hw); have hm:u= ((W:ℂ))⁻¹* ∑ _ : Fin W,u:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul, inv_mul_cancel_left₀ hv]
       conv_lhs => arg 1; rhs; rw [hm]
       rw [←mul_sub,←Finset.sum_sub_distrib,norm_mul,norm_inv,Complex.norm_natCast]; refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum fun k _=> hp k)) hh.le).trans_eq ?_; simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; exact inv_mul_cancel_left₀ (by exact_mod_cast hw.ne') _
end YM.UVExtension.Beach

import YM.MergeProof.West.Arch
import YM.MergeProof.West.Stencil
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Acme
open Filter Function Set
open scoped Topology BigOperators ContDiff Classical
variable (k:ℕ) (x:E4) (a:ℝ) (v:Axis)
-- good means nonzero multiple
abbrev taper (r:ℝ)(y:E4):= {w:Axis|∃ i:ℤ, y w=r*i ∧ i≠0}
def arm (n:ℕ):ℝ:=4*(((2^n:ℕ):ℝ)+2)
lemma arm_pos (n:ℕ):0 < arm n:=by unfold arm;positivity
def chord (i:Axis)(x:E4)(a t:ℝ):= Ward.inc i x (t*a)
lemma arctic (h:0<a):∃ p:Fin (2^k)→ℝ, arced k (arm k) p∧∀ i, v∈ taper a (chord v x a (p i)):=by
   let w := x v/a; let N := 2^k; let r:= ⌊w⌋
   have hr : (r:ℝ)≤ w:= Int.floor_le w
   have he:w< r+1:=Int.lt_floor_add_one _
   have hw : a*w=x v:= mul_div_cancel₀ _ h.ne'
   have hh : ∃ f: Fin N→ℤ,(∀ i,f i≠0 ∧ ((f i:ℤ):ℝ)-w ∈ Icc (-(arm k)) (arm k))∧StrictMono f:=by
       by_cases hf : 0≤x v
       · have hq:0≤w:= div_nonneg hf h.le; have hz:0 ≤ r:=Int.floor_nonneg.mpr hq
         refine ⟨fun i=>r+i.val+1,fun i=>⟨ne_of_gt (by dsimp; omega),?_⟩,fun i j h=>?_⟩
         · have hv:(i.val:ℝ) < N:= Nat.cast_lt.mpr i.isLt
           unfold arm; change _ ∈ Icc (-(4*((N:ℝ)+2))) _; constructor
           · change -(4*((N:ℝ)+2)) ≤ ((↑(r+↑i.val+1):ℝ)-_); push_cast; linarith [Nat.cast_nonneg (α:=ℝ) i.val]
           change _ ≤ 4*((N:ℝ)+2); push_cast; linarith [Nat.cast_nonneg (α:=ℝ) N]
         exact (by have := Fin.lt_def.mp h; dsimp;omega)
       have hp:w<0:= div_neg_of_neg_of_pos (lt_of_not_ge hf) h
       have hz:r<0:= by exact_mod_cast (hr.trans_lt hp)
       refine ⟨fun i=> r-↑N+i.val,fun i=>⟨?_,?_⟩,fun i j h=>?_⟩
       · have := i.isLt;dsimp;omega
       · have hv:(i.val:ℝ)<N:= Nat.cast_lt.mpr i.isLt
         change _∈Icc (-(4*((N:ℝ)+2))) (4*((N:ℝ)+2)); constructor
         · dsimp only;push_cast;linarith [Nat.cast_nonneg (α:=ℝ) N,Nat.cast_nonneg (α:=ℝ) i.val]
         dsimp only;push_cast;linarith [Nat.cast_nonneg (α:=ℝ) N]
       exact (by have := Fin.lt_def.mp h; dsimp;omega)
   obtain ⟨f,hf,hg⟩:=hh
   refine ⟨fun i=> (f i:ℝ)-w,⟨fun i=> (hf i).2,fun i j h=>?_⟩,fun i=> ⟨f i,?_,(hf i).1⟩⟩
   · have he: (f i:ℝ)+1≤ f j:=by exact_mod_cast (show f i+1≤ f j from hg h)
     dsimp only; linarith
   simp only [chord,Ward.inc,PiLp.add_apply,PiLp.smul_apply,basis_eq,if_true,smul_eq_mul,mul_one]
   rw [← hw]; ring
lemma reed (i j:Axis) (x:E4)(v b:ℝ)(he:j≠i) (h:j∈taper v x):j∈ taper v (chord i x v b):=by
    obtain ⟨k,hp,hq⟩:= h; refine ⟨k,?_,hq⟩; simp [chord,Ward.inc,he,hp]
lemma rink {p:ℝ}{j:Axis}{t:ℝ}(h:0≤p)(x:E4)(a:ℝ)(ha:0<a) (hv:t∈ Icc (-p) p): ‖chord j x a t-x‖ ≤ p*a:=by
   unfold chord Ward.inc; rw [add_sub_cancel_left,norm_smul, Real.norm_eq_abs,abs_mul,abs_of_pos ha,basis_norm,mul_one]
   exact mul_le_mul_of_nonneg_right (abs_le.mpr hv) ha.le
open Ribbons
lemma mitten (a:ℝ)(r:ℝ)(j:Axis)(p:ℝ)(hr:0<r)(hp:0≤p)(ha:0<a) (hf:p*a ≤ r/128) : ∀ (x y:E4), ∀ t∈ Icc (-p) p, ‖x-y‖≤ r/16 → y∈ YM.Next.UVStress.annulus r → chord j x a t∈ arena r:=by
   intro x y t ht h hy
   have hh: ‖chord j x a t - x‖ ≤ r/128:= le_trans (rink hp x a ha ht) hf
   have hy' :r/4 < ‖y‖ ∧ ‖y‖ <2*r:=hy
   constructor
   · linarith only [hy'.1,norm_sub_norm_le y x,norm_sub_norm_le x (chord j x a t),norm_sub_rev y x,norm_sub_rev x (chord j x a t),h,hh,hr]
   linarith only [hy'.2,norm_sub_norm_le x y,norm_sub_norm_le (chord j x a t) x,h,hh,hr]
end YM.MergeProof.Acme

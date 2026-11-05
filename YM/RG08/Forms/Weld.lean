import YM.RG08.Forms.Lap

/-!
# Binary PDE glue on connected vertices (weighted, all external slots, no line-count
loss of width). This and the lap trace replace estimates by spanning trees of many vertices;
PDE time iteration produces exactly connected formal heat/log coefficients as proved
on finite data separately. Applies to powers of fixed moment as well after taking fixed
width reserves in this approach.
-/
noncomputable section
namespace YM.RG08.Forms
open Pert.Bulk Packets Finset Function
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false
variable {I : Type}{p q:ℕ}

def seam (Γ : Line I) (F : Flake (p+1) I)(G : Flake (q+1) I)(w : Tape (p+q) I)(u:I×I) := F (Fin.cons u.1 (fun i:Fin p=>w (Fin.castAdd q i))) * Γ u.1 u.2 * G (Fin.cons u.2 (fun i=>w (Fin.natAdd p i)))

def weld (Γ : Line I) (F : Flake (p+1) I) (G : Flake (q+1) I):Flake (p+q) I:=fun w=>∑' u,seam Γ F G w u

def bridge (Γ : Line I) (F : Flake (p+1) I) (G : Flake (q+1) I):Flake (p+q) I:=bleach (weld Γ F G)

variable {d:Ground I}{σ C D B : ℝ}{Γ : Line I}{F : Flake (p+1) I}{G : Flake (q+1) I}
lemma seam_tool (x:Tape p I)(y:Tape q I) (u v : I) : seam Γ F G (Fin.append x y) (u,v) = F (Fin.cons u x)*Γ u v*G (Fin.cons v y):=by simp only [seam,Fin.append_left,Fin.append_right]

lemma arc (d : Ground I) (x : Tape p I)(y : Tape q I)(u v:I): d.radius (Fin.append x y) ≤ d.radius (Fin.cons u x)+d.span u v+d.radius (Fin.cons v y):=by
 let a:=d.radius (Fin.cons u x);let b:=d.radius (Fin.cons v y)
 have hx (i j:Fin p):d.span (x i) (x j) ≤a:=by simpa [a] using d.le_radius (Fin.cons u x) i.succ j.succ
 have hy (i j:Fin q):d.span (y i) (y j)≤b:=by simpa [b] using d.le_radius (Fin.cons v y) i.succ j.succ
 have hc (i:Fin p)(j:Fin q):d.span (x i) (y j) ≤ a+d.span u v+b:=by
  have hA:d.span (x i) u≤a:=by simpa [a] using d.le_radius (Fin.cons u x) i.succ 0
  have hB:d.span v (y j) ≤b:=by simpa [b] using d.le_radius (Fin.cons v y) 0 j.succ
  linarith [d.slope (x i) u (y j),d.slope u v (y j)]
 have ha : 0 ≤ a:= d.radius_nn _; have hb:0≤b:=d.radius_nn _;have he:=d.nn u v
 apply d.radius_le _ (by change 0 ≤ a + _ + b;linarith); intro i j
 cases i using Fin.addCases with
 | left i => cases j using Fin.addCases with
   | left j=>simp only [Fin.append_left];change _ ≤ a+_+b;linarith [hx i j]
   | right j=> simpa using hc i j
 | right i=> cases j using Fin.addCases with
   | left j=> rw [d.left]; simpa using hc j i
   | right j=> simp only [Fin.append_right];change _≤ a+_+b;linarith [hy i j]

lemma seam_bill (hs:0 ≤ σ) (x:Tape p I)(y:Tape q I)(u v:I) :
  bill (seam Γ F G (Fin.append x y) (u,v)) (σ*d.radius (Fin.append x y)) ≤ mark d σ F (Fin.cons u x)*link d σ Γ u v*mark d σ G (Fin.cons v y):=by
 rw [seam_tool]; apply (bill_mul _ _ (σ * d.radius (Fin.cons u x) + σ * d.span u v) _ (σ*d.radius (Fin.cons v y)) (by nlinarith [arc d x y u v])).trans
 exact mul_le_mul_left (bill_mul _ _ (σ*d.radius _) _ (σ*d.span u v) le_rfl) _

private lemma root_sum (h : Held d σ C F)(hG:Held d σ D G)(hΓ:Wire d σ B Γ)(_hC:0≤C)(i:Fin p)(z:I):
   (∑' x:Tape p I,∑' y:Tape q I,∑' u:I,∑' v:I, row (mark d σ F) i.succ z (Fin.cons u x)*link d σ Γ u v * mark d σ G (Fin.cons v y)) ≤ ENNReal.ofReal C * ENNReal.ofReal B * ENNReal.ofReal D:=by
 let U (x:Tape p I)(u:I):=row (mark d σ F) i.succ z (Fin.cons u x)
 let V (y:Tape q I)(v:I):=mark d σ G (Fin.cons v y)
 change (∑' x,∑' y,∑' u,∑' v,U x u*link d σ Γ u v * V y v) ≤ _
 have hm (x:Tape p I):
    (∑' y,∑' u,∑' v,U x u * link d σ Γ u v * V y v)=∑' u,U x u * ∑' v,link d σ Γ u v * ∑' y,V y v:=by
     rw [ENNReal.tsum_comm]; simp_rw [ENNReal.tsum_comm (f:=fun (y:Tape q I)(v:I)=>_ * link d σ Γ _ v * V y v),mul_assoc,ENNReal.tsum_mul_left]
 simp_rw [hm]
 calc
 _ ≤ ∑' x,∑' u,U x u * (∑' v,link d σ Γ u v * ENNReal.ofReal D):=by
      gcongr with x u v
      unfold V;rw [← ensign_face];exact ensign.mp hG _ _
 _ ≤ ∑' x,∑' u,U x u * (ENNReal.ofReal B * ENNReal.ofReal D):=by
      apply ENNReal.tsum_le_tsum;intro x;apply ENNReal.tsum_le_tsum;intro u;rw [ENNReal.tsum_mul_right];gcongr;exact hΓ.forth u
 _ = (∑' w,row (mark d σ F) i.succ z w) * (ENNReal.ofReal B*ENNReal.ofReal D):=by
      rw [tsum_cons]
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_right]
      rfl
 _ ≤ _:=by rw [mul_assoc]; exact mul_le_mul_left (ensign.mp h _ _) _

lemma binary_EN (h : Held d σ C F)(hG:Held d σ D G)(hΓ : Wire d σ B Γ)(hC:0≤C)(hD:0≤D):
  Ensign (fun x:Tape (p+q) I=>∑' u:I×I,bill (seam Γ F G x u) (σ*d.radius x)) (ENNReal.ofReal (C*B*D)):=by
 rw [ENNReal.ofReal_mul (mul_nonneg hC hΓ.gain), ENNReal.ofReal_mul hC]
 intro i z; rw [tsum_append];cases i using Fin.addCases with
 | left i=>
   apply (ENNReal.tsum_le_tsum fun x=>ENNReal.tsum_le_tsum fun y=>?_).trans (root_sum h hG hΓ hC i z)
   unfold row
   by_cases he:x i=z
   · simp only [Fin.append_left,Fin.cons_succ,he,if_true, ENNReal.tsum_prod']
     exact ENNReal.tsum_le_tsum fun u=>ENNReal.tsum_le_tsum fun v=>seam_bill hΓ.width x y u v
   simp [Fin.append_left, Fin.cons_succ,he]
 | right i=>
   rw [ENNReal.tsum_comm]
   have he : ENNReal.ofReal C*ENNReal.ofReal B*ENNReal.ofReal D= ENNReal.ofReal D*ENNReal.ofReal B*ENNReal.ofReal C:=by ac_rfl
   rw [he]
   apply (ENNReal.tsum_le_tsum fun y=>ENNReal.tsum_le_tsum fun x=>?_).trans (root_sum hG h hΓ.turn hD i z)
   unfold row
   by_cases he:y i=z
   · simp only [Fin.append_right,Fin.cons_succ,he,if_true, ENNReal.tsum_prod']
     conv_lhs=> rw [ENNReal.tsum_comm]
     apply ENNReal.tsum_le_tsum; intro v
     apply ENNReal.tsum_le_tsum; intro u
     have ht : link d σ (Function.swap Γ) v u=link d σ Γ u v:=by simp [link,swap,d.left v]
     rw [ht]
     calc
       _ ≤ mark d σ F (Fin.cons u x) * link d σ Γ u v *
           mark d σ G (Fin.cons v y) := seam_bill hΓ.width x y u v
       _ = _ := by ac_rfl
   simp [Fin.append_right, Fin.cons_succ,he]

lemma Held.weld (h : Held d σ C F)(hg:Held d σ D G)(hΓ:Wire d σ B Γ)(hc:0≤C)(hd:0≤D) : Held d σ (C*B*D) (Forms.weld Γ F G):=ensign.mpr ((binary_EN h hg hΓ hc hd).mono (fun _=>bill_tsum ..) le_rfl)
lemma Held.bridge (h : Held d σ C F)(hg:Held d σ D G)(hΓ:Wire d σ B Γ)(hc:0≤C)(hd:0≤D) : Held d σ (C*B*D) (Forms.bridge Γ F G):=(h.weld hg hΓ hc hd).bleach (mul_nonneg (mul_nonneg hc hΓ.gain) hd)

lemma binary_sum (h : Held d σ C F)(hg:Held d σ D G)(hΓ:Wire d σ B Γ)(hc:0≤C)(hd:0≤D) (hn : 0<p+q)(x:Tape (p+q) I) : Summable fun u:I×I=> ‖seam Γ F G x u‖ := by
 have he:=bill_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((binary_EN h hg hΓ hc hd).point hn x))
 exact (he.mul_right (Real.exp (σ*d.radius x))⁻¹).congr fun u=>by simp [Real.norm_eq_abs,Real.exp_ne_zero]

end YM.RG08.Forms

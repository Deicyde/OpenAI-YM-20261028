import YM.RG08.Skiff.Buoy

/-! # Wick pairing on marked kernels, with rank-zero price -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Skiff
open Forms Jetty Pert.Bulk Finset Function
open scoped BigOperators Topology ENNReal Classical
variable {I:Type}{m n d:ℕ}{L:Loom I}{A:Ground I}{σ B C D:ℝ}{h:0<σ}
-- Lap
variable {F:Pack (n+2) I}{Γ:Forms.Line I}
def nut (Γ:Forms.Line I)(F:Pack (n+2) I):Blue n I (I×I):= fun x u=> Γ u.1 u.2 • F (Fin.cons u.1 (Fin.cons u.2 x))
lemma seed (he:Lyrics F):Bare (nut Γ F):= fun _ _=>(he _).smul _
lemma looted (hg:Wire A σ C Γ)(he:Sings L d h F B):CableCar L d h (nut Γ F) (ENNReal.ofReal (B*C)):=by
 have hi (x:Tape n I)(u v:I): fruit L d h (nut Γ F) x (u,v) ≤ ENNReal.ofReal C * gems L d h F (Fin.cons u (Fin.cons v x)):=by
   apply (gifts d h F (Fin.cons u (Fin.cons v x)) (l:=L) x (Γ u v) 0 ?_).trans -- edit
   · exact mul_le_mul_left (show bill _ 0≤ENNReal.ofReal C by simp [bill]; exact ENNReal.ofReal_le_ofReal (hg.plain u v)) _
   rw [add_zero]; apply mul_le_mul_of_nonneg_left _ h.le
   exact L.racks x (L.cage_nn _) fun i=>by simpa using! L.float (Fin.cons u (Fin.cons v x)) i.succ.succ
 unfold CableCar;simp_rw [ENNReal.tsum_prod']
 apply (ENNReal.tsum_le_tsum fun x=> ENNReal.tsum_le_tsum fun u=>ENNReal.tsum_le_tsum fun v=> hi x u v).trans
 rw [ENNReal.tsum_comm]
 simp_rw [ENNReal.tsum_comm (f:=fun (x:Tape n I)(v:I)=>ENNReal.ofReal C*gems L d h F (Fin.cons _ (Fin.cons v x))), ENNReal.tsum_mul_left]
 rw [mul_comm B C,ENNReal.ofReal_mul hg.gain]
 apply mul_le_mul_right ?_ (ENNReal.ofReal C)
 unfold Sings at he; rw [tsum_cons] at he; simp_rw [tsum_cons (p:=n)] at he; exact he

def pocket (Γ:Forms.Line I)(F:Pack (n+2) I):Pack n I:=breeze (decker (nut Γ F))
lemma opening (hp:0≤B)(H:Lyrics F)(he:Sings L d h F B)(hg:Wire A σ C Γ):Lyrics (pocket Γ F)∧Sings L d h (pocket Γ F) (B*C):=by
 have hv:= looted hg he;exact ⟨(hv.lyric (seed H)).breeze,hv.sings.breeze (mul_nonneg hp hg.gain)⟩

-- fuse
def fits (L:Loom I)(A:Ground I):= ∀ u v:I,L.height v≤L.height u+A.span u v
variable {P:Pack (m+1) I}{G:Flake (n+1) I}
def sleeve (Γ:Forms.Line I)(P:Pack (m+1) I)(G:Flake (n+1) I):Blue (m+n) I (I×I):=
 fun w u=>(Γ u.1 u.2 * G (Fin.cons u.2 (fun i=>w (Fin.natAdd m i)))) • P (Fin.cons u.1 (fun i=>w (Fin.castAdd n i)))
lemma sleeved(x:Tape m I)(y:Tape n I)(u v:I):sleeve Γ P G (Fin.append x y) (u,v)=(Γ u v*G (Fin.cons v y)) • P (Fin.cons u x):=by simp only [sleeve,Fin.append_left,Fin.append_right]
lemma cuff (he:Lyrics P):Bare (sleeve Γ P G):=fun _ _=> (he _).smul _

lemma chest (hf:fits L A)(x:Tape m I)(y:Tape n I)(u v:I) : L.cage (Fin.append x y)≤L.cage (Fin.cons u x) + A.span u v + A.radius (Fin.cons v y):=by
 let R:=L.cage (Fin.cons u x); let S:= A.radius (Fin.cons v y)
 have hr:0≤R:=L.cage_nn _; have hs:0≤S:=A.radius_nn _; have he:= A.nn u v
 change _ ≤ R+_+S; rw [L.snoc,max_le_iff];refine ⟨?_,?_⟩
 · refine L.racks _ (by linarith) (fun i=>?_); have hu:L.height (x i)≤R:=by simpa [R] using L.float (Fin.cons u x) i.succ
   linarith only [hu,he,hs]
 refine L.racks _ (by linarith) (fun i=>?_)
 have hz:L.height u≤ R:=by simpa [R] using L.float (Fin.cons u x) 0
 have ht:A.span v (y i)≤ S:=by simpa [S] using A.le_radius (Fin.cons v y) 0 i.succ
 linarith only [hz,ht,hf u (y i),A.slope u v (y i)]

lemma jackets (hf:fits L A)(he:Sings L d h P B)(hv:Held A σ C G)(hg:Wire A σ D Γ)(hB:0≤B):CableCar L d h (sleeve Γ P G) (ENNReal.ofReal (B*D*C)):=by
 have H (x:Tape m I)(y:Tape n I)(u v): fruit L d h (sleeve Γ P G) (Fin.append x y) (u,v) ≤ gems L d h P (Fin.cons u x)*link A σ Γ u v * mark A σ G (Fin.cons v y):=by
   rw [fruit,sleeved]
   apply (gifts d h P (Fin.cons u x) (Fin.append x y) (Γ u v*G (Fin.cons v y)) (σ*A.span u v+σ*A.radius (Fin.cons v y)) ?_).trans
   · apply (mul_le_mul_left (bill_mul (Γ u v) (G (Fin.cons v y)) _ _ _ le_rfl) (gems L d h P (Fin.cons u x))).trans_eq
     change link A σ Γ u v * mark A σ G _*_= _; ac_rfl
   nlinarith only [h,chest hf x y u v]
 unfold CableCar;rw [tsum_append]; simp_rw [ENNReal.tsum_prod']
 apply (ENNReal.tsum_le_tsum (fun x=>ENNReal.tsum_le_tsum fun y=> ENNReal.tsum_le_tsum fun u=>ENNReal.tsum_le_tsum fun v=>H x y u v)).trans
 let U(x:Tape m I)(u:I):=gems L d h P (Fin.cons u x)
 let V(y:Tape n I)(v:I):=mark A σ G (Fin.cons v y)
 change (∑' x,∑' y,∑' u,∑' v,U x u*link A σ Γ u v*V y v)≤_
 have ha(x:Tape m I):(∑' (y:Tape n I),∑' u,∑' v,U x u*link A σ Γ u v*V y v)=∑' u,U x u*(∑' v,link A σ Γ u v * ∑' y,V y v):=by
   rw [ENNReal.tsum_comm]
   simp_rw [ENNReal.tsum_comm (f:=fun (y:Tape n I)(v:I)=>U x _*link A σ Γ _ v*V y v),mul_assoc,ENNReal.tsum_mul_left]
 simp_rw [ha]
 calc
  _ ≤ ∑' x,∑' u,U x u*(∑' v,link A σ Γ u v * ENNReal.ofReal C):=by
    gcongr with x u v;unfold V;rw [← ensign_face];exact ensign.mp hv _ _
  _ ≤ ∑' x,∑' u,U x u*(ENNReal.ofReal D * ENNReal.ofReal C):=ENNReal.tsum_le_tsum fun x=>ENNReal.tsum_le_tsum fun u=>mul_le_mul_right (by rw [ENNReal.tsum_mul_right];exact mul_le_mul_left (hg.forth _) _) _
  _ = (∑' w,gems L d h P w)*(ENNReal.ofReal D * ENNReal.ofReal C):=by
     rw [tsum_cons];conv_lhs=>rw [ENNReal.tsum_comm]; simp only [ENNReal.tsum_mul_right];rfl
  _ ≤ _:=by rw [ENNReal.ofReal_mul (mul_nonneg hB hg.gain), ENNReal.ofReal_mul hB,mul_assoc];exact mul_le_mul_left he _

def cloak (Γ:Forms.Line I)(P:Pack (m+1) I)(G:Flake (n+1) I):Pack (m+n) I:=breeze (decker (sleeve Γ P G))
lemma enrobes (hB:0≤B)(hC:0≤C)(H:Lyrics P)(hf:fits L A)(he:Sings L d h P B)(hv:Held A σ C G)(hg:Wire A σ D Γ):Lyrics (cloak Γ P G)∧Sings L d h (cloak Γ P G) (B*D*C):=by
 have hv:=jackets hf he hv hg hB
 exact ⟨(hv.lyric (cuff H)).breeze,hv.sings.breeze (mul_nonneg (mul_nonneg hB hg.gain) hC)⟩
end YM.RG08.Skiff

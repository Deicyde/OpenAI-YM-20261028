import YM.TraceExtension.Perfect.Bill

/-!
# Poly gauge removal on actual box. Avoid lens-cut: sawtooth saturates, then rolls back.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Matrix Lattice Precision Laurent Stationary Bloch Next.Free Exterior Finset
open scoped BigOperators Topology ContDiff
variable {I : Type}{f:Side}
-- integer plateau clamp one-dimensional no max cost diff from wrapping. use circ from lift. center root.
def reedy (d:ℕ)(x:ℤ) : ℤ:= min x d - max (min (x-(d:ℤ)) d) 0

def streamX (d:ℕ)(x:ℤ):ℤ:= reedy d (max x 0)-reedy d (max (-x) 0)
def beam (d:ℕ)(x:Site f)(i:Axis)(y: Site f): ℝ:= streamX d (lift (y-x) i)
lemma stream_neutral (d:ℕ)(x:ℤ)(h : x.natAbs≤d): streamX d x=x := by unfold streamX reedy; omega
lemma stream_cut (d:ℕ)(x:ℤ)(h : 2*d ≤ x.natAbs):streamX d x=0:=by unfold streamX reedy; omega
lemma stream_limit (d:ℕ)(x:ℤ):-(d:ℤ)≤ streamX d x ∧ streamX d x ≤ d:=by unfold streamX reedy; omega
lemma stream_run (d:ℕ)(x:ℤ) : -1 ≤ streamX d (x+1)-streamX d x ∧ streamX d (x+1)-streamX d x≤1:=by unfold streamX reedy; omega
lemma beam_neutral (d:ℕ)(x:Site f)(i:Axis)(y:Site f)(h : separation y x ≤ d): beam d x i y=lift (y-x) i:=by unfold beam; rw [stream_neutral d _ ((component_le ..).trans h)]
lemma glower_step (n:Side)(x:Site n)(i j:Axis)(h:i ≠ j): lift (x+step i) j=lift x j:=by simp [lift,h,Ne.symm h]
lemma beam_side (x y : Site f)(i j:Axis)(h:i≠j)(d): beam d x i (y+step j)=beam d x i y:=by unfold beam; rw [add_sub_right_comm,glower_step _ _ _ _ (Ne.symm h)]
lemma beam_size (d:ℕ)(x y : Site f)(i): |beam d x i y| ≤ d:=by rw [abs_le]; unfold beam; exact_mod_cast stream_limit d (lift (y-x) i)
lemma grow_lit (x:Site f)(i:Axis)(hx : 2*(lift x i+1) ≤ f.val) : lift (x+step i) i=lift x i+1:=by
 let y :=lift x; have he : lift (x+step i)=y+step i:=by
   refine lift_eq_iff.mpr ⟨?_,fun j=> ?_⟩
   · unfold y; simp
   by_cases hv : j=i
   · subst j; have he:= lift_centers x i; simp [y]; omega
   simpa [hv] using lift_centers x j
 rw [he]; simp [y]
private lemma hinge (x:Site f)(i:Axis)(h : (f.val:ℤ)<2*(lift x i+1)) : lift (x+step i) i=lift x i+1-f.val:=by
 let y:= lift x
 let v := (step i:Cover); let z:= y+v-f.val • v
 have hF : 0 < f.val:= f.property
 have hy : lift (x+step i)=z:=by
   refine lift_eq_iff.mpr ⟨?_,fun j=>?_⟩
   · unfold z v y; rw [map_sub,map_nsmul,map_add,wrap_step,wrap_lift]; ext j; simp [nsmul_eq_mul]
   unfold z v y; by_cases he : j=i
   · subst j; have hx:= lift_centers x i; simp [nsmul_eq_mul]; omega
   simpa [he] using lift_centers x j
 rw [hy]; simp [z,y,v,nsmul_eq_mul]
lemma beam_walk (x y : Site f)(d)(h : 8*d+4 ≤ f.val)(i:Axis): |beam d x i (y+step i)-beam d x i y| ≤ 1:=by
 let q:=y-x;let z:= lift q i
 have he:= lift_centers q i
 by_cases hh : (f.val:ℤ) < 2*(z+1)
 · unfold beam; rw [add_sub_right_comm, hinge _ _ hh]; change |(streamX d (z+1-f.val):ℝ)-(streamX d z:ℝ)| ≤ 1
   change -(f.val:ℤ)<2*z ∧ 2*z ≤ f.val at he
   rw [stream_cut _ _ (by omega),stream_cut _ _ (by omega)]; simp
 unfold beam; rw [add_sub_right_comm, grow_lit _ _ (le_of_not_gt hh)]
 change |(streamX d (z+1):ℝ) - (streamX d z:ℝ)| ≤ 1; rw [abs_le]; exact_mod_cast stream_run d z
lemma beam_alive (x y : Site f)(d)(h : 8*d+4 ≤ f.val)(he : separation y x<d)(i:Axis): beam d x i (y+step i)-beam d x i y=1:=by
 have hs:=pdist_step (n:=f) i
 have hp : separation (y+step i) x ≤ d:=by unfold separation; rw [add_sub_right_comm]; apply (pdist_triangle _ _).trans; change pdist (y-x)<d at he; omega
 have hz:(lift (y-x) i).natAbs<d:= (component_le ..).trans_lt he
 rw [beam_neutral _ _ _ _ hp,beam_neutral _ _ _ _ he.le, add_sub_right_comm,grow_lit _ _ (by omega)]; simp

-- shoulder of gauge at distant links. (transverse too)
private def bendCut (D:ℕ)(x:Site f)(y:Site f):ℕ:=min D (2*D-separation x y)
def glow (D:ℕ)(x:Site f)(y:Site f) := ((bendCut D x y:ℕ):ℝ)/(D:ℝ)
lemma glow_home (d:ℕ)(x y: Site f)(h : separation y x≤d)(he : 0<d): glow d x y=1:=by
 rw [glow, show bendCut d x y=d from min_eq_left (show d≤ 2*d-separation x y from by rw [separation_comm]; omega), div_self]; exact_mod_cast he.ne'
lemma glow_far (d:ℕ)(x y:Site f)(h: 2*d<separation y x): glow d x y=0:=by unfold glow bendCut; rw [separation_comm,Nat.sub_eq_zero_of_le h.le]; simp
lemma glow_fee (d:ℕ)(x y : Site f): |glow d x y| ≤ 1:=by unfold glow; by_cases h:d=0; rw [h]; simp; rw [abs_of_nonneg (by positivity),div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero h))]; exact Nat.cast_le.mpr (min_le_left ..)
lemma glow_turn (d:ℕ)(x y: Site f)(i): |glow d x (y+step i)-glow d x y| ≤ ((d:ℝ))⁻¹ :=by
 unfold glow; rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d),div_eq_mul_inv]; apply mul_le_of_le_one_left (inv_nonneg.mpr (Nat.cast_nonneg _)) _
 have hx := separation_triangle x y (y+step i); have hy:=separation_triangle x (y+step i) y
 have ht : separation y (y+step i) ≤ 1 :=by rw [separation_comm,separation,add_comm y, add_sub_cancel_right]; exact pdist_step _
 rw [separation_comm (y+step i)] at hy
 rw [abs_le]; exact_mod_cast (by unfold bendCut; omega : -(1:ℤ) ≤ ((bendCut d x (y+step i):ℕ):ℤ) - bendCut d x y ∧ ((bendCut d x (y+step i):ℕ):ℤ)-bendCut d x y ≤ 1)
lemma wrap_pad (d:ℕ)(x y : Site f)(a b:Axis)(h:8*d+4 ≤ f.val) : |glow d x (y+step a)*beam d x b (y+step a)-glow d x y*beam d x b y|≤2:=by
 let p:=glow d x (y+step a);let q:=glow d x y;let P:=beam d x b (y+step a);let Q:=beam d x b y
 have he:|P-Q| ≤ 1:=by
    by_cases he:a=b
    · subst b; exact beam_walk x y d h a
    unfold P Q; rw [beam_side _ _ _ _ (Ne.symm he)]; simp
 change |p*P-q*Q| ≤ _; rw [show p*P-q*Q=p*(P-Q)+(p-q)*Q by ring]; apply le_trans (abs_add_le ..); rw [abs_mul,abs_mul]
 have hp := mul_le_mul (glow_fee d x (y+step a)) he (abs_nonneg _) zero_le_one; change |p| * |P-Q| ≤ 1*1 at hp
 have hh := mul_le_mul (glow_turn d x y a) (beam_size d x y b) (abs_nonneg _) (inv_nonneg.mpr (Nat.cast_nonneg _)); change |p-q| * |Q| ≤ _ at hh
 by_cases hz:d=0
 · rw [hz] at hh; simp only [Nat.cast_zero,_root_.inv_zero,mul_zero] at hh; linarith only[hh,hp]
 rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hz)] at hh; linarith only[hh,hp]
variable (W:Matrix (Body 1 f) I ℝ)
def gaugePad (x:Site f) (d:ℕ)(z: Body 0 f): I→ℝ:= ∑ i : Axis, (glow d x z.1*beam d x i z.1) • W (x,coord i)
def fleece (D:ℕ)(x:Site f) (e: Body 1 f) : I→ℝ:= fun i => W e i - (d 0 f *ᵥ (fun z=> gaugePad W x D z i)) e
lemma scalar_clamp (D:ℕ)(x:Site f)(a:Axis)(y:Site f): gaugePad W x D (y+step a,vac)-gaugePad W x D (y,vac)=
   ∑ i:Axis,(glow D x (y+step a)*beam D x i (y+step a)-glow D x y*beam D x i y) • W (x,coord i):=by
 unfold gaugePad; rw [← Finset.sum_sub_distrib]; simp only [sub_smul]
lemma scalar_lift (D:ℕ)(x:Site f)(a:Axis)(y:Site f): fleece W D x (y,coord a)= W (y,coord a) - ∑ i:Axis, (glow D x (y+step a)*beam D x i (y+step a)-glow D x y*beam D x i y) • W (x,coord i):=by
 funext i; unfold fleece; rw [d_sites]; exact congr_arg (W (y,coord a) i-·) (congr_fun (scalar_clamp W D x a y) i)
lemma fleece_card (D:ℕ)(x:Site f)(a:Axis)(y:Site f)(h : separation y x < D): fleece W D x (y, coord a)= W (y,coord a) - (beam D x a (y+step a)-beam D x a y) • W (x,coord a):=by
 have hx : 0<D:=lt_of_le_of_lt (Nat.zero_le _) h
 have hy : separation (y+step a) x ≤ D:=by
    unfold separation; rw [add_sub_right_comm]; apply (pdist_triangle ..).trans; exact (by change pdist (y-x)+pdist (step a:Site f) ≤ D; change pdist (y-x)<D at h; have hV:=pdist_step (n:=f) a; omega)
 rw [scalar_lift, glow_home _ _ _ h.le hx, glow_home _ _ _ hy hx]
 simp_rw [one_mul]; rw [sum_eq_single a]; exact fun b _ hb => by rw [beam_side _ _ _ _ hb]; simp
 simp
end YM.Trace.Perfect

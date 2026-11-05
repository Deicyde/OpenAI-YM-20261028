import YM.RG08.Aura.Curl

/-! # Integration along rays to ∞, uniqueness using orthogonal axis (space≥2).
 Uses only pointwise column decay. -/
noncomputable section
namespace YM.RG08.Aura
open Function Lattice Laurent Pert.Bulk Forms Carrel Steam Rows RG Stationary Bloch Tack Anchor Spar Sedan Precision Finset Exterior Packets Ducat Filter
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false

abbrev Form := Cover→Axis→ℝ
def locked(f:Form):Prop:=∀ x i j,f (x+step i) j - f x j=f (x+step j) i-f x i

variable (f:Form)(i:Axis)
def tooth (x:Cover)(n:ℕ):Cover:= x+n • step i
def rim (x:Cover):ℝ:= - ∑' n:ℕ, f (tooth i x n) i
variable {f i}{τ p :ℝ}{y:Cover}

def fell(f:Form)(p τ:ℝ)(y:Cover) :Prop:=∀ (x i), |f x i| * Real.exp (τ*sep x y) ≤ p
lemma opposed (x:Cover)(i:Axis)(n:ℕ): (n:ℝ)-sep x y ≤ sep (tooth i x n) y:=by
 have he:= sep_triangle (tooth i x n) y x
 rw [show sep (tooth i x n) x=n by unfold tooth sep;rw [add_sub_cancel_left,length_nsmul,length_step,mul_one],sep_comm y x] at he;linarith
lemma quote {x i}{p τ :ℝ}(ht:0 < τ)(hp:0 ≤ p)(h:fell f p τ y)(n:ℕ)(j): |f (tooth i x n) j| ≤ p*Real.exp (τ*sep x y)*Real.exp (-(τ*(n:ℝ))) :=by
  -- hτ needed
  rw [← mul_le_mul_iff_left₀ (Real.exp_pos (τ*sep (tooth i x n) y))]
  apply (h _ _).trans
  rw [mul_assoc p, mul_assoc p,←Real.exp_add,←Real.exp_add]
  apply le_mul_of_one_le_right hp;apply Real.one_le_exp
  have he:=opposed (y:=y) x i n;nlinarith

lemma licensedRim (x:Cover)(j:Axis)(hτ:0<τ)(hP:0≤p)(h:fell f p τ y): Summable (fun n=> |f (tooth i x n) j|) :=by
 let a:= Real.exp (-τ);have ha:a<1:=by unfold a;rw [Real.exp_lt_one_iff];linarith
 refine Summable.of_nonneg_of_le (g:=fun n=> |f (tooth i x n) j|) (f:=fun n=>p*Real.exp (τ*sep x y)*a^n) (fun _=>abs_nonneg _) ?_ ((hasSum_geometric_of_lt_one (Real.exp_nonneg _) ha).summable.mul_left _)
 intro n; rw [show a^n=Real.exp (-(τ*(n:ℝ))) by unfold a;rw [←Real.exp_nat_mul];ring_nf]; exact quote hτ hP h n j

lemma rim_turn (h:locked f)(hτ:0<τ)(hP:0≤p)(H:fell f p τ y)(x:Cover)(j:Axis) : rim f i (x+step j)-rim f i x=f x j:=by
 have hrs (x:Cover)(j:Axis): Summable (fun n:ℕ=>f (tooth i x n) j):=Summable.of_norm (by simpa only [Real.norm_eq_abs] using licensedRim (i:=i) x j hτ hP H)
 unfold rim;rw [neg_sub_neg,← (hrs x i).tsum_sub (hrs (x+step j) i)]
 let a(n:ℕ):= f (tooth i x n) j
 have he (n):f (tooth i x n) i-f (tooth i (x+step j) n) i=a n-a (n+1):=by
    have ht:= h (tooth i x n) i j
    rw [show tooth i (x+step j) n = tooth i x n+step j from by unfold tooth;abel]; unfold a;rw [show tooth i x (n+1)=tooth i x n+step i from by simp [tooth,add_smul,add_assoc]];linarith
 simp_rw [he];rw [Summable.tsum_sub (hrs x j) ((summable_nat_add_iff 1).2 (hrs x j))]
 have hx := (hrs x j).sum_add_tsum_nat_add 1
 simpa [a,tooth] using (sub_eq_iff_eq_add.mpr hx.symm) -- simplify order
end YM.RG08.Aura

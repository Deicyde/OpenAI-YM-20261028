import YM.TraceExtension.Det.Rota
import YM.Push.LOOP_COEFFICIENT.Frequency
import YM.Next.STATIONARY.OneLoop.MomentumIntegral

/-!
# Aperture taps on finite physical meshes, keep rooted Laurent continuations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r:ℕ}{α σ μ a b c τ A C D:ℝ}
    {I:Type} [Fintype I]
def pitchf (f:Side):= 2*Real.pi/f.val
def reel (u:Cover): Track:= fun i=> u i
lemma pitch_pos : 0<pitchf f:= div_pos (by positivity) (side_pos _)
lemma reel_home : reel 0=0:=by ext1 i;simp[reel]
lemma reel_be (U V: Cover): reel (U+V)=reel U+reel V:=by ext1 i; simp[reel]
lemma reel_z (i:ℤ)(U:Cover): reel (i • U)=(i:ℝ) • reel U:=by ext1 j; simp [reel]
lemma reel_i (b:Axis): reel (step b) = step b:=by ext1 j; by_cases h:j=b<;> simp [reel,h]
lemma reel_neg (U:Cover): reel (-U)=-reel U:=by ext1 i;simp[reel]
lemma reel_roll (f:Side)(U:Cover): rolls (mon (wrap f U)) (axes (pitchf f • reel U)):=by
    rw[show axes (pitchf f • reel U)= Push.Loops.quant f U from ?_]; exact (Push.Loops.quant_matches f U).canonical
    ext1 i; unfold reel Push.Loops.quant; simp [axes,reciprocal,pitchf,div_eq_mul_inv]; ring
lemma norm_char {J:Type}[Fintype J](p:J→ℝ)(z:J→ℤ) : ‖mode (axes p) z‖=1:=by
    unfold mode; rw[Complex.norm_exp, show (Complex.I*∑ i,(axes p i)*(z i)).re=0 from ?_,Real.exp_zero]
    simp [axes,Complex.mul_re,Complex.mul_im]
-- real displacement
lemma mul_cell (n:Side)(u v z:Site n): cell (u+v) z=cell u z*cell v z:=by rw [cell_duality,cell_add,cell_duality z,cell_duality z]
lemma norm_cell (n:Side)(x y:Site n): ‖cell x y‖=1:=by unfold cell; rw [← axes_of_real (real_frequency x), norm_char]
def barca {I:Type} [Fintype I][DecidableEq I] (o: Site f)(x:Track)(b:I)(i:Co f I):= mode (axes x) (lift (i.1-o))* ((Pi.single (M:=fun _=>ℂ) b (1:ℂ)) i.2)
lemma barca_0 {p:Site f}(x:Track)(h:rolls (mon p) (axes x))(b:I) : barca (0:Site f) x b=relay p b:=by
    ext1 i; unfold barca relay tune; rw[sub_zero,← h.exp];rfl
-- sign check anchor
lemma barca_x {p:Site f}(x:Track)(o:Site f)(h:rolls (mon p) (axes x))(b:I) : cell p o • barca o x b=relay p b:=by
    ext1 i; simp only [Pi.smul_apply,barca, relay,tune,smul_eq_mul]; rw[← h.exp]
    change cell p o*(cell p (i.1-o)*_)=_; rw[← mul_assoc, ← cell_add, show o+(i.1-o)=i.1 by abel]

-- uniform all angles, dimensionful direction costs
variable {X Y Z:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup Z][NormedSpace ℝ Z]
lemma pullAll {L:X→L[ℝ] Y}{F:Y→ Z}{x:X} (h:Allows k F (L x) C)(hx:‖L‖ ≤ a)(hv:1≤a): Allows k (F ∘ L) x (C*a^k):=by
    have hc:=h.nonneg; have ha:0 ≤ a:=zero_le_one.trans hv
    refine ⟨h.analytic.comp _ L.contDiff.contDiffAt, fun i hi=>?_⟩
    rw [iter_lin_at (h.analytic.of_le le_top)]; apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..)
    calc
     _ ≤ C*(∏ _j:Fin i,a):=mul_le_mul (h.norm_le i hi) (prod_le_prod (fun _ _=>norm_nonneg L) (fun _ _=>hx)) (prod_nonneg fun _ _=>norm_nonneg L) hc
     _ ≤ _:=by simp; gcongr
private def sale (I:Type) [Fintype I]: Corn I→L[ℝ] Phase I:= ContinuousLinearMap.pi fun i=> Complex.ofRealCLM ∘L ContinuousLinearMap.proj i
lemma sea_mark (x:Site f)(z:Track)(ha:0 < a) (o:Site f):
    Allows k (fun y :Track=> mode (axes y) (lift (x-o))) z
      (Real.exp (4*a*separation x o)*((1+(2:ℝ)^k/a)^k)):=by
    let L:= sale Axis; have he(x:Track) i: L x i=x i:=rfl
    let F(y:Momentum):=mode y (lift (x-o))
    let V:= Real.exp (4*a*separation x o)
    have hh:Allows k F (L z) (V*((1+(2:ℝ)^k/a)^k)):=by
       apply allows_real_of_entire k _ ha
       · intro p hp; change p∈Metric.ball _ _ at hp; unfold V F; apply (reward _ _ a ?_).trans
         · have hv := ambient_size (x-o)
           have ht: ↑(size (lift (x-o)) :ℕ)≤ (4:ℝ)*separation x o:=by exact_mod_cast hv
           exact Real.exp_monotone (by nlinarith only [mul_le_mul_of_nonneg_left ht ha.le])
         intro i; have hx:=Complex.abs_im_le_norm ((p-L z) i); change |Complex.im _| ≤ a; simp only [Pi.sub_apply,Complex.sub_im,he,Complex.ofReal_im,sub_zero] at hx; rw[Metric.mem_ball,dist_eq_norm] at hp; exact hx.trans ((norm_le_pi_norm (p-L z) i).trans hp.le)
       unfold F mode; fun_prop
    have hL : ‖L‖ ≤ 1:= L.opNorm_le_bound zero_le_one (fun x=>by rw[one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i; rw[he,Complex.norm_real];exact norm_le_pi_norm ..)
    have ht:=pullAll hh hL le_rfl; rw[one_pow,mul_one] at ht; exact ht
end YM.Trace.Lamp

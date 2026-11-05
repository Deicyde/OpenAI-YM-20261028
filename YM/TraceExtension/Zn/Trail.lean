import YM.TraceExtension.Zn.Have
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Zn
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft
open scoped BigOperators Topology Classical
variable {F G:ℝ→ℝ}{a b c:ℝ}{j k:ℕ}
-- lean tails pay explicit x exponents
def Tigh (f:ℝ→ℝ)(k:ℕ):Prop:=∀ᶠ x:ℝ in atTop,0≤ f x ∧ f x≤(x^k)⁻¹
lemma Tigh.tight(h:Tigh F k)(hp:j≤k):Tigh F j:=by
    filter_upwards [h,eventually_gt_atTop (1:ℝ)] with x hx hp'; exact ⟨hx.1,hx.2.trans (inv_anti₀ (by positivity) (pow_le_pow_right₀ hp'.le hp))⟩
lemma Tigh.mono(h:Tigh F k)(he:∀ᶠ x:ℝ in atTop, 0 ≤ G x∧ G x ≤ F x): Tigh G k:=by filter_upwards [h,he] with x hx hy using ⟨hy.1,hy.2.trans hx.2⟩
lemma Tigh.join(h:Tigh F (k+1))(he:Tigh G (k+1)): Tigh (fun x=>F x+G x) k:=by
    filter_upwards[h,he,eventually_ge_atTop (2:ℝ)] with x hx hv hp; refine ⟨add_nonneg hx.1 hv.1,(add_le_add hx.2 hv.2).trans ?_⟩; rw [← two_mul, pow_succ]; have ht:0<x:=by linarith
    field_simp; linarith
lemma Tigh.mult(h:Tigh F (k+1))(hp:ConstMass a G): Tigh (fun x=>G x*F x) k:=by
   filter_upwards[h,hp (a+1) (lt_add_one _), wave_sub (a+1) 1 zero_lt_one,eventually_gt_atTop (0:ℝ)] with x h hv hz hx
   refine ⟨mul_nonneg hv.1 h.1,(mul_le_mul (hv.2.trans hz) h.2 h.1 (by positivity)).trans_eq ?_⟩; rw [Real.rpow_one, pow_succ]; field_simp
lemma Tigh.fly (h:Tigh F (k+1))(hp:ConstMass a G) : Tigh (fun x=>F x*G x) k:=by simpa only [mul_comm] using! h.mult hp
lemma Tigh.fact(h:Tigh F (k+1))(b:ℝ)(he:0 ≤ b): Tigh (fun x=> b*F x) k:= h.mult (mass he)
def shock (x:ℝ):ℝ:= (x^(100:ℕ))⁻¹
lemma shockT : Tigh shock 100:=by filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx using ⟨inv_nonneg.mpr (pow_nonneg hx.le _),le_rfl⟩
lemma eastP(f:ℝ→ℝ:=Perfect.east) (h:f=Perfect.east:=by rfl): ∀ᶠ x:ℝ in atTop, 0<f x ∧ f x≤1:=by rw [h]; filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx; exact ⟨inv_pos.mpr (lt_of_lt_of_le zero_lt_one hx),inv_le_one_of_one_le₀ hx⟩
lemma boomM (i:ℕ): ConstMass 0 (fun x=> momentPrice i (Perfect.east x/4)) :=by
    obtain h:=eastP
    apply ( (mass (show 0 ≤ Real.exp 1*i.factorial by positivity)).cop (((mass (show 0 ≤ (4:ℝ) by norm_num)).cop logC).crop i)).mono
    filter_upwards [eastP] with x hx; refine ⟨(momentPrice_pos _ (by positivity [hx.1])).le,?_⟩; unfold momentPrice; rw [div_eq_mul_inv, ← inv_pow, Perfect.east,inv_div,div_inv_eq_mul]; have hr : 0 ≤ Real.log x:= by have he : 0 < (Real.log x)⁻¹:=hx.1; exact (inv_pos.mp he).le
    gcongr; exact le_trans (div_le_self (a:=Perfect.east x) hx.1.le (by norm_num)) hx.2
lemma stern (k:ℕ) (hs:0<c): Tigh (fun t=> Real.exp (-c*rim t)) k:=by
    filter_upwards[Real.tendsto_log_atTop.eventually_ge_atTop (k/c),eventually_gt_atTop (1:ℝ)] with v hv hx; have h:= Real.log_pos hx; have hl:= Nat.le_ceil ((Real.log v)^2); refine ⟨(Real.exp_pos _).le,?_⟩
    rw [show v^k=Real.exp (k*Real.log v) from Eq.symm (by rw[Real.exp_nat_mul,Real.exp_log (by linarith)]), ← Real.exp_neg]; apply Real.exp_le_exp.mpr; unfold rim radiusB; push_cast; have hz:=(div_le_iff₀ hs).1 hv; have he := mul_le_mul_of_nonneg_right hz h.le; nlinarith
lemma roop : Tigh (fun t=> Real.exp (-(Perfect.east t/4)*rim t)) 100:=by
    filter_upwards[eventually_gt_atTop (1:ℝ)] with x hx; have ht:=Nat.le_ceil ((Real.log x)^2); refine ⟨(Real.exp_pos _).le,?_⟩;rw[← show Real.exp ((100:ℕ)*Real.log x)=x^ (100:ℕ) from by rw[Real.exp_nat_mul,Real.exp_log (by linarith)],← Real.exp_neg, Real.exp_le_exp]
    unfold Perfect.east rim radiusB; push_cast; have hX:=Real.log_pos hx; field_simp; linarith
lemma cupM: ConstMass 0 Loft.trophy:=by
    refine ConstMass.summit (range 5) (fun i b=>|reed b i+1|) ?_
    intro i _; apply (((logC.crop i).gather (mass (show 0 ≤ (1:ℝ) by norm_num)))).mono; filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx; have hh:=Real.log_pos hx; exact ⟨abs_nonneg _,(abs_of_nonneg (show 0≤reed x i+1 by unfold reed; positivity)).le⟩
end YM.Trace.Zn

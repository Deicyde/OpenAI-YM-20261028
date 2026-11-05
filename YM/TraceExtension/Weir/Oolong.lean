import YM.TraceExtension.Wicket.Sum
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Weir
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels Wicket
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{R:Rep G n}{P:BudgetPoint}
-- actual stage quals.Kernel.Good. Λ explicit.
abbrev hue(x:ℝ):=(Real.sqrt x)⁻¹^((11:ℝ)/5)
abbrev smoke(x:ℝ):= Real.exp (-(fog x^((1:ℝ)/5)))
structure Age (S:Stage)(x Λ:ℝ)(R:Rep G n) : Prop where
   hM : Made S x R
   paid : R.p.power=S.power
   rank : R.p.order=S.order
   depth : R.p.supportExponent=S.supportExponent
   thresh : R.p.threshold=thetaP x
   beta : |R.beta| ≤ 4*x
   coverage : Geo.Width R.p R.clip S.width
   good : R.Lawful S.width S.paths Λ (hue x) (smoke x)
   bnd : Λ ≤ humble x
   dialect : WilsonStartup.Decent R.clip R.p
   high : 4≤ R.p.supportExponent
def Lim(a:ℝ)(f:ℝ→ℝ):Prop:=∀ b:ℝ,a<b→∀ᶠ x:ℝ in atTop,0 ≤ f x∧f x≤ x^b
variable {a b C:ℝ}{F H:ℝ→ℝ}
lemma Lim.spot (h:Lim a F)(ht:b≥a):Lim b F:=fun c hc=> h c (lt_of_le_of_lt ht hc)
lemma Lim.plus(h:Lim a F)(hp: Lim a H): Lim a (fun x=> F x+H x) :=by
    intro c hc; let t:=(a+c)/2; have hx:a<t:=by unfold t;linarith;
    have htc:= (tendsto_rpow_atTop (show 0<c-t by unfold t; linarith))
    filter_upwards [h t hx, hp t hx, htc.eventually_ge_atTop 2, eventually_gt_atTop (0:ℝ)] with x h hp he ht; refine ⟨add_nonneg h.1 hp.1,(add_le_add h.2 hp.2).trans ?_⟩; rw [← two_mul]; exact (mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ x^t)).trans_eq (by rw[←Real.rpow_add ht,sub_add_cancel])
lemma Lim.prod (h:Lim a F)(hp:Lim b H): Lim (a+b) (fun x=>F x* H x):=by
   intro c hc; let t:=(c-(a+b))/2; have ht:0<t:=by unfold t; linarith
   filter_upwards [h (a+t) (lt_add_of_pos_right _ ht),hp (b+t) (lt_add_of_pos_right _ ht),eventually_gt_atTop (0:ℝ)] with x h hP hx; refine ⟨mul_nonneg h.1 hP.1,(mul_le_mul h.2 hP.2 hP.1 (by positivity)).trans_eq ?_⟩; rw [← Real.rpow_add hx, show a+t+(b+t)=c from by unfold t; ring]
lemma Lim.down (h:Lim a H)(hp:∀ᶠ x:ℝ in atTop,0 ≤ F x∧F x ≤ H x): Lim a F:=by intro c hc; filter_upwards [h c hc,hp] with x h hP using ⟨hP.1,hP.2.trans h.2⟩
lemma ferry (h:ConstMass a H):Lim 0 H:=by
   intro c hc;filter_upwards [h (a+1) (by linarith), wave_sub (a+1) c hc] with x h hP using ⟨h.1,h.2.trans hP⟩
lemma board(h:0 ≤ a):Lim 0 (fun _=>a):= ferry (mass h)
lemma sands(a:ℝ): Lim a (fun x:ℝ=>x^a):= by intro c hc; filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx using ⟨by positivity,Real.rpow_le_rpow_of_exponent_le hx hc.le⟩
lemma Lim.pow (h: Lim a F)(k:ℕ):Lim (k*a) (fun x=>F x^k):=by induction k with
    | zero=>simpa using board zero_le_one
    | succ k ih=> have h:= ih.prod h; simpa only[pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using! h
lemma Lim.tiny (h:Lim a F)(ha:a < 0) :∀ᶠ x:ℝ in atTop,F x ≤ 1:=by
    filter_upwards [h 0 ha] with x hx; simpa using hx.2
lemma isomV (a:F =ᶠ[atTop] H)(hp:Lim b F):Lim b H:= hp.down (by filter_upwards [a,hp (b+1) (by linarith)] with x hx ht;rw [← hx]; exact ⟨ht.1,le_rfl⟩)
lemma hey: Lim (-(1:ℝ)/2) (fun x:ℝ=>(Real.sqrt x)⁻¹) := by apply isomV _ (sands (-1/2)); filter_upwards[eventually_gt_atTop (0:ℝ)] with x hx; change x^(-(1:ℝ)/2)=_; rw[neg_div,Real.rpow_neg hx.le,Real.sqrt_eq_rpow]
lemma tall : Lim (-1/2) thetaP:= by simpa only [add_zero] using hey.prod (ferry (waveM 1))
lemma chime: Lim (-(11:ℝ)/10) hue:= by
    apply isomV _ (sands _); filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; change x^_=hue x; unfold hue; rw[Real.sqrt_eq_rpow, ← Real.rpow_neg hx.le,← Real.rpow_mul hx.le]; ring_nf
lemma cool: Lim (-(1/2:ℝ)-(1/24:ℝ)) peace:=by
    have h:= tall.prod (sands (-(1/24:ℝ))); rw [neg_div] at h
    apply isomV _ (b:= -(1/2:ℝ)-(1/24:ℝ)) (show Lim _ _ from h)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; change thetaP x *_=peace x; unfold peace; rw [Real.rpow_neg hx.le,div_eq_mul_inv]; rw[div_eq_mul_inv]
lemma fieryG : Lim ((1/2:ℝ)+1/24) (fun x=> (peace x)⁻¹):=by
    refine ((sands (1/24)|>.prod (sands (1/2))).down (F:=fun x=>(peace x)⁻¹) ?_) |>.spot (le_of_eq (add_comm ..))
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have he:0< fog x:=Zn.wake ..; have h:1≤fog x:=wok _ _ (by norm_num); refine ⟨by unfold peace thetaP; positivity,?_⟩; unfold peace thetaP; rw [inv_div,← Real.sqrt_eq_rpow]; refine (div_le_iff₀ (by positivity)).mpr ?_; calc
       _ ≤ x^((1:ℝ)/24)*fog x:=le_mul_of_one_le_right (by positivity) h
       _ = _:=by field_simp
lemma swole_b :∀ᶠ x:ℝ in atTop,x^ (-(101/100:ℝ))≤ swole x:=by
    filter_upwards[eventually_gt_atTop (1:ℝ)] with x hx; have ht:0<x:=by linarith
    have h:fog x ≥ 1:=wok _ _ (by norm_num); unfold swole thetaP; rw[mul_pow]; calc
       _ = ((Real.sqrt x)⁻¹)^ (2:ℕ) * x^ (-(1/100:ℝ)):=by rw [inv_pow,Real.sq_sqrt ht.le,← Real.rpow_neg_one, ← Real.rpow_add ht]; congr 1; norm_num
       _ ≤ _:=mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) (one_le_pow₀ h)) (by positivity)
lemma hStep(S:Stage):Lim (-1/2) (sash S):=by simpa only[add_zero] using tall.prod (ferry (((mass zero_le_one).gather expansion).crop S.power))
lemma oil(k:ℕ)(h:Tigh F k):Lim (-(k:ℝ)) F:=by
   apply (sands (-(k:ℝ))).down; filter_upwards [h,eventually_gt_atTop (0:ℝ)] with x h hv; simp only [Real.rpow_neg hv.le,Real.rpow_natCast]; exact h
def towerH(x:ℝ)(q:ℕ):= radiusB x^q +1100
lemma bankH(q:ℕ):ConstMass 0 (fun x:ℝ=>(towerH x q:ℝ)):=by unfold towerH; push_cast; exact ((upperB.crop q).gather (mass (show 0 ≤ (1100:ℝ) by norm_num)))
def Cleft(x:ℝ)(q:ℕ):= high x+10+ q*(4* radiusB x+2)+2*radiusB x
lemma campC (k:ℕ): ConstMass 0 (fun x:ℝ=>(Cleft x (towerH x k):ℝ)):=by
   unfold Cleft;push_cast; exact (((expansion.gather (mass (show 0≤ (10:ℝ) by norm_num))).gather ((bankH k).cop ((mass (show 0 ≤ (4:ℝ) by norm_num)|>.cop upperB).gather (mass (show 0≤ (2:ℝ) by norm_num))))).gather (upperB.times 2 zero_le_two))
lemma Cleft_mon (x:ℝ): Monotone (Cleft x):= fun _ _ h=> by unfold Cleft;gcongr
end YM.Trace.Weir

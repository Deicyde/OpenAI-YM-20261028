import YM.TraceExtension.Zn.Setup
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Zn
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft Xo
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {F:ℝ→ℝ}{a b c:ℝ}{k:ℕ}{G:Gauge}{n:Side}
abbrev tightf(x:ℝ):ℝ:=(x^ (70:ℕ))⁻¹
def Deja (J:Dart G n)(k:ℕ)(A x:ℝ):Prop:=
    (∀ i j:Axis,Turret.Bond (J.J i j) (Meld J x i j) k (puff x+1) (eastD x) (thinM x) (calorie x) A)∧(∀ i,Turret.Bond (J.Q i) (pluck (rim x) J i) k (puff x) (eastD x) (thinM x) (calorie x) A)∧
    (∀ i j a:Axis, Turret.Bond (J.twist i j a) (pluckD (rim x) J i j a) k (puff x) (eastD x) (thinM x) (calorie x) A)∧ ∀ i,Turret.Bond (boom J.J i) (boom (Meld J x) i) k (puff x+1+4) (eastD x) (thinM x) (tightf x) A
private lemma drum_f1 (C:ℝ): drumA C= (drumA 1)*C:=by unfold drumA; rw[Finset.sum_mul]; refine sum_congr rfl fun i _=>?_ ; ring
private lemma du(Z:ℝ):plumAmount Z=plumAmount 1*Z:=by unfold plumAmount; ring
private lemma vu(Z:ℝ): papa Z=papa 1*Z:=by unfold papa; ring
lemma sense (G:Gauge)(A:ℝ)(k:ℕ)(ha:0≤A): ∀ᶠ x:ℝ in atTop,∀ (n:Side)(J:Dart G n)(R:Rep G n),Sight x R J → Deja J k A x:=by
    obtain ⟨P,W,D,hP,hW,H⟩:= greet G k A ha
    let f(x:ℝ):= P (rim x)*Loft.trophy x; let B(x:ℝ):= W * momentPrice D (Perfect.east x/4)* Real.exp (-(Perfect.east x/4)*rim x)*Loft.trophy x
    have hv: Tigh B 98:= (((roop.mult ((boomM D).times W hW))).fly cupM)
    let U:=fun x=>plumAmount (f x);let V:=fun x=>papa (B x)
    have ht: ConstMass 0 f:= ((ConstMass.under P hP (G:=rim) rim_S).cop cupM); have hz: ConstMass 0 U:=by
       unfold U; rw[show (fun x=>plumAmount (f x))=fun x=>plumAmount 1 * f x from funext fun x=>du _];
       exact ht.times _ (by norm_num [plumAmount])
    have hu:Tigh V 97:=by unfold V; rw [show (fun x=>papa (B x))=fun x=>papa 1 * B x from funext fun _=> vu _]; exact hv.fact _ (by unfold papa; have h:= Perfect.shelter_pos 1 4 (show (0:ℝ)≤1 from zero_le_one); positivity)
    have hm:0≤drumA 1:=sum_nonneg fun _ _=> by positivity
    let v(x):=4*droneD (V x); let g(x):=4*drumA (U x);
    have hV : Tigh v 94:=by
       have he(x):v x=4*(drumA 1* (Perfect.shelter 1 4 (4:ℕ)*V x)):=by unfold v droneD; nth_rw 1 [drum_f1]
       rw[funext he]; exact (((hu.fact _ (Perfect.shelter_pos _ _ (by positivity)).le).fact _ hm).fact _ (by norm_num))
    have hg:ConstMass 0 g:=by
       rw[show g=fun x=>(4:ℝ)*(drumA 1*U x) from funext fun x=>congr_arg ((4:ℝ)*·) (drum_f1 _)]; exact ((hz.times _ hm).times _ (by norm_num))
    filter_upwards [ht _ (by norm_num:0< (1/200:ℝ)),hz _ (by norm_num:0 < (1/200:ℝ)),hg _ (by norm_num:0 < (1/200:ℝ)),hV.tight (show 70≤94 by omega), hu.tight (show 30≤97 by omega),hv.tight (show 30≤98 by omega), eastP] with x hx hz hh hH hJ hm he n J R hY
    obtain ⟨h,hb,hr⟩:= Turret.pulse (a:= Perfect.east x) (ht:= H _ _ (Loft.trophy x) he.1 he.2 (sum_nonneg fun _ _=>abs_nonneg _)) hY.1 hY.2 he.1.le he.2 hx.1 hm.1
    have hp(i j:Axis): Turret.Bond (J.J i j) (Meld J x i j) k (puff x+1) (eastD x) (U x) (V x) A:= hr i j
    exact ⟨fun i j=> (hp i j).top hz.2 hJ.2 le_rfl, fun i=>(h i).top hx.2 hm.2 le_rfl, fun i j k=>(hb i j k).top hx.2 hm.2 le_rfl, fun i=> (swell hp (div_nonneg he.1.le (by norm_num)) (le_trans (div_le_self he.1.le (by norm_num)) he.2) i).top hh.2 hH.2 le_rfl⟩
lemma weather(G:Gauge)(A:ℝ)(ha:0 ≤ A)(k:ℕ)(v:ℝ)(hv:0 < v): ∀ᶠ x:ℝ in atTop,∀ (n:Side)(J:Dart G n)(R:Rep G n),Sight x R J → ∀ i:Axis,
    Clouded (YCore x J i) (Bay n x) ∧ Climate (YCore x J i) k (Wave v x) A ∧ Estate 0 (bottom (J.Y i 0-YCore x J i)) (eastD x) (fun _=>tightf x) ∧
       Estate 0 (bottom (J.Y i 0)) (eastD x) (fun _=> Loft.trophy x):=by
    obtain ⟨Z,hZ,H⟩:= allp G A ha k
    obtain ⟨C,P,hC,h⟩:= Filch.dew G
    let f(x:ℝ):= C*momentPrice P (Perfect.east x/4)*Real.exp (-(Perfect.east x/4)*(rim x))*Loft.trophy x; have hh : Tigh f 98:=(roop.mult ((boomM P).times C hC)).fly cupM
    filter_upwards [hh.tight (show 70≤98 by omega), ((ConstMass.under Z hZ (G:=rim) rim_S).cop cupM) v hv, eastP] with x hx hv he n J R hY i
    have hg:0 ≤ Loft.trophy x:=sum_nonneg fun _ _=> abs_nonneg _; let T:= J.Y i 0; have hT:T∈rains G n:=hY.1.sound.palm ..
    have hV:Estate 0 (bottom T) (Perfect.east x) (fun _=>Loft.trophy x):=hY.1.Y ..
    have hp:= (h n 0 (rim x) (Perfect.east x) (Loft.trophy x) he.1 he.2 hg).2 T hT hV
    refine ⟨say _ _ hT,⟨fun V _ _ W y hW i'=> ((H n 0 (rim x) T _ _ he.1.le hg hT hV).laps V W y hW i').mono hv.2⟩, ⟨fun i hi h=> (hp.values i hi h).trans hx.2⟩, ⟨fun i hi h=>?_⟩⟩
    exact (cost_tiny (Perfect.leaf (bottom T) 0 i) _ _ _ _ _ _ (div_nonneg he.1.le (by norm_num)) (div_le_self he.1.le (by norm_num)) le_rfl).trans (hV.values i hi h)
end YM.Trace.Zn

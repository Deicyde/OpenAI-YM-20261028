import YM.TraceExtension.Perfect.Hoop
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{R:PathData G}{α C D:ℝ} (x:Site f)
private lemma push_ride (U:Config G f)(s:Signed): pull s 0 (ride x U)=ride (s⁻¹.act x) (pull s 0 U) := by
 unfold ride; rw [←pull_one,← pull_one,pull_pull,pull_pull]; simp [affine]
private lemma slot_ride (U:Config G f)(s:Slot)(y:Site f): s.atSite (ride x U) y=s.atSite U (y+x):=by unfold Slot.atSite; rw [show expandAt y (ride x U)=expandAt (y+x) U from funext (fun i=>by simp [expandAt,ride,Lattice.translate,add_assoc])]
lemma main_ride (p:Clip)(R:PathData G)(U:Config G f): mainTerm p R (ride x U)= mainTerm p R U:=by
 have ht {k:ℕ}(R:ℕ→Atom G k)(x:Site f)(U:Config G f): uncut R (ride x U)=uncut R U:=by
    unfold uncut Atom.unmasked; simp_rw [slot_ride]; exact (paceV x).sum_comp (fun y=>∑' i,(R i).unmasked U y)
 unfold mainTerm; simp_rw[push_ride,ht]; apply congr_arg; ext1 i; congr 2
 let y:=i⁻¹.act x; let V:=pull i 0 U
 have he(j: Face (Per f)): faceValue (ride y V) j=faceValue V (rideI y j):=by unfold ride faceValue; rw [← pull_one,travel_pull]; simp [affine];rfl
 have hp(j): R.ell (ride y V) j=R.ell V (rideI y j):=by unfold PathData.ell PathData.ellTerms; simp_rw [slot_ride]; rfl
 change quadratic p R (ride y V)=quadratic p R V; unfold quadratic; simp_rw[he,hp]; exact Equiv.sum_comp (rideI y) (fun b:Face (Per f)=>p.direct*G.price (faceValue V b)+‖R.ell V b‖^2/2)

lemma smell (Y:Gal G f)(h:R.Bounds p α C D) : aroma p R (ry x Y)=rj x (aroma p R Y):=by
 ext1 V; let A:= burn p R V; let U:=ride x V; let F:= burn p R U; let L:= rideC (G:=G) (-x)
 have hp : A ∘ L=F:=funext fun k=> by
    change mainTerm p R (input _ _ _ * _)=mainTerm p R (input _ _ k * _); rw [r_imp]
    have hx : ride (-x) (input _ _ k *U)=ride (-x) (input _ _ k)*V:=by ext1 i; change (input _ _ k _ * V ((i.1+-x)+x,_))= _* _;rw [neg_add_cancel_right];rfl
    rw [← hx,main_ride]
 have hv : ContDiffAt ℝ ω A 0:= by
    exact Work.F02.mainTerm_contDiffAt (A:=fun v:Link G f=>input G f v*V) h ((Army.powL (v:=id) contDiffAt_id).mul (Army.park V _))
 change fderiv ℝ A 0 (L (Y U))=fderiv ℝ F 0 (Y U); rw [← hp, fderiv_comp 0 (by rw[map_zero]; exact hv.differentiableAt (by simp)) L.differentiableAt,map_zero,L.fderiv]; rfl

-- transport
namespace Dart
variable (Z:Dart G f)
def loopB {B:Type*}[AddCommGroup B][Module ℝ B](L:B→ₗ[ℝ] B)(b:Site f): (Site f→B)→ₗ[ℝ] (Site f→B) where
 toFun f i:= L (f (i-b))
 map_add':=fun _ _=>funext fun i=> map_add ..
 map_smul':=fun c F=>funext fun i=> L.map_smul c (F _)
lemma loop_elm {B:Type*}[AddCommGroup B][Module ℝ B](L:B→ₗ[ℝ] B)(f:Site f→B)(i): loopB L x (elm i f)=elm i (loopB L x f):=by
 funext y; change L (elm i f (y-x)) = _; unfold elm Pull.dTap; rw [map_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [map_smul,map_sub]; simp only[loopB,LinearMap.coe_mk,AddHom.coe_mk]; rw [sub_add_eq_add_sub, sub_add_eq_add_sub]
lemma loop_twig {B:Type*}[AddCommGroup B][Module ℝ B](L:B→ₗ[ℝ] B)(f:Site f→B)(i): loopB L x (twig i f)=twig i (loopB L x f):=by funext y; change L (f (y-x+step i)-f (y-x))=L (f (y+step i-x))- _;rw[map_sub,sub_add_eq_add_sub]; rfl

def gait : Dart G f where
 J a b:= loopB (rj x) x (Z.J a b)
 Y a:= loopB (ry x) x (Z.Y a)
 E a:=loopB (rj x) x (Z.E a)
 Q a:= loopB (rj x) x (Z.Q a)
 twist a b v:= loopB (rj x) x (Z.twist a b v)

lemma gait_wit (h:Z.Sound R p)(hp:R.Bounds p α C D): (gait x Z).Sound R p:=by
 refine ⟨fun i j k=> taking_loom x _ (h.heart ..),fun i j=>taking_rain x _ (h.palm ..),fun i j=>taking_loom x _ (h.plum ..),fun i j=>taking_loom x _ (h.plumQ ..),fun a b i j=>taking_loom x _ (h.mint ..),?_,fun a b=>?_,fun i y=>?_⟩
 · dsimp only[gait]; simp only[← loop_twig,← map_sum,h.hue]
 · dsimp only[gait]; simp only[← loop_twig,← map_sum,←map_sub,h.tint]
 dsimp only[gait]; let L:Link G f→L[ℝ]Link G f:=rideC x
 simp_rw [← loop_elm,← map_sum,← map_sub]
 let V:= ((∑ a:Axis,elm a (Z.J a i))-Z.E i)
 obtain ⟨hc,hc',H⟩:= h.fin i (y-x)
 change Cleric (V (y-x)) at hc; change braid _ _ 0 4 at H
 let k:= Z.Y i (y-x)
 change (rj x (V (y-x)),aroma p R (ry x k))∈wing f G
 have hs : Cleric (rj x (V (y-x))):=by
    have ht : V (y-x)∈loom G f:=by
       unfold V; simp only[Pi.sub_apply,Finset.sum_apply,elm,Pull.dTap]; exact (loom G _).sub_mem ((loom _ _).sum_mem fun a _=>(loom _ _).sum_mem fun j _=> (loom _ _).smul_mem _ ((loom _ _).sub_mem (h.heart ..) (h.heart ..))) (h.plum ..)
    obtain ⟨t,_⟩:=taking_loom x _ ht; exact t
 obtain ⟨hy,hz⟩:=taking_rain x _ (h.palm i (y-x)); refine ⟨hs, aroma_diff hp hy,?_⟩
 change braid ((rj x (V (y-x))) ∘ _) ((aroma p R (ry x k)) ∘ _) _ _
 rw[smell x k hp,take_px,take_px]; exact wove (w:=L) ((map_zero L).symm ▸ H) ((map_zero L).symm ▸ hc.dye) ((map_zero L).symm ▸ (show Cleric (aroma p R k) from hc').dye) L.contDiff.contDiffAt

lemma gait_viz (hp:R.Bounds p α C D)(v:ℝ)(P Q:ℕ→ℝ)(ε:ℝ)(h:Viz Z p R v P Q ε): Viz (gait x Z) p R v P Q ε:=by
 have ht (y:Site f)(u) (hx:u∈loom G f)(A':ℕ→ℝ)(hv:Estate (y-x) (ballX u) v A'): Estate y (ballX (rj x u)) v A':=by
    rw [ride_ball]; apply sub_add_cancel y x ▸ (show Estate (y-x+x) _ _ A' from ?_)
    refine ⟨fun j hi hj=> ?_⟩; rw [ride_jet v _ _ _ (loom_read hx).2.2];exact hv.values j hi hj
 refine ⟨gait_wit x Z h.sound hp,fun a b y=>ht y _ (h.sound.heart ..) _ (h.J ..),fun i y=>?_,fun _ y=> ht y _ (h.sound.plum ..) _ (h.E ..),fun a y=>ht y _ (h.sound.plumQ ..) _ (h.plum ..),fun a b i y=>ht y _ (h.sound.mint ..) _ (h.mint ..),fun a b y=> ?_,fun i y=> ?_⟩
 · let s:= Z.Y i (y-x); change Estate y (bottom (ry x s)) v _; refine ⟨fun j hi hj=>?_⟩; rw [ride_bottom]; have he:= ride_jet v _ x (y-x) ((rain_read (h.sound.palm i (y-x))).2.2.1) j; rw[sub_add_cancel] at he; rw [he]; exact (h.Y i (y-x)).values j hi hj
 · change Testify y (ballX (rj x (Z.J a b (y-x)))) _ _ _; rw[ride_ball]; have hp:=ride_tell x (h.ox a b (y-x)) (loom_read (h.sound.heart a b (y-x)) |>.2.2); rw [sub_add_cancel] at hp; exact hp
 change Testify y (bottom (ry x (Z.Y i (y-x)))) _ _ _; rw [ride_bottom]; have hp:= ride_tell x (h.orb i (y-x)) (rain_read (h.sound.palm i (y-x)) |>.2.2.1); rw [sub_add_cancel] at hp; exact hp
end Dart
end YM.Trace.Perfect

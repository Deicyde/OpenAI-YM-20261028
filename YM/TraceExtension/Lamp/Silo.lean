import YM.TraceExtension.Lamp.Torque

/-!
# Flip shape invariant diagonal leading form. Handle real plane p tilt.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {F:Peat G f}{t:Signed}
structure Contours (F:Peat G f) : Prop where
    coat: Cleric F
    lit: ∀ s:Signed,F ∘ input G f ∘ orderTurn s =ᶠ[𝓝 0] F ∘ input G f
    still x: F ∘ input G f ∘ rideC x=ᶠ[𝓝 0] F ∘ input G f

lemma contours_m {μ:ℝ}{p:Clip}{R:PathData G} (hμ:0<μ)(hp:R.Bounds p α C D)(h:(stock p R μ (1:Config G f)).det≠0) : Contours (marke p R μ (f:=f)):=by
    refine ⟨dyed_mark hp hμ h,fun s=> Eventually.of_forall (fun x=>?_), fun x=>Eventually.of_forall fun y=>?_⟩
    · simp only [Function.comp_apply]; change marke p R μ (input G f (flipCoords s ℝ x))=_; rw [← flip_links,mark_signed _ s μ hp]
    simp only[Function.comp_apply];rw[r_imp,marks_trans _ _ μ hp]
lemma contours_main {R: PathData G}{p:Clip}(h:R.Bounds p σ C D): Contours (mainTerm p R (n:=f)):=by
    refine ⟨⟨Work.F02.mainTerm_contDiffAt h (Army.powL (n:=f) (v:=id) contDiffAt_id), fun T _ _ _ _ V k u _ _ _ _=> Eventually.of_forall fun i=> Work.F05.mainTerm_gauge h _ _⟩,fun s=>Eventually.of_forall fun v=>?_,fun z=>Eventually.of_forall fun v=> ?_⟩
    · change mainTerm p R (input G f (flipCoords s ℝ v))=_; rw [← flip_links]; exact orbit_axis (fun b=>quadratic p R b+ uncut R.cubic b+uncut R.quartic b) _ _
    simp only[Function.comp_apply];rw [r_imp, main_ride]
lemma silk (h:Contours F)(z:Site f): Kbody F*car G 1 z=car G 1 z*Kbody F:=by
    have ht: Kbody F=damage (pocket _) (F ∘ input G f) 0:=by unfold Kbody beamH; rw [show bal 1 F=_ from (show _=F ∘ input G f from funext (fun i=>by simp[bal]))];
    rw[ht]; let V:=F ∘ input G f; let L:= rode G 1 z
    apply (mil_c z G 1).pulls
    exact Eq.trans (damage_rate _ _ V L h.coat.dye|>.symm) (damage_congr _ (show V ∘ L=ᶠ[𝓝 0] V from h.still z))

def shark (F:Peat G f)(i j:Loc G 1)(p:Site f):= (Kane F *ᵥ relay p j) (0,i)
def bay (F:Peat G f)(i j: Loc G 1)(x:Track): ℂ:= ∑ z: Site f,(Kane F (0,i) (z,j))* mode (axes x) (lift z)
lemma bores (i j:Loc G 1)(q:Cover): shark F i j (wrap f q) = bay F i j (pitchf f • reel q):=by
    have hv: relay (wrap f q) j=barca (0:Site f) (pitchf f • reel q) j:=by ext1 i; change cell (wrap f q) i.1*_=mode _ _*_;rw [←(reel_roll f q).exp]; unfold cell; simp only[sub_zero]
    unfold shark;rw [hv,barge_point,Matrix.mulVec_sum,Finset.sum_apply]; unfold bay; apply Finset.sum_congr rfl; intro i _; rw [Matrix.mulVec_smul,mulVec_single_one];simp [mul_comm]
lemma shark_ro (h:Contours F)(x:Site f)(b:Loc G 1): Kane F*ᵥ relay x b= ∑ a:Loc G 1, shark F a b x • relay x a:=by
    have hs(z:Site f)(i:Loc G 1): (Kane F*ᵥ relay x b) (z,i)= cell x z * shark F i b x:=by
       let s:=shark F i b x
       unfold shark Matrix.mulVec dotProduct; rw [Finset.mul_sum]; conv_lhs=> rw[← Equiv.sum_comp (rideI (I:=Loc G 1) z)]
       apply Finset.sum_congr rfl; intro v _
       have hv: Kane F (z,i) (rideI z v)= Kane F (0,i) v:=by
            have ht: (Kbody F) (0,i) v=(Kbody F) (z,i) (rideI z v):=by
               rw [show (z,i)=rideI z (0,i) from ?_]; · exact ((car_elem z _ _).1 (silk h z) (0,i) v)
               change (z,i)=(0+z,i);simp
            exact congr_arg ((↑):ℝ→ ℂ) ht.symm
       dsimp only; rw [hv]; rcases v with ⟨p,c⟩; unfold relay tune; rw [show rideI z (p,c)=(p+z,c) from rfl,show cell x (p+z)=_ from cell_add ..]; ring
    ext1 ⟨z,i⟩; rw[hs,Finset.sum_apply, sum_eq_single i];
    · simp[relay,tune,mul_comm]
    · intro j _ hj; simp [relay,tune,Ne.symm hj]
    simp
lemma ivo (s:Signed)(p:Site f): (s⁻¹).act (s.act p)=p:=by simp
lemma ray_shark (h:Contours F)(p:Site f)(a b:Loc G 1): beat (F ∘ input G f) 0 2 ![relay (-p) a,relay p b] = (Fintype.card (Site f):ℂ)*shark F a b p:=by
    have he(i:Loc G 1): dotProduct (relay (-p) a) (relay p i)= if i=a then (Fintype.card (Site f):ℂ) else 0:=by
       unfold relay; rw [ray_dots, if_pos (neg_add_cancel _)]; by_cases h:i=a
       · subst i; simp
       simp[h]
    rw [stiff_body, shark_ro h, dotProduct_sum]; simp_rw [dotProduct_smul,he]; simp [mul_comm]
lemma shark_her (h:Contours F)(x:Site f)(p q:Axis)(a b:G.ColorIndex) (s:Signed):
    shark F (coord (s.perm p),a) (coord (s.perm q),b) (s.act x)=reflectFee s (mon (-(s.act x))) p * reflectFee s (mon (s.act x)) q * shark F (coord p,a) (coord q,b) x:=by
    let T:=F ∘ input G f; let N:=orderTurn (G:=G) (m:=f) s
    let Z:= flipCoords (G:=G) (m:=f) s ℂ
    let u:=s.act x
    have hx:=evaluated (L:=N) (f:=T) Z (fun p=>flip_scalar s p) h.coat.dye.analyticAt (n:=2)
    have he: beat (T ∘ N) 0 2=beat T 0 2:=by unfold beat; rw [show iteratedFDeriv ℝ 2 (T ∘ N) 0=iteratedFDeriv ℝ 2 T 0 from ((h.lit s).iteratedFDeriv ℝ 2|>.eq_of_nhds)]
    let C := (Fintype.card (Site f):ℂ); have hp:C≠0:=Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
    apply mul_left_cancel₀ hp
    rw [show C*_=_ from (ray_shark h (s.act x) (coord (s.perm p),a) (coord (s.perm q),b)).symm, ← he, hx, MultilinearMap.compLinearMap_apply];
    rw [show (fun k:Fin 2=> Z ((![relay (-u) (coord (s.perm p),a),relay u (coord (s.perm q),b)]:Fin 2→Phase (Lines G f 1)) k))=(fun k=> ( ![reflectFee s (mon (-u)) p,reflectFee s (mon u) q]:Fin 2→ℂ) k • ((![relay (-x) (coord p,a),relay x (coord q,b)]:Fin 2→ Phase (Lines G f 1)) k)) from ?_, MultilinearMap.map_smul_univ,Fin.prod_univ_two,smul_eq_mul]
    · change _ * beat _ 0 2 _=_; unfold T; rw [ray_shark h]; unfold C u; simp; ring
    ext1 k; fin_cases k; · change Z _=_ • relay (-x) _; have ht:=flipped s (-u) p a; rwa [Signed.act_neg,show s⁻¹.act u=x from ivo ..] at ht
    change Z _= _ • relay x _; have ht:=flipped s u q b; rwa [show s⁻¹.act u=x from ivo ..] at ht
end YM.Trace.Lamp

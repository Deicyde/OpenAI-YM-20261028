import YM.RG08.Spin.Aura
/-! # Symmetry of full Wick covariance, kernels with real physical weighting.
Not using regulators. Good for horizontal uses (breaks zero-mode separately). -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Spin
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Pivot Carrier Place Scores.Pages Drift
open scoped BigOperators Topology Real ContDiff Classical
open Wings Summit
variable {G:Gauge}{c f : Side}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{H:Hol G}{S:SectionData F}{h:1/2≤R}{Z : Ratio c f}
section
variable (s:Signed)
lemma orbit_sig (p:Site c): ∃ x:Cover, mon (s.act p)=s.act (mon p)+reciprocal x:= by
    obtain ⟨x,hx⟩:= cover_of_eq (n:=c) (s.act (lift p)) (lift (s.act p)) (by rw [← wrap_signed,wrap_lift,wrap_lift]); refine ⟨x,?_⟩; funext i; obtain ⟨i,rfl⟩:= s.perm.surjective i
    rw [Pi.add_apply, s.act_at]; have he := congr_fun hx (s.perm i)
    rw [Pi.add_apply,s.act_at] at he; unfold mon; cases hb:s.flip i <;> simp only [hb,Bool.false_eq_true,↓reduceIte,reciprocal, he,Int.cast_add,Pi.smul_apply, nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,Int.cast_neg] <;>  simp only [smul_eq_mul] <;> field_simp [side_ne]
lemma curb_sig (w:Train j)(p:Site c)(a:Axis): curfew R w (mon (s.act p)) (coord (s.perm a)) (coord (s.perm a))=curfew R w (mon p) (coord a) (coord a):= by
    rw [punctual_curfew,punctual_curfew]; simp only [mon_here,show s.act p=0 ↔ p=0 from by rw [← Signed.act_zero s,s.act_injective.eq_iff,Signed.act_zero]]; split; rfl
    obtain ⟨z,hz⟩:= orbit_sig s p; rw [hz, Train.D_stable]; rw [← coord_map, ← coord_map, axisEquiv.symm_apply_apply,axisEquiv.symm_apply_apply]; exact Train.D_signed ..
omit s in
lemma bed_van (w: Train j) (p q:Site c) (i j : TypeFace 1) (ht:i≠j): bedtime R w c (p,i) (q,j)=0:= by
    unfold bedtime Drift.daylight; rw [Matrix.map_apply, orchard_show]; rw [Finset.sum_eq_zero]; simp
    intro j _; unfold curfew; split; simp
    simp only [fieldD,mask_value,if_neg ht,mul_zero,zero_mul]
lemma bed_spun (w:Train j)(p q:Site c)(a:Axis)(y:Site c): bedtime R w c (s.act p+y,coord (s.perm a)) (s.act q+y,coord (s.perm a))=bedtime R w c (p,coord a) (q,coord a):= by
    rw [trace_nimb,trace_nimb w c p q,add_sub_add_right_eq_sub]; unfold bedtime Drift.daylight; simp only [Matrix.map_apply, orchard_show]
    congr 2
    rw [← Equiv.sum_comp (Signed.actEquiv s (R:=Per c)).toEquiv]
    refine Finset.sum_congr rfl fun t _=>?_
    change cell (s.act t) 0 * curfew R w (mon (s.act t)) _ _ *star (cell (s.act t) (s.act q-s.act p)) = _
    rw [curb_sig, show s.act q-s.act p= s.act (q-p) from (map_sub (Signed.actEquiv s (R:=Per c)) q p).symm, mirror_cell]; simp [cell_origin]
-- tensor physical Wick under exactly stated turn, no harmonic.
def rotM (s:Signed)(c:Side)(G:Gauge): Matrix (Stationary.Lines G c 1) (Stationary.Lines G c 1) ℝ:= LinearMap.toMatrix' (orderTurn s).toLinearMap
lemma rot_eval (s:Signed)(x:Link G c): (rotM s c G)*ᵥ x=orderTurn s x:= LinearMap.toMatrix'_mulVec ..
def lidM (p:Fare G)(c:Side) : Lines G c 1 := (wrap c p.1,p.2)
lemma coin_m (c:Side)(p : Fare G) (u: Stationary.Lines G c 1) : rotM s c G (lidM p c) u= if u=lidM (loc_sig s p) c then bias s (Vale.heap p).2 else 0:= by
    let P:=rotM s c G; let v:Link G c:= Pi.single u (1:ℝ); have hz(i): P i u= (P*ᵥ v) i:= by simp [mulVec,dotProduct,v,Pi.single_apply]
    change P _ _ =_; unfold lidM; rw [hz, show P*ᵥ v= _ from rot_eval s v, slip_loc]
    simp [v,Pi.single_apply,Eq.comm]
lemma rot_eq (w: Train j)(c:Side)(G:Gauge):
    rotM s c G*tensor G (bedtime R w c)*(rotM s c G)ᵀ=tensor G (bedtime R w c):= by
    let A:=rotM s c G; let S:= FreeResolvent.tensor G (bedtime R w c) -- possible namespace
    have hv (i:Fare G)(b) : (A*S) (lidM i c) b=bias s (Vale.heap i).2 * S (lidM (loc_sig s i) c) b:= by
       unfold A; rw [Matrix.mul_apply]; simp_rw [coin_m]; simp [ite_mul]
    have hh (p q: Cover) (a b: Axis) (i j:G.ColorIndex): let X:Fare G:= (p,coord a,i); let Y : Fare G:= (q,coord b,j)
        S (lidM X c) (lidM Y c)=(bias s a*bias s b)* S (lidM (loc_sig s X) c) (lidM (loc_sig s Y) c):= by
       intro x y; unfold S FreeResolvent.tensor; dsimp only [loc_sig,x,y,Vale.heap,Film.up,bias,lidM, Matrix.of_apply]
       simp only [show axisEquiv.symm (Exterior.coord a)=a from axisEquiv.symm_apply_apply a,show axisEquiv.symm (Exterior.coord b)=b from axisEquiv.symm_apply_apply b]
       by_cases hb:a=b
       · subst b
         simp_rw [going_spec, map_add, ←wrap_signed,bed_spun]; split_ifs <;> ring
       have hx : Exterior.coord (s.perm a) ≠ Exterior.coord (s.perm b):= axisEquiv.injective.ne (s.perm.injective.ne hb); split_ifs <;> first|omega|simp [bed_van w _ _ _ _ (show Exterior.coord a ≠ Exterior.coord b from axisEquiv.injective.ne hb),bed_van w _ _ _ _ hx]
    ext ⟨p,a,i⟩ ⟨q,b,j⟩; obtain ⟨a,rfl⟩:=axisEquiv.surjective a; obtain ⟨b,rfl⟩:=axisEquiv.surjective b
    obtain ⟨p,rfl⟩:= (show Surjective (wrap c) from fun x=>⟨lift x,wrap_lift x⟩) p; obtain ⟨q,rfl⟩:= (show Surjective (wrap c) from fun x=>⟨lift x,wrap_lift x⟩) q
    let X:Fare G:=(p,coord a,i); let Y : Fare G:= (q,coord b,j)
    change (A*S*Aᵀ) (lidM X c) (lidM Y c) = S (lidM X c) (lidM Y c); rw [hh p q a b i j,Matrix.mul_apply]; simp_rw [hv,transpose_apply,A,coin_m]; simp only [mul_ite,mul_zero, Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
    rw [show (Vale.heap X).2=a from axisEquiv.symm_apply_apply a,show (Vale.heap Y).2=b from axisEquiv.symm_apply_apply b,mul_right_comm]
end
end YM.RG08.Spin

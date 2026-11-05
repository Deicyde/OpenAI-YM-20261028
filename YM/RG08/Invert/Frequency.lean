import YM.RG08.Spin.Flash
/-!
 # Simultaneous inversion in the E1 unmodified kernel supplies
   (extension of RuneTurn, direct proof on T too). This does not assert
   even external characters; phase inversion arguments belong to other stages.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Invert
open Function Filter Set Lattice Wilson Exterior Precision Laurent Next.Free Next.Free.Flight RG RG.Supply Bloch Input Finset Matrix
open Planned.PrimaryIntegral295 Carrier
open scoped BigOperators Topology Real Classical Matrix
variable {G:Gauge}{i j k t r:ℕ}{L:Side}

def sigma : YM.Signed:= ⟨Equiv.refl _,fun _=> true⟩
lemma sig_act {V:Type} [AddCommGroup V] (x:Four V): sigma.act x= -x:=rfl

def penny (p:Momentum)(i:Axis):= aspect sigma p i -- -(mode p (step i)); positive phase, orientation shader after field transformation
lemma penny_at (p: Momentum)(i:Axis): penny p i= -mode p (step i):= by change -twirl _ _= _; congr 1; rw [factor]; simp [twirl]
private lemma chip_sp (p: Momentum)(i:Axis): penny p i * chip (-p i)=chip (p i):= by
   rw [penny_at, factor,chip,chip,mul_neg,Complex.exp_neg]; field_simp [Complex.exp_ne_zero]; ring

def shineF (p:Momentum)(r:ℕ): Frequency r r:= mask r (penny p)
lemma gleam (p:Momentum)(r:ℕ): shineF p r * shineF (-p) r=1:=by
   unfold shineF; rw [mask_mul,show (fun i=> penny p i * penny (-p) i)=_ from funext fun i=>aspect_cancel sigma p i, mask_one]
-- Covariance notation in positive phase.
private def Gears (p q:Momentum)(A B:Frequency i j): Prop:= shineF p i * B=A*shineF q j
namespace Gears
variable {p q t : Momentum}{A B X Y:Frequency i j}
private lemma nil (p:Momentum)(r:ℕ) : Gears p p (1:Frequency r r) 1:= by simp [Gears]
private lemma zero (p q:Momentum)(r s:ℕ):Gears p q (0:Frequency r s) 0:=by simp [Gears]
private lemma mat (h:Gears p q A B)(hv:Gears p q X Y) : Gears p q (A+X) (B+Y):=by unfold Gears at *; rw [Matrix.mul_add,h,hv,Matrix.add_mul]
private lemma less (h:Gears p q A B)(hv:Gears p q X Y) : Gears p q (A-X) (B-Y):=by unfold Gears at *; rw [Matrix.mul_sub,h,hv,Matrix.sub_mul]
private lemma scale (h:Gears p q A B)(c:ℂ): Gears p q (c • A) (c • B):= by unfold Gears at *; rw [Matrix.mul_smul,h,Matrix.smul_mul]
private lemma prod {U V : Frequency j k} (h:Gears p q A B)(hv:Gears q t U V): Gears p t (A*U) (B*V):= by unfold Gears at *; rw [← Matrix.mul_assoc,h,Matrix.mul_assoc,hv, Matrix.mul_assoc]
private lemma diag (p:Momentum)(r:ℕ)(t:Axis→ℂ): Gears p p (mask r t) (mask r t):=by unfold Gears shineF; rw [mask_mul,mask_mul,show (fun i=> penny p i*t i)=fun i=> t i*penny p i from funext fun i=>mul_comm ..]
private lemma source (L:Side)(p: Momentum)(r:ℕ): Gears p p (signal L r p) (signal L r (-p)):=by
   unfold Gears shineF signal; rw [mask_insert]; congr! 2 with i; unfold tripQ; funext i; rw [mul_left_comm,show penny p i*chip ((-p) i)=_ from chip_sp p i]
private lemma retainH {p q:Momentum}(h:Gears p q A B): Gears q p Bᵀ Aᵀ:= by
   -- shader trans symmetric means orientation of B/A flips
   unfold Gears at *; apply Matrix.transpose_injective; simpa only [Matrix.transpose_mul,shineF, mask_trans,Matrix.transpose_transpose] using h.symm
private lemma breaths (L:Side)(p: Momentum)(r:ℕ): Gears p p (mirage L r p) (mirage L r (-p)) := by
   have h:=source L p r; unfold mirage; simp_rw [neg_neg]; exact retainH h
private lemma field (P : Train j)(u:ℝ)(hu:0<u)(L:Side)(p:Momentum)(hp:p∈realCube zone): Gears p p (pulse u P p) (pulse u P (-p))∧ Gears p p (fieldD L u P p) (fieldD L u P (-p)):=by
   rw [(heart_even u hu P hp).1,fieldD,fieldD,fieldD_even]; exact ⟨(diag ..).scale _,diag ..⟩

-- shift rail sign, even plank.
private lemma rail_opp (P:Flight j i)(p: Momentum)(l:Site P.L)(a:Axis):
     let q:= aliasAt p l; penny q a*rail P.L (q a)=rail P.L (-q a)*penny p a:= by
   intro q; let z:= q a; let M:ℤ:=mid P.L
   have hm:= mid_double P.L P.odd
   have ht:twirl (p a) 1=twirl z P.L.val:=by
      have hs:= congr_fun (alias_scale p l) a
      have hw : ((P.L.val:ℂ)*z)= p a+ 2*(Real.pi:ℂ)*(lift l a):= by simpa only [z,q,nsmul_eq_mul, Pi.mul_apply,Pi.natCast_apply,Pi.add_apply,reciprocal] using hs
      rw [← twirl_period (p a) (lift l a) 1,← hw]; simpa using! (twirl_scale z P.L.val 1)
   change -(twirl z 1)*_= _ * -(twirl (p a) 1);
   rw [ht, neg_mul,mul_neg]; congr 1
   change twirl z 1 * rail P.L z=rail P.L (-z)*_
   apply mul_left_cancel₀ (show twirl z (-(M+1))≠0 from Complex.exp_ne_zero _)
   rw [← mul_assoc, mul_comm (rail P.L (-z)),← mul_assoc,← twirl_add,← twirl_add,show (-(M+1)+(1:ℤ))=-M by omega, show -(M+1)+(P.L.val:ℤ)=M by unfold M; omega]; have h:= plank_even P.L P.odd z; unfold plank at h; rw [twirl_neg,neg_neg] at h; exact h.symm
private lemma flux_d (P:Flight j i)(p:Momentum)(l:Site P.L)(r:ℕ): let q:=aliasAt p l; Gears q p (flux P r q) (flux P r (-q)):= by
   intro q; unfold flux hinges Gears; simp_rw [transpose_smul,mask_trans,neg_neg,P.massFilter_even,Matrix.mul_smul,Matrix.smul_mul]; unfold shineF; rw [mask_mul,mask_mul]; exact congr_arg (fun f=> massFilter P.patch q • mask r f) (funext fun i=> rail_opp P p l i)
private lemma wire_d (P : Flight j i)(k:ℝ)(h:0<k)(p:Momentum)(hp:p∈realCube zone)(l:Site P.L) : Gears (aliasAt p l) p (wire k P p l) (wire k P (-p) (-l)) := by
   let q:=aliasAt p l
   by_cases ht:p=0
   · subst p; by_cases hl:l=0
     · subst l; simp_rw [toe_zero,neg_zero, wire_origin]; exact nil _ _
     simp_rw [wire_none P k hl,neg_zero, wire_none P k (neg_ne_zero.mpr hl)]; exact zero ..
   rw [wire_match k h P hp ht,wire_match k h P (realCube_neg hp) (neg_ne_zero.mpr ht),alias_reverse p P.odd];
   have hu:=field P.wing k h P.L q (alias_in_real zone_pos hp l P.odd); have hv:=field P.land k h 1 p hp; have hz:=breaths 1 p 1
   have he:chainY k P (-p) (-q)=chainY k P p q:= by unfold chainY; rw [fieldR_even,fieldR_even,yen_symm]
   change Gears q p (scriptT k P p q) (scriptT k P (-p) (-q)); unfold scriptT; rw [he]
   exact mat ((((hu.1.prod (source P.L q 1)).prod hu.2).prod (flux_d P p l 1)).prod hz) (scale ((flux_d P p l 2).prod (less (nil p _) (((hv.1.prod (source 1 p 1)).prod hv.2).prod hz))) _)
end Gears

lemma prospect (P:Flight j i)(k:ℝ)(p:Momentum)(h:0<k)(hp:p∈baseCube)(l:Site P.L) :
    shineF (aliasAt p l) 1*pilot k P (-p) (-l) = pilot k P p l *shineF p 1 ∧
    shineF (aliasAt p l) 2 * wire k P (-p) (-l)=wire k P p l*shineF p 2:= by
    refine ⟨?_, Gears.wire_d P k h p (base_subset_realCube zone_pos hp) l⟩
    ext a b; rw [Matrix.mul_apply,mul_apply]; simp_rw [shineF,mask_value]; obtain ⟨x,rfl⟩:=axisEquiv.surjective a; obtain ⟨y,rfl⟩:=axisEquiv.surjective b
    have hx:=Carrier.perspective sigma p P k h l hp x y; simp only [sig_act] at hx
    simp only [ite_mul,mul_ite,zero_mul,mul_zero,Equiv.symm_apply_apply]; rw [Finset.sum_ite_eq,Finset.sum_ite_eq']; simp only [Finset.mem_univ,↓reduceIte, Equiv.symm_apply_apply]; exact hx
end YM.RG08.Invert

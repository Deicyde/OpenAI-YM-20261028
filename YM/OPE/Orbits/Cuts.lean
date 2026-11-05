import YM.OPE.Orbits.Real

/-!
Compatible finite projections adapted to covariant *averaged* readers.
We annihilate previously chosen strata, also using those fixed actual
physical test maps for all lower projections of subsequent fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Filter Set MeasureTheory Extraction Table Prescription
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{L:Register G}{S:Table L}{Q:DiffPlan S}{P:Prescription Q}{X:Rotation S}{ρ:S.RealSpin}
    {I:Type}[Fintype I] {d:I→ℕ}

/-- Tomography supplies tied to common differential filtration, rotations and
basis. Constructed below from services; never assumed of all models. -/
structure Reader (Q:DiffPlan S) (X:Rotation S) (ρ:S.RealSpin) where
    port : Prescription Q
    spans : port.Coherent
    continuum : S.Hierarchy
    lifts : Q.Inclusions S
    stands : Q.Orientation ρ
    law : X.Laws Q ρ

namespace Reader
variable (R:Reader Q X ρ)
def liftOne (m q:ℕ): S.Field q→ₗ[ℂ] S.Field m :=
    let f:= (checkReal R.port R.law R.continuum m (sole 0) 0 (d:=fun _:Unit=>q))
    f.toLinearMap 0 () -- 0 overwritten at ()
lemma liftOne_check (m q) (v:S.Field q): R.liftOne m q v = checkReal R.port R.law R.continuum _ (sole 0) 0 (d:=fun _:Unit=>q) (sole v) :=by
   rw [liftOne, MultilinearMap.toLinearMap_apply]; change (checkReal _ _ _ _ _ _ (d:=fun _:Unit=>q) _) = _
   exact congr_arg _ (funext fun (i:Unit) => by cases i; exact update_self ..)

private lemma shadow_neck (u q m : ℕ)(h:q ≤ m)(z:S.Field q):
    OPE.shadow R.port u (sole 0) (sole (quoteTag (⟨m,Q.rise h z⟩:S.Tag))) 0 = OPE.shadow R.port u (sole 0) (sole (quoteTag (⟨q,z⟩:S.Tag))) 0:=by
    apply Finset.sum_congr rfl; intro i hi; unfold quoteTag; rw [R.port.insertOne m _ R.continuum,R.port.insertOne q _ R.continuum]; simp only [S.rep]; rw [R.port.affinity R.continuum.laws.toSymmetric R.lifts i z h]
private lemma liftOne_affinity (u q m : ℕ)(h:q ≤ m)(z:S.Field q): R.liftOne u m (Q.rise h z) = R.liftOne u q z :=by
    rw [liftOne_check,liftOne_check,checkValue,checkValue] -- if not rw
    have ha(z:S.Field q) (j:ℕ) (y:q ≤ j): averageV R.port X u (sole 0) 0 (d:=fun _:Unit=>j) (sole (Q.rise y z))= averageV R.port X u (sole 0) 0 (d:=fun _:Unit=>q) (sole z) := by
       classical
       unfold averageV; split; swap; rfl
       apply integral_congr_ae; refine Eventually.of_forall fun k=>?_ ; unfold spinning
       have hx:Ortho.move k⁻¹ 0=0:=map_zero (Ortho.motion k⁻¹); have hg:Ortho.move k⁻¹ ∘ sole (0:E4)=sole (0:E4):=funext fun i=>hx
       change X.act u k (OPE.shadow R.port u _ (sole (quoteTag (S:=S) ⟨(j:ℕ),X.act j k⁻¹ (Q.rise y z)⟩)) _) = X.act u k (OPE.shadow R.port u _ (sole (quoteTag (S:=S) ⟨q,X.act q k⁻¹ z⟩)) _)
       rw [hg,hx,R.law.filtered,shadow_neck]
    have hh (v:ℕ)(w:S.Field v): bar ρ (d:=fun _:Unit=> v) (sole w)=sole (S.conj ρ v w):=rfl
    rw [hh,hh,R.stands.realInc, ha z m h,ha (S.conj ρ q z) m h]

def knife (m : ℕ) : S.Field m →ₗ[ℂ] S.Field m:= Nat.strongRecOn (motive:=fun m=> S.Field m →ₗ[ℂ] S.Field m) m (fun n I=> LinearMap.id - ∑ i:Fin n, Q.rise (d:=i.val) i.isLt.le ∘ₗ I i.val i.isLt ∘ₗ R.liftOne i.val n)

def cutTest (m q):= R.knife m ∘ₗ R.liftOne m q

lemma knife_apply (m q:ℕ){h:q ≤ m} (z:S.Field q):
    R.knife m (Q.rise h z) = Q.rise h z - ∑ i:Fin m, Q.rise i.isLt.le (R.cutTest i.val q z):=by
    have hi(k:ℕ):R.liftOne k m (Q.rise h z)=R.liftOne k q z :=by
       exact R.liftOne_affinity .. -- coherence of R.port.ope under inclusions+rot averages (for testing one only, old P.test affinity)
    have hw:R.knife m = LinearMap.id - ∑ i:Fin m, (Q.rise i.isLt.le) ∘ₗ R.cutTest i.val m:=by
          apply Nat.strongRecOn_eq
    rw [hw]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply, LinearMap.comp_apply]; apply congr_arg (_-·); refine Finset.sum_congr rfl ?_; intro i hv; rw [cutTest,LinearMap.comp_apply,hi]; rfl
lemma test_formula (m q:ℕ)(h:q ≤ m) (z:S.Field q):
    R.cutTest m q z = Q.rise h z - ∑ i:Fin m, Q.rise i.isLt.le (R.cutTest i.val q z) :=by
   have hs:=checkReal_fixed m R.law R.continuum q z R.spans R.lifts R.stands h
   change R.knife m (R.liftOne m q z) = _
   rw [liftOne_check,hs]; exact R.knife_apply ..
lemma reconstruct (m q:ℕ)(h:q ≤ m) (z:S.Field q): ∑ i:Fin (m+1), Q.rise (d:=i.val) (Nat.le_of_lt_succ i.isLt) (R.cutTest i.val q z)=Q.rise h z :=by
    rw [Fin.sum_univ_castSucc]; change ∑ i:Fin m,Q.rise (d:=i.val) i.isLt.le (R.cutTest i.val q z) + Q.rise (Nat.le_refl m) (R.cutTest m q z) = _
    rw [Q.arrival R.continuum.laws.toSymmetric R.lifts (R.cutTest m q z),test_formula R m q h]; abel

lemma kills_lower (m q:ℕ)(h:q < m) (z:S.Field q): R.cutTest m q z=0:=by
    cases m with
    | zero=> exact (Nat.not_lt_zero _ h).elim
    | succ m=>
       rw [R.test_formula (m+1) q h.le]
       have he: (∑ i:Fin (m+1),Q.rise i.isLt.le (R.cutTest i.val q z))= Q.rise h.le z := by
          rw [← Q.transit R.continuum.laws.toSymmetric R.lifts (Nat.le_sub_one_of_lt h) m.le_succ]
          have hw:= congr_arg (Q.rise m.le_succ) (R.reconstruct m q (by omega) z)
          rw [map_sum] at hw; apply Eq.trans ?_ hw; refine Finset.sum_congr rfl fun i _=> (Q.transit R.continuum.laws.toSymmetric R.lifts ..).symm
       rw [he,sub_self]
lemma cut_rise (m v q:ℕ)(h:v≤q)(z:S.Field v): R.cutTest m q (Q.rise h z)=R.cutTest m v z:=by
      change R.knife m (R.liftOne m q _) = R.knife m _; rw [R.liftOne_affinity]

def stratum (m:ℕ) : Submodule ℂ (S.Field m):= ⨅ i:Fin m, (R.cutTest i.val m).ker
lemma piece_mem {m:ℕ}{z:S.Field m} : z∈ R.stratum m ↔ ∀ i:Fin m,R.cutTest i.val m z=0:=by simp [stratum,LinearMap.mem_ker]

lemma knife_mem (m:ℕ) (x:S.Field m) : R.knife m x∈R.stratum m:= by
   induction m using Nat.strong_induction_on with
   | h m ih =>
      refine (piece_mem R).mpr fun i=> ?_
      rw [show x=Q.rise (d:=m) le_rfl x from (Q.arrival R.continuum.laws.toSymmetric R.lifts _).symm] -- occurrences?
      rw [R.knife_apply, map_sub,map_sum]; simp_rw [R.cut_rise]; apply sub_eq_zero.mpr (?_); symm; rw [Finset.sum_eq_single i]; rotate_left
      · intro j _ h
        rcases lt_or_gt_of_ne (show i.val ≠ j.val from (fun he=> h ((Fin.ext he).symm))) with he|he
        · exact (piece_mem R).1 (ih j.val j.isLt (R.liftOne j.val m x)) ⟨i.val,he⟩
        exact R.kills_lower i.val j.val he _
      · exact fun hi=> False.elim (hi (Finset.mem_univ ..))
      have hx:= ih i.val i.isLt (R.liftOne i.val m x)
      let p:=R.cutTest i.val m x
      change R.cutTest i.val i.val p = R.cutTest i.val m x
      rw [test_formula R _ _ le_rfl p, Q.arrival R.continuum.laws.toSymmetric R.lifts p, Finset.sum_eq_zero fun j _=>?_ , sub_zero]
      erw [(piece_mem R).1 hx j,map_zero]
end Reader
end YM.OPE.Orbits

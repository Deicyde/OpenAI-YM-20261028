import YM.OPE.Orbits.Cuts

/-! Each fixed weight in the prescription is biorthogonal to the fixed
physical readouts. No selection parameter and no dependence on an eventual
exterior list. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits.Reader
open Function Filter Set MeasureTheory Extraction Table Prescription
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{L:Register G}{S:Table L}{Q:DiffPlan S}{ρ:S.RealSpin}{X:Table.Rotation S}
    {I:Type}[Fintype I]{d:I→ℕ}
variable (R:Reader Q X ρ)

def fresh (m:ℕ)(x:I→E4)(o:E4):MultilinearMap ℂ (fun i=> S.Field (d i)) (S.Field m) := (R.knife m).compMultilinearMap (checkReal R.port R.law R.continuum m x o)
lemma fresh_eq (m:ℕ)(x:I→E4)(o:E4)(v:Labels S d): R.fresh m x o v=R.knife m (checkReal R.port R.law R.continuum m x o v):=rfl
variable (m j h:ℕ) (c:S.Field j) (x:I→E4)(o:E4) (v:Labels S d)
lemma fresh_mem : R.fresh m x o v∈R.stratum m := R.knife_mem m (checkReal R.port R.law R.continuum m x o v)
lemma test_fixes (h:c∈R.stratum j): R.cutTest j j c=c:=by
    rw [test_formula R j j le_rfl c]
    rw [Q.arrival R.continuum.laws.toSymmetric R.lifts c, Finset.sum_eq_zero fun i _=> by rw [(piece_mem R).1 h i, map_zero], sub_zero]
lemma test_orthogonal (h:c∈R.stratum j) (hp:m≠j): R.cutTest m j c=0:=by
   rcases hp.lt_or_gt with hp|hp
   · exact (R.piece_mem.1 h) ⟨m,hp⟩
   exact R.kills_lower _ _ hp _
lemma single : R.fresh m (sole 0) 0 (d:= fun _:Unit=>j) (sole c)=R.cutTest m j c:= by apply congr_arg (R.knife m) ((R.liftOne_check m j _).symm)
lemma fresh_smooth (hv:orbitMargin R.port m x o):ContDiffAt ℝ ∞ (fun z:(I→E4) × E4=>R.fresh m z.1 z.2 v) (x,o) :=((LinearMap.toContinuousLinearMap (R.knife m)).restrictScalars ℝ).contDiff.contDiffAt.comp _ (smoothReal m R.law R.continuum _ _ _ hv)

lemma rotate_knife (k:Ortho)(c:S.Field m): R.knife m (X.act _ k c) = X.act _ k (R.knife m c):=by
   induction m using Nat.strong_induction_on with
   | h m ih=>
     let h(i:ℕ):i ≤ i := le_rfl
     have hc(g):R.knife m g=g - ∑ i:Fin m, Q.rise i.isLt.le (R.cutTest i.val m g):=by
         simpa only [Q.arrival R.continuum.laws.toSymmetric R.lifts] using (knife_apply R m m g (h:=le_rfl))
     rw [hc,hc,map_sub,map_sum]; apply congr_arg (_-·) (Finset.sum_congr rfl ?_)
     intro i hi; rw [R.law.filtered]; apply congr_arg (Q.rise _)
     simp only [cutTest,LinearMap.comp_apply,liftOne_check, (ih _ i.isLt _).symm]; rw [show (sole (X.act m k c))=((roll X k (d:=fun _:Unit=>m)) (sole c)) from rfl,← checkReal_rotate _ R.law R.continuum]; rw [show Ortho.move k 0=0 from map_zero (Ortho.motion k), (show Ortho.move k ∘ sole (0:E4)=sole (0:E4) from funext fun _=> map_zero (Ortho.motion k))]

lemma real_knife (c:S.Field m): R.knife m (S.conj ρ m c)=S.conj ρ m (R.knife m c):=by
    induction m using Nat.strong_induction_on with
    | h m ih =>
       have hc(g):R.knife m g=g - ∑ i:Fin m, Q.rise i.isLt.le (R.cutTest i.val m g):=by
          simpa only [Q.arrival R.continuum.laws.toSymmetric R.lifts] using (knife_apply R m m g (h:=le_rfl))
       rw [hc,hc,map_sub,map_sum]; apply congr_arg (_-·) (Finset.sum_congr rfl ?_); intro i hi; rw [R.stands.realInc]; apply congr_arg (Q.rise _)
       simp only [cutTest,LinearMap.comp_apply,liftOne_check]; rw [show (sole (S.conj ρ m c))= bar ρ (d:=fun _:Unit=>m) (sole c) from rfl,checkReal_real,ih i.val i.isLt]

lemma rotate_fresh (k:Ortho): R.fresh m (Ortho.move k ∘ x) (Ortho.move k o) (roll X k v)= X.act _ k (R.fresh m x o v):=by rw [fresh_eq,checkReal_rotate,rotate_knife,fresh_eq]
lemma real_fresh : R.fresh m x o (bar ρ v)= S.conj ρ m (R.fresh m x o v):=by rw [fresh_eq,checkReal_real,real_knife,fresh_eq]
lemma rotate_test (k:Ortho): R.cutTest m j (X.act j k c) = X.act m k (R.cutTest m j c):=by
    have hx:=rotate_fresh (d:=fun _:Unit=>j) R m (sole 0) 0 (sole c) k
    rw [show Ortho.move k 0=0 from map_zero (Ortho.motion k), (show Ortho.move k ∘ sole (0:E4)=sole (0:E4) from funext fun _=> map_zero (Ortho.motion k))] at hx; exact (single R m j _).symm.trans (hx.trans (congr_arg _ (single R m j _)))
lemma real_test: R.cutTest m j (S.conj ρ j c) = S.conj ρ m (R.cutTest m j c):=by
    have hx:=real_fresh (d:=fun _:Unit=>j) R m (sole 0) 0 (sole c); exact (single R m j _).symm.trans (hx.trans (congr_arg _ (single R m j _)))
lemma turn_mem (k:Ortho)(hp:c∈ R.stratum j) : X.act j k c∈R.stratum j:=(piece_mem R).2 (fun i=> by rw [rotate_test, (piece_mem R).1 hp i,map_zero])
lemma bar_mem (hp:c∈R.stratum j): S.conj ρ j c∈R.stratum j:=(piece_mem R).2 (fun i=> by rw [real_test, (piece_mem R).1 hp i,map_zero])
lemma fresh_transport (s:E4): R.fresh m (fun i=> x i+s) (o+s) v=R.fresh m x o v:=by simp only [fresh_eq,checkReal_transfer]
lemma fresh_perm {J:Type}[Fintype J](e:J≃I): R.fresh m (x ∘ e) o (d:= fun j=>d (e j)) (fun j=> v (e j))= R.fresh m x o v:=congr_arg _ (checkReal_perm m R.law R.continuum x o v e)
end YM.OPE.Orbits.Reader

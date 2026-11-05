import YM.MergeProof.East.Canes
import YM.MergeProof.East.Crust
import YM.MergeProof.East.Ducat
import YM.MergeProof.East.Oast

/-!
# Oriented selection of k-probes with same prices
-/
set_option autoImplicit false
set_option maxHeartbeats 580000
noncomputable section
namespace YM.Next.Rank.East
open Function Filter RG Labels Source Thirst Baler Lattice Wilson MeasureTheory Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Cells Spindle Atlas Edition Normal LiftMark Rise MvPolynomial Configuration Ribbon Price
open Extra.Histories Motion PhysicalNext PhysicalNext.RankCovariance
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{b D k i N p d q:ℕ} {C:Family G} {t a g δ e:ℝ}
lemma lengthens {V Z:Type*}(f:V→Z)(h:Injective f)(P:poly V):totalDegree P ≤ totalDegree (rename f P):=by
  let M := fun i : Z => if h:∃ j,f j=i then Finsupp.single (Classical.choose h) (1:ℂ) else 0
  have hv i:M (f i)=Finsupp.single i (1:ℂ):=by
    unfold M; split
    · rename_i hp; rw [h (Classical.choose_spec hp)]
    rename_i hp; exact False.elim (hp ⟨i,rfl⟩)
  have hs : (exchange M).comp (rename f)=(AlgHom.id ..) := by ext1 i; rw [AlgHom.comp_apply, rename_X, exchange_x, hv, glyph, Finsupp.linearCombination_single,one_smul]; rfl
  exact le_trans (show totalDegree P=totalDegree (exchange M (rename f P)) from congr_arg totalDegree (DFunLike.congr_fun hs P).symm).le (Rise.ascent ..)

private lemma thins {V Z:Type*}(f:V→Z)(P:poly V):coin (rename f P)≤coin P:=by
    rw [Normal.labelled]; apply (Rise.rise _ 0 zero_le_one (r:=1) (c:=1) le_rfl (fun _=>by simp) P le_rfl).trans; rw [one_pow,mul_one]
local notation "F"=> C.labels.level d
local notation "σ"=> orbitCost (F)
local notation "A"=> C.path.levels
local notation "X"=> stamp A N p
local notation "τ"=>control (k:=k) (X) 0 (wood A k)
variable {B:Binding C}
-- slack after pin
lemma labelledT (hp:0<a)(hk:a*σ*σ ≤ 1) (W:C.label d→ₗ[ℂ] poly (slotC G (sizeQ C k))) (V:Heater C k d)
    (r:4*sizeQ C k≤wood A k)(T:Module.End ℂ (C.label d))(c: LCheque k N p d D V T a) (he:∀ x,V x=milk τ (rename (calls r) (W x)))
    (H:ParadeX C)(h:C.ref d≤k)(hN:k≤N)(B:Binding C)(s: Signed):
    let P:= (exchange (pivot s)).toLinearMap ∘ₗ W ∘ₗ mir F s⁻¹
    let U:= Wick X ((rename (calls r)).toLinearMap.comp P)
    Heating C k N p d D U (emblaze F s T):=by
   intro P U
   let f:=C.labels.level d;let K:=emblaze f s T;let j(x):=mir f s⁻¹ x
   have hx(x):U x= milk (control (k:=k) (RankCovariance.stamp C.path.levels N p) 0 (wood C.path.levels k)) (rename (calls r) (exchange (pivot s) (W (j x)))):=rfl
   have h'(x):Spindle.paid C d k N p (j x) ≤ σ*paid C d k N p x:=by unfold paid j mir; rw [(H d k h N p hN s⁻¹ _).1]; exact pirouette ..
   have h'(x):paid C d k N p (j x) ≤ σ*Spindle.paid C d k N p x:=h' x
   obtain ⟨hσ,hc⟩: 0<σ ∧ 1≤σ:= ⟨zero_lt_one.trans_le (orbitCost_one_le _),orbitCost_one_le _⟩
   have hv: a*σ≤1:= (le_mul_of_one_le_right (mul_nonneg hp.le hσ.le) hc).trans hk
   refine ⟨⟨?_,fun x=>?_,?_⟩,fun x=>?_,fun x=>?_,fun x=>?_⟩
   · change mir f s (T (mir f _ (C.refUnit d))) = _
     rw [show mir f s⁻¹ (C.refUnit d)=C.refUnit d from by unfold Family.refUnit unitVec; rw [map_smul]; exact congr_arg (_ • ·) (beginning _ _), c.heats.span.unit]; exact beginning ..
   · change f.act s.ortho (T (f.act ((s⁻¹).ortho) (star x)))=star (f.act s.ortho (T (f.act ((s⁻¹).ortho) x))); rw [Motion.act_conj, c.heats.span.preserves,Motion.act_conj]
   · intro x y z; let v:= awake C d k N p (j x)
     have hj : mir f s v=z:= by unfold v j mir; rw [(H d k h N p hN s⁻¹ x).1];exact undone ..
     change f.coeffSize (z-mir f s (T (j x))) ≤ _
     have hR : σ*(a*paid C d k N p (j x)/2) ≤ f.coeffSize z/2:=by
        apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (h' x) hp.le) (by norm_num)) hσ.le).trans ?_
        let A':=Spindle.paid C d k N p x; change σ*(a*(_*A')/2) ≤ A'/2; linarith only [mul_le_mul_of_nonneg_right hk (paid_pos C d k N p x)]
     rw [show z-mir f s (T (j x))=mir f s (v-T (j x)) by rw [map_sub,hj]]
     exact (pirouette f s _).trans ((mul_le_mul_of_nonneg_left (c.credit (j x)) hσ.le).trans hR)
   · rw [hx,pearl,Normal.prepared,treats_wind B hN r]; let p':= milk (collar r τ) (W (j x))
     change coin (rename (calls r) (exchange (pivot s) p')) ≤ _; apply le_trans ((thins ..).trans ((cheaper s p').trans (coin_rename p' (calls r) (call_inj r))))
     have hE:= he (j x); rw [pearl] at hE
     rw [show rename (calls r) p'=V (j x) from hE.symm]; apply (c.bill_ _).trans
     let g:= paid C d k N p;let t:= C.path.levels.clock.monitor k; have ht:0<t:=Real.exp_pos _
     change a*t*g (j x) ≤ t*g x
     refine (mul_le_mul_of_nonneg_left (h' x) (mul_pos hp ht).le).trans ?_
     linarith only [mul_le_mul_of_nonneg_right hv (mul_nonneg ht.le (paid_pos C d k N p x))]
   · rw [hx,pearl,Normal.prepared,treats_wind B hN r]; let p':= milk (collar r τ) (W (j x))
     change totalDegree (rename (calls r) (exchange (pivot s) p')) ≤ _; apply le_trans ((totalDegree_rename_le ..).trans ((Rise.ascent ..).trans (lengthens (calls r) (call_inj r) p')))
     have hh:=he (j x); rw [pearl] at hh
     rw [show rename (calls r) p'=V (j x) from hh.symm]; exact c.heats.order _
   · have hV:= c.heats.test (j x); rw [he] at hV
     change Verdict _ _ (U x) (f.coords.symm (f.scaled (Price.shrink C k N p) (f.act s.ortho (T (j x)))))
     rw [hx,f.scaling,Frame.act]; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,f.coords.symm_apply_apply]; exact stamp_at B hN r s _ _ hV
end YM.Next.Rank.East

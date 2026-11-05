import YM.WilsonBulk.Series.Clockwork
import YM.WilsonBulk.Heat.Package

/-!
# Tape transport assembly, exact formal chain rules

Any real derivation requiring no more than one order acts. (Condition automatic;
not pretending continuity in weighted series.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open scoped Classical BigOperators
open Finset PowerSeries
variable {A B M : Type} [CommRing A] [CommRing B] [CommRing M]
  [Algebra ℝ A] [Algebra ℝ B] [Algebra ℝ M] {n : ℕ} {p q : PowerSeries A}
lemma Steps.along (D : Derivation ℝ (PowerSeries A) (PowerSeries A)) (h : Steps (n+1) p q) : Steps n (D p) (D q) := by
  rw [Steps.dvd, ← map_sub]; obtain ⟨u,hu⟩:= Steps.dvd.mp h
  rw [hu,D_leib,D.leibniz_pow]; simp only [nsmul_eq_mul, smul_eq_mul,Nat.add_one_sub_one]; refine ⟨((n+1:ℕ):PowerSeries A)*(D X)*u+ X*D u, by rw [pow_succ]; ring⟩
lemma clock_C (a : A) : clockD A (C a)=0 := by ext1 i; simp [clock_coeff]
lemma clock_X : clockD A X=1 := PowerSeries.derivative_X
lemma clock_parallel (L : A→ₗ[ℝ]B) (p : PowerSeries A) : clockD B (parallel L p)=parallel L (clockD A p) := by ext1 n; simp only [clock_coeff,coeff_parallel,map_smul]
lemma clock_adjunct (D : Derivation ℝ A A) (p : PowerSeries A) : parallelD D (clockD A p)=clockD A (parallelD D p) := (clock_parallel D.toLinearMap p).symm
-- polynomial coordinate chain, any target ring
open Sheet
open MvPolynomial (pderiv)
variable {α β : Type} {g : PowerSeries A} (D : Derivation ℝ (PowerSeries A) (PowerSeries A))
lemma poly_chain [Fintype α] (F : Formula α →ₐ[ℝ]A) (P : Formula α) (D : Derivation ℝ A A) : D (F P)= ∑ i,F (pderiv i P)*D (F (MvPolynomial.X i)) := by
  induction P using MvPolynomial.induction_on with
  | C a=> rw [MvPolynomial.C_eq_algebraMap,F.commutes]; simp
  | add p q h h'=> simp only [map_add,add_mul,sum_add_distrib,h,h']
  | mul_X p j h=>
    simp only [map_mul,D_leib,map_add,h,add_mul,sum_add_distrib,sum_mul]
    congr 1
    · exact sum_congr rfl fun _ _=> by ring
    simp [Pi.single_apply,apply_ite]
lemma poly_agree {F1 F2 : Formula α →ₐ[ℝ] PowerSeries A} (h : ∀ i, Steps n (F1 (MvPolynomial.X i)) (F2 (MvPolynomial.X i))) : ∀ P, Steps n (F1 P) (F2 P) := by
  intro P; induction P using MvPolynomial.induction_on with
  | C a=> rw [MvPolynomial.C_eq_algebraMap,F1.commutes,F2.commutes]; exact Steps.self
  | add p q hp hq=> simp only [map_add]; exact hp.add hq
  | mul_X p j ih=> simp only [map_mul]; exact ih.mul (h j)

lemma parallelD_C (p : A) (D : Derivation ℝ A A) : parallelD D (C p)=C (D p) := parallel_C _ _
lemma parallelD_X (D : Derivation ℝ A A) : parallelD D X=0 := by ext1 i; rw [parallel_D,coeff_X,map_zero]; split <;> simp

-- differential as local map
abbrev named (i : α) : Tape α := C (MvPolynomial.X i)
abbrev player (i : α) : Derivation ℝ (Tape α) (Tape α) := parallelD (pderiv i)
@[simp] lemma player_name (i j : α) : player i (named j)= if j=i then 1 else 0 := by simp only [named,player,parallelD_C,MvPolynomial.pderiv_X,Pi.single_apply]; split <;> simp
lemma player_live (i j : α) (p : Tape α) : player i (player j p)=player j (player i p) := by ext1 k; exact Eq.trans (by simp only [player,parallel_D]; rw [deriv_commutes i j]) (by simp [player,parallel_D] : pderiv j (pderiv i (coeff k p))=_)

abbrev code (V : α→PowerSeries A) (h : constantCoeff g=0) : Tape α →ₐ[ℝ]PowerSeries A := tuner (MvPolynomial.aeval V) h
abbrev submit (V : α→PowerSeries A) : Tape α →ₐ[ℝ]PowerSeries A := code V (g:=X) constantCoeff_X
lemma code_X (V : α→PowerSeries A) (h : constantCoeff g=0) : code V h X=g := tuner_X _ _
lemma code_C (V : α→PowerSeries A) (h : constantCoeff g=0) (p : Formula α) : code V h (C p)=MvPolynomial.aeval V p := tuner_C _ _ _
lemma code_named (V : α→PowerSeries A) (h : constantCoeff g=0) (i : α) : code V h (named i)= V i := by rw [named,code_C,MvPolynomial.aeval_X]
def post (A : Type) [CommRing A] [Algebra ℝ A] : A→ₐ[ℝ] PowerSeries A where
  toRingHom:= C
  commutes' _:= PowerSeries.algebraMap_apply.symm
lemma post_p (a : A) : post A a=C a := rfl

theorem code_ext (U V : Tape α →ₐ[ℝ] PowerSeries A) (h : constantCoeff (U X)=0) (hx : U X=V X) (hd : ∀ i,U (named i)=V (named i)) : U=V := by
  have he : U.comp (post _)=V.comp (post _):= by ext1 i; exact hd i
  have hc (p : Formula α) : U (C p)=V (C p) := DFunLike.congr_fun he p
  calc
    _ = tuner (V.comp (post _)) h := tuning _ U h hc
    _ = tuner (V.comp (post _)) (show constantCoeff (V X)=0 from hx ▸ h) := by congr!
    _ = V := (tuning _ V (hx ▸ h) fun _=> rfl).symm
theorem submit_by (F : Formula α →ₐ[ℝ] A) (p : Tape α) : submit (fun i=> C (F (MvPolynomial.X i))) p = parallel F.toLinearMap p := by
  have h : submit (fun i=> C (F (MvPolynomial.X i))) = PowerSeries.mapAlgHom F := by
    refine code_ext _ _ (by rw [code_X,constantCoeff_X]) (by rw [code_X,PowerSeries.mapAlgHom_apply,map_X]) (fun i=> by rw [code_named, PowerSeries.mapAlgHom_apply,named,map_C]; rfl)
  rw [h, parallel_by]; rfl
lemma submit_X (V : α→PowerSeries A) : submit V X=X := code_X ..
lemma submit_C (V : α→PowerSeries A) (p : Formula α) : submit V (C p)=MvPolynomial.aeval V p := code_C ..
lemma submit_named (V : α→PowerSeries A) (i : α) : submit V (named i)=V i := code_named ..
lemma submits (U : α→Tape β) (V : β→PowerSeries A) (p : Tape α) : submit V (submit U p)=submit (fun i=>submit V (U i)) p := by
  refine DFunLike.congr_fun (code_ext ((submit V).comp (submit U)) _ ?_ ?_ ?_) p
  · rw [AlgHom.comp_apply,submit_X,submit_X,constantCoeff_X]
  · rw [AlgHom.comp_apply,submit_X,submit_X,submit_X]
  intro i; rw [AlgHom.comp_apply,submit_named,submit_named]
theorem byNames (U : α→PowerSeries A) (V : Tape α →ₐ[ℝ] PowerSeries A) (h : V X=X) (hv : ∀ i,V (named i)=U i) : V=submit U := code_ext _ _ (by rw [h,constantCoeff_X]) (h.trans (submit_X _).symm) (fun i=>(hv i).trans (submit_named _ _).symm)
lemma submit_id (p : Tape α) : submit named p=p := by rw [← byNames named (AlgHom.id ..) rfl (fun _=>rfl)]; rfl
lemma code_agree {U V : α→PowerSeries A} {hp : Tape α} {q : Tape α} (hg : constantCoeff g=0) {x : PowerSeries A} (he : constantCoeff x=0) (h : ∀ i,Steps n (U i) (V i)) (hm : Steps n g x) (hr : Steps n hp q) : Steps n (code U hg hp) (code V he q) :=
  tuneAny_agree _ (poly_agree (fun i=> by rw [MvPolynomial.aeval_X,MvPolynomial.aeval_X]; exact h i)) hm hr

-- trajectory
variable [Fintype α]
def scanRate (U : Tape α →ₐ[ℝ] PowerSeries A) (p : Tape α) := U (clockD _ p)*D (U X) + ∑ i:α, U (player i p) * D (U (named i))
lemma scan_mul (U : Tape α→ₐ[ℝ] PowerSeries A) (p q : Tape α) : scanRate D U (p*q)= scanRate D U p * U q+ U p * scanRate D U q := by
  unfold scanRate; simp only [D_leib,map_add,map_mul,add_mul,mul_add,sum_add_distrib,sum_mul,mul_sum]; simp_rw [mul_left_comm (U p), mul_right_comm _ (U q)]; simp_rw [mul_assoc (U p),mul_left_comm (U p)]; abel
lemma scan_sum {ι : Type} (s : Finset ι) (p : ι→Tape α) (U : Tape α→ₐ[ℝ] PowerSeries A) : scanRate D U (∑ i∈s,p i)=∑ i∈s,scanRate D U (p i) := by
  simp only [scanRate,map_sum,sum_mul,sum_add_distrib]; exact congr_arg _ sum_comm
lemma scan_agree {p q : Tape α} (U : Tape α→ₐ[ℝ] PowerSeries A) (h : constantCoeff (U X)=0) (hp : Steps (n+1) p q) : Steps n (scanRate D U p) (scanRate D U q) := ((hp.clock.push U h).mul Steps.self).add (Steps.sum' _ (fun i _ => (Steps.push U h ((hp.along (player i)))).mul Steps.self))
lemma scan (U : Tape α→ₐ[ℝ] PowerSeries A) (hu : constantCoeff (U X)=0) (p : Tape α) : D (U p)=scanRate D U p := by
  have hx : D (U X) = scanRate D U X := by simp only [scanRate,clock_X,map_one,one_mul,player,parallelD_X,map_zero,zero_mul,sum_const_zero,add_zero]
  have hc (a : Formula α) : D (U (C a)) = scanRate D U (C a) := by
    simp only [scanRate,clock_C,map_zero,zero_mul,zero_add,player,parallelD_C]; exact poly_chain (U.comp (post _)) a D
  have ht (a : Formula α) (n : ℕ) : D (U (X^n * C a)) = scanRate D U (X^n*C a) := by
    induction n with
    | zero=> simp [hc]
    | succ k ih=> rw [pow_succ',mul_assoc,map_mul,D_leib,scan_mul,hx,ih]
  ext1 i
  let m j:= (X^j * C (coeff j p))
  have he : Steps (i+2) p (∑ j∈range (i+2),m j):= before_end (i+2) p
  calc _ = coeff i (D (U (∑ j∈range (i+2),m j))) := ((he.push U hu).along D) i (by omega)
       _ = coeff i (scanRate D U (∑ j∈range (i+2),m j)) := congr_arg _ (by simp only [m,map_sum,scan_sum,ht])
       _ = _ := (scan_agree D U hu he).symm i (by omega)
lemma chain (V : α→PowerSeries A) (p : Tape α) : D (submit V p)=submit V (clockD _ p)*D X+∑ i:α,submit V (player i p)*D (V i) := (scan D _ (by rw [submit_X,constantCoeff_X]) p).trans (by simp only [scanRate,submit_X,submit_named])
lemma player_chain (V : α→Tape β) (p : Tape α) (j : β) : player j (submit V p)= ∑ i:α,submit V (player i p)*player j (V i) := by rw [chain]; simp only [player, parallelD_X,mul_zero,zero_add]
lemma clock_chain (V : α→PowerSeries A) (p : Tape α) : clockD _ (submit V p)=submit V (clockD _ p)+∑ i:α,submit V (player i p)*clockD _ (V i) := by rw [chain,clock_X,mul_one]
end YM.WilsonBulk

import YM.WilsonBulk.Slice.Tunnel

/-!
# Kick out spectator jets on centered transform automatically

Leading Gaussian eigensystem identity from equality of invariant full action,
no Hessian asserted on high-order vertices themselves. Used after subtracting
stationary center with leading rank, then any analytic gauge change between
equal-power Wick forms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical BigOperators ContDiff
open Function Filter Matrix Finset PowerSeries
variable {α β κ ι A : Type} [CommRing A] [Algebra ℝ A] [Fintype α] [Fintype ι]
variable {G H V B J : Matrix α α ℝ} {W : Matrix α ι ℝ} {T : α→StageD α ι} {n : ℕ}

-- utilities quill across clocks
omit [Fintype α] [Fintype ι] in
lemma Steps_prime (x : α) {p q : StageD α ι} (hs : Steps n p q) : Steps n (inflow x p) (inflow x q) := parallel_agree hs _
section
omit [Algebra ℝ A]
lemma Steps_addneg {p q f g : PowerSeries A} (hp : Steps n p q) (hf : Steps n f g) : Steps n (p-f) (q-g) := by rw [sub_eq_add_neg,sub_eq_add_neg]; exact hp.add hf.neg
lemma Steps_cancel {p q f g : PowerSeries A} (hp : Steps n (p+f) (q+g)) (hf : Steps n f g) : Steps n p q := by simpa only [add_sub_cancel_right] using Steps_addneg hp hf
end
lemma quill_cons (x : α→PowerSeries A) (V : Matrix β α ℝ) (i : β) : constantCoeff (quill V x i)=quill V (fun i=>constantCoeff (x i)) i := by simp only [quill,map_sum,constantCoeff_smul]
lemma quill_cons₂ (V : Matrix β α ℝ) (x : α→ A) (i : β) : quill V (fun i=>C (x i)) i=C (quill V x i) := (quill_map V x (post A).toLinearMap i).symm
lemma quill_steps (V : Matrix β α ℝ) {x y : α→PowerSeries A} (h : ∀ i,Steps n (x i) (y i)) (i : β) : Steps n (quill V x i) (quill V y i) := Steps.sum' _ (fun j _=> (h j).scale _)
lemma force_steps (V : Matrix α α ℝ) {x y : α→PowerSeries A} (h : ∀ i,Steps n (x i) (y i)) : Steps n (forceQ V x) (forceQ V y) := (Steps.sum' _ (fun j _=> (h j).mul (quill_steps V h j))).scale _
lemma right_mission [DecidableEq α] (h : J*V=1) : V*J=1 := _root_.mul_eq_one_comm.mp h
lemma fare_nz [DecidableEq α] (h : B*J=1) : B.det≠0 := by intro he; apply zero_ne_one (α:=ℝ); rw [← Matrix.det_one (n:=α), ← h, Matrix.det_mul, he]; ring

-- linear admission kick
abbrev viewer (j : ι) : StageD α ι := named (Sum.inr j)
def day (V : Matrix α α ℝ) (W : Matrix α ι ℝ) := quill V privateName + quill W viewer
lemma day_range (hv : J.IsSymm) (i : α) : inflow i (forceQ J (day V W))= quill (V.transpose*J) (day V W) i := by
  have he (j) : inflow i (day V W j)= algebraMap ℝ _ (V j i) := by
    rw [day,Pi.add_apply,map_add,inflow_quill]; simp [inflow,quill,viewer]
  rw [force_D hv,furrow,knot,←quill_chain]; simp_rw [he, quill, transpose_apply,Algebra.smul_def]
lemma day_trace (hv : J.IsSymm) (i : α) : inflow i (forceQ J (day V W))= quill (V.transpose*J*V) (fun j:α=> privateName (ι:=ι) j) i + quill (V.transpose*J) (quill W viewer) i := by rw [day_range hv,day,quill_add,quill_chain,Pi.add_apply]
omit [Fintype α] in
lemma day_view (V : Matrix α β ℝ) [Fintype β] (W : Matrix β ι ℝ) (i j : α) : inflow j (quill V (quill W viewer) i)=0 := by simp [quill,inflow,viewer]

lemma quill_conjugate (h : J.IsSymm) (hb : B.IsSymm) {p q : Tape ι} (he : Steps 1 (boast α ι p+ seedQ ι B) (boast α ι q+ forceQ J (day V W))) : V.transpose*J*V=B := by
  have hu (i j : α) : Steps 1 (algebraMap ℝ (StageD α ι) (B i j)) (algebraMap ℝ (StageD α ι) ((V.transpose*J*V) i j)) := by
    have hy := Steps_prime j (Steps_prime i he)
    simp only [map_add, hat_still, zero_add,seedQ,force_player hb,day_trace h, inflow_quill,day_view, zero_add,add_zero] at hy; exact hy
  ext i j
  have hz := (steps_initial ..).mp (hu i j)
  simp only [PowerSeries.algebraMap_apply,constantCoeff_C,← MvPolynomial.C_eq_algebraMap] at hz
  exact MvPolynomial.C_injective (R:=ℝ) (Chamber α ι) hz.symm
lemma quill_derive (T : Tabletop (Chamber α ι)→ Tabletop α) (hT : ContDiffAt ℝ ω T 0) :
    ∃ V W, ∀ i,Steps 1 (exposure T i) (day V W i) := by
  let f i z := T z i
  let h (i : α) (j : Chamber α ι):= leafD j (f i) 0
  refine ⟨Matrix.of fun i j=> h i (Sum.inl j),Matrix.of fun i j=> h i (Sum.inr j),fun i=>?_⟩
  apply (steps_initial ..).mpr
  unfold exposure day; rw [Pi.add_apply, flash_const (contDiffAt_pi.mp hT i), Fintype.sum_sum_type]; simp only [map_add,map_sum, quill, privateName,viewer,named,Matrix.of_apply,h,f,constantCoeff_smul, MvPolynomial.C_mul', constantCoeff_C]

lemma Steps_derive (T : α→StageD α ι) (hT : ∀ i, Steps 1 (T i) (day V W i)) {p q : Tape ι} [DecidableEq α]
    (hB : B.IsSymm) (hJ : J.IsSymm)
    (hb : B*G=1) (hj : J*H=1) (he : Steps 1 (boast α ι p +seedQ ι B) (boast α ι q+ forceQ J T)) :
    V.transpose*J*V=B ∧ V.det≠0 ∧ V*G*V.transpose=H ∧ Starting T V := by
  have hy : Steps 1 (boast α ι p+ seedQ ι B) (boast α ι q+ forceQ J (day V W)) := he.trans (Steps.add Steps.self (force_steps J hT))
  have hv := quill_conjugate hJ hB hy
  have hz : V.det≠0 := by
    intro h; apply fare_nz hb
    rw [← hv,Matrix.det_mul,h]; ring
  have hu := right_mission hb
  have hs := right_mission hj
  let Y:= V.transpose*J
  have hx : Y*(V*G)=1 := by rw [← Matrix.mul_assoc,hv,hb]
  refine ⟨hv,hz,?_,?_⟩
  · calc
      _ = V*G*(V.transpose*(J*H)) := by rw [hj,mul_one]
      _ = H := by rw [←mul_assoc V.transpose, ←mul_assoc,show _*Y=1 from right_mission hx,one_mul]
  · have hh (i : α) : Steps 1 (quill Y (quill W (α:=ι) (fun j=>viewer (α:=α) j)) i) 0 := by
      have h := Steps_prime i hy; simp only [map_add,hat_still,seedQ,force_player hB,zero_add,day_trace hJ,hv] at h
      rw [Steps.dvd, pow_one,sub_zero, X_dvd_iff]; -- use const coeff additive h
      refine (add_right_inj ..).mp ((show constantCoeff (quill B privateName i : StageD α ι) + _ = _ + 0 from ?_))
      rw [add_zero]; exact Eq.trans (map_add constantCoeff _ _).symm ((steps_initial ..).mp h).symm
    intro i; apply (hT i).trans; unfold day; rw [Pi.add_apply]
    have hp i : Steps 1 (quill W (fun j=>viewer (α:=α) j) i) 0 := by simpa only [quill_chain (V*G) Y, right_mission hx, quill_one, show quill (V*G) 0 i=(0:StageD α ι) from congr_fun (quill_zero _) i] using quill_steps (V*G) (x:=quill Y (quill W (fun j=>viewer (α:=α) j))) (y:=0) hh i
    simpa only [add_zero] using Steps.add (q:=quill V privateName i) Steps.self (hp i)
end YM.WilsonBulk.Sheet

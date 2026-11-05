import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Payroll


/-!
# Per actual infinite array term

No silent replacement of nonlinear curvature; budget for exact written
lengths *on cover*. Allows purchases at the wide width also when the next
step gets a narrower rate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {n l : Side} {ι : Type*} [DecidableEq ι] {k : ℕ}
variable {P : Purse ι (Site n)} {η C σ : ℝ}
open Purse Logfee Plaque
namespace Cargo

lemma fields {X E α : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype α] (P : Purse ι α)
    (F : E→α→X→ℝ) (u : Finset E) {x : X} (d : ι→X) (C : E → ℝ) {m : ℕ}
    (h : ∀ i∈u, ∀ a : α,ContDiffAt ℝ ω (F i a) x) (S : Finset ι) (hm : S.card ≤ m)
    (hf : ∀ i∈u, ∀ T⊆S, P.Jets T d (F i) x (C i)) :
    P.Jets S d (fun i y => ∏ j∈u,F j i y) x (∏ j∈u, (2:ℝ)^m*C j) := by
  classical
  induction u using Finset.induction_on generalizing S with
  | empty =>
    rcases Finset.eq_empty_or_nonempty S with ht|ht
    · rw [ht]; unfold Jets; simp_rw [Finset.prod_empty,blank]
      exact Pays.blank zero_le_one fun _ => norm_one.le
    unfold Jets; simp_rw [Finset.prod_empty,mute ht]; exact Pays.zero zero_le_one
  | insert e u he ih =>
    simp_rw [Finset.prod_insert he, mul_assoc];
    refine Jets.priced (ContinuousLinearMap.mul ℝ ℝ) (fun a b => norm_mul_le a b) (h e (by simp)) ?_ (hf e (by simp)) ?_ m hm
    · intro i; exact contDiffAt_prod fun j hj => h j (Finset.mem_insert_of_mem hj) i
    intro T ht
    exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) T ((Finset.card_le_card ht).trans hm) (fun j hj U hu => hf j (Finset.mem_insert_of_mem hj) U (hu.trans ht))

lemma quits {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (F : E→X→ℝ) (u : Finset E) {x : X}
    (d : ι→X) (h : ∀ i∈u,ContDiffAt ℝ ω (F i) x) (hh : ∀ i∈u, F i x=0)
    (S : Finset ι) (ht : S.card < u.card) : bill S d (fun y => ∏ j∈u,F j y) x=0 := by
  classical
  induction u using Finset.induction_on generalizing S with
  | empty => simp_all
  | insert e u he ih =>
    rw [Finset.card_insert_of_notMem he] at ht
    let L := ContinuousLinearMap.mul ℝ ℝ
    let p (z : X) := ∏ i∈u,F i z
    have hx : ContDiffAt ℝ ω p x := contDiffAt_prod fun i hi => h _ (Finset.mem_insert_of_mem hi)
    simp_rw [Finset.prod_insert he]
    change bill S d (fun x => L (F e x) (p x)) x=0
    rw [account L _ _ _ _ x (h e (by simp)) hx]; refine Finset.sum_eq_zero fun i hi => ?_
    have hi := Finset.mem_powerset.mp hi
    change bill _ _ _ _ * bill _ _ p x = 0
    rcases Finset.eq_empty_or_nonempty i with he|he
    · rw [he,blank,hh e (by simp),zero_mul]
    have hc := Finset.card_sdiff_add_card_eq_card hi; have ht' := Finset.card_pos.mpr he
    rw [show bill (S \ i) d p x=0 from ih (fun j hj => h _ (Finset.mem_insert_of_mem hj))
      (fun j hj => hh _ (Finset.mem_insert_of_mem hj)) (S\i) (by omega),mul_zero]

def effect (A : Atom G k) (x : Site n) (y : Dir G n) := A.unmasked (represent y) x
def bit (A : Atom G k) (b : Fin k→G.ColorIndex) (i : Fin k) (x : Site n) (y : Dir G n) : ℝ := spool (A.leg i) x y (b i)
lemma bit_charge (A : Atom G k) (b : Fin k→G.ColorIndex) (i : Fin k) (x : Site n) : ContDiff ℝ ω (bit A b i x) :=
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ => ℝ) (b i)).contDiff.comp (spinner (A.leg i) (G:=G) x)
lemma effective (A : Atom G k) (x : Site n) : ContDiff ℝ ω (effect A x) :=
    ContDiff.sum fun b _ => contDiff_const.mul (show ContDiff ℝ ω (fun y => ∏ i, bit A b i x y) from
      contDiff_prod fun _i _ => bit_charge ..)
lemma submissing (A : Atom G k) (x : Site n) (d : ι→Dir G n) (S : Finset ι) (hm : S.card < k) :
    bill S d (effect A x) 0=0 := by
  let p (b : Fin k→G.ColorIndex) (x : Site n) (y : Dir G n) := ∏ i,bit A b i x y
  have h (b) : ContDiffAt ℝ ω (p b x) 0 := contDiffAt_prod fun i _ => (bit_charge ..).contDiffAt
  change bill S d (fun y => ∑ b,(A.coeff b • p b x) y) 0=0
  rw [sum_bill Finset.univ S d (fun b => A.coeff b • p b x)]
  · refine Finset.sum_eq_zero fun i _ => ?_
    have ht (j : Fin k) (_ : j ∈ Finset.univ) : bit A i j x 0=0 := by unfold bit; rw [spool_start]; rfl
    have he : bill S d (p i x) 0=0 := quits _ _ d (fun b _ => (bit_charge ..).contDiffAt) ht S (by simpa using hm)
    rw [smul_price S d (h i),he,smul_zero]
  intro i _; exact (h i).const_smul (A.coeff i)

lemma fee_limit (x : ℕ) {η σ : ℝ} {m : ℕ} (h : 5*m*η ≤ σ*l.val) : guide l (5*m*η) x ≤ Real.exp (σ*x) := by
  refine Real.exp_monotone (mul_le_mul_of_nonneg_right ((div_le_iff₀ ?_).mpr h) (by positivity : 0 ≤ (x:ℝ)))
  positivity

lemma multiply (l : Side) (η : ℝ) (e : Fin k → ℕ) : ∏ i, guide l η (e i)=guide l η (∑ i,e i) := by
  unfold guide; rw [← Real.exp_sum]; push_cast; rw [Finset.mul_sum]

lemma levy {d : ι→Dir G n} (h : Linkbill l P d) (he : tollRate P l η) (hp : 0 < η)
    (a : Dir G n) (ha : ‖a‖ ≤ 1) (S : Finset ι) (m : ℕ) (hm : S.card ≤ m) (hq : 5*m*η ≤ σ*l.val)
    (C : ℝ) (hb : ∀ q : PlaqAxes, ∀ T⊆S, P.Jets T d (plasty q) a C)
    (A : Atom G k) (hc : 0 ≤ C) : P.Jets S d (effect A) a (((2:ℝ)^m*(mailCharge G η m*C))^k*A.budget σ) := by
  let r (i : Fin k) := guide l (5*m*η) (A.leg i).length
  let c (i : Fin k) := mailCharge G η m*C*r i
  have ht (b i) (T : Finset ι) (ht : T⊆S) : P.Jets T d (bit A b i) a (c i) := by
    have hS := spool_pays h he hp m ((Finset.card_le_card ht).trans hm) a ha (A.leg i) C (fun v hv => hb _ _ (hv.trans ht))
    apply hS.change_map (PiLp.proj (𝕜:=ℝ) 2 (fun _ => ℝ) (b i)) (fun v => (spinner ..).contDiffAt)
    intro y
    change |(y (b i))| ≤ _
    rw [← EuclideanSpace.basisFun_inner]; exact (abs_real_inner_le_norm ..).trans_eq (by rw [OrthonormalBasis.norm_eq_one,one_mul])
  let u (b : Fin k→G.ColorIndex) i (z : Dir G n) := ∏ j, bit A b j i z
  have hU (i j) : ContDiffAt ℝ ω (u i j) a := contDiffAt_prod fun k _ => (bit_charge ..).contDiffAt
  apply (Jets.allotted Finset.univ (fun i j z => A.coeff i • u i j z) (fun i _ j => (hU i j).const_smul _)
    (fun i _ => Jets.rate (fields P (bit A i) _ d c (fun _ _ _ => (bit_charge ..).contDiffAt) S hm (fun j _ v hv => ht i _ _ hv)) _ (hU i))).mono
  simp only [Atom.budget,Atom.magnitude, ← Finset.sum_mul,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin,c,r,multiply,Atom.length]
  rw [mul_pow ((2:ℝ)^m),mul_pow (mailCharge G η m)]
  have he := fee_limit A.length hq
  have ht := mailCharge_pos G η m
  refine ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he
    (by positivity : 0 ≤ mailCharge G η m ^ k * C ^ k)) (by positivity : 0 ≤ ((2:ℝ)^m)^k))
    (by unfold Atom.magnitude; positivity : 0 ≤ A.magnitude))).trans_eq (by unfold Atom.magnitude Atom.length; ring)
end Cargo
end YM.AnalyticNext.QuarticMatch.Estimate

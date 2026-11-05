import YM.Next.FREE_KERNELS.Curl

/-!
# Real defects and curl prices

These identities at every coarse and fine torus use the *same* Row/Cross,
compared by installed. Closure includes periods not just supported-test sizes.
`deposit` refers to the unmodified defect, before a positive-stack correction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08
open scoped Topology BigOperators ComplexConjugate
variable {j t : ℕ} {m n d' : Type*} {L : Side}

/-- Composition across an installed pair and summing over shared FINE index. -/
def net {m n d : Type*} [Fintype m] (A : Cross L m n) (B : Cross L m d) := composeRows (transRows A) B
lemma net_action [Fintype m] {c f : Side} (g : Ratio c f) {A : Cross g.count m n} {B : Cross g.count m d'} (ha : Whole A) (hb : Whole B) :
    (net A B).acts c=(installed g A).transpose * installed g B := by
  unfold net; rw [ha.flipped.acts hb,acts_trans]; unfold installed
  ext i j; simp only [Matrix.mul_apply,Matrix.transpose_apply, Matrix.submatrix_apply,id_eq]
  exact (Equiv.sum_comp (splitCo g m) _).symm
lemma Whole.from_fine [Fintype m] {c f : Side} (g : Ratio c f) {A : Row n m} {B : Cross g.count m d'} (ha : Whole A) (hb : Whole B) : installed g (fineCompose A B)=A.acts f*installed g B := by
  obtain ⟨σ,C,hp,h⟩ := ha; obtain ⟨θ,D,hq,h'⟩ := hb
  exact installed_fine g (lt_min hp hq).le (strip_mono h (min_le_left σ θ) le_rfl) (strip_mono h' (min_le_right σ θ) le_rfl)
lemma Whole.from_coarse [Fintype m] {c f : Side} (g : Ratio c f) {A : Cross g.count n m} {B : Row m d'} (ha : Whole A) (hb : Whole B) : installed g (composeRows A B)=installed g A* B.acts c := by
  obtain ⟨σ,x,y,hp,h,h'⟩ := ha.pass hb; exact installed_compose g hp.le h h'

namespace Flight

/-- `p=0` fiber still accounted. -/
def gap (k : ℝ) (P : Flight j t) : Row (TypeFace 2) (TypeFace 2) :=
    minusRows (minusRows (blue k P.land) (net (P.duo k).T (buckle k P)))
      (scaleRows k⁻¹ (composeRows (cobound 1) (transRows (cobound 1))))

def deposit (k : ℝ) (P : Flight j t) := composeRows (composeRows (pink k P.land) (gap k P)) (pink k P.land)

def leftFunds (k : ℝ) (P : Flight j t) := Double.both (deposit k P)

def quarter (A : Row m m) := scaleRows (1/2) (plusRows A (transRows A))

def fund (k : ℝ) (P : Flight j t) := quarter (P.leftFunds k)

abbrev Guide (f : Flight j t → Row m n) := Stock (α:=fun _=>m) (β:=fun _=>n) (fun _ => 1) f

variable (k : ℝ) (hk : 0<k) (hj : 4≤j) (ht : 4≤t) (P : Flight j t)

section coverage
include hk hj ht
lemma gap_cost : Guide (gap (j:=j) (t:=t) k) := by
  obtain ⟨h₁,h₂⟩ := budgets_linear k hk hj ht
  have hp := (heart_saves k hk ht (fun P : Flight j t => P.land)).2
  let L (P : Flight j t) := P.L
  have hh := Stock.prod h₂.flipped h₁
  have hu : Guide (fun P : Flight j t => net (P.duo k).T (buckle k P)) := by
    let B := (Fintype.card (TypeFace 2):ℝ)
    apply hh.raise (c:=B+1) (by unfold B; positivity); intro P
    have hL := side_pos P.L
    unfold fee
    change (Fintype.card (Co (L P) (TypeFace 2)):ℝ)*_ ≤ _
    unfold Co L B at *; rw [Fintype.card_prod,site_card]; push_cast
    field_simp; nlinarith
  let d := Stock.constant (ι:=Flight j t) (cobound 1) (Whole.boundary 1)
  have hc := (d.times d.flipped).weight k⁻¹; simp only [mul_one] at hc
  exact (hp.minus hu).minus hc
lemma deposit_cost : Guide (deposit (j:=j) (t:=t) k) := by
  have hp := (heart_saves k hk ht (fun P : Flight j t => P.land)).1
  have hz := (hp.times (gap_cost k hk hj ht)).times hp; simp only [mul_one] at hz; exact hz
lemma invested : Guide (leftFunds (j:=j) (t:=t) k) := Double.duplex_stock (A:=deposit k) (deposit_cost k hk hj ht)
lemma funded : Guide (fund (j:=j) (t:=t) k) := by
  have h := invested k hk hj ht; exact (h.plus h.flipped).weight _
end coverage

section profession
variable {c f : Side} (hc : f.val=c.val*P.L.val)
include hk ht
lemma buckle_physical : installed (P.visitRatio hc) (P.buckle k)=(blue k P.wing).acts f*installed (P.visitRatio hc) (P.duo k).T := by
  let r := P.visitRatio hc
  have he := sail_run P hc (agility k hk P.legal ht) P.legal 2
  have hx := sail_run P hc (secure_both k hk P.legal ht).2 P.legal 2
  have hb := ((heart_true k hk P.legal P.wing).2.fine r P.odd).product hx
  have hu : braceAll r (vault k P.wing)*solo c (P.fromBank (wire k) 2)=solo c (P.fromBank (agile k) 2) := by
    unfold braceAll solo; rw [fiber_mult]; congr! 2 with i; unfold fromBank agile; rw [alias_after]; congr! 2 with l; rw [Matrix.mul_smul]
  rw [hu] at hb; exact he.lands hb (rotations_crew c _)
lemma mark_charge :
    let g := P.visitRatio hc
    let T := installed g (P.duo k).T
    installed g (P.charge k)=d 2 f*(blue k P.wing).acts f*T*(pink k P.land).acts c := by
  have he := budgets_linear k hk P.legal ht
  have hg := (heart_saves k hk ht (fun P : Flight j t => P.land)).1
  intro g T; unfold charge
  rw [Whole.from_coarse g ((budget_curl k hk P.legal ht).whole P) (hg.whole P)]
  unfold curlStep; rw [Whole.from_fine g (Whole.boundary 2) (he.1.whole P)]
  unfold g; rw [buckle_physical k hk ht P hc]; simp only [Matrix.mul_assoc]; rfl
lemma gap_physical :
    let T := installed (P.visitRatio hc) (P.duo k).T
    (gap k P).acts c=(blue k P.land).acts c-T.transpose*(blue k P.wing).acts f*T-k⁻¹ • (d 1 c*(d 1 c).transpose) := by
  have he := budgets_linear k hk P.legal ht
  have hg := (heart_saves k hk ht (fun P : Flight j t => P.land)).2
  have hh := Whole.boundary 1
  have hN := ((he.2.whole P).flipped).prod (he.1.whole P)
  change Whole (net (duo k P).T (buckle k P)) at hN
  intro T; unfold gap; rw [((hg.whole P).minus hN).less ((hh.prod hh.flipped).weight _) c, (hg.whole P).less hN c]
  rw [net_action (P.visitRatio hc) (he.2.whole P) (he.1.whole P),buckle_physical k hk ht P hc,acts_scale,hh.acts hh.flipped c,acts_trans,← Matrix.mul_assoc]
end profession

-- A live step S with the given kernel choices can use the calculations even
-- on any coarse side (callers at c need recovery of corresponding f).
section carry
variable (K : KernelChoices)
include ht
lemma closed_charge (c : Side) : (P.charge K.penalty).acts c*d 1 c=0 := by
  let k := K.penalty
  let f := c*P.L
  let g := P.visitRatio (c:=c) (f:=f) rfl
  have he := mark_charge k K.penalty_pos ht P (c:=c) (f:=f) rfl
  have hh := tangent P K ht (c:=c) (f:=f) rfl
  have hs := heart_inverse k K.penalty_pos P.legal P.wing f
  let H := (pink k P.wing).acts f
  let H' := (pink k P.land).acts c
  let B := (blue k P.wing).acts f
  let T := installed g (duo k P).T
  have hm : T*H'*d 1 c=H*d 1 f*installed g (duo k P).A0 := hh.2.2
  have hb : B*H=1 := mul_eq_one_comm.mp hs.1
  have hI : installed g (P.charge k)*d 1 c=0 := by
    rw [show installed g (P.charge k)=d 2 f * B * T * H' from he]
    rw [Matrix.mul_assoc,Matrix.mul_assoc (d 2 f * B),← Matrix.mul_assoc T,hm]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc B,hb, Matrix.one_mul,← Matrix.mul_assoc (d 2 f),Exterior.closed 1 f,Matrix.zero_mul]
  ext ⟨p,x⟩ y
  let i := (splitCo g (TypeFace 3)).symm (p,x)
  have hu := congr_fun (congr_fun hI i) y
  unfold installed at hu; simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.zero_apply] at hu
  simp only [show splitCo g (TypeFace (2+1)) i=(p,x) from Equiv.apply_symm_apply ..] at hu
  exact hu
variable {c f : Side} (hc : f.val=c.val*P.L.val)
lemma intake :
    let k := K.penalty; let r := P.visitRatio hc
    let T := installed r (P.duo k).T
    installed r (P.sale k)*d 2 c*(blue k P.land).acts c = d 2 f*(blue k P.wing).acts f*T := by
  intro k r T
  let W := (blue k P.land).acts c; let G := (pink k P.land).acts c
  have he := dormant_right (r:=1) ((budget_charge k K.penalty_pos P.legal ht).whole P)
    (P.closed_charge ht K) c
  have hu : installed r (P.sale k)*d 2 c=installed r (P.charge k) := by
    unfold installed
    change submatrix ((sale k P).acts c * d 2 c)  (splitCo r (TypeFace 3)) id=submatrix ((charge k P).acts c)  (splitCo r (TypeFace 3)) id
    rw [show (sale k P).acts c*d 2 c=_ from he]
  rw [hu,show installed r _=_ from mark_charge k K.penalty_pos ht P hc]
  rw [Matrix.mul_assoc _ ((pink k P.land).acts c), (heart_inverse k K.penalty_pos ht P.land c).1, Matrix.mul_one]

lemma dep_eq (c : Side) :
    let k := K.penalty; let H := (pink k P.land).acts c
    (deposit k P).acts c=H*(gap k P).acts c*H := by
  intro k H; have hh := (heart_saves k K.penalty_pos ht (fun i : Flight j t => i.land)).1.whole P
  have hg := (gap_cost k K.penalty_pos P.legal ht).whole P
  unfold deposit; rw [(hh.prod hg).acts hh,hh.acts hg]

lemma dep_zero (c : Side) :
    let k := K.penalty; let M := (deposit k P).acts c
    M*d 1 c=0 ∧ Mᵀ=M := by
  intro k M
  let f := c * P.L; let g := P.visitRatio (c:=c) (f:=f) rfl
  let T := installed g (duo k P).T; let Q := mean (visit P K (c:=c) (f:=f) rfl); let A := installed g (duo k P).A0
  let H₁ := (pink k P.land).acts c; let H₂ := (pink k P.wing).acts f
  let B₁ := (blue k P.land).acts c; let B₂ := (blue k P.wing).acts f
  let d := Exterior.d 1 c; let e := Exterior.d 1 f
  have hM : M=H₁*(B₁-Tᵀ*B₂*T-k⁻¹ • (d*dᵀ))*H₁ := by
    unfold M; rw [show (deposit k P).acts c=_ from P.dep_eq ht K c,gap_physical k K.penalty_pos ht P (c:=c) (f:=f) rfl]
  have he₁ := heart_inverse k K.penalty_pos ht P.land c
  have he₂ := heart_inverse k K.penalty_pos P.legal P.wing f
  have hv₁ : B₁*H₁=1 := mul_eq_one_comm.mp he₁.1; have hv₂ : B₂*H₂=1 := mul_eq_one_comm.mp he₂.1
  have h := tangent P K ht (c:=c) (f:=f) rfl
  obtain ⟨hq₁,hq₂,hq₃⟩ := h
  have hn : T*H₁*d=H₂*e*A := hq₃
  have hq : Tᵀ*e=d*Q := hq₂
  have hb : Q*A=1-k⁻¹ • (dᵀ*H₁*d) := hq₁.dual
  rw [hM]
  constructor
  · change _*_*H₁*d=0
    have hh : (B₁-Tᵀ*B₂*T-k⁻¹ • (d*dᵀ))*H₁*d=0 := by
      have ha : Tᵀ*B₂*T*H₁*d=d*(1-k⁻¹ • (dᵀ*H₁*d)) := by
        rw [Matrix.mul_assoc,Matrix.mul_assoc _ T,← Matrix.mul_assoc T,hn]
        simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc B₂,hv₂,Matrix.one_mul,← Matrix.mul_assoc Tᵀ,hq,Matrix.mul_assoc,hb]; simp only [Matrix.mul_assoc]
      rw [Matrix.sub_mul,Matrix.sub_mul,Matrix.sub_mul,Matrix.sub_mul,hv₁,Matrix.one_mul,ha,Matrix.mul_sub]; simp only [Matrix.mul_one,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]; abel
    rw [Matrix.mul_assoc,Matrix.mul_assoc, ← Matrix.mul_assoc _ H₁ d,hh, Matrix.mul_zero]
  have h1 : B₁ᵀ=B₁ := he₁.2.2; have h2 : B₂ᵀ=B₂ := he₂.2.2; have h3 : H₁ᵀ=H₁ := he₁.2.1
  simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_smul,h1,h2,h3, Matrix.transpose_transpose,Matrix.mul_assoc]

lemma fund_sym : Whole (fund K.penalty P) ∧ ∀ p : Momentum, physical p → IsHermitian ((fund K.penalty P).read p) := by
  let k := K.penalty
  have hb := (invested k K.penalty_pos P.legal ht).whole P
  refine ⟨(funded k K.penalty_pos P.legal ht).whole P,fun p hp => ?_⟩
  unfold fund quarter; rw [read_weight,hb.read_plus hb.flipped hp, read_opposite _ hp]; unfold IsHermitian
  rw [Matrix.conjTranspose_smul,conjTranspose_add]; simp; abel

lemma pledge_deposit (c : Side) :
    let k := K.penalty
    (d 2 c).transpose*(fund k P).acts c*d 2 c=(deposit k P).acts c := by
  intro k
  let A := deposit k P; let B := leftFunds k P
  have hA := (deposit_cost k K.penalty_pos P.legal ht).whole P
  have hd (c : Side) : A.acts c*d 1 c=0 := (P.dep_zero ht K c).1
  have hs (c : Side) : (A.acts c)ᵀ=A.acts c := (P.dep_zero ht K c).2
  have he (c : Side) : (d 1 c)ᵀ*A.acts c=0 := by rw [← hs,← Matrix.transpose_mul,hd,transpose_zero]
  let D := d 2 c
  have hf : Dᵀ*B.acts c*D=A.acts c := Double.duplex hA hd he c
  have hg : Dᵀ*(B.acts c)ᵀ*D=A.acts c := by
    have h' : (Dᵀ*B.acts c*D)ᵀ=(A.acts c)ᵀ := congr_arg Matrix.transpose hf
    simpa only [hs, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using h'
  have hb := (invested k K.penalty_pos P.legal ht).whole P
  unfold fund quarter; rw [acts_scale,hb.acts_plus hb.flipped,acts_trans];
  rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_add,Matrix.add_mul,hg,hf];
  ext i j; simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]; ring

lemma banked_dollars (c : Side) :
    let k := K.penalty; let B := (blue k P.land).acts c; let W := d 2 c * B
    (gap k P).acts c = W.transpose*(fund k P).acts c*W := by
  intro k B W
  let H := (pink k P.land).acts c
  have hx := heart_inverse k K.penalty_pos ht P.land c
  have hh : H * B = 1 := hx.1
  have hg := mul_eq_one_comm.mp hh
  calc
    _ = B*(deposit k P).acts c*B := by
      rw [show (deposit k P).acts c=H*(gap k P).acts c*H from P.dep_eq ht K c,Matrix.mul_assoc,Matrix.mul_assoc _ H B,hh,Matrix.mul_one,← Matrix.mul_assoc,hg,Matrix.one_mul]
    _ = _ := by
      unfold W; rw [← show (d 2 c)ᵀ*(fund k P).acts c*d 2 c = _ from P.pledge_deposit ht K c, Matrix.transpose_mul,show Bᵀ=B from hx.2.2]; simp only [Matrix.mul_assoc]

end carry
end Flight
end YM.Next.Free

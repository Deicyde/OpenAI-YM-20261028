import YM.Next.FREE_KERNELS.Hall

/-!
# Modifying the two-form precision before stack repair

Penalize closed-components in the **inverse** metric with constant `l`.
Real spectral positivity is independent of L. This does not change the
potential precision (all harmonic conventions retained). These lemmas don't
assume any stack extensions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft
open Work.F06 (sqLength pairingRe countCeil)
open Work.F07 (Band)
open scoped Topology BigOperators ComplexConjugate
variable {j : ℕ} {ι : Type*} {m : Type} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
lemma Warm.fixed {f : ι → Row m m} (h : Warm f) (i : ι) {p : Momentum} (hp : physical p) : IsHermitian ((f i).read p) := by obtain ⟨v,C,hv,hC,h⟩ := h.funds; exact (h i p hp).1
lemma Warm.swap {f : ι → Row m m} (h : Warm f) (i : ι) (n : Side) : ((f i).acts n)ᵀ=(f i).acts n := by
  obtain ⟨v,C,hv,hC,g⟩ := h.funds; exact (obey_band (f i) (h.stock.whole i) (g i) n).1
omit [DecidableEq m] in
lemma cross_chart (S : Matrix m m ℂ) (h : S.IsHermitian) {n : Type*} [Fintype n] (R : Matrix m n ℂ) : IsHermitian (Rᴴ*S*R) := by unfold IsHermitian; rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,h,Matrix.mul_assoc]
omit [DecidableEq m] in
lemma paid_through (S : Matrix m m ℂ) {n : Type*} [Fintype n] (R : Matrix m n ℂ) (x : n → ℂ) : pairingRe (Rᴴ*S*R) x x=pairingRe S (R*ᵥx) (R*ᵥx) := by rw [Matrix.mul_assoc,paid_after]; unfold pairingRe; rw [Matrix.mulVec_mulVec]

def drawer (k : ℝ) (v : Train j) := composeRows (cobound 2) (blue k v)
def pledge (k l : ℝ) (v : Train j) := plusRows (blue k v) (scaleRows l (composeRows (transRows (drawer k v)) (drawer k v)))
def amend (k l : ℝ) (v : Train j) := oppositeRow (pledge k l v)
def bail (k l : ℝ) (v : Train j) := plusRows (unitRow (TypeFace 3)) (scaleRows l (composeRows (drawer k v) (transRows (cobound 2))))
def treble (k l : ℝ) (v : Train j) := oppositeRow (bail k l v)

section all
variable (k l : ℝ) (hk : 0<k) (hl : 0 ≤ l) (hj : 4 ≤ j)
include hj hk
lemma billed_drawer (v : ι → Train j) : Stock (fun _ : ι => 1) (α:=fun _ => TypeFace 3) (β:=fun _ => TypeFace 2) fun i => drawer k (v i) := by
  have he := (Stock.constant _ (Whole.boundary 2)).times (heart_saves _ hk hj v).2; simp only [one_mul] at he; exact he
include hl
lemma pledge_warm (v : ι → Train j) : Warm fun i => pledge k l (v i) := by
  have hd := billed_drawer k hk hj v
  have hb := (heart_heats k hk hj v).2
  have hh := (hd.flipped.times hd).weight l; simp only [one_mul] at hh
  obtain ⟨a,A,ha,hA,g⟩ := hb.funds
  refine safe_lower_gives _ (hb.stock.plus hh) a ha (fun i p hp => ?_)
  let B := blue k (v i)
  let X := drawer k (v i)
  have hx := hd.whole i
  have hr := (g i p hp).1
  change IsHermitian ((pledge k l (v i)).read p) ∧ _
  have hy : (pledge k l (v i)).read p=B.read p+(l:ℂ) • ((X.read p)ᴴ*X.read p) := by
    unfold pledge
    rw [(hb.stock.whole i).read_plus ((hx.flipped.prod hx).weight _) hp,read_weight,hx.flipped.read hx hp,read_opposite _ hp]
  simp only [hy]
  constructor
  · unfold IsHermitian; simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]; rw [show (B.read p)ᴴ=B.read p from hr]; simp
  intro x; rw [Work.F06.pairingRe_add,Work.F06.pairingRe_scale,Work.F06.pairingRe_gram]
  exact le_add_of_le_of_nonneg ((g i p hp).2 x).1 (mul_nonneg hl (Work.F06.sqLength_nonneg _))
lemma bail_warm (v : ι → Train j) : Warm fun i => bail k l (v i) := by
  have hg := billed_drawer k hk hj v
  have hh := Whole.boundary 2
  have hx := (hg.times (Stock.constant _ hh).flipped).weight l; simp only [one_mul] at hx
  have ha := (heart_heats k hk hj v).2
  obtain ⟨a,C,hp,hc,H⟩ := ha.funds
  refine safe_lower_gives _ ((Stock.constant _ (Whole.coin _)).plus hx) _ one_pos fun i p h => ?_
  let S := (blue k (v i)).read p; let W := (cobound 2).read p
  have hs : IsHermitian S := (H i p h).1
  have hb : (bail k l (v i)).read p=1+(l:ℂ) • (W*S*Wᴴ) := by
    unfold bail; rw [(Whole.coin _).read_plus (((hg.whole i).prod hh.flipped).weight _) h,
      read_unit,read_weight,(hg.whole i).read hh.flipped h,read_opposite _ h]; unfold drawer; rw [hh.read (ha.stock.whole i) h]
  simp only [hb]; constructor
  · unfold IsHermitian; simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,Matrix.conjTranspose_one,Matrix.conjTranspose_conjTranspose]; rw [hs,Matrix.mul_assoc]; simp
  intro x; rw [Work.F06.pairingRe_add,Work.F06.pairingRe_scale,price_unit]
  have hy : pairingRe (W*S*Wᴴ) x x=pairingRe S (Wᴴ*ᵥx) (Wᴴ*ᵥx) := by simpa only [conjTranspose_conjTranspose] using paid_through S Wᴴ x
  rw [hy,one_mul]; exact le_add_of_nonneg_right (mul_nonneg hl ((mul_nonneg hp.le (Work.F06.sqLength_nonneg _)).trans ((H i p h).2 _).1))

lemma insurance (v : ι → Train j) : Warm (fun i => amend k l (v i)) ∧ Warm fun i => treble k l (v i) :=
    ⟨(heated (pledge_warm k l hk hl hj v)).1, (heated (bail_warm k l hk hl hj v)).1⟩
lemma forced_amend (v : Train j) : (amend k l v).read 0=1 := by
  let w := fun _ : Unit => v
  have hm := (heated (pledge_warm k l hk hl hj w)).2 () |>.1
  have he : (0:Momentum)∈baseCube := ⟨by rw [physical]; simp,by intro i; simp [Real.pi_pos.le]⟩
  have hu : (blue k v).read 0=1 := ((heart_true k hk hj v).2.echo 0 he).trans (vault_zero ..)
  have hX := (billed_drawer k hk hj w).whole ()
  have ha := (heart_saves k hk hj w).2.whole ()
  change Whole (drawer k v) at hX
  change Whole (blue k v) at ha
  rw [show (amend k l v).read 0=_ from hm.echo _ he]
  change ((pledge k l v).read 0)⁻¹=_
  unfold pledge; rw [ha.read_plus ((hX.flipped.prod hX).weight _) he.1,hu,read_weight,hX.flipped.read hX he.1];
  have ht : (drawer k v).read 0=0 := by
    unfold drawer; rw [(Whole.boundary _).read ha he.1]; rw [Exterior.reading,← signal_unit, Flight.signal_zero]; simp
  rw [ht]; simp
lemma obligations (v : Train j) (n : Side) :
    let B := (blue k v).acts n; let H := (pink k v).acts n; let X := d 2 n * B; let G := (amend k l v).acts n; let A := (pledge k l v).acts n; let D := (treble k l v).acts n
    H*B=1 ∧ (G*A=1 ∧ A=B+l • (Xᵀ*X)) ∧ G*d 1 n=H*d 1 n ∧
      X*G=D*d 2 n ∧ Gᵀ=G ∧ Dᵀ=D := by
  intro B H X G A D
  let w := fun _ : Unit => v
  have hb := (heart_saves k hk hj w).2.whole ()
  have hg := (heated (pledge_warm k l hk hl hj w)).2 ()
  have hm := (heated (bail_warm k l hk hl hj w)).2 ()
  obtain ⟨ht,hs⟩ := insurance k l hk hl hj w
  have hh := Whole.boundary 2
  have hX := (billed_drawer k hk hj w).whole ()
  change Whole (drawer k v) at hX; change Whole (blue k v) at hb
  have hxx : (drawer k v).acts n=X := hh.acts hb n
  have hA : G*A=1 := hg.2 n
  have he := heart_inverse k hk hj v n; have he' : H*B=1 := he.1; have hB : B*H=1 := mul_eq_one_comm.mp he'
  have h₂ : A=B+l • (Xᵀ*X) := by unfold A pledge; rw [hb.acts_plus ((hX.flipped.prod hX).weight _) n,acts_scale,hX.flipped.acts hX,acts_trans,hxx]
  refine ⟨he',⟨hA,h₂⟩,?_,?_,ht.swap () n,hs.swap () n⟩ -- index ()
  · have hxd : X*H*d 1 n=0 := by
      unfold X; rw [Matrix.mul_assoc (d 2 n), hB,Matrix.mul_one]; exact Exterior.closed 1 n
    have hh : A*H*d 1 n=d 1 n := by
      rw [h₂,Matrix.add_mul,hB,Matrix.add_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.smul_mul,
        Matrix.mul_assoc,Matrix.mul_assoc Xᵀ,← Matrix.mul_assoc X,hxd,Matrix.mul_zero,smul_zero,add_zero]
    calc G*d 1 n=G*(A*H*d 1 n) := by rw [hh]
         _ = _ := by simp only [← Matrix.mul_assoc,hA,Matrix.one_mul]
  let R := 1+l • (X*(d 2 n)ᵀ)
  have hu : D*R=1 := by
    have he : (bail k l v).acts n=R := by unfold bail R; rw [(Whole.coin _).acts_plus ((hX.prod hh.flipped).weight _) n,acts_unit,acts_scale,hX.acts hh.flipped,acts_trans,hxx]
    rw [← he]; exact hm.2 n
  have hx : R*X=d 2 n*A := by unfold R X; rw [h₂]; unfold X; have ht : Bᵀ=B := he.2.2; simp only [Matrix.transpose_mul,ht,Matrix.mul_add,Matrix.mul_smul,Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul, Matrix.mul_assoc]
  calc
    _ = (D*R)*X*G := by rw [hu,Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc D, hx]; simp only [Matrix.mul_assoc,mul_eq_one_comm.mp hA,Matrix.mul_one]
end all
end YM.Next.Free

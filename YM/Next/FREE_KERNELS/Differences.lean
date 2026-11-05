import YM.Next.FREE_KERNELS.Sell

/-!
# Exact periodic difference convention for optional Ψ transfer

On-cover quotient API: if a `Whole` row spectrum vanishes with the
required real multipliers (with continuous quotients), spend finitely many
(reduced) width shares to get an **exact** row preimage. Don't compare
jets on a single discrete torus instead. `motion` orders coordinate forward
differences on physical cochain sites.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid
open scoped Topology BigOperators ComplexConjugate

variable {m n ι : Type*}

/-- Forward difference convolution stencil. -/
def knock (m : Type*) [DecidableEq m] (s : Axis) : Row m m :=
    minusRows (fun i j x => if i=j then token (step s) x else 0) (unitRow m)
lemma knock_whole (m : Type*) [Fintype m] [DecidableEq m] (s : Axis) : Whole (knock m s) := by
  apply Whole.minus _ (Whole.coin m)
  refine ⟨1,envelopeW 1 (step s),one_pos,fun i j => ?_⟩
  by_cases h : i=j <;> simp only [h,↓reduceIte]
  · exact token_rate (step s) 1
  simp [Laurent.Width, SumBudget, (envelope_pos _ _).le]
lemma knock_read (m : Type*) [Fintype m] [DecidableEq m] (s : Axis) (p : Momentum) :
    (knock m s).read p=chip (p s) • 1 := by
  ext i j; unfold knock
  rw [Row.read,of_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  by_cases he : i=j
  · rw [if_pos he,mul_one,chip,← factor]
    -- two-term expression exactly
    unfold Laurent.read
    let x := (step s:Cover)
    have hh : x≠0 := by intro hx; have hb := congr_fun hx s; simp [x] at hb
    rw [tsum_eq_sum (s:={x,0})];
    · simp [minusRows,token,x,sub_eq_add_neg,he,unitRow,show step s≠(0:Cover) from hh, Ne.symm (show step s≠(0:Cover) from hh)]
    exact fun i h => by
      have hy : i≠0 ∧ i≠x := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or, and_comm] using h
      simp [minusRows,unitRow,token,show i≠step s from hy.2,hy.1]
  simp [minusRows,he,unitRow,Laurent.read]
lemma knock_entry (m : Type*) [Fintype m] [DecidableEq m] (L : Side) (s : Axis) (x : Co L m) (f : Co L m → ℝ) :
    ((knock m s).acts L *ᵥ f) x=f (x.1+step s,x.2)-f x := by
  unfold Matrix.mulVec dotProduct; rw [Fintype.sum_prod_type];
  have hh (i : m) (y : Site L) : (knock m s).acts L x (y,i)=(if i=x.2 then ((if y=x.1+step s then 1 else 0) - (if x.1=y then 1 else 0)) else 0) := by
    rw [Row.acts,of_apply]; have ht : step s≠(0:Cover) := by intro hx; have he := congr_fun hx s; simp at he
    rw [tsum_eq_sum (s:={step s,0})];
    · by_cases h : i=x.2
      · by_cases hb : y=x.1 <;> by_cases hs : y=x.1+step s <;> by_cases hu : (step s : Site L)=0 <;>
          simp [h,hb,hs,knock,minusRows,unitRow,token,ht,Ne.symm ht,hu,Ne.symm,eq_comm,sub_eq_add_neg]
      simp [h,Ne.symm h,knock,minusRows,unitRow]
    intro x hx; have h : x≠step s ∧ x≠0 := by simpa using hx
    simp [knock,minusRows,unitRow,token,h.1,h.2]
  simp_rw [hh, ite_mul,zero_mul,sub_mul];
  simp [Finset.sum_sub_distrib,ite_mul]

def pathJet (m : Type*) [Fintype m] [DecidableEq m] : List Axis → Row m m
| [] => unitRow _
| a::s => composeRows (knock m a) (pathJet m s)
lemma jet_whole (m : Type*) [Fintype m] [DecidableEq m] (s : List Axis) : Whole (pathJet m s) := by
  induction s with
  | nil => exact Whole.coin _
  | cons a s ih => exact (knock_whole _ a).prod ih
lemma jet_read (m : Type*) [Fintype m] [DecidableEq m] (s : List Axis) {p : Momentum} (hp : physical p) :
    (pathJet m s).read p=listChip p s • 1 := by
  induction s with
  | nil => rw [pathJet,read_unit]; simp [listChip]
  | cons a s ih => rw [pathJet,(knock_whole m a).read (jet_whole m s) hp, knock_read, ih]; simp [listChip,smul_smul,mul_comm]

def motion (m : Type*) [Fintype m] [DecidableEq m] (L : Side) (s : List Axis) := (pathJet m s).acts L
lemma motion_zero (m : Type*) [Fintype m] [DecidableEq m] (L : Side) : motion m L []=1 := acts_unit _
lemma motion_walk (m : Type*) [Fintype m] [DecidableEq m] (L : Side) (a : Axis) (s : List Axis) :
    motion m L (a::s)=(knock m a).acts L*motion m L s := (knock_whole _ _).acts (jet_whole _ _) _

lemma move_forward {L : Side} (ho : Odd L.val) (A : Cross L m n) [Fintype m] [DecidableEq m] (b : Axis) :
    fineCompose (knock m b) A=forwardC L A b := by
  funext ⟨r,i⟩ j p; unfold fineCompose; rw [Finset.sum_eq_single i]; swap
  · intro a _ ha; unfold routed; simp [knock,minusRows,Ne.symm ha,unitRow]
  swap; · simp
  let x := (step b:Cover); have hb : x ≠ 0 := by intro hh; have hx := congr_fun hh b; simp [x] at hx
  unfold routed
  rw [tsum_eq_sum (s:={x,0})]; swap
  · intro i hi; have h : i≠x ∧ i≠0 := by simpa using hi
    simp [knock,minusRows,unitRow,h.2,token,show i≠step b from h.1]
  have hx : step b ≠ (0:Cover) := hb
  unfold x; simp only [Finset.sum_pair hx]
  simp [knock,minusRows,token,hx,Ne.symm hx,unitRow,forwardC,show carry r (step b)=carryStep b r from carry_crank L ho b r,stays_here,carryStep,arrives,mid,sub_eq_add_neg]; rfl

lemma flow_movement {c f : Side} [Fintype m] [DecidableEq m] (g : Ratio c f) (A : Cross g.count m n) (s : List Axis)
    (hp : Odd g.count.val) (hs : ∀ u : List Axis,u.length≤s.length → Whole (advanceC g.count A u)) :
    installed g (advanceC g.count A s)=motion m f s * installed g A := by
  induction s with
  | nil => rw [advanceC,motion_zero,Matrix.one_mul]
  | cons i s ih => rw [advanceC,← move_forward hp, motion_walk, Whole.from_fine g (knock_whole m i) (hs s (by simp)), ih fun u hu => hs u (by simp; omega),Matrix.mul_assoc]

/-- Take the real-axis (Hadamard) quotient in order. Use only on actual
spectra divisible by the whole list with continuous quotients; no result
promised about values of arbitrary regular spectra e.g. at q_i=0. -/
def proceeds (A : Row m n) : List Axis → Row m n
| [] => A
| a::l => proceeds (dashAxis a A) l
lemma proceeds_whole {A : Row m n} (h : Whole A) (s : List Axis) : Whole (proceeds A s) := by
  induction s generalizing A with
  | nil => exact h
  | cons a s ih => exact ih (dash_whole h a)
lemma list_cont (s : List Axis) : Continuous fun p : Momentum => listChip p s := by
  induction s with
  | nil => simpa only [listChip,List.map_nil,List.prod_nil] using (continuous_const : Continuous fun _ : Momentum => (1:ℂ))
  | cons a s ih =>
    have he : (fun p => listChip p (a::s))=(fun p => chip (p a)*listChip p s) := by simp [listChip]
    rw [he]; exact Continuous.mul (by unfold chip; fun_prop) ih
lemma real_divides (s : List Axis) {A : Row m n} (h : Whole A) {g : Momentum → Matrix m n ℂ}
    (hg : ∀ p∈baseCube, ContinuousAt g p) (hh : ∀ p∈baseCube,A.read p=listChip p s • g p) :
    ∀ p∈baseCube,(proceeds A s).read p=g p := by
  induction s generalizing A with
  | nil => simpa only [listChip,List.map_nil,List.prod_nil,one_smul,proceeds] using hh
  | cons a l ih =>
    apply ih (dash_whole h a)
    intro p hp
    let f (p : Momentum) := listChip p l • g p
    have hx (p : Momentum) (hp : p ∈ baseCube) : A.read p=q p a • f p := by rw [hh p hp]; simp [listChip,switch_axis,f,smul_smul]
    apply renew_q _ f a _ _ _ p hp
    · exact fun p => read_here (dashAxis a A) (dash_whole h a)
    · intro p hp; unfold f; exact (list_cont l).continuousAt.smul (hg p hp)
    intro p hp hc
    apply smul_right_injective _ hc
    have he := read_part h a hp.1
    have ht := hx (update p a 0) (bank_blank hp a); rw [switch_axis,Function.update_self,chip_origin,zero_smul] at ht
    rw [ht,sub_zero] at he
    exact he.trans (hx p hp)
lemma proceeds_stock {α β : ι → Type*} {w : ι → ℝ} {A : ∀ i, Row (α i) (β i)} (h : Stock w A) (s : List Axis) : Stock w (fun i => proceeds (A i) s) := by
  induction s generalizing A with
  | nil => exact h
  | cons a s ih => exact ih (dash_stock h a)
end YM.Next.Free

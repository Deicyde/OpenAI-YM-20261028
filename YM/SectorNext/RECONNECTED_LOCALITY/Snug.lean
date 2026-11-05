import YM.SectorNext.RECONNECTED_LOCALITY.Lodge

set_option warningAsError false

/-! # Full Gaussian precision identity at the actual labels

Given earlier E supplies (incl large-B Agenda), exact absolute HasSum BEFORE
Mayer factors. $Z$ on positive coordinates with common orientation/color,
no small-z or period restriction, no determinant formula needed here (that's
separate). The root chosen in `Aligned` need NEVER be denoted by this inverse.
Inactive entries automatically included. -/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect.Ice
open Function Matrix Finset Lattice RG Wilson Bind Window Filter MeasureTheory
open scoped BigOperators Classical
variable {I J κ : Type*} [Fintype I] [Fintype κ]
private abbrev Pa (I κ : Type*) := Matrix (I×κ) (I×κ) ℝ
variable {A H : Pa I κ}

-- plain Schur strict on entries enough for literal inverse *entry* series,
-- irrespective of order of norm identification.
lemma backlog [Fintype J] [DecidableEq J] (A C : Matrix J J ℝ) (g : Radar J) {m k : ℝ}
    (h : Deck g (1-A*C) 0 k) (he : Deck g A 0 m) (hk : 0≤k) (hr : k<1) (hm : 0≤m)
    (hi : IsUnit A.det) (hc : IsUnit C.det) (i j : J) :
    HasSum (fun n:ℕ=>((1-A*C)^(n+1)*A) i j) ((C⁻¹-A) i j) := by
  let K:=1-A*C
  let f (n:ℕ) := K^n*A
  have hd (n:ℕ) : Deck g (f n) 0 (k^n*m) := by
    induction n with
    | zero => simpa [f] using he
    | succ n ih =>
      unfold f; rw [pow_succ',Matrix.mul_assoc,pow_succ',mul_assoc]; exact h.mul ih le_rfl hk (by positivity)
  have hg := summable_geometric_of_lt_one hk hr
  have hy x y : Summable (fun i=>(f i x y)) := Summable.of_norm_bounded (hg.mul_right m) fun n=> by
    simpa only [Real.norm_eq_abs,bill_zero] using (hd n).each x y
  let B : Matrix J J ℝ := of fun x y=> ∑' n,f n x y
  have hb : K*B + A=B := by
    ext x y; rw [Matrix.add_apply]; unfold B; simp_rw [mul_apply,of_apply,←tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun i _=> (hy i y).mul_left _),add_comm]
    symm
    have h0 : f 0=A:=by simp [f]
    have h1 (n : ℕ) : f (n+1)=K*f n := by dsimp [f]; rw [pow_succ',Matrix.mul_assoc]
    simpa only [h0,h1,mul_apply] using (hy x y).tsum_eq_zero_add
  unfold K at hb; rw [sub_mul,one_mul,sub_add] at hb -- ?
  have hh : A*C*B=A := by exact sub_eq_zero.mp (by grind)
  rw [Matrix.mul_assoc] at hh
  have hl : C*B=1 := by
    calc
      _ = A⁻¹*(A*(C*B)) := by rw [← Matrix.mul_assoc,nonsing_inv_mul _ hi,one_mul]
      _ = _ := by rw [hh,nonsing_inv_mul _ hi]
  have ht : B=C⁻¹ := by calc
    _ = C⁻¹*(C*B) := by rw [← Matrix.mul_assoc,nonsing_inv_mul _ hc,one_mul]
    _ = _ := by rw [hl,mul_one]
  have h0 : f 0=A:=by simp [f]
  have he := (hy i j).tsum_eq_zero_add
  have hm : (∑' b,f b i j)=C⁻¹ i j := congr_fun (congr_fun ht i) j
  rw [hm,h0] at he
  rw [Matrix.sub_apply,show C⁻¹ i j-A i j=∑' b,f (b+1) i j by linarith]
  exact ((hy i j).comp_injective (fun x y (h : x+1=y+1)=> Nat.add_right_cancel h)).hasSum

 -- needs Decidable

local notation "M" => Matrix (I×κ) (I×κ) ℝ

-- Explicit DecidableEq via section classical: Class defeq with other witnesses?
-- see `display` proof


-- Summability or hit supplies: always achievable for large B. Tie Z law
-- to shelter by not introducing a second z-space in this theorem. Requires
-- the SAME typeclass choices throughout (use `open scoped Classical` when
-- creating the alignment, or pass reindexed DecidableEq transports separately).
variable {ι η : Type*} {Y : η→Type*} [∀ i,MeasurableSpace (Y i)] {G : Gauge} {c:Side}
variable {X : Form G c ι (I×κ) Y} {tag : η→Site c} {u : I→Site c}
variable {D : Slip G c ι Y → Matrix (I×κ) (I×κ) ℝ} {W : I×κ→Finset (I×κ)}
variable {σ k δ b ν V E : ℝ} {r t r0 B P d : ℕ}


end YM.SectorNext.Reconnect.Ice

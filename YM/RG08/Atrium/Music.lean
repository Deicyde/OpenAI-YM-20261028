import YM.RG08.Atrium.Ibis
/-! # Tilts & finite nilpotent actual matrices. Triangular calculation before existential.
 Same-slot price. Not claiming sharp inverse coercivity of any matrix tickets.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Atrium
 set_option linter.unusedSectionVars false
open Function Finset Jetty Lattice Isles Forms Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Spar Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Yurt Halo Trill
open RG Precision Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius PowerSeries Matrix
variable {I G:Type}{d n p l e D k:ℕ}
-- any horizon placement order.
structure Parade (I:Type)(d:ℕ) where
 slot:I→ℕ
 act:I→ℕ
 org(i:I):slot i≤d
 led(i:I):act i≤d
variable (H:Parade I d)
def tick (i:I):=(d+1)*(d-H.slot i)+H.act i
def hops (i j:I):Prop:=H.slot i < H.slot j ∨ H.slot i=H.slot j ∧ H.act j < H.act i
lemma tick_rank {i j:I}:hops H i j ↔ tick H j<tick H i:=by
 rcases lt_trichotomy (H.slot i) (H.slot j) with he|he|he
 · have hh:(d-H.slot j)+1≤d-H.slot i:=by have :=H.org j; omega
   have ht:= Nat.mul_le_mul_left (d+1) hh;rw [mul_add,mul_one] at ht
   exact iff_of_true (Or.inl he) (by unfold tick;have := H.led j;omega)
 · unfold tick hops;rw [he];simp
 have hh:(d-H.slot i)+1≤d-H.slot j:=by have :=H.org i;omega
 have ht:=Nat.mul_le_mul_left (d+1) hh;rw [mul_add,mul_one] at ht
 apply iff_of_false
 · unfold hops;omega
 unfold tick;have :=H.led i;omega
lemma tick_bound (i:I):tick H i≤ (d+1)*d+d:=by unfold tick;gcongr;exact Nat.sub_le d (H.slot i);exact H.led _

-- ordered ordinary matrices
abbrev Hearth (I:Type):=Matrix I I ℝ
/-- A(E) implies unchanged slot component triangular etc. W score in Off. D(j) true diag scale here real. -/
def Harsh (A:Hearth I):Prop:=∀ i j,A i j≠0→ hops H i j
def Ordered (A:Hearth I):Prop:=∀ i j,A i j≠0→ i=j∨hops H i j
lemma Ordered.slots {A:Hearth I}(he:Ordered H A){i j:I}(h:A i j≠0):H.slot i ≤ H.slot j:=by rcases he _ _ h with h|h|⟨h,h'⟩;subst j;rfl; exact h.le; exact h.le
lemma Harsh.ordered {A:Hearth I}(he:Harsh H A):Ordered H A:=fun _ _ h=>.inr (he _ _ h)
variable [Fintype I]
lemma Ordered.mul{A B:Hearth I}(hA:Ordered H A)(hB:Ordered H B):Ordered H (A*B):=by
 intro i j he
 obtain ⟨k,_,hk⟩:=exists_ne_zero_of_sum_ne_zero (by simpa only [Matrix.mul_apply] using he)
 obtain rfl|ha:=hA i k (left_ne_zero_of_mul hk);exact hB i j (right_ne_zero_of_mul hk)
 obtain rfl|hb:=hB k j (right_ne_zero_of_mul hk);exact .inr ha
 exact .inr ((tick_rank H).mpr (((tick_rank H).mp hb).trans ((tick_rank H).mp ha)))
lemma Ordered.sum {s:Finset G}{M:G→Hearth I}(hM:∀ g∈s,Ordered H (M g)):Ordered H (s.sum M):=by
 intro i j he; rw [Matrix.sum_apply] at he
 obtain ⟨k,hk,hx⟩:=exists_ne_zero_of_sum_ne_zero he;exact hM k hk i j hx
lemma Ordered.one : Ordered H (1:Hearth I):=by intro i j he;rw [Matrix.one_apply] at he;split at he;exact .inl (by assumption);exact (he rfl).elim
lemma Ordered.pow {A:Hearth I}(hA:Ordered H A)(n:ℕ):Ordered H (A^n):=by
 induction n with
 | zero=>exact pow_zero A ▸ one H -- rw
 | succ n ih=>rw [pow_succ]; exact ih.mul H hA -- dot?
lemma Ordered.neg {A:Hearth I}(he:Ordered H A):Ordered H (-A):=by intro i j hx;exact he i j (by rw [Matrix.neg_apply] at hx; simpa using hx)
lemma Harsh.neg {A:Hearth I}(he:Harsh H A):Harsh H (-A):=by intro i j hx;exact he i j (by rw [Matrix.neg_apply] at hx;simpa using hx)
lemma Harsh.pow {A:Hearth I}(he:Harsh H A)(n:ℕ)(i j:I)(h:(A^n) i j≠0):tick H j+n≤ tick H i:=by
 induction n generalizing i j with
 | zero=>rw [pow_zero,Matrix.one_apply] at h;split at h;rename_i hi;subst hi;rfl;exact (h rfl).elim
 | succ n ih=>rw [pow_succ,Matrix.mul_apply] at h; obtain ⟨k,_,hk⟩:=exists_ne_zero_of_sum_ne_zero h; have ht:=ih _ _ (left_ne_zero_of_mul hk);have :=(tick_rank H).mp (he _ _ (right_ne_zero_of_mul hk));omega
def turns (d:ℕ):ℕ:=(d+1)*d+d+1
lemma Harsh.nil {A:Hearth I}(he:Harsh H A):A^(turns d)=0:=by ext i j :1; exact Classical.not_not.mp fun h=>by have ht:=he.pow H (turns d) i j h;have := tick_bound H i;unfold turns at ht;omega

def Fade (k:I→ℝ):Hearth I:=Matrix.diagonal k
/-- slot-first, inverse diagonal pays inverse scale in exact leading. -/
structure Arrow (H:Parade I d)(a:I→ℝ)(M:Hearth I):Prop where
 ordered0: Ordered H M
 each(i:I):M i i=a i
 positive(i:I):0<a i
lemma Fade_order (a:I→ℝ):Ordered H (Fade a):=by intro i j hh; unfold Fade at hh;rw [Matrix.diagonal_apply] at hh;split at hh;exact .inl (by assumption);exact (hh rfl).elim
variable {M:Hearth I}{a:I→ℝ}
def finger (M:Hearth I)(a:I→ℝ):Hearth I:=M*Fade (fun i=>(a i)⁻¹)-1
lemma finger_h (he:Arrow H a M):Harsh H (finger M a):=by
 have ht:=Ordered.mul H he.ordered0 (Fade_order H (fun i=>(a i)⁻¹))
 intro i j hx
 by_cases hi:i=j
 · subst j;rw [finger,Matrix.sub_apply,Matrix.one_apply_eq,Fade,Matrix.mul_diagonal,he.each,mul_inv_cancel₀ (he.positive i).ne',sub_self] at hx;exact (hx rfl).elim
 rw [finger,Matrix.sub_apply,Matrix.one_apply_ne hi,sub_zero] at hx; exact (ht _ _ hx).resolve_left hi
lemma fade_inv (a:I→ℝ)(hA:∀ i,a i≠0): Fade a * Fade (fun i=>(a i)⁻¹)=1:=by
 ext i j :1;unfold Fade;rw [Matrix.mul_diagonal,Matrix.diagonal_apply,Matrix.one_apply];split_ifs with he;subst j;rw [mul_inv_cancel₀ (hA i)];simp

def mosaic (d:ℕ)(a:I→ℝ)(M:Hearth I):Hearth I:=∑ i∈range (turns d),(-(finger M a))^i
def acrossF (d:ℕ)(a:I→ℝ)(M:Hearth I):Hearth I:=Fade (fun i=>(a i)⁻¹)*mosaic d a M
lemma seq (M:Hearth I)(n:ℕ):(1-M)*(∑ i∈range n,M^i)=1-M^n∧ (∑ i∈range n,M^i)*(1-M)=1-M^n:=by
 induction n with
 | zero=>simp
 | succ n ih=>rw [sum_range_succ,mul_add,add_mul,ih.1,ih.2,sub_mul,mul_sub,one_mul,mul_one,pow_succ' M,← pow_succ,← pow_succ'];constructor <;> abel
lemma acrossF_held (he:Arrow H a M): Ordered H (acrossF d a M):=by
 unfold acrossF; exact Ordered.mul H (Fade_order H _) (Ordered.sum H (fun i _=>Ordered.pow H (Harsh.ordered H (Harsh.neg H (finger_h H he))) i))
lemma acrossF_inverse (he:Arrow H a M):
 M*acrossF d a M=1∧acrossF d a M*M=1:=by
 let N:= -finger M a
 have hh:N^turns d=0:= Harsh.nil H (Harsh.neg H (finger_h H he))
 have H':1-N=M*Fade (fun i=>(a i)⁻¹):=by unfold N finger;abel
 have h:=seq N (turns d);rw [hh,sub_zero,H'] at h
 let F:=mosaic d a M
 let D:=Fade fun i=>(a i)⁻¹; let B:=Fade a
 change M*D*F=1 ∧ F*(M*D)=1 at h
 have hs:D*B=1:=by
    have ht:=fade_inv (fun i=>(a i)⁻¹) (fun i=>inv_ne_zero (he.positive i).ne')
    simpa only [inv_inv] using ht
 constructor;unfold acrossF;rw [←mul_assoc];exact h.1
 change D*F*M=1
 calc
   D*F*M=D*(F*(M*D))*B:=by simp only [mul_assoc,hs,mul_one]
   _=1:=by rw [h.2,mul_one,hs]

-- cost: pre normalized same-slot; post across slots, important power. Can skip one post constant in inverse LP.
def pre (A:Hearth I)(C:ℝ):Prop:= ∀ i j,H.slot i=H.slot j→ |A i j|≤C
def post (A:Hearth I)(C:ℝ):Prop:= ∀ i j,|A i j|≤C
lemma pre.mul {A B:Hearth I}{C D:ℝ}(hA:Ordered H A)(hB:Ordered H B)(he:pre H A C)(hg:pre H B D)(hc:0≤C)(hd:0≤D):pre H (A*B) (Fintype.card I*C*D):=by
 intro i j hi;rw [Matrix.mul_apply]
 refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (g:=fun _=>C*D) (fun k _=>?_)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul,mul_assoc]))
 rw [abs_mul]; by_cases hh:A i k=0;rw [hh,abs_zero,zero_mul];positivity
 by_cases ht:B k j=0;rw [ht,abs_zero,mul_zero];positivity
 have hv:H.slot i=H.slot k:=le_antisymm (Ordered.slots H hA hh) ((Ordered.slots H hB ht).trans_eq hi.symm)
 exact mul_le_mul (he i k hv) (hg k j (hv.symm.trans hi)) (abs_nonneg _) hc
lemma post.mul {A B:Hearth I}{C D:ℝ}(he:post A C)(hg:post B D)(hc:0≤C):post (A*B) (Fintype.card I*C*D):=by
 intro i j;rw [Matrix.mul_apply];refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (g:=fun _=>C*D) (fun k _=>?_)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul,mul_assoc]))
 rw [abs_mul];exact mul_le_mul (he ..) (hg ..) (abs_nonneg _) hc
lemma post.sup {A B:Hearth I}{C D:ℝ}(he:post A C)(ht:post B D):post (A+B) (C+D):=fun i j=>(abs_add_le ..).trans (add_le_add (he i j) (ht i j))
lemma post.diff {A:Hearth I}{C:ℝ}(he:post A C):post (-A) C:=fun i j=>by rw [Matrix.neg_apply,abs_neg];exact he i j

-- Pair ledger use post Δ at any slots, pre leading preserved. matrix shell d before stage J. LF. D diag may large, require one for lower.
lemma fin_pre {C:ℝ} (he:Arrow H a M)(hs:∀ i j,H.slot i=H.slot j→|M i j| ≤ C*a j):pre H (finger M a) (C+1):=by
 intro i j hi;rw [finger,Matrix.sub_apply,Fade,Matrix.mul_diagonal]
 refine (abs_sub _ _).trans (add_le_add ?_ ?_)
 · rw [abs_mul,abs_of_pos (inv_pos.mpr (he.positive _))];exact (mul_le_mul_of_nonneg_right (hs i j hi) (inv_pos_of_pos (he.positive _)).le).trans_eq (by rw [mul_inv_cancel_right₀ (he.positive j).ne'])
 rw [Matrix.one_apply];split <;> norm_num
-- universal pre bill before L & compatible with diagonal variation. exponent on inverse entry T0^-1 occurs also post precursor. diagonals NOT allowed >1 in products. statements mechanical.
lemma powers_pre {A:Hearth I}{C:ℝ}(ht:Ordered H A)(hf:pre H A C)(hc:0≤C)(n:ℕ): pre H (A^n) (((Fintype.card I:ℝ)*C)^n):=by
 induction n with
 | zero=>rw [pow_zero,pow_zero]; intro i j _;rw [Matrix.one_apply];split <;> norm_num
 | succ n ih=> rw [pow_succ,pow_succ];convert pre.mul H (Ordered.pow H ht n) ht ih hf (pow_nonneg (by positivity) _) hc using 1;ring
lemma powers_post {A:Hearth I}{C:ℝ}(hf:post A C)(hc:0≤C)(n:ℕ): post (A^n) (((Fintype.card I:ℝ)*C)^n):=by
 induction n with
 | zero=>rw [pow_zero,pow_zero]; intro i j;rw [Matrix.one_apply];split <;> norm_num
 | succ n ih=> rw [pow_succ,pow_succ];convert post.mul ih hf (pow_nonneg (by positivity) _) using 1;ring

def plum (I:Type)[Fintype I](d:ℕ)(C:ℝ):ℝ:=∑ i∈range (turns d),((Fintype.card I:ℝ)*(C+1))^i
lemma plum_nn {C:ℝ}(he:0≤C):0≤plum I d C:=sum_nonneg fun _ _=>by positivity
lemma plum_wage (I:Type)[Fintype I](d:ℕ): Wage (plum I d):=by
 apply Wage.sum
 intro i _
 induction i with
 | zero=> simpa using Wage.constant 1 zero_le_one
 | succ i ih=>
    let P:ℝ→ℝ:=fun x=> (Fintype.card I:ℝ)*(x+1)
    have hv: Wage P:= (Wage.constant _ (by positivity)).mul (Wage.input.add (Wage.constant 1 zero_le_one))
    have ht: Wage (fun x=>P x^i):=ih (by simp only [mem_range] at *;omega) -- memory hi implicit? intro named _ ignored bound not generalized!
    simp_rw [pow_succ];exact ht.mul hv
lemma inverse_price {C:ℝ} (hc:0≤C)(he:Arrow H a M)(hs:∀ i j,H.slot i=H.slot j→|M i j| ≤ C*a j)(i j:I)(hx:H.slot i=H.slot j):
 |acrossF d a M i j| ≤ (a i)⁻¹*plum I d C:=by
 let F:=finger M a; have h:pre H (-F) (C+1):=fun i j hh=>by rw [Matrix.neg_apply,abs_neg];exact fin_pre H he hs _ _ hh
 have ht:= Ordered.neg H ((Harsh.ordered H (finger_h H he)):Ordered H F)
 rw [acrossF,Fade,Matrix.diagonal_mul,abs_mul,abs_inv,abs_of_pos (he.positive _)];apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (he.positive _)).le
 unfold mosaic;rw [Matrix.sum_apply];exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _=>powers_pre H ht h (by linarith) k i j hx)
lemma inv_diag (he:Arrow H a M)(i j:I)(hs:H.slot i=H.slot j)(hx:H.act i≤H.act j):acrossF d a M i j=if i=j then (a i)⁻¹ else 0:=by
 rw [acrossF,Fade,Matrix.diagonal_mul,mosaic,Matrix.sum_apply];let P:= -finger M a; have h:=Harsh.neg H (finger_h H he); change _ * (∑ c∈range (turns d),(P^c) i j)=_
 rw [sum_eq_single 0];rw [pow_zero,Matrix.one_apply];split <;> simp
 · intro b _ hb;apply Classical.not_not.mp;intro hk;have ht:=h.pow H b i j hk; unfold tick at ht;rw [hs] at ht;omega
 intro hh;exfalso;apply hh;rw [mem_range]; exact Nat.zero_lt_succ _
lemma inv_board {C:ℝ}(hc:1≤C)(he:Arrow H a M)(hp:post M C)(h1:∀ i:I,1≤a i):post (acrossF d a M) (plum I d C):=by
 intro i j; let P:= -finger M a;let E:=C+1
 have ht(i): |(a i)⁻¹|≤1:=by rw [abs_of_pos (inv_pos.mpr (he.positive _))];exact inv_le_one_of_one_le₀ (h1 i)
 have hA:post P E:=by
    intro i j;unfold P finger;rw [Matrix.neg_apply,abs_neg,Matrix.sub_apply,Fade,Matrix.mul_diagonal];apply (abs_sub _ _).trans (add_le_add _ _)
    · rw [abs_mul];exact (mul_le_mul (hp i j) (ht j) (abs_nonneg _) (by linarith)).trans_eq (mul_one _)
    rw [Matrix.one_apply];split <;> norm_num
 rw [acrossF,Fade,Matrix.diagonal_mul,abs_mul,mosaic,Matrix.sum_apply];apply (mul_le_of_le_one_left (abs_nonneg _) (ht i)).trans ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _=>?_));exact powers_post hA (by unfold E; linarith) k i j
end YM.RG08.Atrium

import YM.RG08.Atrium.Music
/-! # Toeplitz layer calculus and triangular assembly full PSC. Both inverses and
 upper price formulas. Allows variation of step matrices, not Wick/post read here -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Atrium
open Function Finset Jetty Lattice Isles Forms Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Spar Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Yurt Halo Trill
open RG Precision Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius PowerSeries Matrix
variable {I:Type}{G:Gauge}{d n p l e D k:ℕ}

abbrev Sock (I:Type):=Matrix I I Dig
def dusk (e:ℕ)(M:Sock I):Hearth I:=Matrix.of fun i j=>tap e (M i j)
lemma dusk_apply (e:ℕ)(M:Sock I)(i j:I):dusk e M i j=tap e (M i j):=rfl
def land (M:ℕ→Hearth I): Sock I:=Matrix.of fun i j=>PowerSeries.mk fun e=>M e i j
lemma land_value (M:ℕ→Hearth I)(i j:I)(e:ℕ):tap e (land M i j)=M e i j:=PowerSeries.coeff_mk e (fun e=>M e i j)
def ink (M:Sock I):=dusk 0 M
lemma dusk_land (M:ℕ→Hearth I)(e:ℕ): dusk e (land M)=M e:= Matrix.ext fun _ _=>land_value ..
lemma land_dusk (M:Sock I):land (fun e=>dusk e M)=M:=by ext i j k;apply land_value
lemma dusk_plus (e:ℕ)(M N:Sock I): dusk e (M+N)=dusk e M +dusk e N:=Matrix.ext fun i j=>map_add (PowerSeries.coeff _) (M i j) (N i j)
lemma dusk_diff (e:ℕ)(M N:Sock I): dusk e (M-N)=dusk e M - dusk e N:=Matrix.ext fun i j=>map_sub (PowerSeries.coeff _) (M i j) (N i j)
lemma dusk_one (e:ℕ): dusk e (1:Sock I)=if e=0 then 1 else 0:=by
 ext i j :1;rw [dusk_apply,Matrix.one_apply];split_ifs <;> simp [*,tap,Matrix.one_apply]
variable [Fintype I]
lemma dusk_mul (e:ℕ)(M N:Sock I):dusk e (M*N)=∑ a∈range (e+1),dusk a M*dusk (e-a) N:=by
 ext i j :1;rw [dusk_apply,Matrix.mul_apply,tap,map_sum,Matrix.sum_apply];simp_rw [Matrix.mul_apply]; rw [sum_comm];apply sum_congr rfl;intro a _;exact tap_mul (M i a) (N a j) e

-- filtration general. No slope. At e=0 need additionally weight ordering.
def Wax (H:Parade I d)(e:ℕ)(A:Hearth I):Prop:=∀ i j,H.slot j+e < H.slot i→A i j=0
lemma Wax.mul {H:Parade I d}{A B:Hearth I}(he:Wax H e A)(hk:Wax H k B):Wax H (e+k) (A*B):=by
 intro i j hi;rw [Matrix.mul_apply];apply sum_eq_zero;intro l _; by_cases ht:H.slot l+e<H.slot i;rw [he i _ ht,zero_mul];rw [hk _ _ (by omega),mul_zero]
def Drip (H:Parade I d)(M:Sock I):Prop:=∀ n,Wax H n (dusk n M)
 omit [Fintype I] in
lemma wax_ord {H:Parade I d}{A:Hearth I}(he:Ordered H A):Wax H 0 A:=fun i j hj=> Classical.not_not.mp fun hp=>by have ht:=Ordered.slots H he hp;omega

-- universal inverse, achieved whenever constant inverts. 
def salon (M:Sock I)(B:Hearth I):ℕ→(ℕ→Hearth I)
 | 0=>fun _=>B
 | n+1=>Function.update (salon M B n) (n+1) (-(∑ i∈range (n+1),salon M B n i*dusk (n+1-i) M)*B)
def deputy (M:Sock I)(B:Hearth I):Sock I:=land fun i=>salon M B i i
lemma salon_held (M:Sock I)(B:Hearth I)(n i:ℕ)(hi:i≤n):salon M B n i=salon M B i i:=by
 induction n,hi using Nat.le_induction with
 | base=>rfl
 | succ n he ih=>rw [salon,update_of_ne (by omega),ih]
def tension (M Q:Sock I)(n:ℕ):Hearth I:= ∑ i∈range (n+1),dusk i Q *dusk (n+1-i) M
lemma emboss (M:Sock I)(B:Hearth I)(n:ℕ): dusk (n+1) (deputy M B) = -tension M (deputy M B) n * B:=by
 unfold deputy;rw [dusk_land,salon,update_self];congr 2;unfold tension;apply sum_congr rfl;intro i hi;rw [dusk_land,salon_held M B n _ (by simpa only [mem_range,Nat.lt_succ_iff] using hi)]
lemma deputy_home (M:Sock I)(B:Hearth I):dusk 0 (deputy M B)=B:=by unfold deputy;rw [dusk_land];rfl
/-- Left inverse for Toeplitz, generic PSC. -/
lemma deputy_trained (M:Sock I)(B:Hearth I)(he:B*dusk 0 M=1): deputy M B*M=1:=by
 rw [← land_dusk (deputy M B * M),← land_dusk (1:Sock I)]; congr 1;funext n
 rw [dusk_mul,dusk_one]
 cases n with
 | zero=>simpa [deputy_home] using he
 | succ n=>rw [sum_range_succ,if_neg (by omega),Nat.sub_self,emboss M B n,mul_assoc,he,mul_one];exact add_neg_cancel _
 omit [Fintype I] in
lemma dusk_trans (M:Sock I)(e:ℕ): dusk e (Matrix.transpose M)=(dusk e M).transpose:=rfl
lemma deputy_full (M:Sock I)(B:Hearth I)(he:B*dusk 0 M=1)(hh:dusk 0 M*B=1):M*deputy M B=1:=by
 let M':=Matrix.transpose M;let B':=Matrix.transpose B; let Q:=deputy M' B'; let V:=Matrix.transpose Q
 have hf:B'*dusk 0 M'=1:=by unfold M' B'; rw [dusk_trans,← Matrix.transpose_mul,hh,Matrix.transpose_one]
 have hx:M*V=1:=by
    rw [show M*V=(Q*M').transpose from by rw [Matrix.transpose_mul];simp [M',V]]
    rw [show Q*M'=1 from deputy_trained _ _ hf,Matrix.transpose_one]
 have hz:deputy M B=V:= calc
    _= deputy M B * (M*V):=by rw [hx,mul_one]
    _=_:=by rw [←mul_assoc,deputy_trained M B he,one_mul]
 rw [hz];exact hx
lemma deputy_preserves (M:Sock I)(B:Hearth I){H:Parade I d}(hB:Ordered H B)(hM:Drip H M):Drip H (deputy M B):=by
 let N:=deputy M B;intro n
 induction n using Nat.strong_induction_on with
 | h n ih=>cases n with
   | zero=> rw [deputy_home];exact wax_ord hB
   | succ n=> rw [emboss];let F:=tension M N n
              have ht: Wax H (n+1) F:=by
                intro i j hi;unfold F tension;rw [Matrix.sum_apply];apply Finset.sum_eq_zero;intro k hk
                have hh:=mem_range.mp hk
                have he : H.slot j+(k+(n+1-k))<H.slot i:=by omega
                exact Wax.mul (ih k hh) (hM _) _ _ he
              rw [neg_mul] -- generic neg_mul
              intro i j hi
              rw [Matrix.neg_apply, Wax.mul ht (wax_ord hB) i j (by omega),neg_zero]
-- lock grade wrapper exact - at any length L. use inverse operator with cut grades in matrix.
def street {X:Labels.Frame G d}:Parade (Accent X) d where
 slot:=octave
 act:=gamut
 org:=octave_le
 led:=gamut_le
variable {X:Labels.Frame G d}
lemma drip_cover (M:Playbook X):Drip street M ↔ Cloth M:=Iff.intro (fun h i j e he=>h e i j he) (fun h e i j he=>h i j e he)
def evacuate (M:Playbook X)(a:Accent X→ℝ):Playbook X:=deputy M (acrossF d a (ink M))
structure Wins (M B:Playbook X):Prop where
 left:B*M=1
 right:M*B=1
 leading0Cloth: Cloth B
 ordered: Ordered street (ink B)
theorem evacuation {M:Playbook X}{a:Accent X→ℝ}(he:Cloth M)(hp:Arrow street a (ink M)):Wins M (evacuate M a):=by
 let F:=acrossF d a (ink M)
 obtain ⟨hV,hW⟩:=acrossF_inverse street hp
 have h:=acrossF_held street hp
 refine ⟨deputy_trained M F hW,deputy_full M F hW hV, (drip_cover _).mp (deputy_preserves _ F h ((drip_cover _).mpr he)),?_⟩
 unfold evacuate ink;rw [deputy_home];exact h
end YM.RG08.Atrium

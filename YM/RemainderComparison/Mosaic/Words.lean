import YM.MergeProof.Emit

/-!
# Connected and forced copies: combined real & marked world

Arbitrarily many layout choices emitted, with marker bookkeeping.
Registration fixes capacity `Jm.Census τ`, β-dependent costs & root sites.
Real alphabet also admits non-nil amplitudes (assign 1 for `i∉A`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Mosaic
open Function Filter Finset MeasureTheory Marker Merge Switch
open scoped Topology BigOperators Classical
structure Verse (ι U: Type) where
  letters : Multiset ι
  utter : U→ℝ
namespace Verse
variable {ι U : Type} (V : Verse ι U) (A:Set ι) (r:ι→ℝ)
open Multiset (map)

def stock := (V.letters.map r).prod
def emit u:= V.stock r * V.utter u

def phrase (f:ι→Ways ι) (s:Multiset ι) : Ways ι := (s.map f).prod

def roll (i:ι) : Ways ι:= if i∈A then click {i} (1:ℝ) else 1
def wave (t:ℝ)(v:Finset ι):ι→ℝ:= fun i=> r i * roll A i t v

def opera (u:U): Ways ι:= fun t v=> V.emit (wave A r t v) u
lemma factor {ρ:Type*} [CommMonoid ρ] (f g:ι→ρ) (s:Multiset ι): (s.map fun i=>f i*g i).prod = (s.map f).prod*(s.map g).prod:=by
  induction s using Multiset.induction_on with
  | empty=>simp
  | cons i s ih=> simp only [Multiset.map_cons,Multiset.prod_cons];rw [ih]; ac_rfl
lemma ahead (f:ι→Ways ι) (s:Multiset ι) (t:ℝ)(v:Finset ι): (s.map fun i=>f i t v).prod=phrase f s t v:=by
  unfold phrase; induction s using Multiset.induction_on with
  | empty=>simp
  | cons i s he=>simp only [Multiset.map_cons,Multiset.prod_cons,Pi.mul_apply]; rw [he]

def still (u:U) : Ways ι:= fun _ _=> V.emit r u
lemma assembled (u:U): V.opera A r u= V.still r u * phrase (roll A) V.letters:=by
  funext t v; unfold opera still emit stock wave; rw [factor]; rw [ahead]; exact mul_right_comm ..

variable [Fintype ι]
variable {τ:Type} [DecidableEq τ] {B:Census τ} (Z : ι→Poly B) (hr:∀ i,Z i*Z i=0)

def controls (p : Multiset ι):Poly B:= (p.map (fun i=>if i∈A then Z i else 1)).prod
lemma roll_call (i:ι)(X : Type) : Paid (fun _ : X=> roll A i) 1 ∧ sound Z (roll A i)=(if i∈A then Z i else 1):=by
  unfold roll; split
  · refine ⟨paidClick _ zero_le_one (fun _=>norm_one.le),?_⟩
    rw [gather];simp
  exact ⟨paidOne,(const_sounds Z 1).trans (by simp)⟩
lemma tune (p:Multiset ι)(U:Type) : Paid (fun _ : U=> phrase (roll A) p) 1 := by
  induction p using Multiset.induction_on with
  | empty => unfold phrase; simp only [Multiset.map_zero,Multiset.prod_zero]; exact paidOne
  | cons i s he=>
     rw [show phrase (roll A) (i ::ₘ s)= roll A i * phrase (roll A) s from (by unfold phrase; rw [Multiset.map_cons,Multiset.prod_cons])]
     have hp: Paid (fun _ : U=> roll A i) 1:= by
        unfold roll; split
        · exact paidClick _ zero_le_one (fun _=>norm_one.le)
        exact paidOne
     exact (hp.mul he).weaken (by simp)
include hr
lemma color_song (p:Multiset ι): sound Z (phrase (roll A) p)=controls A Z p:=by
  induction p using Multiset.induction_on with
  | empty => unfold phrase controls; rw [Multiset.map_zero, Multiset.map_zero,Multiset.prod_zero,Multiset.prod_zero]; exact (const_sounds Z 1).trans (by simp)
  | cons i s he=>
     have hp:= (roll_call A Z i Unit); unfold phrase controls; rw [Multiset.map_cons,Multiset.map_cons,Multiset.prod_cons,Multiset.prod_cons]; change sound Z (roll A i*phrase _ s)=_*_; rw [mul_sounds Z hr (show Models (roll A i) _ from (hp.1.works ()).choose_spec) (show Models (phrase (roll A) s) _ from ((tune A s Unit).works ()).choose_spec),hp.2];exact congr_arg (_*·) he

def paint (u:U): Poly B:= (↑(V.emit r u):ℂ) • controls A Z V.letters
lemma tones u: sound Z (V.opera A r u)= V.paint A r Z u:=by
  rw [assembled]; have hv:= Switch.constant (ι:=ι) (fun _ : Unit=> V.emit r u) (norm_nonneg _) (fun _=>le_rfl)
  rw [mul_sounds Z hr (show Models (V.still r u) _ from (hv.works ()).choose_spec) (show Models (phrase _ _) _ from ((tune A _ Unit).works ()).choose_spec),color_song A Z hr]; exact congr_arg (·*_) (const_sounds Z _)|>.trans (Poly.product_bead _ _)
omit hr
lemma earns (b:ℝ)(h:0 ≤ b)(hp:∀ u,‖V.emit r u‖ ≤ b): Paid (V.opera A r) b:=by
  rw [show V.opera A r=(V.still r)*(fun _=>phrase (roll A) V.letters) from funext fun u=>assembled ..]
  apply Paid.weaken ((Switch.constant (V.emit r) h hp).mul (tune A _ U)); simp

-- CAPACITY COST by occurrence; later bridge to Census
variable {A}
def load (A : Set ι) (L : Multiset ι): ℕ:= (L.filter (fun i=> i∈A)).card

def marked (A : Set ι) (x:ℝ):ι→ℝ:= fun i=> if i∈A then x else 1
omit [Fintype ι] in
lemma gauge (x:ℝ)(L:Multiset ι): (L.map (marked A x)).prod=x^load A L:=by
  induction L using Multiset.induction_on with
  | empty=> simp [load]
  | cons i s he=>
    rw [Multiset.map_cons,Multiset.prod_cons,he]; unfold load marked; by_cases h:i∈A
    · simp [h,pow_succ,mul_comm]
    simp [h]

omit [Fintype ι] in
lemma extension (x:ℝ): V.stock (marked A x*r) = x^load A V.letters * V.stock r :=by
  unfold stock; rw [show marked A x*r=fun i=> marked A x i*r i from rfl,factor,gauge]
omit [Fintype ι] in
lemma excursion (x:ℝ)(u:U): V.emit (marked A x*r) u= x^load A V.letters * V.emit r u:=by rw [emit,extension,mul_assoc]; rfl
omit [Fintype ι] in
lemma visitor (x:ℝ)(p:Multiset ι) : controls A (fun i=>(x:ℂ) • Z i) p = (↑(x^load A p):ℂ) • controls A Z p:=by
  induction p using Multiset.induction_on with
  | empty=> simp [load,controls]
  | cons i s he=>
    unfold controls at *; rw [Multiset.map_cons,Multiset.map_cons,Multiset.prod_cons,Multiset.prod_cons,he]; unfold load at *; by_cases h:i∈A
    · simp only [h,↓reduceIte,Multiset.filter_cons_of_pos,Multiset.card_cons,smul_mul_smul_comm]; rw [pow_succ', Complex.ofReal_mul]
    simp [h]

omit [Fintype ι] in
lemma transfer (x:ℝ)(u:U): V.paint A r (fun i=>(x:ℂ) • Z i) u = V.paint A (marked A x*r) Z u:=by
  unfold paint; rw [excursion,visitor,smul_smul,Complex.ofReal_mul]; apply congr_arg (· • _); rw [mul_comm]
end Verse
end YM.RemainderComparison.Mosaic

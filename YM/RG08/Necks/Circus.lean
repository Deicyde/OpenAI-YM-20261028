import YM.RG08.Necks.Turn
/-! # Uniform-degree receipts for *changing* stages. Exponential J exponents
 may see finite stencil horizons, tag counts, coupling/slot degree, etc., but
 must NOT vary with smoothing J in solved estimates. This exposes that layer. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Necks
open Forms Steam Finset
open scoped Classical
/-- polynomial growth of declared degree, on [1, ∞). coefficient can be logged BEFORE L
 when function type only sees preceding stage assets. -/
def Week (n:ℕ)(P:ℝ→ℝ):Prop:=∃ C:ℝ,0≤C∧∀ x≥1,0≤P x ∧ P x≤C*x^n
variable {n m k:ℕ}{P Q:ℝ→ℝ}
protected theorem Week.wage (h:Week n P):Wage P:=by obtain ⟨C,h,h'⟩:=h;exact ⟨C,n,h,h'⟩
lemma Week.nn (h:Week n P){x:ℝ}(hx:1≤x):0≤P x:=h.wage.nn hx
lemma Week.fixed (x:ℝ)(h:0≤x):Week 0 (fun _=>x):=⟨x,h,fun a _=>by simp [h]⟩
lemma Week.variable0:Week 1 id:=⟨1,zero_le_one,fun x h=>by simpa using (zero_le_one.trans h) ⟩
lemma Week.rise (h:Week n P)(hu:n ≤ m):Week m P:=by
 obtain ⟨C,hc,h⟩:=h; refine ⟨C,hc,fun x hx=>?_⟩; have hd:=h x hx;exact ⟨hd.1,hd.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hu) hc)⟩
lemma Week.add (h:Week n P)(hh:Week m Q):Week (max n m) (fun x=>P x+Q x):=by
 obtain ⟨C,hc,h⟩:= h.rise (m:=max n m) (le_max_left ..);obtain ⟨D,hd,H⟩:=hh.rise (m:=max n m) (le_max_right ..)
 exact ⟨C+D,add_nonneg hc hd,fun x hx=>⟨add_nonneg (h x hx).1 (H x hx).1,by rw [add_mul];exact add_le_add (h x hx).2 (H x hx).2⟩⟩
lemma Week.mul (h:Week n P)(hh:Week m Q):Week (n+m) (fun x=>P x*Q x):=by
 obtain ⟨C,hc,h⟩:=h;obtain ⟨D,hd,H⟩:=hh
 refine ⟨C*D,mul_nonneg hc hd,fun x hx=>⟨mul_nonneg (h x hx).1 (H x hx).1,?_⟩⟩; dsimp only;rw [pow_add,mul_mul_mul_comm];exact mul_le_mul (h x hx).2 (H x hx).2 (H x hx).1 ((h x hx).1.trans (h x hx).2)
lemma Week.pow (h:Week n P)(m:ℕ):Week (n*m) (fun x=>(P x)^m):=by
 induction m with
 | zero=>simpa using Week.fixed 1 zero_le_one
 | succ m ih=>simp_rw [pow_succ,Nat.mul_succ];exact ih.mul h
lemma Week.sum {I:Type}(s:Finset I)(f:I→ℝ→ℝ)(h:∀ i∈s,Week n (f i)):Week n (fun x=>∑i∈s,f i x):=by
 induction s using Finset.induction_on with
 | empty=>simp only [sum_empty];exact (Week.fixed _ le_rfl).rise (Nat.zero_le _)
 | insert=>simp_rw [sum_insert (by assumption)];rw [←max_self n]; apply Week.add;apply h; exact mem_insert_self ..; apply_assumption;intro i hi;exact h _ (mem_insert_of_mem hi)

def grade (P:ℝ→ℝ)(h:Wage P):ℕ:=h.choose_spec.choose
theorem grade_week (h:Wage P):Week (grade P h) P:=⟨h.choose,h.choose_spec.choose_spec⟩
-- lock exponents using actual chosen uniform functions
def portW (n e l:ℕ):ℝ→ℝ:=(portFee n e l).choose
lemma portHW (n e l:ℕ):Wage (portW n e l):=(portFee n e l).choose_spec.1
def portR (n e l:ℕ):ℕ:=grade (portW n e l) (portHW n e l)
def cometW (n d:ℕ):ℝ→ℝ:=(comet n d).choose
lemma cometHW (n d:ℕ):Wage (cometW n d):=(comet n d).choose_spec.1
def cometR(n d:ℕ):ℕ:=grade (cometW n d) (cometHW n d)
-- exponents propagating along fixed query
abbrev driveR(n:ℕ):=n+1
abbrev conquerR(n e l d:ℕ):=max (max (driveR n) (portR n e l)) (cometR n d)
def olderR(N e l:ℕ):ℕ:= (Finset.univ:Finset (Fin (N+1)×Fin (e+1))).sup fun s=>portR s.1.val s.2.val l
abbrev docketR(n e l d W0:ℕ):=max (conquerR n e l d) (olderR W0 e l)
abbrev transitR (n e l d k:ℕ):=(max (docketR n e l d (d+k)) (max 1 (docketR n e l d (d+k))))*10
end YM.RG08.Necks

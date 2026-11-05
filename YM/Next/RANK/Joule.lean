import YM.Next.RANK.Foiling
import YM.Next.RANK.Odometer

/-!
# Forecasting bills after all pre-L choices
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Asymptotics Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation Paint Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable (x : ℝ)
variable {f g : ℝ→ℝ} {a b e : ℝ}

def Volt (a : ℝ) (f : ℝ→ℝ) := ∃ c : ℝ,0 ≤ c ∧ ∀ᶠ t in atTop,|f t| ≤ c * Perch.bill a t
namespace Volt
lemma high (h : Volt a f) (hp:a≤b): Volt b f:= by
  obtain ⟨c,h,hx⟩:=h; exact ⟨c,h,hx.mono (fun i ht=> ht.trans (mul_le_mul_of_nonneg_left (Glimmer.billed i hp) h))⟩
lemma plus (h : Volt a f) (H : Volt a g): Volt a fun s=> f s+g s:= by
  obtain ⟨c,h,hx⟩:=h; obtain ⟨u,hU,hp⟩:= H; refine ⟨c+u,add_nonneg h hU,(hx.and hp).mono ?_⟩; rintro i ⟨hh,he⟩; exact (abs_add_le ..).trans ((add_le_add hh he).trans_eq (add_mul ..).symm)
lemma times (h : Volt a f) (H : Volt b g): Volt (a+b) fun s=> f s * g s:= by
  obtain ⟨c,h,hx⟩:=h; obtain ⟨u,hU,hp⟩:= H; refine ⟨c*u,mul_nonneg h hU,(hx.and hp).mono ?_⟩; rintro i ⟨hh,he⟩; rw [abs_mul]
  apply (mul_le_mul hh he (abs_nonneg _) (mul_nonneg h (Real.exp_pos _).le)).trans_eq; rw [← overlap]; ring
lemma pulse (x : ℝ) : Volt x (bill x):= ⟨1,zero_le_one, Eventually.of_forall fun s=> by simp only [one_mul,abs_of_pos (show 0<Perch.bill x s from Real.exp_pos _),le_refl]⟩
lemma scalar (x : ℝ) : Volt 0 fun _=>x:= by refine ⟨|x|,abs_nonneg x,Eventually.of_forall fun s=>?_⟩; simp only [bill,mul_zero,Real.exp_zero,mul_one,le_refl]
lemma scale (i : ℝ) (h : Volt a f) : Volt a fun t=> i*f t:=by simpa only [zero_add] using (scalar i|>.times h)
lemma power (h : Volt a f) : ∀ i : ℕ, Volt (i*a) fun t=> (f t)^i
  | 0 =>by simpa only [Nat.cast_zero,zero_mul,pow_zero] using scalar 1
  | i+1=>by simpa only [Nat.cast_add_one,add_mul,one_mul,pow_succ] using times (power h i) h
lemma met (h : Volt a f) (hb : a<b) : ∀ᶠ s in atTop, f s ≤ bill b s:= by
  obtain ⟨c,h,hx⟩:=h; filter_upwards [hx, absorb _ _ hb c] with s hp hz; exact (le_abs_self _).trans (hp.trans hz)
lemma lift {M : ℕ} (h : Volt a f) : Volt (M*a) fun s=> Common.priced (f s) M:= by
  suffices H : Volt (M*a) (fun s=> (2*((M:ℝ)+1)*f s)^M) by convert H using 1; ext i; unfold Common.priced; ring
  apply Volt.power (h.scale _) _
end Volt

namespace Purse
variable (P : Purse)
def bigZ (p : Purse) : ℝ:= (2*p.credit+3) + 8*p.taylor+10
def budget (p : Purse) := p.goal+10*p.bigZ+10 ≤ p.foil
lemma bank (P : Purse) :
    Volt (-P.foil+6*P.bigZ) (fun s=> Tapes.grant (knox s) (sends P s) (double P s) (2*P.taylor)):= by
  let x:=P.bigZ; let e:=P.credit; let a:= 2*e+3; let f:= sends P; let t:= -P.foil; let w:= double P; let d:= 2*P.taylor; let C (m:ℕ):=fun s=>Common.priced (knox s) m;let z:=fun s=> defect (knox s) (f s) (w s) d
  have hf:Volt t f:= Volt.pulse _; have hw : Volt a w:= Volt.pulse _
  have hc : Volt 1 knox:=Volt.pulse _
  have he := P.motion; change 1≤ e at he
  have ht:0≤a:=by dsimp only [a];linarith only [he]
  have hX : (8*P.taylor:ℝ)≤ x-a-10:=le_of_eq (by unfold x a e bigZ; ring)
  have hp : 0≤ x:= by linarith [Nat.cast_nonneg (α:=ℝ) P.taylor]
  have hb : t≤0:=neg_nonpos.mpr P.positive
  have HM (k : ℕ) : Volt (k:ℝ) (C k):= by simpa only [mul_one] using! (Volt.lift (M:=k) hc)
  have hd : (d:ℝ)=2*(P.taylor:ℝ):=by push_cast [d];rfl
  have hy : Volt (2*x+t) z := by apply (hw.times (((hc.power d).scale d).times hf)).high; linarith only [hd,hX,hp]
  let v:= fun s=> capZ (knox s) d (w s)
  let u:=fun s => grant₁ (knox s) (f s) (w s) d; let r:= fun s=> grant₂ (knox s) (f s) (w s) d
  have hi:Volt x v:= (hw.times (HM d)).high (by linarith only [hX,hd,Nat.cast_nonneg (α:=ℝ) P.taylor])
  have hq:Volt (t+2*x) u:= by
    unfold u grant₁; apply Volt.plus (Volt.plus (Volt.plus (hy.high (by linarith only)) ((hf.times ((hw.power 2).times (HM (2*d)))).high ?_)) (hf.high (by linarith only [hp]))) ((hw.times (hf.times (HM d))).high ?_)
    all_goals push_cast; linarith only [hX,hp,hd,Nat.cast_nonneg (α:=ℝ) P.taylor]
  have hv : Volt (t+6*x) r:= by
    unfold r grant₂; apply Volt.plus (Volt.plus (Volt.plus (((hi.scale 2).times hy).high (by linarith only [hp])) ((hf.times (((hw.power 2).power 2).times (HM (2*(2*d))))).high ?_)) ((hf.scale 2).high (by linarith only [hp]))) (((hw.power 2).times (hf.times (HM (2*d)))).high ?_)
    all_goals push_cast; linarith only [hX,hp,hd,Nat.cast_nonneg (α:=ℝ) P.taylor,ht]
  let u':=t+6*x
  exact Volt.plus ((hq.high (show t+2*x≤ u' by dsimp only [u'];linarith only [hp])).plus hv)
    (Volt.plus (((Volt.plus (hi.high (show x≤2*x by linarith only [hp])) (hq.high (show t+2*x≤ 2*x by linarith only [hb]))).times hq).high (by change _≤ t+6*x; linarith only [hb,hp])) ((hq.times hi).high (by change _≤ t+6*x; linarith only [hb,hp])))
lemma gifts (p : Purse) (h : p.budget) : ∀ᶠ s in atTop,
    let J:= p.era.coast;4*(rentQ J.Q (load p.era)*Tapes.grant (knox s) (p.sends s) (p.double s) (2*p.taylor))≤ p.demand s:= by
  apply (((bank p).scale _).scale 4).met
  have hx:=p.motion; unfold budget bigZ at h; unfold bigZ; linarith [Nat.cast_nonneg (α:=ℝ) p.taylor]
lemma deputed (p : Purse) (h : p.budget) : ∀ᶠ s in atTop,
    fault s p * Common.priced (knox s) (2*p.taylor) + defect (knox s) (p.sends s) (p.double s) (2*p.taylor) ≤ Perch.bill (-3/2) s:= by
  let x:= p.credit;let u:= p.bigZ; let f:= -p.foil
  have ht:Volt x p.principal:=Volt.pulse _; have hp:Volt 1 knox:=Volt.pulse 1; have hq : Volt f p.sends:= Volt.pulse _
  let O:=2*p.taylor
  have he:=p.motion; have hh:=p.positive; have hz:=p.tolerance
  have hb : Volt (f+2*u) (fun s=>fault s p):= by
    have hC:=((ht.times hp).times hp).times hq
    apply Volt.plus (Volt.plus (hC.high ?_) (((((ht.power 2).times hp).times hp).times hq).high ?_)) ((((ht.times hp).scale 2).times hC).high ?_)
    all_goals unfold x f u bigZ; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) p.taylor]
  have ht : Volt (f+4*u) (fun s=> defect (knox s) (p.sends s) (p.double s) (2*p.taylor)):= by
    apply ((Volt.pulse (2*p.credit+3)).times (((hp.power O).scale _).times hq)).high; unfold u bigZ O; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) p.taylor]
  apply Volt.met (((hb.times (Volt.lift hp)).high ?_).plus ht);rotate_left
  · unfold u bigZ; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) p.taylor]
  unfold budget bigZ at h; unfold u bigZ f; linarith [Nat.cast_nonneg (α:=ℝ) p.taylor,Nat.cast_nonneg (α:=ℝ) p.goal]
end Purse
end YM.Next.Rank.Tapes

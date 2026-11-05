import YM.RemainderComparison.Exchange.Queue
import YM.Next.RANK.Exponential
import YM.Next.RANK.Array
/-!
 # Finite square marker at relative REAL chart sizes

 IN Page model already uses specified linear or grouped real test names,
 keep distinct marker arms, including allowed merges downstream. Part of
 quota proof for polynomial many sources (price at up to a FIXED horizon
 here on the checks not final marker scales). This is before MS or
 Leg poles. No ring source factorials omitted. Algebra `Exponential.roll`
 and `Poly.pass` from Rank (applies to complex ring); bridge to real jets
 for using the angle budgets at equality.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Portal
open Set Filter Function Lattice RG Pressure Push Push.AbsoluteSums Finset
open ConnectedActivityE6 Coat Blaze Brush PhysicalNext PhysicalNext.Repeat
open Marker Next.Rank.Glyph Next.Rank.Exponential
open Trace Exchange Queue
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{L:Side}
variable {ι : Type} [Fintype ι]

abbrev Cabinet (ι:Type) [Fintype ι] := modes ι→ℝ
def deckR (A: Cabinet ι) : veil ι:= Poly.inject fun i=> (A i:ℂ)
def sProduct (A B : Cabinet ι) : Cabinet ι := fun i=> ∑ s∈ i.val.powerset, A (scene s)*B (scene (i.val\s))
def lensOne (ι : Type) [Fintype ι]: Cabinet ι:=fun i=> if i=quiet ι then 1 else 0
def sTarget (f:Cabinet ι) : ℕ→ Cabinet ι | 0=>lensOne _ | n+1=> sProduct (sTarget f n) f
def sSpring (f:Cabinet ι) (i:modes ι):ℝ:= ∑ j∈Finset.range (Fintype.card ι+1), (j.factorial:ℝ)⁻¹ * sTarget f j i
def sEcho (f:Cabinet ι) : ℕ → Cabinet ι | 0=> fun _=>0 | n+1=>sEcho f n + (f-sSpring (sEcho f n))
def sWard (f:Cabinet ι) := sEcho f (Fintype.card ι)

lemma river (a b: Cabinet ι): deckR (a+(b-a)) = deckR a+(deckR b-deckR a):=by ext i; change ((a i + (b i-a i):ℝ):ℂ)= (a i:ℂ)+((b i:ℂ)-(a i:ℂ)); simp
lemma series (a b:Cabinet ι) : deckR (sProduct a b)=deckR a*deckR b:= by
  ext i; rw [Next.Rank.Glyph.part_mul]; change ((∑ s∈i.val.powerset, a (scene s)*b (scene (i.val\s)):ℝ):ℂ) = ∑ s∈i.val.powerset,(a (scene s):ℂ)*(b (scene (i.val\s)):ℂ); simp
lemma rights (f:Cabinet ι)(k:ℕ) : deckR (sTarget f k)=deckR f^k:=by
   induction k with
   | zero=> rw [pow_zero]; ext i; rw [Poly.one_part]; change ((lensOne _ i:ℝ):ℂ)=_; unfold lensOne; split_ifs <;> simp
   | succ k ih=> rw [sTarget,series,ih,pow_succ]
lemma snips (f: Cabinet ι) : deckR (sSpring f)=Poly.pass (deckR f):=by
   ext i; rw [Poly.pass,Poly.part_sum]; simp_rw [Poly.part_smul, ← rights f]
   change ((sSpring f i:ℝ):ℂ)=∑ s∈_,(_*(sTarget f s i:ℂ):ℂ); simp [sSpring]
lemma sprints (f:Cabinet ι)(k:ℕ) : deckR (sEcho f k)=roll (deckR f) k:=by
   induction k with
   | zero=>ext i; change ((0:ℝ):ℂ)=0; simp
   | succ k ih=> rw [sEcho,roll, ← ih, ←snips]; ext i; change ((sEcho f k i + (f i-sSpring _ i):ℝ):ℂ)= _; rw [Poly.part_plus,Next.Rank.Exponential.part_sub,Complex.ofReal_add,Complex.ofReal_sub]; rfl

variable {E : Type}[NormedAddCommGroup E] [NormedSpace ℝ E] {u v A B b C D:ℝ} {n k j r K i:ℕ}{x:E}
section
lemma collect {V: Type} (s : Finset V) (f:ℝ×E→V→ℝ)(p:E→V→ℝ)(h:∀ i∈s,Queue (fun x=>f x i) (fun x=>p x i) b x v u j k C)(he:(b,x)∈Germ.patch E v u)(hp:0<b) : Queue (fun x=>∑ i∈s,f x i) (fun x=>∑ i∈s,p x i) b x v u j k (s.card*C) := by
   induction s using Finset.induction_on with
   | empty=> simpa only [sum_empty,Finset.card_empty,Nat.cast_zero,zero_mul,norm_zero] using Queue.constant (0:ℝ) he hp
   | insert i s hi ih=>
     simp only [card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm (#s:ℝ), sum_insert hi]
     exact (h i (mem_insert_self ..)).adds (ih (fun i hi=> h i (mem_insert_of_mem hi))) -- edit
end
abbrev May (f:ℝ×E→Cabinet ι)(g:E→Cabinet ι) (b:ℝ)(x:E)(v u:ℝ)(j r:ℕ)(A:ℝ) :=∀ i:modes ι, Queue (fun x=> f x i) (fun x=>g x i) b x v u j r A
section Cap
variable {f F: ℝ×E→Cabinet ι} {p P: E→ Cabinet ι}
lemma commute (hh: May f p b x v u j k A)(hf:May F P b x v u j k B)(hb:b≤1)(ht:Fintype.card ι≤K):
   May (fun x=> sProduct (f x) (F x)) (fun x=> sProduct (p x) (P x)) b x v u j k (2^K*productPrice j k A B):=by
   intro i; let f₀ z s:= f z (scene s)*F z (scene (i.val\s)); let p₀ z s:= p z (scene s)* P z (scene (i.val\s)); let Q₀:= hh (quiet ι)
   apply Queue.grows (collect i.val.powerset f₀ p₀ (fun i _=>(hh _).productQ (hf _) hb) Q₀.site Q₀.coupling)
   apply mul_le_mul_of_nonneg_right _ ((Q₀.productQ (hf (quiet ι)) hb).cost)
   simp only [card_powerset,Nat.cast_pow,Nat.cast_ofNat]; exact pow_le_pow_right₀ one_le_two ((Finset.card_le_univ _).trans ht)

def sJolt (j k K:ℕ) (A:ℝ) : ℕ→ℝ
   | 0=>1
   | n+1=> 2^K* Queue.productPrice j k (sJolt j k K A n) A
lemma sTerms (hh: May f p b x v u j k A)(hb:b≤1)(ht:Fintype.card ι≤K)(n:ℕ):
   May (fun x=> sTarget (f x) n) (fun x=>sTarget (p x) n) b x v u j k (sJolt j k K A n):=by
   induction n with
   | zero=> intro i; refine (Queue.constant (lensOne ι i) (hh i).site (hh i).coupling).grows ?_; unfold sJolt lensOne; split <;> simp
   | succ k ih=> exact commute ih hh hb ht
section
variable {f₁:ℝ×E→ℝ}{g₁:E→ℝ}
lemma scaleAmt (P:Queue f₁ g₁ b x v u j k A)(c:ℝ) : Queue (fun x=>c*f₁ x) (fun x=>c*g₁ x) b x v u j k (‖c‖*A):=by
   refine ⟨mul_nonneg (norm_nonneg _) P.cost, P.site, P.coupling, fun x h=> (P.scope x h).smul c,?_⟩
   exact ((P.return'.smul c).climb (by apply le_of_eq; ring) le_rfl).shimmy (Filter.Eventually.of_forall (fun i=> by dsimp only; rw [← mul_sub]; rfl))
lemma sJolt_pos (h:0≤A)(l:ℕ):0≤ sJolt j k K A l:=by
   induction l with
   | zero=> exact zero_le_one
   | succ l ih=> unfold sJolt Queue.productPrice Queue.tfee; positivity
end

def spray (j k K:ℕ) (A:ℝ):ℝ:= ∑ i∈Finset.range (K+1), ‖(i.factorial:ℝ)⁻¹‖*sJolt j k K A i
def flute (j k K:ℕ) (A:ℝ): ℝ:= ((K:ℝ)+1)* spray j k K A
lemma barrel (hh: May f p b x v u j k A)(hb:b≤1)(ht:Fintype.card ι≤K):
   May (fun x=>sSpring (f x)) (fun x=>sSpring (p x)) b x v u j k (flute j k K A):=by
   intro i; apply Queue.grows (collect (Finset.range (Fintype.card ι+1)) (p:=fun x z=>(z.factorial:ℝ)⁻¹*sTarget (p x) z i) (f:=fun x z=>(z.factorial:ℝ)⁻¹*sTarget (f x) z i) (C:=spray j k K A) (fun l hi=> ?_) (hh i).site (hh i).coupling) -- pos args
   · unfold flute; simp only [card_range,Nat.cast_add,Nat.cast_one]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show Fintype.card ι+1 ≤ K+1 from by omega)) (sum_nonneg fun _ _=> mul_nonneg (norm_nonneg _) (sJolt_pos (hh i).cost _))
   apply Queue.grows (scaleAmt (sTerms hh hb ht l i) _)
   exact Finset.single_le_sum (f:=fun i:ℕ =>‖(i.factorial:ℝ)⁻¹‖*sJolt j k K A i) (fun z _=> mul_nonneg (norm_nonneg _) (sJolt_pos (hh i).cost z)) (Finset.range_mono (show Fintype.card ι+1≤ K+1 by omega) hi)

def returner (j k K:ℕ)(A:ℝ):ℕ→ℝ
   | 0=> 0
   | n+1=> returner j k K A n+(A+flute j k K (returner j k K A n))
lemma rewind (hh: May f p b x v u j k A)(hb:b≤1)(ht:Fintype.card ι≤K) (n:ℕ):
   May (fun x=>sEcho (f x) n) (fun x=>sEcho (p x) n) b x v u j k (returner j k K A n):=by
   induction n with
   | zero=> intro i; simpa only [sEcho,returner,norm_zero] using! Queue.constant (0:ℝ) (hh i).site (hh i).coupling
   | succ l ih => intro i; exact (ih i).adds ((hh i).sub_fit (barrel ih hb ht i))
-- costs maybe monotone but suffice selecting ledger up to K

def rehearsal (j k K:ℕ)(A:ℝ) := ∑ i∈ Finset.range (K+1), |returner j k K A i|
lemma played (hh: May f p b x v u j k A)(hb:b≤1)(ht:Fintype.card ι≤K) :
   May (sWard ∘ f) (sWard ∘ p) b x v u j k (rehearsal j k K A):=by
    intro i; exact (rewind hh hb ht (Fintype.card ι) i).grows ((le_abs_self _).trans (single_le_sum (fun i _=>abs_nonneg (returner j k K A i)) (Finset.mem_range.mpr (by omega))))
lemma stanza {p:ℝ→ℝ}(hp:Reserve G L p):Reserve G L fun x=>rehearsal j k K (p x):=by -- Parameter p shadow
   let a:=Reserve.const (G:=G) (L:=L); have h (p':ℝ→ℝ)(he:Reserve G L p')(i:ℕ):Reserve G L (fun x=> sJolt j k K (p' x) i):= by
      induction i with
      | zero=> exact a _
      | succ i ih => exact (a _).mul ((((ih.mul he).mul (a _)).add (((ih.mul (he.add he)).mul (a _)).add ((ih.mul he).mul (a _)))))
   have H (p':ℝ→ℝ)(he:Reserve G L p'): Reserve G L (fun x=> flute j k K (p' x)):=
      (a _).mul (Reserve.sum (K+1) (fun i x=>‖(i.factorial:ℝ)⁻¹‖*sJolt j k K (p' x) i) fun i _=>(a _).mul (h p' he i))
   have hh i : Reserve G L (fun x=> returner j k K (p x) i):=by
      induction i with
      | zero=> exact a _
      | succ i ih => exact ih.add (hp.add (H _ ih))
   exact Reserve.sum _ _ (fun i _=> (hh i).absolute)
end Cap
end YM.RemainderComparison.Portal

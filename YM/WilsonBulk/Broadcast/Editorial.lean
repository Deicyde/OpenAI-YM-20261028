import YM.WilsonBulk.Transit.Meaning
import YM.WilsonBulk.Broadcast.Stem
import YM.WilsonBulk.Slice.Planar
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Editorial stratum (all coefficient orders but not uniform in the order)

Standard valence and truncation contract. E terms have displayed potential
ranks and prechosen sym coherences. Later add Watch predicates on the
solution. `Document` holds full vacuum action or just V, called with
Cashless except explicit finite `receive` and normalization tapes. Includes
rank0 at τ,ρ periods when transported; printing always removes it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open Function Filter Equiv Finset Matrix Bloch Lattice Pert.Bulk
open scoped Topology Classical BigOperators ENNReal ContDiff
open PowerSeries (coeff constantCoeff)
open MvPolynomial (C X)
variable {X Y α β ι : Type} {p q σ θ : ℝ} {D : ℕ→Side} {I J : Record X} {n m : ℕ}

-- API Standard shape = with natural parity and upper cap. rank below 2 maybe.
structure Document (I : Record X) : Prop where
  cap : FrameBound I
  coherent : Based I
  parity : Alternating I
abbrev Cashless (I : Record X) := ∀ e,I e 0=0
lemma regular_no (P : Page α 0) : Regular P:=fun i=> by rw [Subsingleton.elim i (Equiv.refl _)]; exact rfl
lemma Free.plus (h : Free I) (he : Free J) : Free (I+J) := fun i=> by simp [h i,he i]
lemma Free.minus (h : Free I) (he : Free J) : Free (I-J) := fun i=> by simp [h i,he i]
lemma Free.negative (h : Free I) : Free (-I) := fun i=> by simp [h i]
lemma Cashless.plus (h : Cashless I) (he : Cashless J) : Cashless (I+J) := fun i=> by simp [h i,he i]
lemma Cashless.minus (h : Cashless I) (he : Cashless J) : Cashless (I-J) := fun i=> by simp [h i,he i]
def switchBoard (i : ℕ→ℕ→Prop) (u : Record X) : Record X := fun e n=> if i e n then u e n else 0
abbrev later (u : Record X) := switchBoard (fun i _=> i≠0) u
lemma later_eq {I : Record X} (h : Free I) : later I=I := funext fun i=> funext fun j=> by unfold later switchBoard; split; exact rfl; rename_i he; simp only [Decidable.not_not] at he; simpa [he] using (h j).symm
lemma Free.later (u : Record X) : Free (Sheet.later u) := fun _=> if_neg (not_not_intro rfl)

namespace Document
lemma plus (h : Document I) (he : Document J) : Document (I+J) := ⟨fun i j p=> by simp [h.cap i j p,he.cap i j p], fun i j=> (h.coherent i j).plus (he.coherent i j),fun i j p=>by simp [h.parity i j p,he.parity i j p]⟩
lemma minus (h : Document I) (he : Document J) : Document (I-J) := ⟨fun i j p=> by simp [h.cap i j p,he.cap i j p], fun i j=> (h.coherent i j).minus (he.coherent i j),fun i j p=>by simp [h.parity i j p,he.parity i j p]⟩
lemma zero : Document (0: Record X) := ⟨fun _ _ _=> rfl,fun _ _=>Regular.zero,fun _ _ _=> rfl⟩
lemma scale (h : Document I) (r : ℝ) : Document (r • I) := ⟨fun i j p=> by simp [h.cap i j p],fun i j=> (h.coherent i j).scaled r,fun i j p=> by simp [h.parity i j p]⟩
lemma board (h : Document I) (f : ℕ→ℕ→Prop) : Document (switchBoard f I) :=
  ⟨fun i j he=> by simp [switchBoard,h.cap i j he],fun i j=> by unfold switchBoard; split; exacts [h.coherent i j,Regular.zero], fun i j p=>by simp [switchBoard,h.parity i j p]⟩
lemma receives (h : Document I) (G : Page X 2) (hr : Free I) (b : Bool) :
    Document (receive G I b) := let e:=siteLimits G b h.cap hr h.coherent; ⟨e.1,e.2.1,receive_parity G b h.parity⟩
end Document

section pamphlet
variable {V W : Record (Market α)} {v w : Text α n}
-- `Located` rank0 still nonnegative cost (tsum vacuous). no absolute statements there!
structure Public (v : Text α n) : Prop where
  style : Pervasive v
  money : ∃ σ p,0<σ ∧ Within (lawn α) σ p v
abbrev Pamphlet (V : Record (Market α)) := ∀ e n,Public (V e n)
-- proxy helper without assumption witnesses
lemma Proxy.claim (G : Leaf D α n) (h : Proxy G v) : Public v:=⟨h.pervasive,h.priced⟩
namespace Public
lemma zero : Public (0:Text α n) := ⟨Pervasive.zero,⟨1,0,one_pos,Within.zero le_rfl⟩⟩
lemma plus (hv : Public v) (hw : Public w) : Public (v+w) := by
  obtain ⟨s,σ,p,h,hp⟩:= hv; obtain ⟨t,θ,q,k,hq⟩:= hw; exact ⟨s.plus t,⟨min σ θ,p+q,lt_min h k,(hp.mono (min_le_left ..) le_rfl).add (hq.mono (min_le_right ..) le_rfl)⟩⟩
lemma scale (h : Public v) (r : ℝ) : Public (r • v) := by obtain ⟨s,σ,p,h,hp⟩:= h; exact ⟨s.scale r,⟨σ,|r| * p,h,hp.scale r⟩⟩
lemma minus (h : Public v) (f : Public w) : Public (v-w) := by simpa [sub_eq_add_neg] using! h.plus (f.scale (-1))
lemma polish (h : Public v) : Public (Sheet.polish v) := by obtain ⟨s,σ,p,hs,h⟩:= h; exact ⟨s.polished,σ,p,hs,h.clean⟩ -- tuple Prop
lemma gather (s : Finset β) {U : β→ Text α n} (h : ∀ i∈s,Public (U i)) : Public (∑ i∈s,U i) := by
  induction s using Finset.induction with
  | empty=> simp only [sum_empty]; exact Public.zero
  | insert x s hx ih => rw [sum_insert hx]; exact (h x (mem_insert_self ..)).plus (ih fun i hi=> h i (mem_insert_of_mem hi))
end Public
-- orientation invariant twist and WT transported later. issue always print

def coupon (c : Side) : (n:ℕ)→ Text α n→ Page (Co c α) n
| 0 => fun _=>0
| _+1 => Sheet.print c
abbrev issue (c : Side) (V : Record (Market α)) : Record (Co c α) := fun e n=> coupon c n (V e n)
lemma coupon_succ (v : Text α (n+1)) (c : Side) : coupon c (n+1) v=print c v := rfl
lemma coupon_reads (c : Side) (h : Pervasive v) : Orates (small c α) v (coupon c n v) := by cases n; exact fun i=> Fin.elim0 i; exact reads h
lemma Public.orates_once (h : Public v) (c : Side) {U : Page (Co c α) n} (hh : Orates (small c α) v U) (hn : n≠0) : coupon c n v=U := (coupon_reads c h.style).uniq hh (small_onto c α) hn
lemma Public.forever (h : Public v) (c : ℕ→ Side) : Proxy (fun i=> coupon (c i) n v) v := by
  obtain ⟨x,p,hs,hp⟩:= h.money; exact Proxy.always _ _ (Eventually.of_forall fun _=> coupon_reads _ h.style) h.style hp hs
@[simp] lemma coupon_zero (c : Side) (i : ℕ) : coupon c i (0:Text α i)=0 := by
  cases i; exact rfl; apply Public.zero.orates_once c Orates.zero (by omega)
lemma coupon_plus (c : Side) (h : Public v) (g : Public w) : coupon c n (v+w)=coupon c n v + coupon c n w := by
  obtain ⟨σ,p,hs,hp⟩:= h.money; obtain ⟨θ,q,ht,hq⟩:= g.money
  cases n; simp [coupon]; exact (h.plus g).orates_once c ((coupon_reads c h.style).plus (coupon_reads c g.style) hp hq hs.le ht.le) (by omega)
lemma coupon_scale (c : Side) (h : Pervasive v) (r : ℝ) : coupon c n (r • v)=r • coupon c n v := by
  cases n; simp [coupon]; exact (coupon_reads c (h.scale r)).uniq ((coupon_reads c h).scale r) (small_onto c _) (by omega)
lemma coupon_minus (c : Side) (h : Public v) (g : Public w) : coupon c n (v-w)=coupon c n v-coupon c n w:= by
  rw [sub_eq_add_neg,sub_eq_add_neg, show -w=(-1:ℝ) • w from by simp,coupon_plus _ h (g.scale _),coupon_scale _ g.style]; simp
namespace Pamphlet
lemma zero : Pamphlet (0:Record (Market α)) := fun _ _=> Public.zero
lemma plus (h : Pamphlet V) (g : Pamphlet W) : Pamphlet (V+W) := fun i j=> (h i j).plus (g i j)
lemma minus (h : Pamphlet V) (g : Pamphlet W) : Pamphlet (V-W) := fun i j=>(h i j).minus (g i j)
lemma scale (h : Pamphlet V) (r : ℝ) : Pamphlet (r • V) := fun i j=> (h i j).scale r
lemma board (h : Pamphlet V) (s) : Pamphlet (switchBoard s V) := fun i j=> by unfold switchBoard; split; exacts [h i j,Public.zero]
lemma at_issue (h : Pamphlet V) (c : Side) (hu : Document V) : Document (issue c V) := ⟨fun i j h=> by simp [issue,hu.cap i j h],fun i j=> by
  cases j; exact regular_no _; exact (coupon_reads c (h i _).style).regular (hu.coherent i _) (small_onto c α) (by omega),fun i j h=> by simp [issue,hu.parity i j h]⟩
lemma issued_plus (c : Side) (h : Pamphlet V) (g : Pamphlet W) : issue c (V+W)=issue c V+issue c W := funext fun i=> funext fun j=>coupon_plus c (h i j) (g i j)
lemma issued_minus (c : Side) (h : Pamphlet V) (g : Pamphlet W) : issue c (V-W)=issue c V-issue c W := funext fun i=>funext fun j=>coupon_minus c (h i j) (g i j)
lemma issued_scale (c : Side) (h : Pamphlet V) (r : ℝ) : issue c (r • V)=r • issue c V := funext fun i=>funext fun j=>coupon_scale c (h i j).style r
end Pamphlet
lemma issue_board (c : Side) (U : ℕ→ℕ→Prop) (V : Record (Market α)) : switchBoard U (issue c V)=issue c (switchBoard U V) := funext fun i=>funext fun j=>by by_cases h: U i j <;> simp [switchBoard,issue,h]
lemma issue_free (c : Side) (U : Record (Market α)) (hu : Free U) : Free (issue c U) := fun i=> by simp [issue,hu i]
end pamphlet
end YM.WilsonBulk.Sheet

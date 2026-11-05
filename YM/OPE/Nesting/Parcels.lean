import YM.OPE.Nesting.Grove

/-! Finite alternatives of actual words. Menu terms carry only scalar
amplitudes and physical homogeneous field labels in `S`, allowing the fields
themselves to be summed only after evaluating linear readouts/tests. No
algebra of colliding products. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{B:Register G}{S:Table B}
variable {L I J:Type}

def degrees (v:I→S.Tag)(i:I):ℕ :=(v i).1
def voices (v:I→S.Tag):Labels S (degrees v):=fun i=>(v i).2
def wages (v:I→S.Tag)(i:I):ℝ:=degrees v i

def weightOf [Fintype I](v:I→S.Tag) := weight (degrees v)

lemma weightOf_nonnegative [Fintype I] (v:I→S.Tag):0≤weightOf v:=by unfold weightOf weight; positivity

structure Atom (S:Table B)(L:Type) where
    Slot : Type
    ft : Fintype Slot
    place : L→Slot→E4
    tags : Slot→ S.Tag
    amp : L→ℂ
instance atomFt {A:Atom S L}: Fintype A.Slot:=A.ft

namespace Atom
variable (A:Atom S L)

def cost := weightOf A.tags


def punctum (v:S.Tag)(c:L→ℂ)(o:L→E4):Atom S L where
   Slot:=Unit
   ft:=inferInstance
   place i:=sole (o i)
   tags _:=v
   amp:=c
lemma punctum_cost {v:S.Tag}{c:L→ℂ}{o:L→E4}:cost (punctum v c o)=v.1 := by change (∑ _:Unit,(v.1:ℝ))=v.1; rw [Fintype.sum_unique]

variable [Fintype J]
def splice (v:I→S.Tag)(w:J→S.Tag):I⊕J→S.Tag:= Sum.elim v w
lemma splice_weight [Fintype I] (v:I→S.Tag)(w:J→S.Tag):weightOf (splice v w) =weightOf v + weightOf w:=by
   unfold weightOf weight; rw [Fintype.sum_sum_type]; rfl

def duet [Fintype I] (T:Table B)(x:I→E4)(v:I→S.Tag)(y:J→E4)(w:J→S.Tag):ℂ:= whole T x (voices v) y (voices w)
lemma duet_moment [Fintype I] (T:Table B)(x:I→E4)(v:I→S.Tag)(y:J→E4)(w:J→S.Tag):duet T x v y w = moment T (beside x y) (voices (splice v w)) := by
     unfold duet; rw [whole_observed,observed]
     exact congr_arg _ (funext fun ij=> by cases ij <;> rfl)

-- update result: HEq

def sample (T:L→Table B) (y:L→J→E4)(w:J→S.Tag) (s:L):ℂ:= A.amp s * duet (T s) (A.place s) A.tags (y s) w

local notation "ℛ" => Orbits.Reader
variable {X:S.Rotation}{ρ:S.RealSpin}{Q:DiffPlan S}

def express [Fintype I] (R:ℛ Q X ρ) (m:ℕ)(h:R.channels m) (x:I→E4)(v:I→S.Tag) (o:E4):ℂ := R.coef m h x (voices v) o
lemma express_perm [Fintype I] (R:ℛ Q X ρ) (e:I ≃ J) (m:ℕ)(h:R.channels m) (x:J→E4)(v:J→ S.Tag) (o:E4) : express R m h (x ∘ e) (v ∘ e) o = express R m h x v o := by
     unfold express Orbits.Reader.coef
     refine congr_arg (fun z=> ((R.basis m).repr z) h) ?_
     apply Subtype.ext
     exact R.fresh_perm m x o (voices v) e
lemma express_reindex [Fintype I] {x:I→E4}{z:J→E4}{v:I→S.Tag}{w:J→S.Tag}{o:E4} (R:ℛ Q X ρ) (e:I≃J)(h₁:x=z ∘ e)(h₂:v=w ∘ e) {m:ℕ}{h:R.channels m}: express R m h x v o = express R m h z w o := by rw [h₁,h₂,express_perm R e] 

def issue (R:ℛ Q X ρ) (m:ℕ)(h:R.channels m) (o:L→E4)(s:L):ℂ:= A.amp s * express R m h (A.place s) A.tags (o s)

def bundle [Fintype I](A:I→Atom S L):Atom S L where
   Slot:= Σ i,(A i).Slot
   ft:= inferInstance
   place s i:= (A i.1).place s i.2
   tags i:= (A i.1).tags i.2
   amp s:= ∏ i,(A i).amp s
lemma bundle_cost [Fintype I](A:I→Atom S L):cost (bundle A)= ∑ i:I, cost (A i):=by
   unfold cost weightOf weight; change (∑ t:(Σ i,(A i).Slot),(_ : ℝ))= _
   rw [Fintype.sum_sigma]; rfl
end Atom

structure Menu (S:Table B)(L:Type) where
   Draw:Type
   ft : Fintype Draw
   pick: Draw→Atom S L
instance menuFt {A:Menu S L}:Fintype A.Draw:=A.ft

namespace Menu
variable {X:S.Rotation}{ρ:S.RealSpin}{Q:DiffPlan S}
variable (A:Menu S L)

variable [Fintype J]
def atView (T':L→Table B)(y:L→J→E4)(w:J→S.Tag)(s:L):ℂ:= ∑ h:A.Draw, (A.pick h).sample T' y w s
def charge (R:Reader Q X ρ)(m:ℕ)(h:R.channels m)(o:L→E4)(s:L):ℂ:=∑ q:A.Draw,(A.pick q).issue R m h o s

def raw {t:Tree}(z:Tree.Envelope L t)(v:t.Leaf→S.Tag):Menu S L where
   Draw:=Unit
   ft := inferInstance
   pick _ := {Slot:=t.Leaf,ft:=inferInstance,place:=fun i=> z i ∘ t.leafSeat,tags:=v,amp:=fun _=>1}

-- extend all through given grade
abbrev Cut (R:Reader Q X ρ)(m:ℕ):= (j:Fin (m+1)) × R.channels j.val

def through (R:Reader Q X ρ)(m:ℕ)(A:Atom S L)(o:L→E4):Menu S L where
   Draw:= Cut R m
   ft:= inferInstance
   pick j:=Atom.punctum ⟨j.1.val, R.actor j.1.val j.2⟩ (A.issue R j.1.val j.2 o) o

def fuse [ht:Fintype I](p:I→Menu S L): Menu S L where
    Draw:= (i:I)→(p i).Draw
    ft := inferInstance
    pick c:= (Atom.bundle (fun j=>(p j).pick (c j)))

lemma raw_bundle (n:ℕ)(f:Fin n→Tree)(z:Tree.Envelope L (Tree.fork n f))(v:(Tree.fork n f).Leaf→S.Tag) (c:(@fuse _ _ S L (Fin n) inferInstance (fun j=>raw (Tree.down j z) (Tree.childWages j v))).Draw)(T':L→Table B)(y:L→ J→ E4)(w:J→S.Tag)(s:L):
    ((fuse (fun j=>raw (Tree.down j z) (Tree.childWages j v))).pick c).sample T' y w s=(raw z v).atView T' y w s:=by
    unfold atView; change _ = ∑ u:Unit,((raw z v).pick u).sample T' y w s
    rw [Fintype.sum_unique]
    -- want congruent
    simp only [fuse,raw,Atom.sample,Atom.bundle,Finset.prod_const_one,one_mul]
    rfl

lemma raw_view {t:Tree}(z:Tree.Envelope L t)(v:t.Leaf→ S.Tag)(T:L→Table B)(y:L→J→E4)(w:J→S.Tag)(s:L):
   (Menu.raw z v).atView T y w s = Atom.duet (T s) (z s ∘ t.leafSeat) v (y s) w :=by
     unfold atView; change (∑ _:Unit,(1:ℂ) * _) = _ -- ht unif
     rw [Fintype.sum_unique]; exact one_mul _
lemma raw_charge {t:Tree}(z:Tree.Envelope L t)(v:t.Leaf→ S.Tag)(R:Reader Q X ρ)(m:ℕ)(h:R.channels m) (o:L→E4)(s:L):(Menu.raw z v).charge R m h o s = Atom.express R m h (z s ∘ t.leafSeat) v (o s):=by
    unfold charge; change (∑ _:Unit,(1:ℂ)*_)=_
    rw [Fintype.sum_unique]; exact one_mul _
end Menu

end YM.OPE.Nesting

import YM.RG08.Anchor.Duotone

/-!
# Compress empty flags to (actual curvature/potential type × color index),
 preserve cost/pour and closure. Used both ways.
-/
noncomputable section
namespace YM.RG08.Anchor
open Forms Rudder Packets Isles Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch
open AnalyticNext.QuarticMatch.BoxChain hiding sway
open scoped Topology BigOperators Classical ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I X : Type}{n k:ℕ}{P:Side}{σ C:ℝ}{F:Raw I n}

abbrev Kind (I:Type) (k:ℕ):= TypeFace k × I
def ec (x:X × Kind I k): X×Tone I:=(x.1,x.2.1.val,x.2.2)
def et (x:Tape n (X× Kind I k)):Tape n (X×Tone I):=ec ∘ x
lemma ec_injective:Injective (@ec I X k):=by rintro ⟨a,b,c⟩ ⟨a',b',c'⟩ h;simp only [ec,Prod.mk.injEq] at *;exact ⟨h.1,Subtype.ext h.2.1,h.2.2⟩
lemma et_injective:Injective (@et I X n k):=ec_injective.comp_left

def compress {X:Type}(k:ℕ)(F:Flake n (X×Tone I)):Flake n (X×Kind I k):=F ∘ et
lemma compress_sub{X:Type}(k:ℕ)(F F':Flake n (X×Tone I)):compress k (F-F')=compress k F-compress k F':=rfl
lemma compress_sym{X:Type}(k:ℕ){F:Flake n (X×Tone I)}(h:Forms.Sym F):Forms.Sym (compress k F):=by intro e;funext x; exact congrFun (h e) (et x)
lemma compress_path(k:ℕ)(h:Cohort F):Cohort (compress k F):=fun a x=>h a (et x)
lemma compress_cost (k:ℕ)(h:Held (carpet (Tone I)) σ C F):Held (carpet (Kind I k)) σ C (compress k F):=by
 rw [ensign];intro i z
 calc
  _ ≤ ∑' x,Forms.row (mark (carpet (Tone I)) σ F) i (ec z) x:= ?_
  _ ≤ _:=ensign.mp h i (ec z)
 convert ENNReal.tsum_comp_le_tsum_of_injective (et_injective (X:=Cover) (n:=n) (k:=k) (I:=I)) (Forms.row (mark (carpet (Tone I)) σ F) i (ec z)) using 1
 apply tsum_congr;intro b; unfold Forms.row
 simp_rw [show (et b i=ec z)=(b i=z) from propext ec_injective.eq_iff]
 rw [mark,mark];split_ifs; · rfl -- radius cost defEq except Tower recursor/card? span defin
 rfl

variable (k i : ℕ)

def decoded (X I:Type) (k:ℕ)(x:X × Tone I)(h:(x.2.1).card=k) : X × Kind I k:=(x.1,⟨x.2.1,h⟩,x.2.2)

def permitted(X I:Type) (k:ℕ)(x:Tape n (X×Tone I)):Prop:=∀ i,(x i).2.1.card=k
@[simp] lemma equipped {k:ℕ}(x:Tape n (X×Kind I k)):permitted X I k (et x):=fun i=>(x i).2.1.property

def extend (F:Flake n (X×Kind I k)):Flake n (X×Tone I):=fun x=> if h:permitted X I k x then F (fun i=>decoded X I k (x i) (h i)) else 0
lemma extend_top {k:ℕ}(F:Flake n (X×Kind I k))(x:Tape n (X×Kind I k)):Anchor.extend k F (et x)=F x:=by unfold Anchor.extend;rw [dif_pos (equipped _)];rfl
lemma graded_expand {X:Type}{F:Flake n (X×Tone I)}(h:∀ x:Tape n (X×Tone I),¬permitted X I k x→F x=0):Anchor.extend k (compress k F)=F:=by
 funext x;unfold Anchor.extend;split_ifs with H; · rfl
 exact (h _ H).symm

variable {i k}
lemma expand_path {k:ℕ}{F:Flake n (Market (Kind I k))}(h:Cohort F):Cohort (Anchor.extend k F):=by
 intro a x;unfold Anchor.extend;change (if h:permitted _ _ k x then _ else _) = _;split_ifs with hx
 exact h a (fun i=>decoded _ _ k (x i) (hx i))
 rfl
lemma expand_grade {F:Flake n (Market (Kind I k))}:Graded (Anchor.extend k F) (fun _=>k):=by rw [Symmetry.graded_iff];intro i x he;unfold Anchor.extend;rw [dif_neg (fun H=>he (H i))]
lemma expand_cost{F:Flake n (Market (Kind I k))}(h:Held (carpet _) σ C F):Held (carpet _) σ C (Anchor.extend k F):=by
 rw [ensign];intro i z
 by_cases hz:z.2.1.card=k
 · let w:=decoded Cover I k z hz
   apply le_trans (b:=∑' x,Forms.row (mark (carpet _) σ F) i w x)
   · let f:=Forms.row (mark (carpet _) σ (Anchor.extend k F)) i z
     have he:Function.support f⊆ Set.range (et (X:=Cover) (I:=I) (n:=n) (k:=k)):=by -- SUPPORT zero, not mulSupport
       intro x hx
       by_contra! H
       have huv:¬ permitted _ _ k x:=fun he=>H ⟨fun i=>decoded _ _ k (x i) (he i),rfl⟩
       exact hx (by simp [f,Forms.row,mark,Anchor.extend,huv,Pert.Bulk.bill])
     change (∑' x,f x) ≤ _
     rw [← et_injective.tsum_eq he]; apply ENNReal.tsum_le_tsum;intro x
     unfold f Forms.row mark; rw [extend_top]
     rw [show (et x i=z)=(x i=w) from propext (show ec _=ec w ↔_ from ec_injective.eq_iff)]
     exact le_rfl
   exact ensign.mp h i w
 · have he (x:Tape n (Market (Tone I))):Forms.row (mark (carpet _) σ (Anchor.extend k F)) i z x=0:=by
      unfold Forms.row;split_ifs with hx
      · unfold mark Anchor.extend;rw [dif_neg (fun h=>hz (hx ▸ h i))]; simp [Pert.Bulk.bill]
      rfl
   simp [he]
end YM.RG08.Anchor

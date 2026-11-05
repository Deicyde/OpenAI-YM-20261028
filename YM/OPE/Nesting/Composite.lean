import YM.OPE.Nesting.Fusion

/-!
# Successive finite OPE factors

Only inner vertices belonging to the chosen labeled word receive actual
truncations. `boundNow` gives zero at a leaf merely to enable uniform
index types (`Unit` there), not to project out its input tag. The root
projection for `stack` is at the field grade in the final output. No
dependence of the physical OPE constants on the ratios in these formulas.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting.Composite
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
variable {L:Type}

/-- Output token of a truncated request or singleton choice for a leaf. -/
def Stage (n:ℕ): Tree→Type
 | .bud => Unit
 | .fork .. => Menu.Cut R n
instance stageFt (n:ℕ)(t:Tree):Fintype (Stage U R n t) := match t with
  | .bud=>inferInstanceAs (Fintype Unit)
  | .fork ..=>inferInstanceAs (Fintype (Cut R n))

def boundNow : (t:Tree) → (t.Inner→ℕ) → ℕ
 | .bud,_=>0
 | .fork ..,D=> D (Sum.inl ())

def token : (t:Tree) → {n:ℕ} → (t.Leaf→S.Tag) → Stage U R n t → S.Tag
 | .bud,_,v,_=>v ()
 | .fork ..,_,_,p=>oneTag U R p.1 p.2

def flash {L:Type} : (t:Tree) → {n:ℕ} → (z:t.Envelope L) → (v:t.Leaf→S.Tag) → Stage U R n t → L→ℂ
 | .bud,_,_,_,_,_=>1
 | .fork ..,_,z,v,k,s=> (Menu.raw z v).charge R k.fst k.snd (Tree.center z) s

def beacon {t:Tree}(m:ℕ)(z:Tree.Envelope L t)(v:t.Leaf→S.Tag):Menu S L where
    Draw:=Stage U R m t
    ft:=inferInstance
    pick c:=Atom.punctum (token U R t v c) (flash U R t z v c) (Tree.center z)

section Buds
variable {t:Tree}{z:Tree.Envelope L t}{v:t.Leaf→S.Tag} (h:t=bud) {m:ℕ}{c:Stage U R m t}
include h
lemma bud_token (p:t.Leaf) :token U R t v c = v p:=by cases h; cases p; rfl
lemma bud_flash : flash U R t z v c=fun _=>1:=by cases h; rfl
lemma bud_res (p:t.Leaf)(k:ℝ)(a:t.Inner→ℝ): t.cost k a (wages v) = (degrees v p:ℝ)*(t.topAge k a):=by cases h; cases p; exact mul_comm ..
lemma flash_bud : beacon U R m z v = Menu.raw z v:=by
      cases h
      change @Menu.mk _ _ S L Unit _ _ = @Menu.mk _ _ S L Unit _ _; congr 1
lemma seats_bud (p:t.Leaf)(s:L):z s (t.leafSeat p)=Tree.center z s:= by cases h; cases p; rfl
-- no h needed for nodes
omit h in
lemma beacon_native (h:t≠bud):beacon U R m z v=loadedRaw U R z v (Tree.center z) m:= by
    cases t with
    | bud=>exact (h rfl).elim
    | fork=> unfold beacon Stage loadedRaw Menu.through; congr 1; funext c; unfold flash token oneTag; simp_rw [raw_charge]; change punctum _ _ _=punctum _ (fun i=> (1:ℂ)*_) _; simp_rw [one_mul]; rfl
end Buds

section Fork
variable {n:ℕ}{f:Fin n→Tree}
variable {z:Tree.Envelope L (Tree.fork n f)} {v:(Tree.fork n f).Leaf→S.Tag}

abbrev Branches (j:Fin n→ℕ):= (i:Fin n)→Stage U R (j i) (f i)

def lamps (r:Fin n→ℕ) := fun j:Fin n => beacon U R (r j) (Tree.down j z) (Tree.childWages j v)

def echoTags (v:(Tree.fork n f).Leaf→S.Tag){r:Fin n→ℕ}(p:Branches U R (f:=f) r) (j:Fin n): S.Tag := token U R (f j) (Tree.childWages j v) (p j)
def echoPoints (z:Tree.Envelope L (Tree.fork n f))(s:L)(j:Fin n): E4 := Tree.center (Tree.down j z) s

def factor (z:Tree.Envelope L (Tree.fork n f))(v:(Tree.fork n f).Leaf→S.Tag){r:Fin n→ℕ}(p:Branches U R (f:=f) r){m:ℕ}(c:R.channels m)(s:L):ℂ := express R m c (echoPoints z s) (echoTags U R v p) (Tree.center z s)
def hinge (z:Tree.Envelope L (Tree.fork n f))(v:(Tree.fork n f).Leaf→S.Tag)(r:Fin n→ℕ){m:ℕ}(c:R.channels m)(s:L):ℂ := ∑ p:Branches U R (f:=f) r, (∏ j, flash U R (f j) (Tree.down j z) (childWages j v) (p j) s) * factor U R z v p c s

lemma flash_all (r:Fin n→ℕ) {q:ℕ}(k:R.channels q)(s:L): (Menu.fuse (lamps (z:=z) (v:=v) U R r)).charge R q k (Tree.center z) s = hinge U R z v r k s:=by
     let z':=fun j=> Tree.center (down j z) s
     have hc(p:Branches U R (f:=f) r): express R q k (fun i:Σ j:Fin n,Unit=> ((Tree.center (Tree.down i.1 z) s))) (fun i=>echoTags U R v p i.1) (Tree.center z s)=express R q k z' (echoTags U R v p) (Tree.center z s):= by
           let w:=echoTags U R v p; let e:= Equiv.sigmaUnique (Fin n) (fun _=>Unit)
           exact express_perm (I:=Σ j:Fin n,Unit) (J:=Fin n) R e q k z' w (Tree.center z s)
     -- unpack all positions, preserving product of amplitudes exactly
     let A:=(fuse (lamps (z:=z) (v:=v) U R r)); change (∑ p:A.Draw,(A.pick p).issue R q k (Tree.center z) s) = ∑ p:Branches U R (f:=f) r,(∏ j:Fin n, (flash U R (f j) (down j z) (childWages j v) (p j) s)) * _
     let e: A.Draw ≃ Branches U R (f:=f) r:= Equiv.refl _
     refine Fintype.sum_equiv e (fun p:A.Draw=>(A.pick p).issue R q k (Tree.center z) s) (fun p=> (∏ j,flash U R (f j) (down j z) (childWages j v) (p j) s)*factor U R z v p k s) ?_ 
     intro p; refine congr_arg ((A.pick p).amp s *·) (express_reindex (z:=z') (w:=echoTags U R v p) R (show (A.pick p).Slot ≃ Fin n from Equiv.sigmaUnique (Fin n) (fun _=>Unit)) rfl rfl)
end Fork

variable {N:ℕ}{g:Fin N→Tree}
def rollCaps (D:(Tree.fork N g).Inner→ℕ)(j:Fin N):ℕ:=boundNow (g j) (Tree.childAge j D)

def nShot : (t:Tree) → Tree.Envelope L t → (v:t.Leaf→S.Tag) → (D:t.Inner→ℕ) → Stage U R (boundNow t D) t→ L→ℂ
 | bud,_,_,_,_,_=> 1
 | fork N g,Z,v,D,k,s=>∑ p:Branches U R (f:=g) (rollCaps D), (∏ i:Fin N,nShot (g i) (Tree.down i Z) (Tree.childWages i v) (Tree.childAge i D) (p i) s) * factor U R Z v p k.2 s

/-- Gains charged along every internal edge and also from the current tree's
root to its own parent. At the ultimate root omit the latter. -/
def gapAll : (t:Tree)→ℝ→(t.Inner→ℝ)→(t.Inner→ℕ)→ℝ→Prop
 | bud,_,_,_,_ => True
 | fork n f,b,e,D,g => let k:=e (Sum.inl ()); g ≤ ((D (Sum.inl ()):ℕ)+1:ℕ) * (k-b) ∧ ∀ i,gapAll (f i) k (childAge i e) (childAge i D) g
-- coercion syntax maybe Nat.add type; `gapAll t` expects `ℝ` infer

def gapBelow : (t:Tree)→(t.Inner→ℝ)→(t.Inner→ℕ)→ℝ→Prop
 | bud,_,_,_=>True
 | fork n f,e,D,g => ∀ i,gapAll (f i) (e (Sum.inl ())) (childAge i e) (childAge i D) g
lemma gapAll_below {t:Tree}{b:ℝ}{v':t.Inner→ℝ}{u:t.Inner→ℕ}{r:ℝ}(h:gapAll t b v' u r):gapBelow t v' u r:=by cases t with
 | bud=>trivial
 | fork=>exact h.2

-- outcome of the outer coefficient evaluation
variable (m:ℕ)(q:R.channels m)
variable {n:ℕ}{f:Fin n→Tree}{z:Tree.Envelope L (Tree.fork n f)} {v:(Tree.fork n f).Leaf→S.Tag}

def stacked (z:Tree.Envelope L (Tree.fork n f))(v:(Tree.fork n f).Leaf→S.Tag) (D:(Tree.fork n f).Inner→ℕ)(s:L) := ∑ p:Branches U R (rollCaps D), (∏ i,nShot U R (f i) (Tree.down i z) (Tree.childWages i v) (childAge i D) (p i) s) * factor U R z v p q s

end YM.OPE.Nesting.Composite

import YM.OPE.Nesting.Profiles

/-! The homogeneous basis isn't asserted elementwise fixed under O(4) –
each entire finite-grade component is equivariant; the same rotations on
both kinds of child computations really do compose under the finite sums.
Thus no preferred axes of the price comparisons have been reintroduced by
those evaluations. We also retain the physical real structure in this sense. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting.Motion
open Orbits Orbits.Reader Function Filter Extraction Set Table Measures Menu Atom MeasureTheory Finset TopologicalSpace Composite
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
open Tree
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
local notation "X"=>U.sector.turns
local notation "Q"=>U.sector.derivatives
local notation "ρ"=>U.room.kernel.spin

-- covariance of full tested discrepancy for all Euclidean motions, where both words fit
section Word
variable {I J:Type}[Fintype I][Fintype J]{d:I→ℕ}{e:J→ℕ}{x:I→E4}{o:E4}{y:J→E4}
lemma whole_roll {T:Table C.book}(ht:U.sector.turns.Oriented T) (g:Ortho)(v:Labels S d)(w:Labels S e) (he:Injective (beside x y)):
     whole T (Ortho.move g ∘ x) (roll X g v) (Ortho.move g ∘ y) (roll X g w) = whole T x v y w :=by
     unfold whole
     convert roll_observes X g ht (a:=Orbits.stages v w) he using 1
     rw [show beside (Ortho.move g ∘ x) (Ortho.move g ∘ y)=Ortho.move g ∘ (beside x y) from funext fun ij=>by cases ij <;> rfl]
     apply congr_arg; funext j; cases j <;> rfl
lemma whole_shift {T:Table C.book}(h:T.Hierarchy){s:E4}(v:Labels S d)(w:Labels S e) (hi:Injective (beside x y)): whole T (fun i=>x i+s) v (fun j=>y j+s) w = whole T x v y w:=by
    unfold whole; apply Eq.trans _ (carrying h hi s (a:=Orbits.stages v w)); apply congr_arg (fun u=> moment T u (stages v w)); funext j; cases j <;> rfl
lemma whole_tint {T:Table C.book}(h:T.Hierarchy)(hh:T.respects S)(v:Labels S d)(w:Labels S e) (hi:Injective (beside x y)): whole T x (bar ρ v) y (bar ρ w) = star (whole T x v y w):=by
    unfold whole; apply Eq.trans _ (bar_observes U.room.kernel.spin (a:=Orbits.stages v w) h hh hi); apply congr_arg; funext j; cases j <;> rfl

variable {v:Labels S d}{w:Labels S e} (m:ℕ) (hi:Injective (beside x y))(he:Injective (beside (sole o) y)) (r:Viewers U)
include hi he

lemma formula_rotate (k:Ortho) :formula U R (Ortho.move k ∘ x) (Ortho.move k o) (roll X k v) (Ortho.move k ∘ y) (roll X k w) m r=formula U R x o v y w m r :=by
    let T:=spectator U r; have ht:U.sector.turns.Oriented T := by cases r with | none=> exact U.phase.transport.motion | some q=> exact U.phase.phase.sym q
    simp only [formula,← tested_fields U R]
    unfold balance; rw [whole_roll U ht k _ w hi]; apply congr_arg (_-·)
    refine Finset.sum_congr rfl fun j hj=>?_
    change whole T (sole _) _ _ _=whole T (sole _) _ _ _
    rw [R.rotate_fresh]; exact whole_roll U ht k (d:=fun _:Unit=>j.val) (sole _) w he
lemma formula_translate (s:E4):formula U R (fun j=> x j+s) (o+s) v (fun j=> y j+s) w m r=formula U R x o v y w m r :=by
    let T:=spectator U r; have ht:=spectate U r
    simp only [formula,←tested_fields U R]; unfold balance; rw [whole_shift ht v w hi]; apply congr_arg (_-·)
    refine Finset.sum_congr rfl (fun j hj=>?_); change whole T .. = whole T .. -- centered
    rw [R.fresh_transport]; exact whole_shift (x:=sole o) ht (sole (R.fresh j.val x o v):Labels S (fun _:Unit=>j.val)) w he
lemma formula_reality :formula U R x o (bar ρ v) y (bar ρ w) m r=star (formula U R x o v y w m r):=by
     let T:=spectator U r; simp only [formula,←tested_fields U R]; unfold balance; rw [star_sub,whole_tint U (spectate U r) (spectate_respects U r) v w hi] -- avoid starRingEnd_apply by `change`
     apply congr_arg ((star (whole (spectator U r) x v y w))-·); change (∑ j:Fin (m+1),(_ : ℂ)) = (starRingEnd ℂ) (∑ j:Fin (m+1),(upon T j.val o y w) (R.fresh j.val x o v)); rw [map_sum]; exact Finset.sum_congr rfl fun c hc=>(by change whole T .. =_; rw [R.real_fresh]; exact whole_tint U (spectate U r) (spectate_respects U r) (sole (R.fresh c.val x o v):Labels S (fun _:Unit=>c.val)) w he)
end Word

namespace Vector
variable {t:Tree}
abbrev Grade (t:Tree)(d:t.Leaf→ℕ)(D:t.Inner→ℕ):ℕ:=match t with
 | Tree.bud=> d ()
 | fork n f => Composite.boundNow (fork n f) D
lemma grade_bounds {d:t.Leaf→ℕ}{E:t.Inner→ℕ} (v:Labels S d)(q:Stage U R (boundNow t E) t): (token U R t (Nesting.chars v) q).fst ≤ Grade t d E:=by
     cases t with | bud => exact le_rfl | fork =>exact Nat.le_of_lt_succ q.1.isLt

private abbrev Starts (d:t.Leaf→ℕ) := (i:t.Leaf) → S.Field (d i)

variable {d:t.Leaf→ℕ}(z:Tree.Plot t)(v:Labels S d)(D:t.Inner→ℕ)

def pulse:= ∑ c:Stage U R (boundNow t D) t, (nShot U R t (still z) (Nesting.chars v) D c ()) • U.sector.derivatives.rise (grade_bounds U R v c) (token U R t (Nesting.chars v) c).snd
lemma pulse_bud {d:Tree.bud.Leaf→ℕ}(Z:Tree.Plot bud)(v:Labels S d)(d'):pulse U R Z v d'=v () :=by
    change (∑ c:Unit,nShot U R bud (still Z) (Nesting.chars v) d' c () • _)=_
    rw [Fintype.sum_unique]; exact (one_smul ℂ _ |>.trans (U.sector.derivatives.arrival R.continuum.laws.toSymmetric R.lifts _))

end Vector

variable {n:ℕ}{f:Fin n→Tree}{d:(fork n f).Leaf→ℕ}

abbrev underGrade (t:Tree)(d:t.Leaf→ℕ):=d
private def innerWords (j:Fin n)(v:Labels S d): Labels S (childWages j d) := fun v' => v ⟨j,v'⟩
private abbrev regions (d:(fork n f).Leaf→ℕ)(D:(fork n f).Inner→ℕ) := fun i=>Vector.Grade (f i) (childWages i d) (childAge i D)

def emitted (z:Tree.Plot (fork n f))(v:Labels S d)(D:(fork n f).Inner→ℕ) : Labels S (regions d D) := fun i=> Vector.pulse U R (childPlace i z) (innerWords i v) (childAge i D)
variable (z:Tree.Plot (fork n f)) (v:Labels S d)(D:(fork n f).Inner→ℕ)

lemma chord_vector (m:ℕ): ∑ q:R.channels m,(Kernel.chord U R z (Nesting.chars v) q D) • R.actor m q=R.fresh m (Tree.skyline z) (anchor z) (emitted U R z v D):=by
     -- First exchange the two finite sums. All incoming weights stay scalar coefficients of actual fields.
     unfold Kernel.chord Composite.stacked; let v':=Nesting.chars v
     let P:=Branches U R (f:=f) (rollCaps D); let Choices i:= Stage U R (boundNow (f i) (childAge i D)) (f i)
     let a (i:Fin n)(q:Choices i):=(nShot U R (f i) (still (childPlace i z)) (childWages i v') (childAge i D) q ())
     let b (i:Fin n) : ℕ:=Vector.Grade (f i) (childWages i d) (childAge i D)
     let r i (q:Choices i) : S.Field ((token U R (f i) (childWages i v') q).fst):= (token U R (f i) (childWages i v') q).snd
     have h(i:Fin n)(q:Choices i): (token U R (f i) (Tree.childWages i v') q).fst ≤ b i:= Vector.grade_bounds U R (innerWords i v) q
     let F(i)(q:Choices i): S.Field (b i) := U.sector.derivatives.rise (h i q) (r i q)
     let M:= R.fresh m (Tree.skyline z) (anchor z) (d:=b)
     have hM' (p:P): M (fun i=>F i (p i))=R.fresh m (Composite.echoPoints (still z) ()) (Tree.anchor z) (voices (echoTags U R v' p)) := R.fresh_inclusions (fun i=>h i (p i)) .. -- via rw?
     have hM(p:P): M (fun i=> a i (p i) • F i (p i))= ∑ q:R.channels m, ((∏ i:Fin n,a i (p i))*factor U R (still z) v' p q ()) • R.actor m q := by
         rw [M.map_smul_univ,hM',← R.assemble m (echoPoints (still z) ()) _ (anchor z),smul_sum]
         exact sum_congr rfl (fun i hi=> (mul_smul ..).symm)
     symm; calc
        _ = M (fun i:Fin n=>∑ q:Choices i,a i q • F i q):= rfl
        _ = ∑ p:P,M (fun i=> a i (p i) • F i (p i)):= by
           rw [M.map_sum_finset]; congr -- Fintype.piFinset=univ

        _ = ∑ p:P,∑ q:R.channels m, _:=Finset.sum_congr rfl (fun i hi=>hM i)
        _ = _ := by rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro q hq; exact (Finset.sum_smul ..).symm


lemma pulse_pack : Vector.pulse U R z v D = ∑ q:Fin (boundNow (fork n f) D+1), U.sector.derivatives.rise (d:=q.val) (Nat.le_of_lt_succ q.isLt) (R.fresh q.val (Tree.skyline z) (anchor z) (emitted U R z v D)) := by
    change (∑ p:Menu.Cut R (boundNow (fork n f) D), nShot _ _ _ (still z) _ _ p () • U.sector.derivatives.rise (d:=p.fst.val) (Nat.le_of_lt_succ p.fst.isLt) (R.actor p.fst.val p.snd)) = _ -- fix nShot ..
    rw [Fintype.sum_sigma]; apply Finset.sum_congr rfl fun j hj=>?_
    rw [← chord_vector,map_sum]; exact Finset.sum_congr rfl (fun i hi=> (map_smul ..).symm)

namespace Pulse
variable {t:Tree}{f:t.Leaf→ℕ}(z:Tree.Plot t) (d:Labels S f)(D:t.Inner→ℕ)
lemma shift (s:E4) : Vector.pulse U R (fun v=>z v+s) d D = Vector.pulse U R z d D:=by
    induction t with
    | bud=> rw [Vector.pulse_bud,Vector.pulse_bud]
    | @fork n f ih=>
        have hi:(emitted U R (fun v=>z v+s) d D)=emitted U R z d D:=funext (fun i=> ih i (childPlace i z) (innerWords i d) (childAge i D))
        rw [pulse_pack,pulse_pack,hi]; refine Finset.sum_congr rfl fun j hj=>?_; apply congr_arg _ (R.fresh_transport (x:=skyline z) (s:=s) ..)
lemma shadow : Vector.pulse U R z (bar ρ d) D = S.conj ρ _ (Vector.pulse U R z d D) :=by
    induction t with
    | bud => erw [Vector.pulse_bud,Vector.pulse_bud]; rfl
    | fork n f ih =>
        have h:emitted U R z (bar ρ d) D=bar ρ (emitted U R z d D) :=funext (fun i=> ih i (childPlace i z) (innerWords i d) (childAge i D))
        rw [pulse_pack,pulse_pack,h,map_sum]; exact Finset.sum_congr rfl (fun j _=>(R.stands.realInc .. |>.trans (congr_arg _ (R.real_fresh ..).symm))|>.symm)
lemma turn (k:Ortho): Vector.pulse U R (Ortho.move k ∘ z) (roll X k d) D = U.sector.turns.act _ k (Vector.pulse U R z d D) :=by
    induction t with
    | bud=>erw [Vector.pulse_bud,Vector.pulse_bud]; rfl
    | fork n f ih=>
        have h:emitted U R (Ortho.move k ∘ z) (roll X k d) D= roll X k (emitted U R z d D):=funext (fun i=> ih i (childPlace i z) (innerWords i d) (childAge i D))
        rw [pulse_pack,pulse_pack,h,map_sum]; refine Finset.sum_congr rfl fun j hj=>?_
        rw [R.law.filtered]; apply congr_arg; exact R.rotate_fresh (x:=skyline z) (k:=k) .. -- arguments clarify
end Pulse

variable (m:ℕ)
local notation "join" a h => (∑ c:R.channels m,Kernel.chord U R a (Nesting.chars h) c D • R.actor m c)
def stackVector := ∑ c:R.channels m,Kernel.chord U R z (Nesting.chars v) c D • R.actor m c
lemma stacked_shift (s:E4):stackVector U R (fun i=>z i+s) v D m=stackVector U R z v D m:=by
    have he:(emitted U R (fun u=>z u+s) v D)=emitted U R z v D:=funext (fun i=> Pulse.shift U R (Tree.childPlace i z) (innerWords i v) (childAge i D) s)
    rw [stackVector,chord_vector,stackVector,chord_vector,he]; exact R.fresh_transport (x:=skyline z) (s:=s) ..
lemma stacked_shadow: stackVector U R z (bar ρ v) D m= S.conj ρ m (stackVector U R z v D m) :=by
    have he:emitted U R z (bar ρ v) D = bar ρ (emitted U R z v D):=funext (fun i=>Pulse.shadow U R (Tree.childPlace i z) (innerWords i v) (childAge i D))
    rw [stackVector,chord_vector,stackVector,chord_vector,he]; exact R.real_fresh ..
lemma stacked_turn(k:Ortho) : stackVector U R (Ortho.move k ∘ z) (roll X k v) D m= U.sector.turns.act _ k (stackVector U R z v D m) :=by
    have he:emitted U R (Ortho.move k ∘ z) (roll X k v) D= roll X k (emitted U R z v D):=funext (fun i=>Pulse.turn U R (Tree.childPlace i z) (innerWords i v) (childAge i D) k)
    rw [stackVector,chord_vector,stackVector,chord_vector,he]; exact R.rotate_fresh (x:=skyline z) (k:=k) ..

end YM.OPE.Nesting.Motion

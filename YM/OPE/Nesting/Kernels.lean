import YM.OPE.Nesting.Actual

/-!
# Positions in finite trees and local smoothness on the admissible aperture

Use the canonical path of length `Unit` to write the already defined finite
`Composite.stacked` as a point-position function too. Prove locality (all
paths feed that same expression), not a new prescription. Variable Reader
here is already AFTER all physical limit choices. Both the immediate-child
collars at all finite required orders and the complete raw direct reader
collar fit eventually. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table Measures Menu Atom MeasureTheory Composite
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
namespace Tree


abbrev Plot (t:Tree) := t.Positions→E4
abbrev anchor {t:Tree}(z:Tree.Plot t):E4:= z t.topSeat
abbrev profile {t:Tree}(z:Tree.Plot t):(t.Leaf → E4):= z ∘ t.leafSeat
abbrev skyline {n:ℕ}{f:Fin n→ Tree}(z:Tree.Plot (fork n f))(i:Fin n):= anchor (childPlace i z)
def still {t:Tree}(z:Tree.Plot t): Tree.Envelope Unit t:=fun _=>z
variable {L:Type}
lemma echoPoints_at {n:ℕ}{f:Fin n→Tree}(z:Tree.Envelope L (fork n f))(s:L): Composite.echoPoints z s=skyline (z s):=rfl
lemma center_at {t:Tree}(z:Envelope L t)(s:L): Tree.center z s=(anchor (z s)):=rfl
end Tree
open Tree
variable {L I J:Type}{n:ℕ}{t:Tree}{f:Fin n→Tree}
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)

namespace Kernel
def output (z:Tree.Plot t)(v:t.Leaf→S.Tag){m:ℕ}(c:R.channels m) := R.coef m c (Tree.profile z) (voices v) (anchor z)
def chord (z:Tree.Plot (fork n f))(v:(fork n f).Leaf→S.Tag){m:ℕ}(c:R.channels m)(D:(fork n f).Inner→ℕ):=Composite.stacked U R m c (still z) v D ()
def pipe [Fintype J] (z:Tree.Plot t)(v:t.Leaf→S.Tag)(r:Viewers U)(m:ℕ)(y:J→E4)(w:J→S.Tag):=formula U R (Tree.profile z) (anchor z) (voices v) y (voices w) m r
def normData [Fintype J] (z:Tree.Plot t)(v:t.Leaf→S.Tag)(m:ℕ)(y:J→E4)(w:J→S.Tag):U.α.unselected.algebra:= algebraError U R (Tree.profile z) (anchor z) (voices v) y (voices w) m
def cardPanel (z:Tree.Plot t)(y:J→E4): Loc (t.Leaf) J:= ⟨Tree.profile z,(anchor z),y⟩

def aperture : (t:Tree)→ℕ→(t.Inner→ℕ)→Set (Tree.Plot t)
 | bud,_,_,_=>True
 | fork n f,m,D,z=> (∀ u:Fin (m+1),orbitMargin R.port u.val (skyline z) (anchor z)) ∧ ∀i, aperture (f i) (rollCaps D i) (childAge i D) (childPlace i z)

lemma resonant {z:Tree.Envelope L t}(v:t.Leaf→S.Tag)(D:t.Inner→ℕ) (p:Stage U R (Composite.boundNow t D) t)(s:L): nShot U R t z v D p s = nShot U R t (still (z s)) v D p () := by
       induction t with
       | bud=> rfl
       | fork n f ih=> dsimp [nShot]; rw [eq_comm]; refine Finset.sum_congr rfl fun i _=>?_; apply congr_arg (· *_) (Finset.prod_congr rfl fun j _=>(ih j (z:=down j z) (childWages j v) (childAge j D) (i j)|>.symm))
lemma resonantFork (z:Tree.Envelope L (fork n f))(v:(fork n f).Leaf→S.Tag){m:ℕ}(c:R.channels m)(D:(fork n f).Inner→ℕ)(s:L): Composite.stacked U R m c z v D s = chord U R (z s) v c D:=by
     unfold chord stacked; rw [eq_comm]; refine Finset.sum_congr rfl fun p _=>?_ ; refine congr_arg₂ (·*·) (Finset.prod_congr rfl (fun i _=> (resonant (z:=down i z) U R (childWages i v) (childAge i D) (p i) s).symm)) rfl

private lemma circle_cont (n:ℕ)(f:Fin n→Tree): ContDiff ℝ ∞ (fun z:Tree.Plot (fork n f)=> (skyline z, (anchor z))):=by
    apply ContDiff.prodMk (contDiff_pi.mpr (fun i:Fin n=>contDiff_apply ..)) (contDiff_apply ..)
private lemma opening_line (q:ℕ)(j:Fin n)(f:Fin n→Tree):ContDiff ℝ ∞ (fun z:Tree.Plot (fork n f)=>childPlace j z):= contDiff_pi.mpr (fun (i:(f j).Positions)=> contDiff_apply ℝ E4 (ι:=(fork n f).Positions) (Sum.inr ⟨j,i⟩))

lemma stencil (D:t.Inner→ℕ)(h:ℕ): IsOpen (aperture U R t h D) :=by
     induction t generalizing h with
     | bud=> exact isOpen_univ
     | fork n f ih=>
         apply isOpen_iff_mem_nhds.mpr fun z hz=> ?_
         have hp: ∀ᶠ z': Tree.Plot (fork n f) in 𝓝 z,∀ m:Fin (h+1),orbitMargin R.port m.val (skyline z') (anchor z'):= eventually_all.mpr (fun m=> (circle_cont n f|>.continuous.continuousAt.tendsto).eventually (p:=fun p=>(p∈ {p: (Fin n→E4) ×E4|orbitMargin R.port m.val p.1 p.2})) ((margin_open m.val).mem_nhds (hz.1 m)))
         refine ((Eventually.and hp) (eventually_all.mpr fun i:Fin n=>?_) : ∀ᶠ z': Tree.Plot (fork n f) in 𝓝 z, ((∀ m:Fin (h+1),_) ∧ ∀ i,aperture U R (f i) (rollCaps D i) (childAge i D) (childPlace i z'))) -- replace type
         apply (opening_line i.val i f).continuous.continuousAt.tendsto.eventually ((ih i _ _).mem_nhds (hz.2 i))

private lemma prod_smooth {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]
       {f:I→V→ℂ}{x:V}(s:Finset I)(h:∀ i∈s,ContDiffAt ℝ ∞ (f i) x):ContDiffAt ℝ ∞ (fun y=>∏ i∈s,f i y) x:=by
    induction s using Finset.induction with
    | empty=>simp only [Finset.prod_empty]; exact contDiffAt_const
    | insert j r hj ih=> simp only [Finset.prod_insert hj]; apply ContDiffAt.mul (h _ (Finset.mem_insert_self j r)) (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))

lemma chord_still {z:Tree.Plot t}{D:t.Inner→ℕ}(v:t.Leaf→S.Tag)(p:Stage U R (Composite.boundNow t D) t)(h:z∈aperture U R t (boundNow t D) D): ContDiffAt ℝ ∞ (fun z:Tree.Plot t=> nShot U R t (still z) v D p ()) z:=by induction t with
 | bud=>exact contDiffAt_const
 | fork n f ih=>
       dsimp [nShot]; refine ContDiffAt.sum (s:=Finset.univ) (f:=fun (q:Branches U R (rollCaps D))(z:Tree.Plot (fork n f))=> (∏ i,nShot U R (f i) (down i (still z)) (childWages i v) (childAge i D) (q i) ()) * factor U R (still z) v q p.snd ()) (fun q hq=>ContDiffAt.mul (prod_smooth Finset.univ ?_) ?_)
       · intro j hj; exact (ih j (z:=childPlace j z) (childWages j v) (q j) (h.2 j)).comp z (opening_line j.val j f).contDiffAt
       exact (R.coef_smooth p.fst p.snd (h.1 p.fst) (voices (echoTags U R v q))).comp z (circle_cont n f).contDiffAt

lemma chord_smooth {z:Tree.Plot (fork n f)}(v:(fork n f).Leaf→S.Tag){m:ℕ}(c:R.channels m)(D:(fork n f).Inner→ℕ)(h:z∈aperture U R (fork n f) m D): ContDiffAt ℝ ∞ (fun z=> chord U R z v c D) z:=by
       unfold chord stacked
       refine ContDiffAt.sum (s:=Finset.univ) (f:=fun (q:Branches U R (rollCaps D))(z:Tree.Plot (fork n f))=> (∏ i,nShot U R (f i) (down i (still z)) (childWages i v) (childAge i D) (q i) ()) * factor U R (still z) v q c ()) (fun p hq=>ContDiffAt.mul (prod_smooth Finset.univ ?_) ?_)
       · intro i hi; exact (chord_still U R _ (p i) (h.2 i)).comp z (opening_line i.val i f).contDiffAt
       exact (R.coef_smooth _ c (h.1 (Fin.last m)) _).comp z (circle_cont n f).contDiffAt 

omit U R
lemma plot_smooth [Fintype J]:ContDiff ℝ ∞ (fun u:(Tree.Plot t) × (J→ E4)=>cardPanel u.1 u.2) :=by
    exact ((contDiff_pi.mpr (fun i:t.Leaf=> ((contDiff_apply ..).comp contDiff_fst))) : ContDiff ℝ ∞ (fun u:(Tree.Plot t) × (J→ E4)=>Tree.profile u.1)).prodMk (((contDiff_apply ℝ E4 t.topSeat).comp contDiff_fst).prodMk contDiff_snd)
private lemma duo_smooth:ContDiff ℝ ∞ (fun z:Tree.Plot t=>(Tree.profile z,(anchor z))):= (contDiff_pi.mpr fun i:t.Leaf=>(contDiff_apply ℝ E4 (t.leafSeat i))).prodMk (contDiff_apply ℝ E4 t.topSeat)
include U R
lemma output_smooth {z:Tree.Plot t}(v:t.Leaf→S.Tag){m:ℕ}(c:R.channels m)(h:orbitMargin R.port m (Tree.profile z) (anchor z)): ContDiffAt ℝ ∞ (fun z=>output U R z v c) z:=by
    have hp : ContDiff ℝ ∞ (fun z':Tree.Plot t=>(Tree.profile z',(anchor z'))):= by exact ContDiff.prodMk (contDiff_pi.mpr fun i:t.Leaf=>contDiff_apply ..) (contDiff_apply ..)
    exact (R.coef_smooth m c h (voices v)).comp z hp.contDiffAt

lemma collar_open (m:ℕ): IsOpen {z:Tree.Plot t| orbitMargin R.port m (Tree.profile z) (anchor z)} := (margin_open (P:=R.port) m).preimage (duo_smooth.continuous)

variable {L:Type}{l:Filter L}{T:L→ℝ}{t:Tree}{z:Envelope L t}{a:t.Inner→ℝ}{D:t.Inner→ℕ}{k:ℝ}(hT:Tendsto T l atTop)(hg:Regular l T t k a z)[l.NeBot]
include hT hg
lemma aperture_eventually (H:ℕ):∀ᶠ i in l,z i∈aperture U R t H D:=by induction t generalizing k H with
 | bud=>exact Eventually.of_forall fun _=>True.intro
 | fork n f ih=>obtain ⟨hz,hk,h₀⟩:=echo_room hg hT
                apply (eventually_all.mpr fun m:Fin (H+1)=>eventually_dock R.port h₀ hk.inject m.val).and (eventually_all.mpr fun i:Fin n=> ih i (D:=childAge i D) (hg.inside i) (rollCaps D i))

end Kernel
end YM.OPE.Nesting

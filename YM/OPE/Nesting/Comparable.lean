import YM.OPE.Nesting.Remit

/-!
# Local residue bound with room for undetected alternative weights

Works also when the root scale itself has zero exponential rate on the
subsequence (a much smaller descendant scale set the time); then only the
complete no-improvement estimate is charged at this node. Its readers
still fit, since the actual diameter goes to zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
variable {L I J:Type} {l:Filter L}{T:L→ℝ}{o:L→E4}{z:L→I→E4}
local notation "P₀" => R.port
local notation "Q" => U.sector.derivatives
local notation "X" => U.sector.turns
local notation "ρ" => U.room.kernel.spin

def oneTag (m:ℕ)(j:R.channels m): S.Tag:=⟨m,R.actor m j⟩
def soloView [Fintype J] (m:ℕ)(j:R.channels m)(o:E4)(r:Viewers U)(w:J→S.Tag)(y:J→E4):ℂ:= duet (spectator U r) (sole o) (sole (oneTag U R m j)) y w

def atomDelta [Fintype J] (A:Atom S L)(m:ℕ)(o:L→E4)(r:L→Viewers U)(w:J→S.Tag)(y:L→ J→E4)(i:L):ℂ:= A.sample (spectator U ∘ r) y w i - ∑ c:Menu.Cut R m, A.issue R c.1 c.2 o i * soloView U R c.1 c.2 (o i) (r i) w (y i)

def delta [Fintype J] (A:Menu S L)(m:ℕ)(o:L→E4)(r:L→Viewers U)(w:J→S.Tag)(y:L→J→E4)(i:L):ℂ:= A.atView (spectator U ∘ r) y w i - ∑ c:Menu.Cut R m, A.charge R c.1 c.2 o i * soloView U R c.1 c.2 (o i) (r i) w (y i)

structure Meets (l:Filter L)(T:L→ℝ)(z:L→I→E4)(o:L→E4)(a M:ℝ)(P:Menu S L):Prop where
    output (m:ℕ) (h:R.channels m): RateLE l T (P.charge R m h o) (M-m*a)
    tested {J:Type} [Fintype J] (w:J→S.Tag)(y:L→J→E4)(m:ℕ)(r:L→Viewers U) (b u:ℝ)(h_y:Kept l T b y)
       (h₀:Intervals l T u (fun i=>sole (o i)) y)(h_z:Intervals l T u z y)(hb:0≤u)(h:u≤b)(h':u ≤ a) : RateLE l T (delta U R P m o r w y) (M-(m+1:ℝ)*(a-u) + weightOf w*b)

def Comparable (l:Filter L)(T:L→ℝ)(z:L→I→E4)(a M:ℝ)(P:Menu S L):Prop :=
   ∀ c:P.Draw, (∃ h, (P.pick c).place=fun i=> z i ∘ h) ∧ Kept l T a (P.pick c).place ∧ RateLE l T (P.pick c).amp (M-(P.pick c).cost*a)

section Estimates
variable {a b u M:ℝ}{s:L→Viewers U} (hT:Tendsto T l atTop)[l.NeBot](h:Services C F S)

lemma Comparable.earns {A:Menu S L}(hp:Comparable l T z a M A)(hb:a ≤ b):Eligible l T z b A:= fun c=>⟨(hp c).1, (hp c).2.1.mono hb, _, (hp c).2.2⟩

variable [Fintype I][Fintype J]
include U hT h
lemma pulse_single {w:J→S.Tag}{y:L→J→E4}{j:ℕ}(p:R.channels j) (hp:Intervals l T u (fun i=>sole (o i)) y)(he:Kept l T b y) (hb:0≤u)(h':u≤ b):RateLE l T (fun i=>soloView U R j p (o i) (s i) w (y i)) (j*u+weightOf w*b):=by
   exact upon_cost U h hT s (voices w) hp he hb h' j (R.actor j p)
omit hT h in
lemma local_sum (A:Menu S L)(o:L→E4)(y:L→J→E4)(w:J→S.Tag)(s:L→Viewers U)(m:ℕ)(i:L): delta U R A m o s w y i = ∑ c:A.Draw,atomDelta U R (A.pick c) m o s w y i:=by
     unfold delta atomDelta Menu.atView Menu.charge; rw [Finset.sum_sub_distrib,Finset.sum_comm (f:=fun c (z:Menu.Cut R m)=> (A.pick c).issue R (z.1:Fin (m+1)) z.2 o i * soloView U R _ z.2 (o i) (s i) w (y i))] -- f param name?
     apply congr_arg (_-·) (Finset.sum_congr rfl (fun z _=>by rw [Finset.sum_mul]))
omit hT h in
lemma local_delta (A:Atom S L)(o:L→E4)(y:L→J→E4)(w:J→S.Tag)(s:L→Viewers U)(m:ℕ)(i:L):atomDelta U R A m o s w y i=A.amp i *formula U R (A.place i) (o i) (voices A.tags) (y i) (voices w) m (s i):=by
     unfold atomDelta formula Orbits.trunc Atom.sample Function.comp; rw [mul_sub]; apply congr_arg₂ (·-·) rfl (?_)
     change ∑ z:Menu.Cut R m,A.issue R ..*_ = A.amp i * ∑ z: Fin (m+1), ∑ t:R.channels z.val,_
     rw [Fintype.sum_sigma,Finset.mul_sum]; apply Finset.sum_congr rfl fun z _=>by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _=>mul_assoc _ _ _)

private def oneDish (A:Atom S L):Menu S L:=⟨Unit,inferInstance,fun _=>A⟩
private def blackDish (S:Table C.book)(L:Type):Menu S L:=⟨Empty,inferInstance,fun q=>nomatch q⟩

lemma tag_price {x:L→I→E4}{v:I→S.Tag}{w:J→S.Tag}{y:L→J→E4}(h_x:Kept l T a x)(h_y:Kept l T b y)(hp:Intervals l T u x y)(hu:0≤u)(hb:u≤b)(ha:u≤a): RateLE l T (fun i=>duet (spectator U (s i)) (x i) v (y i) w) (weightOf v*a + weightOf w*b):=by
    simp only [weightOf,duet,whole_observed,weighting (voices w),weighting (voices v)]
    rcases le_total a b with h'|h'; · exact viewer_cost U h.schedule _ _ hT s h_x h_y (hp.mono ha) (hu.trans ha) h'
    exact viewer_alt U h.schedule _ _ hT s h_x h_y (hp.mono hb) (hu.trans hb) h'

omit hT h [l.NeBot] in
lemma one_price (m:ℕ)(A:Atom S L)(o:L→E4)(j:R.channels m)(i:L): A.issue R m j o i = (oneDish A).charge R m j o i-(blackDish (C:=C) S L).charge R m j o i :=by
    change _=(∑ q:Unit, A.issue R m j o i) - ∑ q:(blackDish _ _).Draw,_; change _ = _ - ∑ q:Empty,_; rw [Fintype.sum_unique,Fintype.sum_empty,sub_zero]

variable {P:Menu S L}(A:Atom S L){k V:ℝ} -- k age, V total price
variable (hx:enveloped l T k z o)(hc:Tendsto (fun i=>away (z i) (o i)) l (𝓝 0))(hh:Comparable l T z k V (oneDish A))(ha:0≤k)
include R hx hc hh ha
lemma atom_ticket (m:ℕ)(j:R.channels m) : RateLE l T (A.issue R m j o) (V-m*k):=by
   obtain ⟨α,hα⟩:=(hh ()).1
   change A.place=_ at hα
   have hx₁ : enveloped l T k A.place o:= by rw [hα]; exact envelope_comp hx α
   have h_k:= (hh ()).2.1
   have h_p: RateLE l T A.amp (V-A.cost*k):=(hh ()).2.2
   rcases ha.eq_or_lt with ha | ha
   · subst k
     let A':= oneDish A; let A'':=blackDish (C:=C) S L
     obtain ⟨W,hW⟩:=Sensor.roomFor U R m
     have h₁: Eligible l T z 0 A':= by exact hh.earns (le_refl 0)
     have h₂: Eligible l T z 0 A'':= by intro k; change Empty at k; cases k
     have h_p:RateLE l T A.amp V:= h_p.mono (by rw [mul_zero, sub_zero])
     rw [mul_zero,sub_zero]; apply (Sensor.remit U R A' A'' j (hW m le_rfl) hT (W:=W) (show Agrees U l T z 0 0 W V A' A'' from ?_) h₁ h₂ hc le_rfl le_rfl).congr <| Eventually.of_forall fun i=> (one_price U R m A o j i).symm
     refine fun w y s hg hp hy=> ?_
     have hv:=tag_price (x:=A.place) (b:=0) (a:=0) (v:=A.tags) (w:=w) (s:=s) U hT (C:=C) h h_k hy (by rw [hα]; exact interval_comp hp α id) le_rfl le_rfl le_rfl
     simp only [mul_zero,add_zero] at hv
     refine ((h_p.mul hv).mono (b:=V) (add_zero _|>.le)).congr ?_
     filter_upwards with i; change A.amp _ * duet .. = (∑ q:Unit,_)-(∑ q:Empty,_)
     rw [Fintype.sum_unique,Fintype.sum_empty,sub_zero]; rfl
   let u(p:L):R.stratum m:= ⟨R.fresh m (A.place p) (o p) (voices A.tags),R.fresh_mem m _ _ _⟩
   letI : FiniteDimensional ℝ (R.stratum m):=Module.Finite.trans ℂ _
   let co:= (R.basis m).coord j |>.restrictScalars ℝ
   have hf:= fresh_price U R h hT (voices A.tags) hx₁ h_k ha m
   have hu := pay_fixed hT co (hf.transfer (G:=u) (Eventually.of_forall fun _=>le_rfl))
   exact (h_p.mul hu).mono (by change V - A.cost*k + (A.cost - (m:ℝ))*k≤_; linarith only [])

lemma atom_full {y:L→J→E4}{w:J→S.Tag}(h_y:Kept l T b y)(h₁:Intervals l T u (fun i=>sole (o i)) y)(h₂:Intervals l T u z y)
       (hu:0≤u)(hb:u≤b)(ha':u≤k)(m:ℕ): RateLE l T (atomDelta U R A m o s w y) (V-(m+1:ℝ)*(k-u)+weightOf w*b):=by
    obtain ⟨θ,hθ⟩:=(hh ()).1
    have hx₁:enveloped l T k A.place o := hθ ▸ envelope_comp hx θ -- orientation/elaboration
    have h_k:Kept l T k A.place:= (hh ()).2.1
    have h_p: RateLE l T A.amp (V-A.cost*k):=(hh ()).2.2
    let ξ:=V-(m+1:ℝ)*(k-u)+weightOf w*b
    obtain hi|he:= ha'.eq_or_lt
    · unfold atomDelta; refine RateLE.sub ?_ (RateLE.sum hT ?_) hT
      · exact (h_p.mul (tag_price U hT h h_k h_y (by rw [(show A.place=_ from hθ)]; exact interval_comp h₂ θ id) hu hb ha')).mono (by unfold Atom.cost; rw [hi]; apply Eq.le; ring)
      intro c hc'
      exact ((atom_ticket U R hT h A hx hc hh ha _ c.2).mul (pulse_single (w:=w) U R hT h c.2 h₁ h_y hu hb)).mono (by rw [hi]; apply Eq.le; ring)
    -- strict layer
    have ht:= balance_rate U R h hT (v:=voices A.tags) hx₁ h_k (hu.trans_lt he) s (voices w) h₁ h_y hu hb m he
    refine ((h_p.mul ht).mono (b:=ξ) (by unfold ξ _root_.YM.OPE.Nesting.Atom.cost weightOf; apply Eq.le; ring)).congr (Eventually.of_forall fun i=>?_)
    dsimp only; apply Eq.trans (congr_arg (A.amp i * ·) (tested_fields ..)); exact (local_delta U R A o y w s m i).symm

omit hx hh ha in
lemma Comparable.meets (P:Menu S L)(h₁:enveloped l T k z o)(h₃:0≤k)(hh:Comparable l T z k V P):Meets U R l T z o k V P:=by
       have hh(c:P.Draw):Comparable l T z k V (oneDish (P.pick c)):=fun k=> hh c
       constructor
       · intro m v; exact RateLE.sum hT (fun c _=> atom_ticket U R hT h (P.pick c) h₁ hc (hh c) h₃ m v)
       intros J _ w y m r b u hy hp hz hb he hi; let M:=V-(m+1:ℝ)*(k-u)+weightOf w*b
       exact (RateLE.sum (S:=Finset.univ) hT (fun q (_:q ∈ (Finset.univ:Finset P.Draw))=> atom_full U R hT h (P.pick q) h₁ hc (hh q) h₃ hy hp hz hb he hi m)).congr (Eventually.of_forall fun _=> (local_sum U R ..).symm)
end Estimates
end YM.OPE.Nesting

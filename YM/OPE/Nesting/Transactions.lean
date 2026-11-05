import YM.OPE.Nesting.Fission

/-!
# Finitely many changes of precision

At the step replacing branch j, the requested precision may pay ALL the
labels and amplitudes elsewhere in that comparison. Preceding substitutes
have already been chosen, but later, possibly much bigger auxiliary horizons
have not; only finite tasks are requested. No array has simultaneously all
horizons or asks one to grow with inverse lattice spacing. This calculus
expresses comparisons of exact limit-hierarchy readings (where a nonlinear
change of the model wouldn't suffice).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{B:Register G}{S:Table B}{L I J:Type}

/-- One family of terms is safe on a subset of the displayed locations. We
require an upper exponential price for the AMPLITUDES; this need not be zero
and instead can be charged before the next branch horizon is to be chosen. -/
def Eligible (l:Filter L)(T:L→ℝ)(z:L→I→E4)(b:ℝ)(A:Menu S L) : Prop :=
   ∀ c:A.Draw, (∃ f, (A.pick c).place=fun i=> z i ∘ f) ∧ Kept l T b (A.pick c).place ∧ ∃ r:ℝ, RateLE l T (A.pick c).amp r
variable {l:Filter L}{T:L→ℝ}
variable {n:ℕ}{f:Fin n→Tree}{a:ℝ}{ν:(fork n f).Inner→ℝ}{z:Envelope L (fork n f)}
variable {u b:ℝ}

lemma interval_plenum [Fintype I](A:I→Atom S L){y:L→J→E4}(h:∀ j, Intervals l T b (A j).place y): Intervals l T b (Atom.bundle A).place y:=by
    intro c hc; exact (eventually_all.mpr (fun (s:I)=> h s c hc)).mono fun i hi v k=>hi (show I from v.fst) v.snd k

include a
set_option maxHeartbeats 1000000 in
lemma Eligible.products [Fintype I] {σ:I→Fin n} (P:I→Menu S L) (hσ:Injective σ) (hT:Tendsto T l atTop)
       (h:∀ j,Eligible l T (down (σ j) z) b (P j)) (hb:((fork n f).topAge a ν) ≤ b) (hs:Regular l T (fork n f) a ν z): Eligible l T z b (fuse P):=by
      intro v
      choose α hα using (fun j=>(h j (v j)).1)
      choose γ hγ using (fun j=>(h j (v j)).2.2)
      refine ⟨⟨fun q=>(.inr ⟨σ q.fst,α q.fst q.snd⟩:(fork n f).Positions),?_⟩,?_,⟨∑ i,γ i,RateLE.prod hT (fun j _=>hγ j)⟩⟩
      · funext s q; rcases q with ⟨j,q⟩; exact congr_fun (congr_fun (hα j) s) q
      change Kept l T b (fun i (j:Σ k,((P k).pick (v k)).Slot)=>_) -- inference
      refine kept_sigma (I:=I) (p:=fun k=>((P k).pick (v k)).Slot) (m:=fun k=> ((P k).pick (v k)).place) (fun j=>(h j (v j)).2.1) (fun i j hj=>?_)
      rw [hα i,hα j]; exact interval_comp (hs.buffer (σ i) (σ j) (hσ.ne hj) |>.mono hb) (α i) (α j)
lemma Eligible.rested (P:Fin n→Menu S L)(i:Fin n) (hT:Tendsto T l atTop) (h:∀ j,Eligible l T (down j z) b (P j)) (hb:((fork n f).topAge a ν) ≤ b) (hs:Regular l T (fork n f) a ν z) : Eligible l T z b (rest P i):=by
     refine Eq.mpr ?_ (Eligible.products (ν:=ν) (b:=b) (fun j:RestIndex i=>P j.val) Subtype.val_injective hT (fun j=>h j.val) hb hs)
     unfold rest; congr 2; exact Subsingleton.elim ..
omit a
lemma Eligible.roomAcross [Fintype J] {z:L→I→E4}{P:Menu S L}(h:Eligible l T z b P) (c:P.Draw){y:L→J→E4}(hx:Intervals l T u z y)(hf:Kept l T b y)(hu:u≤b): ∀ᶠ i in l,Injective (beside ((P.pick c).place i) (y i)):= interval_inject (h c).2.1 hf (by obtain ⟨α,hα⟩:=(h c).1; rw [hα]; exact interval_comp hx α id) hu

variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Order}(U:Spec.Final C F S)
variable {T:L→ℝ}

/-- Weak agreement at assigned exponential precision, against EVERY fixed
choice of exterior labels across arbitrary admissible viewer and location
paths of the given rates. Nontrivial statement provided by complete kernel
estimates after limiting. Doesn't require discovery of the coefficients from
these tests. -/
def Agrees (l:Filter L)(T:L→ℝ)(z:L→I→E4)(u b W γ:ℝ)(A A':Menu S L):Prop:=
    ∀ {J:Type}[Fintype J](w:J→S.Tag)(y:L→J→E4)(r:L→Viewers U), weightOf w ≤ W → Intervals l T u z y → Kept l T b y → RateLE l T (fun i=>A.atView (spectator U ∘ r) y w i - A'.atView (spectator U ∘ r) y w i) γ
variable {W r γ:ℝ}{A B' D:Menu S L}{o:L→I→E4}
omit a
lemma Agrees.self : Agrees U l T o u b W r A A:=by intros J _ w y z _ _ _; simp only [sub_self]; exact RateLE.zero (X:=ℂ) l T r
lemma Agrees.then (hT:Tendsto T l atTop)(h:Agrees U l T o u b W r A B')(h':Agrees U l T o u b W r B' D):Agrees U l T o u b W r A D :=fun w y z p q he=> ((h w y z p q he).add (h' w y z p q he) hT).congr (Eventually.of_forall fun _=> sub_add_sub_cancel ..)
lemma Agrees.mono (h:Agrees U l T o u b W r A B') {W' :ℝ}(h₁:W'≤W)(h₂:r≤γ):Agrees U l T o u b W' γ A B':=fun w y z he hi hk=>h w y z (he.trans h₁) hi hk |>.mono h₂
include a
set_option maxHeartbeats 600000 in
lemma change_one {i:Fin n}(P P':Fin n→Menu S L)(h_eq: rest P i = rest P' i)(hg:Regular l T (fork n f) a ν z)(hb:((fork n f).topAge a ν) ≤ b)(hT:Tendsto T l atTop)(h:∀ j,Eligible l T (down j z) b (P j))(h':∀ j,Eligible l T (down j z) b (P' j))
      (h_use:∀ (q:(Menu.rest P i).Draw),∃ ζ:ℝ, RateLE l T ((rest P i).pick q).amp ζ ∧ Agrees U l T (down i z) ((fork n f).topAge a ν) b (W+ ((rest P i).pick q).cost) (r-ζ) (P i) (P' i)):
       Agrees U l T z ((fork n f).topAge a ν) b W r (fuse P) (fuse P') :=by
    intro J _ w y s p q he
    have h₁:= Eligible.products (σ:=id) P injective_id hT h hb hg; have h₂:= Eligible.products (σ:=id) P' injective_id hT h' hb hg
    let Z:= (rest P i).pick; let g (A:Menu S L) (q:(rest P i).Draw)(s':L) := taxi (Z q) (spectator U ∘ s) A y w s'
    refine (RateLE.sum (S:=Finset.univ) (a:=r) (f:=fun k t=>g (P i) k t - g (P' i) k t) hT (fun k _=>?_)).congr ?_
    swap -- reconstruct from fission
    · filter_upwards [eventually_all.mpr (fun c=>h₁.roomAcross c q he hb),eventually_all.mpr (fun c=>h₂.roomAcross c q he hb)] with d he he'
      change ∑ k,(g (P i) k d-g (P' i) k d) = _ - _
      rw [Finset.sum_sub_distrib]; exact congr_arg₂ (·-·) (taxi_formula P (spectator U ∘ s) i y w d (spectate U (s d)) he _ rfl).symm (taxi_formula P' (spectator U ∘ s) i y w d (spectate U (s d)) he' _ h_eq.symm).symm
    let y' (l:L):=beside ((Z k).place l) (y l); let w':= splice (Z k).tags w
    obtain ⟨ζ,hζ,hj⟩:= h_use k
    rw [show r=r-ζ+ζ from (sub_add_cancel ..).symm]
    refine ((hj w' y' s (by rw [splice_weight]; exact add_le_add le_rfl p |>.trans (add_comm ..|>.le)) ?_ ?_).mul hζ).congr (Eventually.of_forall fun t=> sub_mul ..)
    · apply Intervals.swap (pair_intervals ?_ (Intervals.swap (interval_comp q (fun t=>Sum.inr ⟨i,t⟩) id)))
      refine interval_plenum (fun j=>(P j.val).pick (k j)) (fun j=>?_)
      obtain ⟨φ,hφ⟩:= (h j.val (k j)).1; rw [hφ]; exact interval_comp (hg.buffer j.val i j.prop) φ id
    let g' : Eligible l T z b (rest P i):= Eligible.rested P i hT h hb hg
    exact ((g' k).2.1.chorus he (by obtain ⟨φ,hφ⟩:= (g' k).1; rw [hφ]; exact interval_comp (q.mono hb) φ id))
omit a
lemma enough {Z:Menu S L} {o:L→I→E4} (h:Eligible l T o b Z): ∃ W' γ:ℝ, ∀ k:Z.Draw, ∃ ζ:ℝ, RateLE l T ((Z.pick k).amp) ζ ∧ (Z.pick k).cost + W ≤ W' ∧ γ≤r-ζ :=by
   obtain ⟨W',hw'⟩:= (Set.finite_range (fun k=>(Z.pick k).cost+W)).bddAbove
   choose z hz using fun k=>(h k).2.2
   obtain ⟨R,hR⟩:= (Set.finite_range z).bddAbove
   exact ⟨W',r-R,fun k=> ⟨z k, hz k, hw' (mem_range_self _), sub_le_sub_left (hR (mem_range_self _)) _⟩⟩
include a
lemma sequential (P:Fin n→Menu S L)(good:(i:Fin n)→Menu S L→Prop)
       (hg:Regular l T (fork n f) a ν z)(hb:((fork n f).topAge a ν) ≤ b)(hT:Tendsto T l atTop)(h:∀ j,Eligible l T (down j z) b (P j))
       (h_pick : ∀ j W' r', ∃ B:Menu S L,good j B ∧ Eligible l T (down j z) b B ∧ Agrees U l T (down j z) ((fork n f).topAge a ν) b W' r' (P j) B) :
       ∃ P':Fin n→Menu S L, (∀ j,good j (P' j)) ∧ Agrees U l T z ((fork n f).topAge a ν) b W r (fuse P) (fuse P') :=by
    let p:= (fork n f).topAge a ν
    have hell(s:Finset (Fin n)): ∃ P',Agrees U l T z p b W r (fuse P) (fuse P') ∧ (∀ j∈s, good j (P' j)) ∧ (∀ j,j∉s→P j=P' j) ∧ ∀ j, Eligible l T (down j z) b (P' j) :=by
       induction s using Finset.induction_on with
       | empty=>exact ⟨P,Agrees.self U,fun j h=> (Finset.notMem_empty _ h).elim,fun _ _=> rfl,h⟩
       | insert i s h_i hs =>
          obtain ⟨P',h',hf,eq,hgP⟩ := hs; let Z:= Menu.rest P' i
          obtain ⟨W',r',hZ⟩:= enough (Z:=Z) (W:=W) (r:=r) (Eligible.rested P' i hT hgP hb hg)
          obtain ⟨B,he,hE,hi⟩:= h_pick i W' r'; rw [eq i h_i] at hi
          let Q (j:Fin n):= if j=i then B else P' j
          have hV:∀j,Eligible l T (down j z) b (Q j):=by intro j; unfold Q; split_ifs with hh; subst j; exact hE; exact hgP j
          refine ⟨Q,Agrees.then U hT (by exact h') (change_one U (i:=i) P' Q ?_ hg hb hT hgP hV ?_), ?_,?_,hV⟩
          · exact rest_eq i (fun j h=>by simp [Q,h])
          · intro k; rw [show Q i=B from if_pos rfl]
            obtain ⟨ζ,hz,he₁,he₂⟩:= hZ k; exact ⟨ζ,hz,Agrees.mono U (by exact hi) ((add_comm ..).le.trans he₁) he₂⟩
          · simp_rw [Finset.mem_insert]; rintro j (rfl|hj); · simpa [Q] using he
            have hh : j≠i:= fun h=> h_i (h ▸ hj); simpa [Q,hh] using hf j hj
          intro j h; obtain ⟨hh,hj⟩:= not_or.mp (show ¬(j=i∨j∈s) from by simpa using h); simpa only [Q,if_neg hh] using (eq j hj)
    obtain ⟨P',h',hG,hH,ht⟩:=hell Finset.univ
    exact ⟨P', fun j=>hG j (Finset.mem_univ _), h'⟩
end YM.OPE.Nesting

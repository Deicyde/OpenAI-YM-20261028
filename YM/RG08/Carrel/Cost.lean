import YM.RG08.Carrel.Polar

/-! # Canonical completion's cutoff Lipschitz bill, no recurrence -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Carrel
open Camera Cloud Room Glyph Lattice Laurent Forms Pert.Bulk Isles Packets Filter Finset Function RG Extra.Iteration
open Rudder
open scoped Topology ContDiff Classical BigOperators ENNReal
variable {G:Gauge}{k n:ℕ}{F V:Rudder.Raw G.ColorIndex n}{σ p d:ℝ}

private lemma wedge_sub {P : Side} (f g:Still (Bedge G P))(i:Bedge G P)(h:Pace f)(k:Pace g):Camera.wedge i (f-g)=ᶠ[𝓝 0]Camera.wedge i f-Camera.wedge i g:=(Filter.Eventually.and (Pace.diff h) (Pace.diff k)).mono fun x ⟨hi,hj⟩=>by unfold Camera.wedge;rw [fderiv_sub hi hj];rfl
variable {I:Type}[Fintype I]
lemma deck_same {f g:Still I}(n:ℕ)(h:f=ᶠ[𝓝 0] g):Camera.deck n f=Camera.deck n g:=by
 induction n generalizing f g with
 | zero=>ext x; exact h.self_of_nhds
 | succ n ih=>ext x;unfold Camera.deck;rw [ih (wedge_eq _ h)]
lemma deck_sub (n:ℕ){f g:Still I}(h:Pace f)(he:Pace g):Camera.deck n (f-g)=Camera.deck n f-Camera.deck n g:=by
 induction n generalizing f g with
 | zero=>rfl
 | succ n ih=>
   ext x
   change _* Camera.deck _ _ _=_*_ -_*_
   rw [deck_same (n:=n) (((Pace.diff h).and (Pace.diff he)).mono (fun a ⟨hi,hj⟩=>show Camera.wedge (x 0) (f-g) a=(Camera.wedge _ f-Camera.wedge _ g) a by unfold Camera.wedge;rw [fderiv_sub hi hj];rfl)),ih (Pace.wedge _ h) (Pace.wedge _ he)];simp [mul_sub]

omit [Fintype I] in -- maybe var not inferred
theorem taped (A B:Flake n (Market (Rayk G 2)))(o:Fin n)(x:Coord (n:=n))(k:ℕ):stored (deposit (A-B) o x) k=stored (deposit A o x) k-stored (deposit B o x) k:=by
 let a:=deposit A o x; let b:=deposit B o x; let c:=deposit (A-B) o x
 let P:=attic a.length
 have he:c.coeff=a.coeff-b.coeff:=by ext j;change (if _ then (A-B) (join x j) else _) = _-_; simp only [a,b,deposit,neck,Pi.sub_apply];split_ifs <;> simp
 have hh : showAtom c (0:Site P)=showAtom a 0-showAtom b 0:=by
    ext j; simp only [showAtom,Atom.unmasked,Atom.poly,he,sub_mul,Pi.sub_apply,Finset.sum_sub_distrib];rfl
 have hc (a:Atom G n):Pace (showAtom a (0:Site P)):=by obtain ⟨C,hC,H⟩:=per_atom G n 1 (by positivity : 0<(1:ℝ));exact (H a _ _).analytic
 ext W
 change (∑ j:Tape k (Bedge G P), if W= (reach ∘ j) then Camera.deck k (showAtom c (0:Site P)) j else 0)=_-_
 rw [hh,deck_sub k (hc a) (hc b)]
 unfold stored;change _=(∑ j:Tape k (Bedge G P), if W=(reach ∘ j) then _ else 0)-(∑ j:Tape k (Bedge G P),if W=(reach ∘ j) then _ else 0);rw [←sum_sub_distrib];apply Finset.sum_congr rfl;intro j _;split_ifs <;> simp; rfl

variable (F V)
omit [Fintype I] in
lemma spares (o:Fin n)(k:ℕ)(hp:0≤p)(hs:0<σ)(he:Held (carpet _) σ p F)(hh:Held (carpet _) σ p V):
    mass (deposit (Anchor.compress 2 (F-V)) o) k= mass (deposit (Anchor.compress 2 F) o) k - mass (deposit (Anchor.compress 2 V) o) k:=by
 let A:=Anchor.compress 2 F;let B:=Anchor.compress 2 V
 let U (A:Flake n (Market (Rayk G 2)))(x:Coord (n:=n)):=stored (deposit A o x) k
 obtain ⟨C,hC,H⟩:=fleet G n k (σ:=σ/(n:ℝ)) (by have h:0<(n:ℝ):=Nat.cast_pos.mpr o.pos; positivity)
 have h(Ψ:Flake n (Market (Rayk G 2)))(ht:Held (carpet _) σ p Ψ)(x:Slide (Rayk G 1) k):Summable (fun b=>U Ψ b x):=((H (paid Ψ o hs hp ht)).tip (by positivity)).comp_injective (i:=fun y=>(y,x)) (fun _ _ h=>Prod.mk.inj h|>.1)
 rw [Anchor.compress_sub];ext x
 change (∑' b:Coord (n:=n),U (A-B) b x)=_-_
 rw [tsum_congr (fun b=>congrFun (taped A B o b k) x)]
 exact (h A (Anchor.compress_cost _ he) x).tsum_sub (h B (Anchor.compress_cost _ hh) x)

omit [Fintype I] in
lemma cracks (o:Fin n)(j:Fin k)(hp:0≤p)(hs:0<σ)(he:Held (carpet _) σ p F)(hh:Held (carpet _) σ p V):
    completed (F-V) o k=completed F o k-completed V o k:=by
 unfold completed;rw [spares F V _ _ hp hs he hh]
 let η := σ/(n:ℝ)
 have hη : 0<η:=div_pos hs (Nat.cast_pos.mpr o.pos)
 obtain ⟨C,hC,H⟩:=fleet G n k hη
 unfold mass;rw [grown_sub (paidC.books (H (paid (Anchor.compress 2 F) o hs hp (Anchor.compress_cost _ he)))) (paidC.books (H (paid (Anchor.compress 2 V) o hs hp (Anchor.compress_cost _ hh)))) (by unfold η; positivity) j,←bleach_sub];congr 1;unfold Carrel.average;rw [←smul_sub,←sum_sub_distrib];apply congrArg;apply Finset.sum_congr rfl;intro i _;ext u;simp [adjust,mul_sub]


omit [Fintype I] in
/-- Positive rank fields only. -/
theorem repeated (G:Gauge){n k:ℕ}{σ:ℝ}(o:Fin n)(j:Fin k)(hs:0<σ):
 ∃ D:ℝ,0≤D∧∀ (F V:Rudder.Raw G.ColorIndex n)(q d:ℝ), 0≤q→ 0≤d→ Held (carpet _) σ q F→Held (carpet _) σ q V→ Held (carpet _) σ d (F-V)→
    Held (carpet _) (σ/n/32) (D*d) (completed F o k-completed V o k):=by
 obtain ⟨D,hD,H⟩:=completed_held G k o hs
 refine ⟨D,hD,fun F V q d hq hd h h' H'=>?_⟩
 rw [←cracks F V o j hq hs h h'];exact (H _ hd H').1

omit [Fintype I] in
theorem complete_top (o:Fin n)(h:Rudder.Symmetry.Cloak (Symmetry.dressed G n) 2 F)(he:Held (carpet _) σ p F)(hp:0≤p)(hs:0<σ):
 completed F o n = Anchor.compress 1 (picture G.ColorIndex n F):=by
 obtain ⟨D,hD,H⟩:=completed_held G n o hs
 obtain ⟨jc,jk,j⟩:=H F hp he
 have hy:= (Spar.photograph (NextTo.unit hs hp h.path he o.pos)).cohort
 apply crystals (σ:=σ/n/32) (τ:=σ/2) o (by have hi:0<(n:ℝ):=Nat.cast_pos.mpr o.pos; positivity) (by positivity) j (Anchor.compress_path _ hy) jk _ jc (Anchor.compress_cost _ (Spar.encode o.pos hs hp h.path he))
 · intro P _ z;apply emerged o h.path he hs hp _ z;intro s;rw [adjust_compress,←Symmetry.picture_orbit s h.field', h.firm s]
 apply Anchor.compress_sym
 intro i;rw [←Symmetry.picture_woven, h.beam i]
end YM.RG08.Carrel

import YM.RG08.Trill.Bags
import YM.RG08.Trill.Lace
/-! # Wilson alphabet (pinned offshell Frame and derivative chart). Exact through prescribed
 horizon. Own-g coefficient crossing from charged slot germs. No quotient.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Trill
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius
variable {G:Gauge}{d n p l e D k i:ℕ}{σ B:ℝ}
local notation "E"=>Ed G Cover
local notation "Y"=>Snap G d
/-- compatible (X.n,ν) joint. no stress quotient. -/
structure Cue (d:ℕ) where
 play : pedal
 held : weight play ≤ d

structure Accent (X:Labels.Frame G d) where
 ear : X.Index
 test : Cue d
 joint : (X.grades ear).1+weight test.play ≤ d

namespace Cue
noncomputable instance : Fintype (Cue d):=by
 let f(x:Cue d)(j:Axis):Fin (d+1):=⟨x.play j,Nat.lt_succ_of_le ((single_le_sum (f:=x.play) (fun _ _=>Nat.zero_le _) (mem_univ j)).trans x.held)⟩
 refine Fintype.ofInjective f fun a b h=>?_ ;cases a;cases b;congr; funext i;exact congrArg (fun (x:Axis→Fin (d+1))=> (x i).val) h
end Cue
namespace Accent
noncomputable instance {X:Labels.Frame G d}: Fintype (Accent X):=by
 refine Fintype.ofInjective (fun (i:Accent X)=> (i.ear,i.test)) (fun a b h=>?_);cases a;cases b;simpa using h -- equality
end Accent
variable (X:Labels.Frame G d)
/-- individual contribution from rank n at peer d -/
def pix (i:X.Index)(v:pedal)(F:Gras G n):ℝ:=tally X (X.grades i).2 (X.grades i).1 i (harrow F (celloTest v) (X.grades i).2 d)
/-- normalized formal Wilson stencil bracket of sec kforms. Evaluating arbitrary horizon h
 rooted at own coupling. hg already factored out of charge. Coordinates REAL.
 Iteration uses common currency via ratio resets. -/
def project (P:GrainS (Ed G Cover))(e:ℕ)(c:Accent X):ℝ:=
 let l:=(X.grades c.ear).2;∑ n∈range (l+1),if l-n≤e then pix X c.ear c.test.play (P (e-(l-n)) n) else 0
lemma project_split (P:GrainS (Ed G Cover))(e:ℕ)(c:Accent X): project X P e c =
 let l:=(X.grades c.ear).2; (∑ n∈range l,if l-n≤e then pix X c.ear c.test.play (P (e-(l-n)) n) else 0) + pix X c.ear c.test.play (P e l):=by
 unfold project;rw [sum_range_succ,Nat.sub_self,if_pos (Nat.zero_le _),Nat.sub_zero]
lemma pix_def (P:GrainS (Ed G Cover))(he:Calls l P)(hs:Permit D l P)(H:Hol G)(v:pedal)(i:X.Index):
 (pix X i v (P e n):ℂ)=X.coords (stocked he hs H (celloTest v) e n (X.grades i).2 d) i:=used ..
-- in estimates all isometry to Labels bounded pre. one horizon-all.
variable {F:Gras G n}{P:GrainS (Ed G Cover)}
lemma pix_prize (D:ℕ)(σ:ℝ)(h:0<σ):∃ C:ℝ,0≤C ∧ ∀ n≤d,∀ F:Gras G n,∀ B:ℝ,0≤B→Lyrics F→Sings (stance _) D h F B → ∀ i:X.Index,∀ v: Cue d,|pix X i v.play F|≤C*B:=by
 choose E' hE H using fun (a:Fin (d+1)×X.Index× Cue d)=>grant_price G d a.1.val (X.grades a.2.1).2 (X.grades a.2.1).1 σ h X a.2.1
 let V(a:Fin (d+1)×X.Index× Cue d):=E' a * Jetty.beam D h (celloTest a.2.2.play)
 have hv a:0≤V a:=mul_nonneg (hE _) (beam_nn ..)
 refine ⟨∑ a,V a,sum_nonneg fun a _=>hv a,fun n hn F B hp hF hu i v=>?_⟩
 let a:Fin (d+1)×X.Index×Cue d:=(⟨n,by omega⟩,i,v)
 apply (H a D F B hF hu hp (celloTest v.play)).trans; change E' a*B* Jetty.beam D h (celloTest v.play)≤_
 rw [mul_right_comm (E' a)];exact mul_le_mul_of_nonneg_right (single_le_sum (f:=V) (fun _ _=>hv _) (mem_univ a)) hp

-- linear in derivative test on exponential & #height packet, including all colors. real.
lemma grants_test (f:Pearl)(s:ℝ)(h:Lyrics F)(v:Y) : grants F (s • f) p d v=s • grants F f p d v:=by
 unfold grants;rw [smul_eq_mul,mul_sum];apply sum_congr rfl;intro t _
 unfold sonic tote;rw [←tsum_mul_left];apply tsum_congr; intro i;rw [(h i).2];ring
lemma harrow_test (f:Pearl)(s:ℝ)(he:Lyrics F){hs:0<σ}(hh:Sings (stance _) D hs F B)(hB:0≤B) : harrow F (s • f) p d=s • harrow F f p d:=by
 let Q:=harrow F f p d
 apply Tensor.ext_diag _ _ (harrow_sym he hh hB _) (fun v t=> congrArg (s • ·) (harrow_sym he hh hB f (p:=p) (d:=d) v t)); funext X
 rw [harrow_diag he hh hB,grants_test f s he];change s • _=s • Tensor.diagonal Q X;rw [harrow_diag he hh hB]
lemma cello_pal (s:Cargo p): Lagoon.pal s=(beta (Trill.capture s):ℝ) • celloTest (Trill.capture s):=by
 apply Subtype.ext;funext x
 rw [← capture_act]; change faceT (Trill.capture s) x=(beta (Trill.capture s):ℝ) * (celloTest (Trill.capture s)).val x;rw [cello_val,←mul_assoc,mul_inv_cancel₀,one_mul];exact_mod_cast beta_nz _
end YM.RG08.Trill
